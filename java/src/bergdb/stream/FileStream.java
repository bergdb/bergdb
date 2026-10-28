package bergdb.stream;

import java.io.EOFException;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.ByteBuffer;
import java.nio.channels.ClosedByInterruptException;
import java.nio.channels.ClosedChannelException;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.channels.OverlappingFileLockException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import bergdb.common.Bug;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.util.BadFormatException;

/**
 * An object of this class is an AppendOnlyStream that stores the stream data 
 * in one directory in the filesystem.
 * Multiple files are used to be able pretruncate (cut) the stream and reclaim disk space.
 * Files of sizes 200*1000, 1*M, 5*M, 20*M, 100*M, 500*M, 2*G, 10*G, 50*G, 200*G
 * are automatically chosen to store the stream. Decimal factors, M = 1,000,000 bytes.
 * Each file is named <14-digit index>.bergdb. The index is the file's first stream 
 * position divided by 100,000, padded with zeros (indexToString).
 * The first two files are: 00000000000000.bergdb, 00000000000002.bergdb.
 * 
 * Hard sync. Every append is forced to the device before it returns: the bytes are
 * written, then FileChannel.force(true) (F_FULLFSYNC on macOS, fsync on Linux). A new
 * file and its directory entry are forced before the file takes appends. So a completed
 * append means durable bytes, not only bytes in the OS cache, and StorageManager's
 * durable length, which sync() waits for, holds after a power loss, not only after a
 * process crash (2026-10-14, bergdb 011-07).
 * 
 * A force costs a device round trip: well under a millisecond on a fast SSD, more
 * on a slow virtual disk. This class is meant to be used below BufferedStream,
 * which controls the buffering: it collects the database's appends and writes them
 * here in chunks, from a thread of its own, when a buffer time has passed or its
 * buffer is full. So there is one force per chunk, not one
 * per transaction, and a transaction waits for a force only when it asks for a sync.
 * 
 * Reads wait for no write (2026-10-27, bergdb 005-46). A read takes no lock: it reads
 * with positional reads on a channel of the file's own, and finds its file in a list
 * that the writer replaces, never changes. The writer, its append and force, a new file
 * with its forces, and a cut, holds no lock that a read takes; a cut only takes its files
 * off the list, and a thread of its own deletes them, in the same order as before. Before,
 * a read of the last file waited for the writer's append and force, and every read for a
 * new file's forces and a cut's deletes; on a slow disk for seconds.
 * 
 * Interrupts (bergdb 005-46). No method of this class is interruptible: an interrupt of
 * the calling thread neither ends nor fails it, and the thread's interrupt flag is set
 * again when it returns. A channel that an interrupt closes during a read or a force
 * (FileChannel is interruptible) is opened again.
 * 
 * One stream per directory (2026-10-28, bergdb 005-63). The constructor takes an exclusive
 * lock on the file bergdb.lock in the directory before it reads anything, and close()
 * releases it, last. A second FileStream on the directory, in this JVM or in another process,
 * is refused with DirectoryInUseException; so is one while a database closes after stop().
 * The operating system holds the lock and drops it when the process ends, also at a crash,
 * so a lock is never stale; the file is never deleted, and its text is for people. The lock
 * is on one byte far beyond the end of the file: on Windows a lock is mandatory, and the text
 * stays readable. Within the JVM, a set of the locked directories (LOCKED_DIRS) refuses a
 * second FileStream before it opens the file: on macOS and Linux, closing any channel of the
 * file releases the process's lock (FileLock's Javadoc, "Platform dependencies"). That set is
 * global state, a deviation from bergdb 010-P9.
 * 
 * Network file systems. On NFS or SMB the server holds the lock. After a crash of the client,
 * the lock may stay until the server notices (NFSv4: a lease, typically 90 s), and starts on
 * the directory are refused until then. Some setups do not support locks: the constructor
 * then fails with an IOException, or, with NFS's mount option nolock, the lock refuses only
 * FileStreams on the same machine. The hard sync also depends on the server. Use a local
 * disk for a database.
 * 
 * @author Frans Lundberg
 */
public class FileStream implements AppendOnlyStream {
    private static final String SUFFIX = Util.identity(".bergdb");
    private static final long BYTES_PER_INDEX_UNIT = Util.identity(100*1000);
    private static final long M = 1000000L;
    private static final long G = 1000*M;
    
    /** 
     * Smallest possible file size and size that all other file sizes must be a multiple of.
     * This value must be a multiple of stream.RecoverableStream.META_BLOCK_DISTANCE.
     */
    private static final long SMALLEST_FILE_SIZE = Util.identity(200*1000);
    
    /** 
     * File sizes, x5-x4-x5 log scale, always a multiple of BYTES_PER_INDEX_UNIT. 
     */
    private static final long FILE_SIZES[] = new long[] {
        200*1000, 1*M, 5*M, 20*M, 100*M, 500*M, 2*G, 10*G, 50*G, 200*G
    };
    
    /** Factor to next larger file size. */
    private static final int[] FACTOR_UP = new int[] {
        5, 5, 4, 5, 5, 4, 5, 5, 4
    };
    
    /** File size index for 2G. */
    private static final int INDEX_2G = 6;
    
    /** The lock file, in the stream's directory (bergdb 005-63). */
    private static final String LOCK_NAME = "bergdb.lock";
    
    /** The locked byte, far beyond the end of the lock file. */
    private static final long LOCK_POS = 1L << 62;
    
    /** The lock file's text, written once, when the file is created. */
    private static final String LOCK_TEXT = 
            "This directory contains a BergDB database. BergDB locks this file\n"
            + "while a database has the directory open. The lock is held by the\n"
            + "operating system and ends with the process. Do not delete this file\n"
            + "while a database is open.\n";
    
    /**
     * The directories that FileStreams of this JVM hold, by lockKey() (bergdb 005-63). A
     * second FileStream on a directory is refused here, before it opens the lock file:
     * closing its channel would release the first's lock for other processes.
     */
    private static final Set<Object> LOCKED_DIRS = 
            Collections.synchronizedSet(new HashSet<Object>());
    
    private final File dir;
    private final FileStreamIo io;
    private volatile long firstPos = 0;
    private volatile long length = 0;
    private int fileSizeIndex = 0;
    private boolean renameAsDelete = false;
    private boolean max2G = false;
    
    /**
     * The .bergdb files of the stream, in order. Replaced under this, never changed, so that
     * a read takes it without a lock (bergdb 005-46). A file's first position is its spos.
     */
    private volatile DbFile[] dbFiles;
    
    /** The files a cut took off the list, to be deleted in order by the cut's thread. Under this. */
    private final ArrayDeque<DbFile> cutFiles = new ArrayDeque<DbFile>();
    
    /** The cut's thread while it runs, or null. Under this. */
    private Thread cutThread = null;
    
    /** If not null, this stream should be considered faulty and not used any further. */
    private volatile IOException ioException = null;
    
    /** The open lock file, which holds the directory's lock, or null. Under this. */
    private RandomAccessFile lockFile = null;
    
    /** This stream's key in LOCKED_DIRS while it holds the lock. Under this. */
    private Object lockKey = null;
    
    /**
     * Creates a new stream if it does not exist or opens an existing one if it exists.
     * If the directory 'dir' does not exist an attempt to create it is made.
     * 
     * @param dir
     *      The directory to use.
     * @throws IOException
     *      If existing directory cannot be read from / written to, or if 
     *      'dir' does not exist and cannot be created.
     * @throws DirectoryInUseException
     *      If another FileStream holds the directory, in this JVM or in another process
     *      (bergdb 005-63).
     * @throws BadDirStateException
     *      If the directory exists but the files in the directory
     *      are not in a valid state. The files in the directory were modified by some other software.
     */
    public FileStream(File dir) throws IOException {
        this(dir, new FileStreamIo());
    }

    /** 
     * Internal, for testing.
     * As FileStream(dir), with the given persistence boundary; for fault tests.
     */
    public FileStream(File dir, FileStreamIo io) throws IOException {
        if (dir == null) {
            throw new IllegalArgumentException("dir == null not allowed");
        }
        
        this.dir = dir;
        if (io == null) {
            throw new IllegalArgumentException("io == null not allowed");
        }
        this.io = io;
        try {
            createDirIfNeeded();
            lockDir();
            handleExistingFiles();
        } catch (IOException e) {
            closeAfterFailedOpen(e);
            throw e;
        } catch (RuntimeException e) {
            closeAfterFailedOpen(e);
            throw e;
        }
    }

    private void closeAfterFailedOpen(Throwable failure) {
        if (dbFiles != null) {
            for (DbFile file : dbFiles) {
                if (file != null && !file.isClosed) {
                    try { file.close(); } catch (IOException e) { failure.addSuppressed(e); }
                }
            }
        }
        try { unlockDir(); } catch (IOException e) { failure.addSuppressed(e); }
    }
    
    public void read(long spos, byte[] dest, int destOffset, int length) throws IOException {
        //
        // Sync comments. Reads take no lock and run beside each other and beside the writer
        // (bergdb 005-46). Before, reads of a file waited for each other (RandomAccessFile.seek())
        // and for the writer's append to it.
        //
        checkIOException();
        
        int actuallyRead;
        int leftToRead;
        
        while (true) {
            DbFile k = findFile(spos);
            if (k == null) {
                long first = getFirstPos();
                if (spos < first) {
                    // 2026-10-13 (bergdb 011-04, W1): a read admitted before a
                    // cut can come here. It fails alone; the stream is not faulty.
                    throw new ReadBelowFirstPosException("Cannot read at spos " + spos
                            + ", below the first position, " + first + ".");
                }
                this.ioException = new IOException("No file found for reading at spos " + spos + ".");
                throw ioException;
            }
    
            actuallyRead = k.read(spos, dest, destOffset, length);
            if (actuallyRead == 0 && length > 0) {
                // 2026-10-21 (bergdb 005-24): a read at the end of the stream read 0 bytes
                // and tried again forever. It throws, and the stream stays usable.
                throw new EOFException("Cannot read " + length + " bytes at spos " + spos 
                        + ", the end of the stream.");
            }
            leftToRead = length - actuallyRead;
            if (leftToRead == 0) {
                break;
            }
            
            spos += actuallyRead;
            destOffset += actuallyRead;
            length -= actuallyRead;
        }
    }

    public void append(byte[] source, int sourceOffset, int len) throws IOException {
        checkIOException();
        
        int actuallyAppended;
        int leftToAppend;
        
        while (true) {
            DbFile k = findLastFile();
            actuallyAppended = k.append(source, sourceOffset, len);
            length += actuallyAppended;
            leftToAppend = len - actuallyAppended;
            if (leftToAppend == 0) {
                break;
            } else {
                newFile();
            }
            
            sourceOffset += actuallyAppended;
            len -= actuallyAppended;
        }
    }

    public long getLength() {
        return length;
    }

    /**
     * Closes the files, after the cut's thread has deleted what the cuts so far took off
     * (bergdb 005-46), and then releases the directory's lock (bergdb 005-63). Throws the
     * stream's failure, such as a failed delete of a cut.
     */
    public void close() throws IOException {
        awaitCutThread();
        // An I/O failure must not prevent release of the remaining handles,
        // including handles left after a partially completed pretruncate.
        IOException failure = ioException;
        synchronized (this) {
            List<DbFile> all = new ArrayList<DbFile>(Arrays.asList(dbFiles));
            all.addAll(cutFiles);       // Left by a failed cut.
            for (DbFile file : all) {
                if (!file.isClosed) {
                    try {
                        file.close();
                    } catch (IOException e) {
                        if (failure == null) failure = e;
                        else if (failure != e) failure.addSuppressed(e);
                    }
                }
            }
        }
        try {
            unlockDir();
        } catch (IOException e) {
            if (failure == null) failure = e;
            else failure.addSuppressed(e);
        }
        if (failure != null) throw failure;
    }
    
    /**
     * Waits until the cut's thread has deleted the files of every cut so far, and throws the
     * stream's failure if there is one, such as a failed delete. For tests: pretruncate()
     * returns before the files are deleted (bergdb 005-46). Not interruptible.
     */
    public void awaitDeletes() throws IOException {
        awaitCutThread();
        checkIOException();
    }
    
    private void awaitCutThread() {
        boolean interrupted = false;
        synchronized (this) {
            while (cutThread != null) {
                try {
                    wait();
                } catch (InterruptedException e) {
                    interrupted = true;
                }
            }
        }
        if (interrupted) {
            Thread.currentThread().interrupt();
        }
    }

    /**
     * Returns the directory where the stream files are stored.
     */
    public File getDir() {
        return dir;
    }
    
    /**
     * Call this method with "true" to never use stream files larger than 2e9 bytes.
     * This is useful on file systems with a limited maximum file size; for example FAT32 
     * has a maximum file size of 2^32−1 (about 4.29e9 bytes).
     */
    public void setMax2G(boolean b) {
        synchronized (this) {
            this.max2G = b;
        }
    }
    
    public long getFirstPos() {
        return firstPos;
    }

    public synchronized void seekFirstPos(long pos) throws IOException {
        checkIOException();
        
        long len = this.length;
        
        if (pos < len) {
            throw new IllegalStateException("Cannot seek to " + pos 
                    + ", pos less than stream length (" + len + ").");
        }
        
        if (pos % SMALLEST_FILE_SIZE != 0) {
            throw new IllegalArgumentException("pos (" + pos 
                    + ") is not a multiple of " + SMALLEST_FILE_SIZE + ".");
        }
        
        awaitCutThread();
        deleteAllFiles();
        
        this.length = pos;
        this.firstPos = pos;
        
        dbFiles = new DbFile[0];
        newFile();
    }

    /**
     * Takes the files before 'pos' off the stream and returns; the cut's thread deletes them
     * (2026-10-27, bergdb 005-46). Before, this method deleted them, forcing the directory
     * after each, under the stream's monitor, which every read takes to find its file, and on
     * the thread of the commit that made the cut: every read and commit waited for the
     * whole cut, 88 to 171 ms in P4's soak (bergdb 009-04, section 7.3). A read of a file
     * taken off throws ReadBelowFirstPosException, as one of a deleted file did. A failed
     * delete is the stream's failure: the next read, append or cut throws it, and close().
     */
    public synchronized void pretruncate(long pos) throws IOException {
        checkIOException();
        
        int index = -1;      // index of last file to delete
        
        long len = getLength();
        if (pos > len) {
            throw new IllegalArgumentException("pos > length of stream (" + len + ").");
        }
        
        DbFile[] files = dbFiles;
        for (int i = 0; i < files.length; i++) {
            DbFile k = files[i];
            if (k.spos + k.fileLength - 1 < pos) {
                index = i;
            } else {
                break;
            }
        }
        
        if (index != -1) {
            int newSize = files.length - (index + 1);
            if (newSize < 1) {
                throw new Bug("Unexpected newSize: " + newSize + ". pos=" + pos 
                        + ", kfiles.length=" + files.length);
            }
            
            DbFile[] newFiles = new DbFile[newSize];
            System.arraycopy(files, index + 1, newFiles, 0, newSize);
            for (int i = 0; i <= index; i++) {
                files[i].isDeleted = true;      // A read that holds it throws (see DbFile.read).
                cutFiles.addLast(files[i]);
            }
            
            this.firstPos = newFiles[0].spos;
            this.dbFiles = newFiles;
            
            if (cutThread == null) {
                cutThread = new Thread(new Runnable() {
                    public void run() {
                        runCuts();
                    }
                });
                cutThread.setName("FileStream-cut");
                cutThread.setDaemon(true);
                cutThread.start();
            }
        }
    }
    
    /**
     * The cut's thread: deletes the files that cuts took off, oldest first, and forces the
     * directory after each, as pretruncate() did (bergdb 005-46). Each removal of a prefix
     * is persisted before the next one: a crash must not retain an older file while losing
     * a newer one, which would leave a hole before recovery can read the cut table. A crash
     * before a file is deleted leaves it, and the next start cuts again (Reclaim). It ends
     * when nothing is left to delete, or at a failure, which it keeps as the stream's.
     */
    private void runCuts() {
        while (true) {
            DbFile k;
            synchronized (this) {
                k = cutFiles.peekFirst();
                if (k == null || ioException != null) {
                    cutThread = null;
                    notifyAll();
                    return;
                }
            }
            
            try {
                k.delete();
                forceDirectory(dir);
            } catch (IOException e) {
                ioException = e;
            } catch (RuntimeException | Error e) {
                ioException = new IOException("The delete of a cut failed (the cause).", e);
            }
            
            synchronized (this) {
                if (ioException == null) {
                    cutFiles.removeFirst();
                }
            }
        }
    }

    /**
     * Returns the smallest possible file size.
     */
    public static long getSmallestFileSize() {
        // This is a method that we want to have (public), but it should not be part of the API.
        // Requires some special tool. See
        // See http://stackoverflow.com/questions/15812349/is-there-a-way-to-produce-javadoc-for-a-subset-of-public-methods.
        
        return FileStream.SMALLEST_FILE_SIZE;
    }

    /**
     * @throws IOException  If directory does not exist and cannot be created.
     */
    private void createDirIfNeeded() throws IOException {
        boolean exists;
        try {
            exists = dir.exists();
        } catch (SecurityException e) {
            throw new IOException("Directory " + dir.getPath() 
                    + " could not be accessed because of a SecurityException; " + e.getMessage());
        }
        
        if (exists) {
            File parent = dir.getAbsoluteFile().getParentFile();
            if (parent != null) forceDirectory(parent);
            return;
        }

        // mkdirs() can create several ancestors. Persist every new link,
        // from the deepest directory towards the pre-existing ancestor.
        List<File> missing = new ArrayList<File>();
        for (File f = dir.getAbsoluteFile(); f != null && !f.exists(); f = f.getParentFile()) {
            missing.add(f);
        }
        
        boolean created;
        try {
            created = dir.mkdirs();
            if (!created) {
                throw new IOException("Directory " + dir.getPath() + " could not be created.");
            }
        } catch (SecurityException e) {
            throw new IOException("Directory " + dir.getPath() 
                    + " could not be created because of a SecurityException; " + e.getMessage());
        }
        for (File f : missing) {
            forceDirectory(f);
            File parent = f.getParentFile();
            if (parent != null) {
                forceDirectory(parent);
            }
        }
    }

    /**
     * Takes the directory (bergdb 005-63): creates bergdb.lock with its text if it does not
     * exist, and takes an exclusive lock on one byte far beyond its end, held until close().
     * Refused with DirectoryInUseException: before the file is opened if a FileStream of
     * this JVM holds the directory, after if another process holds the lock. Not
     * interruptible, as the rest of this class.
     */
    private void lockDir() throws IOException {
        Object key = lockKey(dir);
        if (!LOCKED_DIRS.add(key)) {
            throw new DirectoryInUseException("Directory " + dir.getPath() 
                    + " is in use by another BergDB database in this JVM (" + LOCK_NAME 
                    + " is locked).");
        }
        
        boolean interrupted = Thread.interrupted();
        boolean locked = false;
        try {
            File file = new File(dir, LOCK_NAME);
            if (file.createNewFile()) {
                try (FileOutputStream out = new FileOutputStream(file)) {
                    out.write(LOCK_TEXT.getBytes(StandardCharsets.UTF_8));
                }
            }
            
            while (true) {
                RandomAccessFile f = new RandomAccessFile(file, "rw");
                FileLock lock;
                try {
                    lock = f.getChannel().tryLock(LOCK_POS, 1, false);
                } catch (ClosedByInterruptException e) {
                    // An interrupt during tryLock() closed the channel; try again.
                    Thread.interrupted();
                    interrupted = true;
                    f.close();
                    continue;
                } catch (OverlappingFileLockException e) {
                    // Held in this JVM, not by a FileStream of it.
                    f.close();
                    throw new DirectoryInUseException("Directory " + dir.getPath() 
                            + " is in use in this JVM (" + LOCK_NAME + " is locked).");
                } catch (IOException e) {
                    f.close();
                    throw new IOException("Could not lock " + file.getPath() + ": " 
                            + e.getMessage(), e);
                }
                
                if (lock == null) {
                    f.close();
                    throw new DirectoryInUseException("Directory " + dir.getPath() 
                            + " is in use by another BergDB database (" + LOCK_NAME 
                            + " is locked by another process).");
                }
                
                synchronized (this) {
                    lockFile = f;
                    lockKey = key;
                }
                locked = true;
                return;
            }
        } finally {
            if (!locked) {
                LOCKED_DIRS.remove(key);
            }
            if (interrupted) {
                Thread.currentThread().interrupt();
            }
        }
    }
    
    /**
     * The directory's key in LOCKED_DIRS: its file key (device and inode on macOS and Linux),
     * so that another path to the same directory finds it, or, where there is none (Windows),
     * its real path.
     */
    private static Object lockKey(File dir) throws IOException {
        Path path = dir.toPath();
        Object key = Files.readAttributes(path, BasicFileAttributes.class).fileKey();
        return key != null ? key : path.toRealPath();
    }
    
    /**
     * Releases the directory's lock, if this stream holds it; the file stays (bergdb 005-63).
     * The lock file is closed before the directory leaves LOCKED_DIRS.
     */
    private synchronized void unlockDir() throws IOException {
        if (lockFile == null) {
            return;
        }
        try {
            lockFile.close();       // Releases the lock.
        } finally {
            lockFile = null;
            LOCKED_DIRS.remove(lockKey);
            lockKey = null;
        }
    }

    /**
     * Handles initialization based on existing *.bergdb files.
     * 
     * @throws IOException
     * @thrown BadDirStateException
     */
    private void handleExistingFiles() throws IOException, BadDirStateException {
        File[] bergdbFiles = getSortedDbFiles();
        long currentSpos = checkDbFiles(bergdbFiles);
        determineFileSizeIndexFromFiles(bergdbFiles);
        createDbFileObjects(bergdbFiles, currentSpos);
    }

    private void createDbFileObjects(File[] bergdbFiles, long currentSpos) throws IOException,
            BadDirStateException {
        // Creates this.dbFiles. Sets this.length.
        
        dbFiles = new DbFile[bergdbFiles.length];
        
        if (bergdbFiles.length == 0) {
            // Special case, no bergdb files, create one.
            newFile();
            return;
        }
        
        for (int i = 0; i < bergdbFiles.length; i++) {
            File f = bergdbFiles[i];
            
            if (i == 0) {
                String name = f.getName();
                if (!(name.length() > SUFFIX.length())) {
                    throw new BadDirStateException("Bad name of bergdb file: " + f.getPath() + ".");
                }
                name = name.substring(0, name.length() - SUFFIX.length());
                
                long index;
                try {
                    index = this.stringToIndex(name);
                } catch (BadFormatException e) {
                    throw new BadDirStateException("Bad name of bergdb file: " + f.getPath() + ".");
                }
                
                currentSpos = index * BYTES_PER_INDEX_UNIT;
                this.firstPos = currentSpos;
            }
            
            if (i == bergdbFiles.length - 1) {
                dbFiles[i] = openForRw(currentSpos, f, FILE_SIZES[fileSizeIndex]);
            } else {
                dbFiles[i] = openForR(currentSpos, f);
            }
            
            currentSpos += f.length();
        }
        
        this.length = currentSpos;
    }

    /**
     * Computes and sets this.fileSizeIndex.
     */
    private void determineFileSizeIndexFromFiles(File[] bergdbFiles) {
        if (bergdbFiles.length == 0) {
            this.fileSizeIndex = 0;
        } else {
            long fileSize = bergdbFiles[bergdbFiles.length - 1].length();
            if (bergdbFiles.length > 1) {
                fileSize = Math.max(fileSize, bergdbFiles[bergdbFiles.length - 2].length());
            }
            
            this.fileSizeIndex = FILE_SIZES.length - 1;    // max
            
            for (int i = FILE_SIZES.length - 1; i >= 0; i--) {
                long s0 = FILE_SIZES[i];
                if (s0 < fileSize) {
                    break;
                }
                this.fileSizeIndex = i;
            }
        }
    }

    private long checkDbFiles(File[] bergdbFiles) throws BadDirStateException {
        long currentSpos = 0;
        
        for (int i = 0; i < bergdbFiles.length; i++) {
            File f = bergdbFiles[i];
            long fileSpos;
            
            String name = f.getName();
            if (!(name.length() > SUFFIX.length())) {
                throw new BadDirStateException("Bad name of bergdb file: " + f.getPath() + ".");
            }
            
            name = name.substring(0, name.length() - SUFFIX.length());
            
            long index;
            try {
                index = this.stringToIndex(name);
            } catch (BadFormatException e) {
                throw new BadDirStateException("Bad name of bergdb file: " + f.getPath() + ".");
            }
            
            fileSpos = index * BYTES_PER_INDEX_UNIT;
            
            
            if (i == 0) {
                currentSpos = fileSpos;
            } else {
                if (currentSpos != fileSpos) {
                    throw new BadDirStateException("Existing files in dir " + dir.getPath() 
                            + " are not in a correct state. File " + f.getPath() 
                            + " has a filename with an index value that does not" 
                            + " match the previous file sizes. currentSpos: " + currentSpos 
                            + ", fileSpos: " + fileSpos);
                }
            }
            
            long fLength = f.length();
            if (i != bergdbFiles.length - 1) {
                if (fLength % BYTES_PER_INDEX_UNIT != 0) {
                    throw new BadDirStateException("Bad size of file " + f.getPath() 
                            + ", should have been a multiple of " + BYTES_PER_INDEX_UNIT 
                            + ", but was " + fLength + ".");
                }
            }
            
            currentSpos += fLength;
        }
        return currentSpos;
    }

    /**
     * Returns berg *.bergdb file in this.dir.
     */
    private File[] getSortedDbFiles() {
        File[] bergdbFiles = dir.listFiles(new FilenameFilter() {
            public boolean accept(File dir, String name) {
                boolean result = name.endsWith(SUFFIX);
                return result;
            }    
        });
        
        Arrays.sort(bergdbFiles, new Comparator<File>() {
            public int compare(File f1, File f2) {
                return f1.getName().compareTo(f2.getName());
            }
        });
        
        return bergdbFiles;
    }
    
    private static String indexToString(long fileIndex) {
        // Remember that String.format might not work with GCJ.
        
        assert fileIndex >= 0;
        String s = "" + fileIndex;
        int zeroCount = 14 - s.length();
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < zeroCount; i++) {
            b.append('0');
        }
        b.append(s);
        
        return b.toString();
    }
    
    /**
     * Parses the index of a file name: its first position divided by BYTES_PER_INDEX_UNIT.
     * A long since 2026-10-21 (bergdb 005-19): an int could not name the files from
     * 2^31 * 100,000 bytes (214.7 TB) on, and such a stream could not be opened.
     * 
     * @throws BadFormatException If not correctly formatted.
     */
    private long stringToIndex(String s) {
        int zeroCount = 0;
        int length = s.length();
        
        for (int i = 0; i < length; i++) {
            if (s.charAt(i) == '0') {
                zeroCount++;
            } else {
                break;
            }
        }
        
        if (zeroCount == length) {
            zeroCount = zeroCount - 1;
        }
        
        s = s.substring(zeroCount);
        
        long result = 0;
        try {
            result = Long.parseLong(s);
        } catch (NumberFormatException e) {
            throw new BadFormatException("Not a long, '" + s + "'.");
        }
        if (result < 0 || result > Long.MAX_VALUE / BYTES_PER_INDEX_UNIT) {
            throw new BadFormatException("Index out of range, '" + s + "'.");
        }
        return result;
    }
    
    private synchronized void deleteAllFiles() throws IOException {
        try {
            for (int i = 0; i < dbFiles.length; i++) {
                dbFiles[i].delete();
                forceDirectory(dir);
            }
        } catch (IOException e) {
            ioException = e;
            throw e;
        }
    }
    
    /**
     * If field FileStream.ioException has been set, that exception is thrown.
     */
    private final void checkIOException() throws IOException {
        IOException e = this.ioException;
        
        if (e != null) {
            throw e;
        }
    }

    /**
     * Makes a new last file; the writer's (append's, seekFirstPos', the constructor's). It
     * creates and forces the file and the directory before it takes the stream's monitor, and
     * takes it only to publish the new list (2026-10-27, bergdb 005-46): every read waited for
     * the forces. No read needs the new file before an append to it has returned.
     */
    private void newFile() throws IOException {
        if (this.length % BYTES_PER_INDEX_UNIT != 0) {
            throw new Bug("Illegal state, length = " + length);
        }
        
        DbFile[] files = dbFiles;
        if (files.length > 0) {
            // The last file takes no more appends; its read channel stays.
            files[files.length - 1].closeWriter();
        }
        
        long index = this.length / BYTES_PER_INDEX_UNIT;
        File file = new File(dir, indexToString(index) + SUFFIX);
        
        applyFileSizeChangeRules();
        
        DbFile newFile = openForRw(length, file, FILE_SIZES[fileSizeIndex]);
        
        // To make sure no-one just created the file and wrote to it.
        long newFileLength = newFile.file.length();
        if (newFileLength != 0) {
            throw new IOException("File " + newFile.file.getPath() 
                    + " already exists and has length " + newFileLength + ".");
        }
        
        synchronized (this) {
            files = dbFiles;    // A cut may have taken files off meanwhile, never the last.
            DbFile[] newKFiles = new DbFile[files.length + 1];
            System.arraycopy(files, 0, newKFiles, 0, files.length);
            newKFiles[newKFiles.length - 1] = newFile;
            dbFiles = newKFiles;
        }
    }

    /**
     * Possibly increases or decreases the stream file size for the new file to be created.
     */
    private void applyFileSizeChangeRules() {
        long streamLength = getLength();
        long streamSize = streamLength - getFirstPos();
        this.fileSizeIndex = determineFileSizeIndex(this.fileSizeIndex, streamLength, streamSize);
    }
    
    private int determineFileSizeIndex(int currentFileSizeIndex, long streamLength, long streamSize) {
        long currentSize = FILE_SIZES[this.fileSizeIndex];
        long size = streamSize / 4;
        long foundSize = FILE_SIZES[0];
        int foundIndex = 0;
        int result = currentFileSizeIndex;
        
        for (int i = 1; i < FILE_SIZES.length; i++) {
            long s = FILE_SIZES[i];
            if (s <= size) {
                foundSize = s;
                foundIndex = i;
            } else {
                break;
            }
        }
        
        if (foundIndex != currentFileSizeIndex) {
            if (foundSize > currentSize) {
                boolean isMaxIndex = max2G ? 
                          currentFileSizeIndex >= INDEX_2G 
                        : currentFileSizeIndex == FILE_SIZES.length - 1;
                
                if (!isMaxIndex) {
                    long oneUpSize = FILE_SIZES[currentFileSizeIndex + 1];
                    if (streamLength % oneUpSize == 0) {
                        result = foundIndex;
                    }
                }
            } else {
                result = foundIndex;
            }
        }
        
        if (max2G && currentFileSizeIndex > INDEX_2G) {
            result = INDEX_2G;
        }
        
        return result;
    }
    
    private DbFile findFile(long spos) {
        // Find file with largest spos that is <= spos.
        // Yes, we use linear search. Likely faster in this case then an O(log N) data structure
        // since number of files should not exceed 100.
        
        // No lock (bergdb 005-46): dbFiles is replaced, never changed.
        DbFile result = null;
        DbFile[] files = dbFiles;
        for (int i = 0; i < files.length; i++) {
            if (files[i].spos <= spos) {
                result = files[i];
            } else {
                break;
            }
        }
        
        return result;
    }
    
    private DbFile findLastFile() {        
        DbFile[] files = dbFiles;
        assert files.length > 0;
        return files[files.length - 1];
    }
    
    private DbFile openForR(long spos, File file) throws IOException {
        DbFile k = new DbFile(spos, file, 0);
        k.channel = io.openRead(file);
        k.fileLength = file.length();     // Not channel.size(), which an interrupt fails.
        if (k.fileLength == 0 && !file.exists()) {
            k.channel.close();
            throw new IOException("File " + file.getPath() + " not found.");
        }
        k.isRw = false;
        synchronized (k) {}
        return k;
    }
    
    private DbFile openForRw(long spos, File file, long maxSize) throws IOException {
        DbFile k = new DbFile(spos, file, maxSize);
        k.rfile = io.open(file);
        try {
            // Persist both the file and its directory entry before it can
            // contribute to StorageManager's confirmed (durable) length.
            k.force();
            forceDirectory(dir);
            k.fileLength = k.rfile.length();
            k.channel = io.openRead(file);
        } catch (IOException e) {
            try {
                k.rfile.close();
            } catch (IOException closeFailure) {
                e.addSuppressed(closeFailure);
            }
            ioException = e;
            throw e;
        }
        k.isRw = true;
        k.maxSize = maxSize;
        synchronized (k) {}
        return k;
    }
    
    /**
     * Forces a directory through FileStreamIo. Not interruptible (bergdb 005-46): it clears
     * the thread's interrupt flag first and sets it again after, and if an interrupt during
     * the force closes its channel anyway, forces again (forceDirectory opens a channel for
     * each force). Before, a cut or a new FileStream by an interrupted thread failed with
     * ClosedByInterruptException, and the cut failed the database.
     */
    private void forceDirectory(File directory) throws IOException {
        boolean interrupted = Thread.interrupted();
        try {
            while (true) {
                try {
                    io.forceDirectory(directory);
                    return;
                } catch (ClosedByInterruptException e) {
                    Thread.interrupted();
                    interrupted = true;
                }
            }
        } finally {
            if (interrupted) {
                Thread.currentThread().interrupt();
            }
        }
    }
    
    /**
     * Cached information about a particular *.bergdb file.
     * 
     * Reads take no lock (bergdb 005-46): they read with positional reads on 'channel', the
     * file's read channel, and check 'fileLength', 'isDeleted' and 'isClosed', which are
     * volatile. The writer's handle, 'rfile', and append() are under this object's monitor,
     * which no read takes. The channel is replaced, under 'channelLock', only when an
     * interrupt closed it; a cut and close() close it under the same lock.
     */
    private class DbFile {
        private final File file;
        private RandomAccessFile rfile = null;      // the writer's handle; null when not rw
        private volatile FileChannel channel;       // the read channel
        private final Object channelLock = new Object();
        private volatile long fileLength;   // current length of the file
        private boolean isRw = false;
        private final long spos;    // spos of first byte in file
        private long maxSize;
        private volatile boolean isClosed = false;
        private volatile boolean isDeleted = false;     // by pretruncate; see read()
        
        private DbFile(long spos, File file, long maxSize) {
            if (file == null) {
                throw new IllegalArgumentException("file == null not allowed");
            }
            this.file = file;
            
            if (spos < 0) {
                throw new IllegalArgumentException("spos = " + spos);
            }
            this.spos = spos;
            
            this.maxSize = maxSize;
        }

        public String toString() {
            return file.getPath() + ", isRw:" + isRw + ", spos:" + spos + ", maxSize:" + maxSize;
        }
        
        /** Closes the writer's handle and the read channel. */
        synchronized void close() throws IOException {
            IOException failure = null;
            if (rfile != null) {
                try {
                    rfile.close();
                } catch (IOException e) {
                    failure = e;
                }
                rfile = null;
                isRw = false;
            }
            synchronized (channelLock) {
                isClosed = true;
                if (channel != null) {
                    try {
                        channel.close();    // Waits for the reads in progress on it.
                    } catch (IOException e) {
                        if (failure == null) failure = e;
                    }
                }
            }
            if (failure != null) {
                ioException = failure;
                throw failure;
            }
        }
            
        /** The writer is done with the file, which takes no more appends; reads go on. */
        synchronized void closeWriter() throws IOException {
            if (rfile != null) {
                try {
                    rfile.close();
                } catch (IOException e) {
                    ioException = e;
                    throw e;
                }
                rfile = null;
            }
            isRw = false;
        }
        
        /**
         * Closes and deletes a file; the cut's thread. 
         * If option renameAsDelete has been set, the file will be renamed instead of deleted.
         * 
         * @throws IOException
         */
        synchronized void delete() throws IOException {
            isDeleted = true;
            close();
            
            if (renameAsDelete) {
                boolean ok = io.rename(file, new File(dir, file.getName() + ".deleted"));
                if (!ok) {
                    ioException = new IOException("Could not rename file " + file.getPath() + ".");
                    throw ioException;
                }
            } else {
                boolean ok = io.delete(file);
                if (!ok) {
                    ioException = new IOException("Cound not delete file " + file.getPath() + ".");
                    throw ioException;
                }
            }
        }
        
        /**
         * Reads bytes from the file, returns number of bytes actually read.
         * No lock and not interruptible (bergdb 005-46): it clears the thread's interrupt
         * flag first and sets it again after, and reads again on a new channel if an
         * interrupt during the read closed the channel; FileChannel is interruptible, and an
         * interrupted read closes it for every thread. Before, under the file's monitor,
         * which the writer held during its append and force.
         */
        int read(long spos, byte[] dest, int destOffset, int lengthToRead) throws IOException {
            if (isDeleted) {
                // 2026-10-13 (bergdb 011-04, W1): a reader found this file
                // just before pretruncate() deleted it. Only this read fails.
                throw deletedException(spos);
            }

            if (isClosed) {
                ioException = new IOException("File closed, " + file.getPath() + ".");
                throw ioException;
            }
            
            final long fileLength = this.fileLength;
            
            if (spos < this.spos) {
                throw new IllegalArgumentException("Cannot read from spos " + spos 
                        + ", this.spos=" + this.spos + ", length=" + fileLength);
            }
            
            // 2026-10-21 (bergdb 005-24): the check said "spos > spos + fileLength", never
            // true, and a read past the end threw IndexOutOfBoundsException from readFully.
            if (spos > this.spos + fileLength) {
                throw new EOFException("Cannot read at spos " + spos + ", past the end of "
                        + file.getPath() + " at " + (this.spos + fileLength) + ".");
            }
            
            long fileOffset = spos - this.spos;
            long actualLengthToRead = lengthToRead > fileLength - fileOffset ? fileLength - fileOffset : lengthToRead;
            assert actualLengthToRead <= Integer.MAX_VALUE;
            int actualLengthToReadInt = (int) actualLengthToRead;
            
            ByteBuffer buffer = ByteBuffer.wrap(dest, destOffset, actualLengthToReadInt);
            boolean interrupted = Thread.interrupted();
            try {
                while (buffer.hasRemaining()) {
                    FileChannel ch = channel;
                    try {
                        int n = ch.read(buffer, fileOffset + buffer.position() - destOffset);
                        if (n < 0) {
                            String message = "EOF when reading from " + file.getPath() 
                                    + ". fileOffset: " + fileOffset 
                                    + ". destOffset: " + destOffset
                                    + ". lengthToRead: " + lengthToRead
                                    + ". file.length(): " + file.length()
                                    + ". dest.length: " + dest.length;
                            ioException = new EOFException(message);
                            throw ioException;
                        }
                    } catch (ClosedChannelException e) {
                        if (Thread.interrupted()) {
                            interrupted = true;
                        }
                        reopenChannel(ch, spos);
                    } catch (IOException e) {
                        if (e != ioException) {
                            ioException = e;
                        }
                        throw e;
                    }
                }
            } finally {
                if (interrupted) {
                    Thread.currentThread().interrupt();
                }
            }
            
            return actualLengthToReadInt;
        }
        
        /**
         * Opens the read channel again after an interrupt closed it (bergdb 005-46), unless
         * another read did, or the file was deleted or closed: then this read fails as one
         * of a deleted or a closed file.
         */
        private void reopenChannel(FileChannel closed, long spos) throws IOException {
            synchronized (channelLock) {
                if (isDeleted) {
                    throw deletedException(spos);
                }
                if (isClosed) {
                    ioException = new IOException("File closed, " + file.getPath() + ".");
                    throw ioException;
                }
                if (channel == closed) {
                    channel = io.openRead(file);
                }
            }
        }
        
        private ReadBelowFirstPosException deletedException(long spos) {
            return new ReadBelowFirstPosException("Cannot read at spos " + spos
                    + ", the file " + file.getPath() + " has been deleted by pretruncate.");
        }
        
        /**
         * Forces the file through FileStreamIo; under this object's monitor. Not
         * interruptible (bergdb 005-46): it clears the thread's interrupt flag first and sets
         * it again after. If an interrupt during the force closes the channel anyway, which
         * closes 'rfile' too, its parent, it opens the file again and forces again.
         */
        void force() throws IOException {
            boolean interrupted = Thread.interrupted();
            try {
                while (true) {
                    try {
                        io.forceFile(file, rfile);
                        return;
                    } catch (ClosedByInterruptException e) {
                        Thread.interrupted();
                        interrupted = true;
                        rfile = io.open(file);
                    }
                }
            } finally {
                if (interrupted) {
                    Thread.currentThread().interrupt();
                }
            }
        }
        
        /**
         * Appends bytes to the file, returns actual number of bytes appended.
         */
        synchronized int append(byte[] bytes, int offset, int len) throws IOException {
            if (!isRw) {
                throw new Bug("Cannot append to file opened in read-only mode.");
            }
            
            if (isClosed) {
                ioException = new IOException("File closed, " + file.getPath() + ".");
                throw ioException;
            }
            
            long available = maxSize - this.fileLength;
            if (available < 0) {
                throw new Bug("maxSize: " + maxSize + ", fileLength: " + fileLength + ", file: " + file.getPath());
            }
            int availableInt = available > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) available;
            int toAppend = len > availableInt ? availableInt : len;
            
            try {
                // 130818 Frans:
                // Alternative to lock file; detects other user appending to this file.
                
                long rfileLength = rfile.length();
                
                if (rfileLength != this.fileLength) {
                    throw new IOException("File " + file.getPath() 
                            + " is not of expected length (" + this.fileLength + "),"
                            + "but " + rfileLength + " bytes."
                            + " Was is modified by someone else?");
                }
                
                rfile.seek(this.fileLength);
                if (toAppend > 0) {
                    io.write(file, rfile, bytes, offset, toAppend);
                    force();
                }
                // Published to reads after the force (volatile).
                fileLength += toAppend;
                assert fileLength == rfile.length() : fileLength + " != " + rfile.length();
            } catch (IOException e) {
                ioException = e;
                throw e;
            }
            
            return toAppend;
        }
    }
    
    // ======== Tests ========

    @Nano
    public static void test0(TestEnvironment c) throws IOException {
        // Simple sanity test.
        File dir = c.createTempDir();
        assert dir != null : "dir is null";
        FileStream f = new FileStream(dir);
        Assert.assertEquals(0, f.getFirstPos());
        Assert.assertEquals(0, f.getLength());
        f.close();
    }
    
    @Nano
    public static void test1(TestEnvironment c) throws IOException {
        // Like test0() but appends a single byte and reads it back.
        byte[] bytes = new byte[] {123};
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir);
        f.append(bytes, 0, bytes.length);
        Assert.assertEquals(0, f.getFirstPos());
        Assert.assertEquals(1, f.getLength());
        byte[] b = new byte[1];
        f.read(0, b, 0, 1);
        f.close();
        Assert.assertEquals((byte) 123, b[0]);
    }
    
    @Nano
    public static void testFileSizeRules0(TestEnvironment c) throws IOException {
        int newIndex;
        long size;
        File dir = c.createTempDir();
        assert dir != null : "dir is null";
        FileStream f = new FileStream(dir);
        
        size = 5 * 1000000L;
        newIndex = f.determineFileSizeIndex(0, size, size);
        Assert.assertEquals(1, newIndex);
        
        size = 3 * 1000000L;
        newIndex = f.determineFileSizeIndex(0, size, size);
        Assert.assertEquals(0, newIndex);
        
        f.close();
    }
    
    @Nano
    public static void testFileSizeRules1(TestEnvironment c) throws IOException {
        // Tests the max2G setting.
        // Sizes: .., 500*M, 2*G, 10*G, 50*G, ...
        
        int newIndex;
        long size;
        File dir = c.createTempDir();
        assert dir != null : "dir is null";
        FileStream f = new FileStream(dir);
        
        size = 50*G;
        
        f.setMax2G(false);
        newIndex = f.determineFileSizeIndex(INDEX_2G, size, size);
        Assert.assertEquals(INDEX_2G + 1, newIndex);
        
        f.setMax2G(true);
        newIndex = f.determineFileSizeIndex(INDEX_2G, size, size);
        Assert.assertEquals(INDEX_2G, newIndex);
        
        f.close();
    }
    
    @Nano
    public static void testRestart0(TestEnvironment c) throws IOException {
        byte[] bytes = new byte[] {123};
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir);
        f.append(bytes, 0, bytes.length);
        f.close();
        f = null;
        
        FileStream f2 = new FileStream(dir);
        byte[] b = new byte[1];
        f2.read(0, b, 0, 1);
        f2.close();
        Assert.assertEquals((byte) 123, b[0]);
    }
    
    @Nano
    public static void testRestartMissingFile(TestEnvironment c) throws IOException {
        // Tests starting a FileStream in directory with a missing file.
        byte[] bytes = new byte[500*1000];     // 3 stream files
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir);
        f.append(bytes, 0, bytes.length);
        f.close();
        f = null;
        
        File second = new File(dir, indexToString(2) + SUFFIX);
        boolean ok = second.delete();
        if (!ok) {
            throw new IOException("Could not delete " + second.getPath() + ".");
        }
        
        Exception ex = null;
        try {
            FileStream f2 = new FileStream(dir);
            f2.close();
        } catch (BadDirStateException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
        
        // bergdb 005-63: the failed open released the directory's lock.
        ex = null;
        try {
            new FileStream(dir).close();
        } catch (BadDirStateException e) {
            ex = e;
        }
        Assert.assertTrue(ex != null);
    }
    
    @Nano
    public static void testBigAppend0(TestEnvironment c) throws IOException {
        byte[] bytes = new byte[10*1000];
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir);
        f.append(bytes, 0, bytes.length);
        bytes = new byte[234*1000];
        f.append(bytes, 0, bytes.length);
        bytes = new byte[445*1000];
        f.append(bytes, 0, bytes.length);
        Assert.assertEquals((10 + 234 + 445) * 1000, f.getLength());
        f.close();
    }
    
    @Nano
    public static void testConstants() {
        Assert.assertTrue(SMALLEST_FILE_SIZE % BYTES_PER_INDEX_UNIT == 0);
        Assert.assertEquals(2L*1000*1000000, FILE_SIZES[INDEX_2G]);
        
        for (int i = 0; i < FACTOR_UP.length; i++) {
            Assert.assertEquals(FILE_SIZES[i + 1], FILE_SIZES[i] * FACTOR_UP[i]);
        }
    }
    
    @Nano
    public static void testSeekFirstPos0(TestEnvironment c) throws IOException {
        FileStream f = new FileStream(c.createTempDir());
        f.seekFirstPos(200*1000 * 30);
        Assert.assertEquals(200*1000 * 30, f.getLength());
        Assert.assertEquals(200*1000 * 30, f.getFirstPos());
        f.close();
    }
    
    /**
     * Regression test for bergdb 005-19: a stream past 2^31 * 100,000 bytes (214.7 TB) could
     * be written but not opened again; the file names were parsed as ints.
     */
    @Nano
    public static void testReopenPast214TB(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        long pos = (1L << 31) * BYTES_PER_INDEX_UNIT;
        FileStream f = new FileStream(dir);
        f.seekFirstPos(pos);
        byte[] bytes = new byte[] {1, 2, 3};
        f.append(bytes, 0, bytes.length);
        f.close();
        
        FileStream f2 = new FileStream(dir);
        Assert.assertEquals(pos, f2.getFirstPos());
        Assert.assertEquals(pos + 3, f2.getLength());
        byte[] b = new byte[3];
        f2.read(pos, b, 0, 3);
        Assert.assertArrayEquals(bytes, b);
        f2.close();
    }
    
    @Nano
    public static void testSeekFirstPos1(TestEnvironment c) throws IOException {
        byte[] bytes = new byte[300*1000];
        FileStream f = new FileStream(c.createTempDir());
        f.append(bytes, 0, bytes.length);
        f.seekFirstPos(200*1000 * 5);
        Assert.assertEquals(200*1000 * 5, f.getLength());
        Assert.assertEquals(200*1000 * 5, f.getFirstPos());
        Assert.assertEquals(1, f.dbFiles.length);
        f.append(bytes, 0, bytes.length);
        Assert.assertEquals(2, f.dbFiles.length);
        Assert.assertEquals(200*1000 * 5 + 300*1000, f.getLength());
        Assert.assertEquals(200*1000 * 5, f.getFirstPos());
        f.close();
    }
    
    @Nano
    public static void testPretruncate0(TestEnvironment c) throws Exception {
        FileStream f = new FileStream(c.createTempDir());            
        byte[] bytes = new byte[500*1000];
        f.append(bytes, 0, bytes.length);
        Assert.assertEquals(3, f.dbFiles.length);
        
        f.pretruncate(200*1000);
        Assert.assertEquals(2, f.dbFiles.length);
        Assert.assertEquals(200*1000, f.getFirstPos());
        Assert.assertEquals(500*1000, f.getLength());
        f.close();
    }
    
    /**
     * 2026-10-13 (bergdb 011-04, W1). A read of bytes that pretruncate()
     * removed used to store a permanent IOException: after it, every read and append failed.
     * Now only the read fails.
     */
    @Nano
    public static void testReadBelowFirstPosDoesNotBreakStream(TestEnvironment c)
            throws Exception {
        FileStream f = new FileStream(c.createTempDir());
        byte[] bytes = new byte[500*1000];
        new Random(1).nextBytes(bytes);
        f.append(bytes, 0, bytes.length);
        f.pretruncate(400*1000);
        Assert.assertEquals(400*1000, f.getFirstPos());

        byte[] dest = new byte[10];
        try {
            f.read(100, dest, 0, dest.length);
            throw new AssertionError("a read below the first position succeeded");
        } catch (ReadBelowFirstPosException e) {
            // Expected.
        }

        f.read(450*1000, dest, 0, dest.length);
        Assert.assertEquals(bytes[450*1000], dest[0]);
        f.append(bytes, 0, 1000);
        f.read(500*1000, dest, 0, dest.length);
        Assert.assertEquals(bytes[0], dest[0]);
        f.close();
    }

    /**
     * Regression test for bergdb 005-24: a read at the end of the stream looped forever, and
     * one past it threw IndexOutOfBoundsException. Now both throw EOFException, and the stream
     * stays usable.
     */
    @Nano
    public static void testReadPastEnd(TestEnvironment c) throws Exception {
        FileStream f = new FileStream(c.createTempDir());
        byte[] bytes = new byte[300 * 1000];        // two files
        new Random(3).nextBytes(bytes);
        f.append(bytes, 0, bytes.length);
        long[] positions = {300 * 1000, 300 * 1000 - 5, 300 * 1000 + 1};
        for (long pos : positions) {
            try {
                f.read(pos, new byte[10], 0, 10);
                throw new AssertionError("a read past the end at " + pos + " succeeded");
            } catch (EOFException e) {
                // Expected.
            }
        }
        byte[] dest = new byte[10];
        f.read(300 * 1000 - 10, dest, 0, 10);
        Assert.assertEquals(bytes[300 * 1000 - 10], dest[0]);
        f.append(bytes, 0, 10);
        f.read(300 * 1000, dest, 0, 10);
        Assert.assertEquals(bytes[0], dest[0]);
        f.close();
    }
    
    /**
     * Same, for a reader that found the file just before pretruncate() deleted it.
     */
    @Nano
    public static void testReadOfFileDeletedMeanwhileDoesNotBreakStream(TestEnvironment c)
            throws Exception {
        FileStream f = new FileStream(c.createTempDir());
        byte[] bytes = new byte[500*1000];
        new Random(2).nextBytes(bytes);
        f.append(bytes, 0, bytes.length);

        DbFile file = f.findFile(100);      // What a reader holds when pretruncate() starts.
        Assert.assertTrue(file != null);
        f.pretruncate(400*1000);

        try {
            file.read(100, new byte[10], 0, 10);
            throw new AssertionError("a read of a deleted file succeeded");
        } catch (ReadBelowFirstPosException e) {
            // Expected.
        }

        byte[] dest = new byte[10];
        f.append(bytes, 0, 1000);
        f.read(450*1000, dest, 0, dest.length);
        Assert.assertEquals(bytes[450*1000], dest[0]);
        f.close();
    }

    @Nano
    public static void testMultiFileRead0(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        Random r = new Random(0);
        byte[] bytes1 = new byte[201*1000];
        r.nextBytes(bytes1);
        
        FileStream f = new FileStream(dir);
        f.append(bytes1, 0, bytes1.length);
        
        byte[] bytes2 = new byte[bytes1.length];
        f.read(0, bytes2, 0, bytes2.length);
        
        Assert.assertArrayEquals(bytes1, bytes2);
        f.close();
    }
    
    @Nano
    public static void testMultiFileRead1(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        Random r = new Random(0);
        byte[] bytes1 = new byte[201*1000];
        r.nextBytes(bytes1);
        
        FileStream f = new FileStream(dir);
        f.append(bytes1, 0, bytes1.length);
        
        byte[] bytes2 = new byte[bytes1.length - 10];
        f.read(10, bytes2, 0, bytes2.length);
        
        byte[] bytes1b = new byte[bytes1.length - 10];
        System.arraycopy(bytes1, 10, bytes1b, 0, bytes1.length - 10);
        
        Assert.assertArrayEquals(bytes1b, bytes2);
        f.close();
    }
    
    @Nano("f")    // Takes too long for unit test
    public static void tFileSizeIncrease(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        byte[] bytes = new byte[100*1000];
        FileStream f = new FileStream(dir);
        
        for (int i = 0; i < 50; i++) {
            f.append(bytes, 0, bytes.length);
        }
        
        Assert.assertEquals(21, f.dbFiles.length);
        Assert.assertEquals(200*1000, f.dbFiles[0].fileLength);
        Assert.assertEquals(1000*1000, f.dbFiles[f.dbFiles.length - 1].fileLength);
        
        f.close();
    }
    
    // ---- bergdb 005-46: reads that wait for no write, and interrupts ----
    
    /**
     * A FileStreamIo whose file force, directory force and delete can be held on a latch,
     * and that counts the read channels it opens (bergdb 005-46).
     */
    static class HeldIo extends FileStreamIo {
        volatile java.util.concurrent.CountDownLatch holdForce, holdDirectoryForce, holdDelete;
        final java.util.concurrent.CountDownLatch held = new java.util.concurrent.CountDownLatch(1);
        final java.util.concurrent.atomic.AtomicInteger readOpens =
                new java.util.concurrent.atomic.AtomicInteger();
        volatile FileChannel lastRead;
        volatile int failDeleteAt = 0;
        int deletes = 0;
        
        private void hold(java.util.concurrent.CountDownLatch latch) throws IOException {
            if (latch == null) return;
            held.countDown();
            try {
                if (!latch.await(10, java.util.concurrent.TimeUnit.SECONDS)) {
                    throw new IOException("held for 10 s");
                }
            } catch (InterruptedException e) {
                throw new IOException(e);
            }
        }
        
        protected void forceFile(File file, RandomAccessFile handle) throws IOException {
            hold(holdForce);
            super.forceFile(file, handle);
        }
        
        protected void forceDirectory(File directory) throws IOException {
            hold(holdDirectoryForce);
            super.forceDirectory(directory);
        }
        
        protected boolean delete(File file) throws IOException {
            hold(holdDelete);
            if (++deletes == failDeleteAt) {
                throw new IOException("injected delete failure");
            }
            return super.delete(file);
        }
        
        protected FileChannel openRead(File file) throws IOException {
            readOpens.incrementAndGet();
            return lastRead = super.openRead(file);
        }
    }
    
    /** Runs 'r' in a new thread, started; its failure is rethrown by join(). */
    static final class Run extends Thread {
        private final Callable r;
        volatile Throwable failure;
        
        interface Callable {
            void call() throws Exception;
        }
        
        Run(Callable r) {
            this.r = r;
            setDaemon(true);
            start();
        }
        
        public void run() {
            try {
                r.call();
            } catch (Throwable e) {
                failure = e;
            }
        }
        
        void finish() throws Exception {
            join(10000);
            Assert.assertTrue("still running after 10 s", !isAlive());
            if (failure != null) throw new AssertionError("failed", failure);
        }
    }
    
    /** Reads 'n' bytes at 'pos' and checks them against 'expected', which starts at 0. */
    private static void readAndCheck(FileStream f, long pos, int n, byte[] expected)
            throws IOException {
        byte[] dest = new byte[n];
        f.read(pos, dest, 0, n);
        for (int i = 0; i < n; i++) {
            Assert.assertEquals(expected[(int) pos + i], dest[i]);
        }
    }
    
    /**
     * Regression test for bergdb 005-46: a read of the last file waited for the writer's
     * append and its force (the file's monitor). Now it reads while the force is held.
     */
    @Nano
    public static void testReadOfLastFileDuringForce(TestEnvironment c) throws Exception {
        HeldIo io = new HeldIo();
        final FileStream f = new FileStream(c.createTempDir(), io);
        final byte[] bytes = new byte[100 * 1000];
        new Random(4).nextBytes(bytes);
        f.append(bytes, 0, 50 * 1000);
        io.holdForce = new java.util.concurrent.CountDownLatch(1);
        Run writer = new Run(() -> f.append(bytes, 50 * 1000, 1000));
        Assert.assertTrue(io.held.await(10, java.util.concurrent.TimeUnit.SECONDS));
        long t0 = System.nanoTime();
        readAndCheck(f, 49 * 1000, 1000, bytes);       // The last file, while its force waits.
        Assert.assertTrue("the read waited", System.nanoTime() - t0 < 2000000000L);
        io.holdForce.countDown();
        writer.finish();
        readAndCheck(f, 50 * 1000, 1000, bytes);
        f.close();
    }
    
    /**
     * Regression test for bergdb 005-46: a new file held the stream's monitor while it forced
     * the file and the directory, and every read, of any file, waited. Now a read of the first
     * file reads while the new file's directory force is held.
     */
    @Nano
    public static void testReadDuringNewFile(TestEnvironment c) throws Exception {
        HeldIo io = new HeldIo();
        final FileStream f = new FileStream(c.createTempDir(), io);
        final byte[] bytes = new byte[300 * 1000];
        new Random(5).nextBytes(bytes);
        f.append(bytes, 0, 150 * 1000);
        io.holdDirectoryForce = new java.util.concurrent.CountDownLatch(1);
        Run writer = new Run(() -> f.append(bytes, 150 * 1000, 100 * 1000));   // A new file.
        Assert.assertTrue(io.held.await(10, java.util.concurrent.TimeUnit.SECONDS));
        long t0 = System.nanoTime();
        readAndCheck(f, 1000, 1000, bytes);
        readAndCheck(f, 140 * 1000, 1000, bytes);
        Assert.assertTrue("the read waited", System.nanoTime() - t0 < 2000000000L);
        io.holdDirectoryForce.countDown();
        writer.finish();
        readAndCheck(f, 210 * 1000, 1000, bytes);
        f.close();
    }
    
    /**
     * Regression test for bergdb 005-46: a cut deleted its files and forced the directory
     * under the stream's monitor, on the caller's thread; every read waited, and the commit
     * that made the cut too. Now pretruncate() returns at once, reads of the files it keeps
     * go on while the cut's thread is held, and close() waits for that thread.
     */
    @Nano
    public static void testCutOnItsOwnThread(TestEnvironment c) throws Exception {
        HeldIo io = new HeldIo();
        File dir = c.createTempDir();
        final FileStream f = new FileStream(dir, io);
        final byte[] bytes = new byte[1000 * 1000];
        new Random(6).nextBytes(bytes);
        f.append(bytes, 0, bytes.length);
        int files = dir.list().length;
        io.holdDirectoryForce = new java.util.concurrent.CountDownLatch(1);
        long t0 = System.nanoTime();
        f.pretruncate(800 * 1000);
        Assert.assertTrue(io.held.await(10, java.util.concurrent.TimeUnit.SECONDS));
        readAndCheck(f, 850 * 1000, 1000, bytes);
        Assert.assertTrue("the cut or the read waited", System.nanoTime() - t0 < 2000000000L);
        Assert.assertEquals(800 * 1000, f.getFirstPos());
        try {
            f.read(100, new byte[10], 0, 10);
            throw new AssertionError("a read of a file the cut took off succeeded");
        } catch (ReadBelowFirstPosException e) {
            // Expected.
        }
        Run closer = new Run(() -> f.close());
        Thread.sleep(100);
        Assert.assertTrue("close() did not wait for the cut's thread", closer.isAlive());
        io.holdDirectoryForce.countDown();
        closer.finish();
        Assert.assertEquals(files - 4, dir.list().length);
    }
    
    /**
     * bergdb 005-46: a failed delete of a cut is the stream's failure; no file after it is
     * deleted, and the next read, cut and close() throw it.
     */
    @Nano
    public static void testFailedDeleteOfACut(TestEnvironment c) throws Exception {
        HeldIo io = new HeldIo();
        io.failDeleteAt = 2;
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir, io);
        byte[] bytes = new byte[1000 * 1000];
        f.append(bytes, 0, bytes.length);
        f.pretruncate(800 * 1000);
        try {
            f.awaitDeletes();
            throw new AssertionError("a failed delete was not passed on");
        } catch (IOException e) {
            Assert.assertEquals("injected delete failure", e.getMessage());
        }
        Assert.assertEquals(2, io.deletes);
        Assert.assertTrue(new File(dir, indexToString(2) + SUFFIX).exists());   // The second.
        Assert.assertTrue(!new File(dir, indexToString(0) + SUFFIX).exists());  // The first.
        try {
            f.read(850 * 1000, new byte[10], 0, 10);
            throw new AssertionError("a read after a failed cut succeeded");
        } catch (IOException e) {
            // Expected.
        }
        try {
            f.close();
            throw new AssertionError("close() after a failed cut did not throw");
        } catch (IOException e) {
            // Expected.
        }
    }
    
    /**
     * bergdb 005-46: a read by a thread whose interrupt flag is set reads, and leaves the
     * flag set; a FileChannel would have closed itself. And a read that finds the channel
     * closed, as an interrupt during a read of another thread closes it, opens it again.
     */
    @Nano
    public static void testReadsAndInterrupts(TestEnvironment c) throws Exception {
        HeldIo io = new HeldIo();
        FileStream f = new FileStream(c.createTempDir(), io);
        byte[] bytes = new byte[100 * 1000];
        new Random(7).nextBytes(bytes);
        f.append(bytes, 0, bytes.length);
        int opens = io.readOpens.get();
        
        Thread.currentThread().interrupt();
        try {
            readAndCheck(f, 1000, 1000, bytes);
            Assert.assertTrue("the interrupt flag was lost", Thread.currentThread().isInterrupted());
        } finally {
            Thread.interrupted();
        }
        Assert.assertEquals(opens, io.readOpens.get());
        
        io.lastRead.close();        // As an interrupt during a read would.
        readAndCheck(f, 2000, 1000, bytes);
        Assert.assertEquals(opens + 1, io.readOpens.get());
        f.append(bytes, 0, 10);
        readAndCheck(f, 3000, 1000, bytes);
        f.close();
    }
    
    /**
     * bergdb 005-46: a cut and a new FileStream by a thread whose interrupt flag is set work,
     * and leave the flag set. Their directory forces closed their FileChannel, and the
     * stream failed with ClosedByInterruptException; the cut failed the database.
     */
    @Nano
    public static void testCutAndOpenByInterruptedThread(TestEnvironment c) throws Exception {
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir);
        byte[] bytes = new byte[1000 * 1000];
        f.append(bytes, 0, bytes.length);
        Thread.currentThread().interrupt();
        try {
            f.pretruncate(800 * 1000);
            f.awaitDeletes();
            f.append(bytes, 0, 100 * 1000);         // Forces, and a new file.
            readAndCheck(f, 900 * 1000, 1000, bytes);
            f.close();
            FileStream f2 = new FileStream(dir);
            f2.close();
            FileStream f3 = new FileStream(new File(c.createTempDir(), "new"));
            f3.close();
            Assert.assertTrue("the interrupt flag was lost", Thread.currentThread().isInterrupted());
        } finally {
            Thread.interrupted();
        }
    }
    
    /**
     * bergdb 005-46: reads beside a writer and cuts, from several threads, read what was
     * written; a read of bytes a cut removed throws ReadBelowFirstPosException only.
     */
    @Nano("f")
    public static void testReadersBesideWriterAndCuts(TestEnvironment c) throws Exception {
        final FileStream f = new FileStream(c.createTempDir());
        final byte[] pattern = new byte[1000 * 1000];
        new Random(8).nextBytes(pattern);
        final java.util.concurrent.atomic.AtomicLong published =
                new java.util.concurrent.atomic.AtomicLong();
        final java.util.concurrent.atomic.AtomicBoolean stop =
                new java.util.concurrent.atomic.AtomicBoolean();
        Run[] readers = new Run[4];
        for (int i = 0; i < readers.length; i++) {
            final int seed = i;
            readers[i] = new Run(() -> {
                Random r = new Random(seed);
                byte[] dest = new byte[500];
                while (!stop.get()) {
                    long end = published.get();
                    long first = f.getFirstPos();
                    if (end - first < dest.length) continue;
                    long pos = first + (long) (r.nextDouble() * (end - first - dest.length));
                    if (seed == 0) Thread.currentThread().interrupt();
                    try {
                        f.read(pos, dest, 0, dest.length);
                    } catch (ReadBelowFirstPosException e) {
                        continue;
                    } finally {
                        if (seed == 0) Assert.assertTrue(Thread.interrupted());
                    }
                    for (int j = 0; j < dest.length; j++) {
                        Assert.assertEquals(pattern[(int) ((pos + j) % pattern.length)], dest[j]);
                    }
                }
            });
        }
        byte[] chunk = new byte[37 * 1000];
        long length = 0;
        for (int i = 0; i < 300; i++) {
            for (int j = 0; j < chunk.length; j++) {
                chunk[j] = pattern[(int) ((length + j) % pattern.length)];
            }
            f.append(chunk, 0, chunk.length);
            length += chunk.length;
            published.set(length);
            if (i % 20 == 19) {
                f.pretruncate(Math.max(0, length - 2 * 1000 * 1000));
            }
        }
        stop.set(true);
        for (Run r : readers) r.finish();
        f.close();
    }
    
    // ---- bergdb 005-63: one stream per directory ----
    
    /**
     * bergdb 005-63: a second FileStream on the directory in the same JVM is refused, also by
     * another path to it, and the first goes on; after the first's close(), a new one opens.
     */
    @Nano
    public static void testSecondStreamRefused(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir);
        byte[] bytes = new byte[] {1, 2, 3};
        f.append(bytes, 0, bytes.length);
        for (File path : new File[] {dir, new File(dir, ".")}) {
            try {
                new FileStream(path).close();
                throw new AssertionError("a second FileStream opened " + path.getPath());
            } catch (DirectoryInUseException e) {
                Assert.assertTrue(e.getMessage(), 
                        e.getMessage().contains("is in use by another BergDB database"));
            }
        }
        f.append(bytes, 0, bytes.length);
        byte[] b = new byte[6];
        f.read(0, b, 0, b.length);
        Assert.assertEquals(3, b[5]);
        f.close();
        
        FileStream f2 = new FileStream(dir);
        Assert.assertEquals(6, f2.getLength());
        f2.close();
    }
    
    /**
     * bergdb 005-63: bergdb.lock holds its text, is not a stream file, and stays as it is
     * through appends, a cut, a close, a new open and seekFirstPos(). A directory without it,
     * as from 2026.1, opens and gets one.
     */
    @Nano
    public static void testLockFile(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        File lock = new File(dir, LOCK_NAME);
        byte[] text = LOCK_TEXT.getBytes(StandardCharsets.UTF_8);
        FileStream f = new FileStream(dir);
        Assert.assertArrayEquals(text, Files.readAllBytes(lock.toPath()));
        byte[] bytes = new byte[500 * 1000];
        new Random(9).nextBytes(bytes);
        f.append(bytes, 0, bytes.length);
        f.pretruncate(200 * 1000);
        f.awaitDeletes();
        Assert.assertEquals(2, f.getSortedDbFiles().length);
        f.close();
        
        FileStream f2 = new FileStream(dir);
        Assert.assertEquals(2, f2.dbFiles.length);
        readAndCheck(f2, 300 * 1000, 1000, bytes);
        f2.seekFirstPos(2000 * 1000);
        f2.close();
        Assert.assertArrayEquals(text, Files.readAllBytes(lock.toPath()));
        
        Assert.assertTrue(lock.delete());
        FileStream f3 = new FileStream(dir);
        Assert.assertEquals(2000 * 1000, f3.getFirstPos());
        f3.close();
        Assert.assertArrayEquals(text, Files.readAllBytes(lock.toPath()));
    }
    
    /**
     * bergdb 005-63: a FileStream in another process holds the directory. The open here is
     * refused; after the child is killed (destroyForcibly(), as kill -9), it opens. And a
     * refusal in this JVM does not release the lock for other processes: a child's open is
     * refused while this JVM holds the directory, also after a second FileStream here was
     * refused. Without LOCKED_DIRS, that refusal closed its channel of the lock file, which
     * released this JVM's lock on macOS and Linux, and the child opened the directory.
     */
    @Nano("f")
    public static void testLockAcrossProcesses(TestEnvironment c) throws Exception {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = c.createTempDir();
        
        Process holder = startLockChild("hold", dir);
        try {
            Assert.assertEquals("held", firstLine(holder));
            try {
                new FileStream(dir).close();
                throw new AssertionError("opened a directory that another process holds");
            } catch (DirectoryInUseException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("another process"));
            }
        } finally {
            holder.destroyForcibly();
        }
        Assert.assertTrue("the child ends", 
                holder.waitFor(60, java.util.concurrent.TimeUnit.SECONDS));
        
        FileStream f = new FileStream(dir);
        try {
            Assert.assertEquals("refused", runLockChild(dir));
            try {
                new FileStream(dir).close();
                throw new AssertionError("a second FileStream opened");
            } catch (DirectoryInUseException e) {
                // Expected.
            }
            Assert.assertEquals("refused", runLockChild(dir));
        } finally {
            f.close();
        }
        Assert.assertEquals("opened", runLockChild(dir));
    }
    
    private static Process startLockChild(String mode, File dir) throws IOException {
        String javaBin = System.getProperty("java.home") + "/bin/java";
        String cp = System.getProperty("java.class.path");
        return new ProcessBuilder(javaBin, "-cp", cp, LockChild.class.getName(), mode, 
                dir.getPath()).redirectErrorStream(true).start();
    }
    
    /** Runs a child that tries to open 'dir', and returns the first line it prints. */
    private static String runLockChild(File dir) throws Exception {
        Process p = startLockChild("try", dir);
        String line = firstLine(p);
        Assert.assertTrue("the child ends", p.waitFor(60, java.util.concurrent.TimeUnit.SECONDS));
        return line;
    }
    
    private static String firstLine(Process p) throws IOException {
        java.io.BufferedReader in = new java.io.BufferedReader(
                new java.io.InputStreamReader(p.getInputStream(), StandardCharsets.UTF_8));
        return in.readLine();
    }
    
    /**
     * testLockAcrossProcesses' child: "hold" opens a FileStream on the directory, prints
     * "held" and keeps it until killed, or until its input ends; "try" prints "opened" or
     * "refused".
     */
    public static class LockChild {
        public static void main(String[] args) throws Exception {
            File dir = new File(args[1]);
            if (args[0].equals("hold")) {
                new FileStream(dir);
                System.out.println("held");
                System.out.flush();
                while (System.in.read() != -1) {
                    // Until killed, or the parent is gone.
                }
            } else {
                try {
                    new FileStream(dir).close();
                    System.out.println("opened");
                } catch (DirectoryInUseException e) {
                    System.out.println("refused");
                }
            }
        }
    }
}
