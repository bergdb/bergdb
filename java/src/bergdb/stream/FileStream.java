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
 * 
 * The files and the disk (2026-11-26, bergdb 028-62). A new file gets the largest of these
 * sizes that is at most a tenth of the stream that the files hold when it is made, from the
 * first file's start to the length: 200 kB below 10 MB, 1 MB from 10 MB, 5 MB from 50 MB;
 * a quarter until 2026-11-26. A larger size than the last file's begins only at a length
 * that is a multiple of the next larger size, a smaller one at once (determineFileSizeIndex).
 * The stream moves to a new file only when the last one has reached its size; a start gives
 * the last file the smallest size not below the lengths of the last two files. A cut
 * (pretruncate) deletes whole files only, those that end before its position, and never the
 * last one. So the files hold the stream from the start of the file that the cut's position
 * lies in: the disk can hold up to about one file more than the stream, about a tenth of the
 * stream when that file was made, and, for a while after a cut, the files that the cut's
 * thread has not yet deleted (since 2026-11-26 a batch at a time, the directory forced once
 * after it: runCuts, bergdb 028-66). This holds also after the stream has shrunk: a database
 * emptied after a large stream keeps the file that its first position lies in until appends
 * fill it (bergdb 033, RB-011: in bergdb 031-02's RetainChurn, seed 5, 10,400 kB of a 20 MB
 * file on disk for 61 kB of stream with the quarter, 400 kB with the tenth). A start accepts
 * files of any of the sizes beside each other, those of the quarter beside those of the
 * tenth: it checks that each file begins where the one before ends, or after a gap (below,
 * "A gap in the files"), and that every file but the last is a multiple of 100,000 bytes
 * long (checkDbFiles; testMixedFileSizes).
 * 
 * A backup by a copy of the files (2026-11-26, bergdb 028-62). This class changes a file
 * only by appends at its end, and removes files only whole, by deletes, issued oldest first
 * (runCuts); it never renames a file, and never writes a byte of one twice but in one case: the first
 * append after an open that left a tail of zeros of the last file out of the stream
 * (below; bergdb 028-60) truncates the file where the zeros begin and then writes there.
 * Recovery after a crash appends too (RecoverableStream). So the stream's files (*.bergdb),
 * copied in the order of their names, are a backup; bergdb.lock is not needed:
 * - Of a closed stream (a stopped database), the copy is the stream.
 * - Of an open one (a running database), a copy that lists the files and then copies them
 *   in that order, the last one last, holds the stream as a kill of the process would
 *   leave it at the moment the copy read the last file's end: every file before the last
 *   whole, as they never change, and the last one up to some point of the appends, its end
 *   possibly torn (on macOS possibly zeros within its length, as after a kill: bergdb 033,
 *   RB-012). A start on the copy recovers it as after a kill. A file made after the
 *   listing is not in the copy, which then ends as at a kill before that file.
 * - Except a copy that overlaps the first append after the open: when the open left zeros
 *   out (after a kill, or of a copy that ended in zeros), the copy can hold the old file's
 *   zeros in place of bytes written after them: it is not a backup. So a copy begins after
 *   an append of at least one byte since the open has returned (an append of nothing does
 *   not cut the zeros), or after close() has returned. For a running
 *   database: after a transaction that changed something, committed since the start, and
 *   a sync() that returned after it; a commit alone is not enough, as it can return
 *   before its bytes reach this class (BufferedStream). For a stopped one: after its
 *   close() has returned; stop() returns before the close ends.
 * - A file that a cut deletes while the copy reads it stays readable to the copy on macOS
 *   and Linux; the copy then holds files that the stream no longer has, as after a crash
 *   before a cut's deletes, and a start on it cuts again (Reclaim). A listed file that a cut
 *   deleted before the copy opened it is missing. A copy with such a gap after files copied
 *   before it opens from the first file after the gap (below); one that misses only its
 *   first files opens from its first file. Either can lack the record of the cut that
 *   deleted the missing files, which may be in a file made after the listing; a start then
 *   refuses the copy, as its first position is after that copy's cut, and writes nothing
 *   before it refuses but what recovery writes at a torn end (Db, start(); bergdb 028-66):
 *   take the copy again. A start that takes such a copy deletes the files before the gap.
 * - Not run on Windows, where a delete of a file that a copy program holds open can fail,
 *   which fails the stream.
 * 
 * A gap in the files (2026-11-27, bergdb 028-66). The cut's thread deletes the files of a cut
 * a batch at a time, the directory forced once after the batch, not after each file
 * (runCuts); a power loss can then keep the delete of a file and lose that of an older one,
 * as no order of the deletes on the device is assumed. So the open takes a gap in the files'
 * sequence, a file that begins after the end of the one before it, as the end of what is
 * not the stream: the stream is the files after the last gap, its first position the first
 * of them's, and the files before it, the leftovers, are not opened or read. A read below
 * the first position throws ReadBelowFirstPosException, whose message names the gap. The
 * first cut at or after the first position, pretruncate(), deletes the leftovers, oldest
 * first, before the files that it takes off; a cut before it deletes none of them. Why this
 * is safe: a file is missing only if a cut deleted it, and the cut's thread deletes a file
 * only after the stream is forced up to its length at the cut (forceTo()), after the
 * record of the cut, which the database writes and makes durable before it cuts (Reclaim,
 * cutIfDurable). So the record of a cut at or after the gap's end survives every power
 * loss that the deletes can leave, and the database's start, which reads its cut from the
 * stream, finds the cut at or after the first position and cuts there (Reclaim,
 * initFromDb); a stream whose first position is after its cut lacks bytes of the database,
 * and the start refuses it before it deletes anything (bergdb 028-66; Db, start()). Not
 * refused, as before 2026-11-27: files before the gap that are not a cut's leftovers, such
 * as another database's put into the directory by hand; the start of the stream after the
 * gap deletes them if it finds its cut at or after the gap's end. Still refused
 * (BadDirStateException): a bad name, a file that begins before the end of the one before
 * it, and a file but the last whose length is not a multiple of 100,000 bytes.
 * 
 * A tail of zeros (2026-11-26, bergdb 028-60; 033, RB-012). At the open, before anything
 * reads the stream, the constructor leaves a run of zero bytes of at most 8 MB at the end
 * of the last file (ZERO_TAIL_MAX) out of the stream: the stream's length ends where the
 * run starts, reads stop there, and appends begin there. The file is not changed at the
 * open: the first append truncates it where the run starts and forces it, also with
 * per-append forcing off, before it writes, and so does a cut that deletes files before it
 * (pretruncate(): else a last file of zeros only, left as the only file, would be taken
 * whole by the next open); close() and an append of nothing do not. So an
 * open that is closed before an append, as a start refused before it writes (another node
 * size, an unsupported version, bytes that are not BergDB's stream format), leaves the
 * files as they were. A start's recovery
 * may append before a later check refuses the start; then the cut is made. The same rule on
 * every operating system and file system, with no detection of either (Frans, 2026-11-26).
 * A kill of the process during an append can leave the last file with zeros within its
 * length on APFS (macOS), from a page boundary on, where the cut write's bytes should be
 * (bergdb 031-02, F1; 035-01); without them the layers above see a stream cut short, a
 * prefix of what was appended (AppendOnlyStream, "CRASHES"), and the start's recovery
 * completes and aborts the torn last record. Safe for BergDB's stream format: a committed
 * record and a valid meta block end in the byte 10, so the zeros at the end hold no
 * committed transaction. A longer run is left in the stream, and the start takes it as
 * before: as a cut tail where its zeros begin inside the last record, else refused, "Bad
 * transaction size in db stream, 0, spos P" (Database, "What a crash keeps"); so is a
 * stream whose only file is all zeros, so that the repair never empties a stream
 * (DatabaseBuilder's open() would then create a database in its place). The bound limits a
 * silent repair in the case outside the contract, a power loss that destroyed forced
 * bytes. Bytes that are not zero are never left out (stale bytes after a kill, bergdb
 * 028-67). The rule holds for every stream that this class opens, with no way to turn it
 * off: a stream of other bytes than BergDB's format, whose last byte can be zero, loses
 * its trailing zeros at each open that appends; BergDB has no such stream since its
 * internal encryption was removed (2026-11-27, bergdb 028-69).
 * getZeroTailRemoved() tells how many bytes the open left out.
 * 
 * Each file is named &lt;14-digit index&gt;.bergdb. The index is the file's first stream 
 * position divided by 100,000, padded with zeros (indexToString).
 * The first two files are: 00000000000000.bergdb, 00000000000002.bergdb. A new stream has
 * no file until its first append, which creates the first (2026-11-06, bergdb 015-06).
 * 
 * Hard sync, the default. Every append is forced to the device before it returns: the
 * bytes are written, then FileChannel.force(true) (F_FULLFSYNC on macOS, fsync on Linux). A
 * new file and its directory entry are forced before the file takes appends. So a completed
 * append means durable bytes, not only bytes in the OS cache, and StorageManager's
 * durable length, which sync() waits for, holds after a power loss, not only after a
 * process crash (2026-10-14, bergdb 011-07).
 * 
 * Per-append forcing off (the constructor's forceAppends false; 2026-11-04, bergdb 005-47).
 * An append writes its bytes, handing them to the operating system, and returns: a
 * completed append means written, not forced, and so does StorageManager's durable length.
 * The bytes survive a crash of the process, when the OS goes on and writes them later; a
 * crash of the OS or a power loss can lose them, also after a sync returned. These forces
 * stay, each a no-op with forcing on, where every byte is forced already:
 * a file opened for appends and its directory entry, before the file takes appends; the
 * last file before the stream moves to a new file, so that no file before the last is
 * short; the last file before the files of a cut are deleted, so that reclaim's decision,
 * which the cut waits for, is on the device before the files it replaces are gone; and the
 * last file at close(), so that a clean stop is durable.
 * A known limit: the OS may write the unforced tail out of order, and a power loss or a
 * crash of the OS can then leave a hole in it, zeros with later bytes intact. Recovery does
 * not handle such a hole (bergdb 005-83, "Power-loss tail experiment": all 56 hole images
 * failed; open in bergdb 014-01): the database may refuse to start, or start and fail
 * reads, which is more than a loss of the last transactions. With forcing on, the window
 * is the one append between its write and its force.
 * 
 * A force costs a device round trip: well under a millisecond on a fast SSD, more
 * on a slow virtual disk. This class is meant to be used below BufferedStream,
 * which controls the buffering: it collects the database's appends and writes them
 * here in chunks, from a thread of its own, when a buffer time has passed or its
 * buffer is full. So with forcing on there is one force per chunk, not one
 * per transaction, and a transaction waits for a force only when it asks for a sync.
 * 
 * Reads wait for no write (2026-10-27, bergdb 005-46). A read takes no lock: it reads
 * with positional reads on a channel of the file's own, and finds its file in a list
 * that the writer replaces, never changes. The writer, its append and force, a new file
 * with its forces, and a cut, holds no lock that a read takes; a cut only takes its files
 * off the list, and a thread of its own deletes them, in the same order as before (a batch
 * at a time, the directory forced once after it, since 2026-11-27, bergdb 028-66). Before,
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
 * Within the JVM, so is one at the path while a stream that opened the directory at that
 * path is open, also when the directory was deleted, moved or replaced since; and such a
 * stream fails before it makes, deletes or opens again a file by its name there
 * (checkDirectory(), 2026-11-09, bergdb 021-20), but for a replacement in a short window
 * right before such a step, usually microseconds, longer if the thread is paused, as by a
 * GC (bergdb 021-24).
 * The operating system holds the lock and drops it when the process ends, also at a crash,
 * so a lock is never stale; the file is never deleted, and its text is for people. The lock
 * is on one byte far beyond the end of the file: on Windows a lock is mandatory, and the text
 * stays readable. Within the JVM, a set of the locked directories (LOCKED_DIRS) refuses a
 * second FileStream before it opens the file: on macOS and Linux, closing any channel of the
 * file releases the process's lock (FileLock's Javadoc, "Platform dependencies"). Each class
 * loader that loads BergDB has a set of its own, so a system property per locked directory,
 * bergdb.lock.KEY, does the same across them (2026-11-03, bergdb 015-24); a program that
 * replaces the system properties while a database is open loses that refusal. That set and
 * those properties are global state, a deviation from bergdb 010-P9.
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
    
    /**
     * The longest tail of zero bytes at the end of the last file that the open leaves out of
     * the stream (zeroTailLength(); 2026-11-26, bergdb 028-60): 8 MB, decimal. A write of
     * BufferedStream's thread is at most 5 MB (bergdb 026-07); the zeros that a kill left on
     * APFS were 115 to 459 kB (bergdb 031-02, F1), in 035-01 within one piece of a write
     * (bergdb 035-01).
     */
    public static final long ZERO_TAIL_MAX = 8*M;
    
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
     * The directories that FileStreams of this copy of the class hold, by lockKey() (bergdb
     * 005-63); each class loader that loads the class has its own (bergdb 015-24). A second
     * FileStream on a directory is refused here, before it opens the lock file: closing its
     * channel would release the first's lock for other processes.
     */
    private static final Set<Object> LOCKED_DIRS = 
            Collections.synchronizedSet(new HashSet<Object>());
    
    /**
     * The system properties that hold the directories of all the JVM's copies of the class,
     * one per class loader that loads it (bergdb 015-24): the name is PROPERTY_PREFIX and
     * lockKey(), the value the holder's COPY. A directory that another copy holds is refused
     * here, before the lock file is opened, as LOCKED_DIRS does within a copy. The names are
     * a contract between the versions of BergDB in one JVM, as the lock is between processes.
     */
    private static final String PROPERTY_PREFIX = "bergdb.lock.";
    
    /** This copy of the class, unique among the JVM's copies: the value of its properties. */
    private static final String COPY = "FileStream " + Long.toHexString(System.nanoTime()) 
            + "." + Integer.toHexString(System.identityHashCode(LOCKED_DIRS));
    
    private final File dir;
    private final FileStreamIo io;
    
    /** Per-append forcing (bergdb 005-47): on, every append is forced before it returns. */
    private final boolean forceAppends;
    
    /**
     * The number of zero bytes at the end of the last file that the open left out of the
     * stream (zeroTailLength(); bergdb 028-60), 0 if none. Set by the constructor.
     */
    private long zeroTailRemoved = 0;
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
    
    /**
     * The files before the last gap at the open, oldest first, not opened: not of the stream;
     * the first cut at or after the first position deletes them (bergdb 028-66). Under this.
     */
    private DbFile[] leftovers = new DbFile[0];
    
    /** The gap that the open found, for the messages of reads below it, or null (028-66). */
    private volatile String gap = null;
    
    /** The cut's thread while it runs, or null. Under this. */
    private Thread cutThread = null;
    
    /** If not null, this stream should be considered faulty and not used any further. */
    private volatile IOException ioException = null;
    
    /**
     * The cut's failure for an exception other than an IOException, made in advance, so that
     * the cut's thread records it without allocating, also when the heap is full (2026-11-06,
     * bergdb 019-39). Its stack trace is the stream's opening; its cause has the cut's.
     */
    private final IOException cutFailure =
            new IOException("The delete of a cut failed (the cause).");
    
    /** The open lock file, which holds the directory's lock, or null. Under this. */
    private RandomAccessFile lockFile = null;
    
    /** This stream's key in LOCKED_DIRS while it holds the lock. Under this. */
    private Object lockKey = null;
    
    /** This stream's path key in LOCKED_DIRS (pathKey()) while it holds the lock. Under this. */
    private Object lockPathKey = null;
    
    /**
     * The directory's lockKey() when the stream locked it, kept after the close; see
     * checkDirectory() (bergdb 021-20).
     */
    private volatile Object dirKey = null;
    
    /**
     * The stream length at the latest cut (bergdb 005-47): the cut's thread has every byte
     * before it forced before it deletes. Under this.
     */
    private long cutForceTo = 0;
    
    /**
     * Creates a new stream if it does not exist or opens an existing one if it exists.
     * If the directory 'dir' does not exist an attempt to create it is made. A new stream's
     * first file is created by its first append (bergdb 015-06): a stream closed before one
     * leaves the directory with no stream file, only bergdb.lock.
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
        this(dir, new FileStreamIo(), true);
    }
    
    /**
     * As FileStream(dir), with per-append forcing on or off (2026-11-04, bergdb 005-47); see
     * the class's Javadoc. True is FileStream(dir): every append is forced to the device
     * before it returns. False: an append is written and returns; its bytes survive a crash of
     * the process, not one of the OS or a power loss. A power loss or a crash of the OS can
     * also leave a hole in the unforced tail, which recovery does not handle (bergdb 014-01):
     * the database may then refuse to start, or fail reads. Throws as FileStream(dir).
     */
    public FileStream(File dir, boolean forceAppends) throws IOException {
        this(dir, new FileStreamIo(), forceAppends);
    }

    /** 
     * Internal, for testing.
     * As FileStream(dir), with the given persistence boundary; for fault tests.
     */
    public FileStream(File dir, FileStreamIo io) throws IOException {
        this(dir, io, true);
    }
    
    /** 
     * Internal, for testing.
     * As FileStream(dir, forceAppends), with the given persistence boundary; for fault tests.
     */
    public FileStream(File dir, FileStreamIo io, boolean forceAppends) throws IOException {
        if (dir == null) {
            throw new IllegalArgumentException("dir == null not allowed");
        }
        
        this.dir = dir;
        if (io == null) {
            throw new IllegalArgumentException("io == null not allowed");
        }
        this.io = io;
        this.forceAppends = forceAppends;
        try {
            createDirIfNeeded();
            lockDir();
            handleExistingFiles();
        } catch (IOException | RuntimeException | Error e) {
            // An Error too (2026-11-05, bergdb 015-32): it left the directory in LOCKED_DIRS,
            // and a new FileStream on it was refused until the JVM ended.
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
        Util.checkRange(dest, destOffset, length);     // Bergdb 019-02: IndexOutOfBounds.
        
        if (dbFiles.length == 0 && spos >= getFirstPos()) {
            // No file before the first append (bergdb 015-06): the stream is empty. As a read
            // of the empty first file was, it reads 0 bytes at 0, and any other read is past
            // the end. A file once made stays: a cut keeps the last one.
            if (spos == 0 && length == 0) {
                return;
            }
            throw new EOFException("Cannot read " + length + " bytes at spos " + spos 
                    + ", the stream is empty.");
        }
        
        int actuallyRead;
        int leftToRead;
        
        while (true) {
            DbFile k = findFile(spos);
            if (k == null) {
                long first = getFirstPos();
                if (spos < first) {
                    // 2026-10-13 (bergdb 011-04, W1): a read admitted before a
                    // cut can come here. It fails alone; the stream is not faulty.
                    String g = gap;
                    throw new ReadBelowFirstPosException("Cannot read at spos " + spos
                            + ", below the first position, " + first + "."
                            + (g == null ? "" : " " + g));
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
        
        // Refused before anything changes (2026-11-05, bergdb 015-26): a negative len was
        // added to the last file's length and to the stream's, which hid appended bytes and
        // failed the next append. A len past the array, an IndexOutOfBoundsException before,
        // too (bergdb 019-02).
        Util.checkRange(source, sourceOffset, len);
        if (len == 0) {
            return;
        }
        if (dbFiles.length == 0) {
            newFile();      // The stream's first file (bergdb 015-06).
        }
        
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
     * stream's failure, such as a failed delete of a cut; also when called again, as
     * BufferedStream.close() does after its thread's close. A read of a file that the close
     * has closed is not a failure of the stream (bergdb 015-17). With per-append forcing off,
     * it first forces the last file, unless the stream has failed, so that a clean stop is
     * durable (bergdb 005-47).
     */
    public void close() throws IOException {
        awaitCutThread();
        // An I/O failure must not prevent release of the remaining handles,
        // including handles left after a partially completed pretruncate.
        IOException failure = ioException;
        synchronized (this) {
            if (failure == null && dbFiles.length > 0) {
                try {
                    findLastFile().forceWritten(FileStreamIo.Force.CLOSE);
                } catch (IOException e) {
                    failure = e;
                }
            }
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
    
    /** Whether every append is forced before it returns, the default (bergdb 005-47). */
    public boolean forcesAppends() {
        return forceAppends;
    }
    
    /**
     * Call this method with "true" to never use stream files larger than 2e9 bytes.
     * This is useful on file systems with a limited maximum file size; for example FAT32 
     * has a maximum file size of 2^32−1 (about 4.29e9 bytes).
     * It holds for the files that the stream creates after the call (bergdb 015-33); call it
     * right after the constructor. A stream written without it can have larger files, and
     * its last file can still grow to the size chosen at the start.
     */
    public void setMax2G(boolean b) {
        synchronized (this) {
            this.max2G = b;
        }
    }
    
    public long getFirstPos() {
        return firstPos;
    }

    /**
     * Erases the stream and makes it start at 'pos', at or above the length and a multiple of
     * the smallest file size: the length and the first position are 'pos'. For this class's
     * own tests, which use it to make large positions (bergdb 019-04); AppendOnlyStream had it,
     * as seekFirstPos(), until 2026-11-05, for replication, which is gone (bergdb 005-11).
     * 
     * @throws IllegalStateException  If the length is greater than 'pos'.
     */
    synchronized void seekFirstPos(long pos) throws IOException {
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
     * 
     * A cut at or after the first position takes off the files before a gap that the open
     * found, the leftovers, too, before its own (2026-11-27, bergdb 028-66; the class's
     * Javadoc, "A gap in the files"); a cut before the first position takes none of them.
     */
    public synchronized void pretruncate(long pos) throws IOException {
        checkIOException();
        
        int index = -1;      // index of last file to delete
        
        long len = getLength();
        if (pos > len) {
            throw new IllegalArgumentException("pos > length of stream (" + len + ").");
        }
        
        // The last file is kept, as a file that the cut ends in is (2026-11-05, bergdb
        // 015-31): a cut at the length took every file, also the empty one of a new stream,
        // and threw a Bug.
        DbFile[] files = dbFiles;
        for (int i = 0; i < files.length - 1; i++) {
            DbFile k = files[i];
            if (k.spos + k.fileLength - 1 < pos) {
                index = i;
            } else {
                break;
            }
        }
        
        if (index != -1) {
            // The zeros that the open left out are cut from the last file first (2026-11-26,
            // bergdb 028-60): a last file of zeros only that the cut leaves as the only file
            // would be taken whole at the next open (zeroTailLength()), past the length.
            files[files.length - 1].cutZeroTailIfPending();
        }
        
        // The leftovers, before the files of the cut: the deletes are issued oldest first.
        // They leave the stream's files as they are, so the zeros need no cut for them.
        boolean queued = false;
        if (leftovers.length > 0 && pos >= getFirstPos()) {
            for (DbFile k : leftovers) {
                k.isDeleted = true;
                cutFiles.addLast(k);
            }
            leftovers = new DbFile[0];
            gap = null;
            queued = true;
        }
        
        if (index != -1) {
            int newSize = files.length - (index + 1);
            
            DbFile[] newFiles = new DbFile[newSize];
            System.arraycopy(files, index + 1, newFiles, 0, newSize);
            for (int i = 0; i <= index; i++) {
                files[i].isDeleted = true;      // A read that holds it throws (see DbFile.read).
                cutFiles.addLast(files[i]);
            }
            
            this.firstPos = newFiles[0].spos;
            this.dbFiles = newFiles;
            queued = true;
        }
        
        if (queued) {
            this.cutForceTo = len;
            
            if (cutThread == null) {
                Thread t = new Thread(new Runnable() {
                    public void run() {
                        runCuts();
                    }
                });
                t.setName("FileStream-cut");
                t.setDaemon(true);
                Util.start(t);
                // Set once started (2026-11-06, bergdb 019-39): a thread that could not start
                // stayed set, and close() waited for it for ever. The thread waits for this
                // monitor, so it finds itself set.
                cutThread = t;
            }
        }
    }
    
    /**
     * The cut's thread: deletes the files that cuts took off, oldest first (bergdb 005-46), a
     * batch at a time (2026-11-27, bergdb 028-66): the files that the cuts so far took off,
     * their deletes issued oldest first, then one force of the directory; files that a cut
     * takes off meanwhile are the next batch. Until 2026-11-27 it forced the directory after
     * each file, as pretruncate() did before 005-46, so that a power loss could not keep the
     * delete of a newer file and lose that of an older one, which left a gap that a start
     * refused: a directory force is a device flush (about 6 ms on F53 alone, more beside a
     * writer's forces), and with new files a tenth of the stream kept (bergdb 028-62) a writer
     * with hard sync at full speed wrote about 40 % slower and the deletes lagged, the disk
     * 1.4 to 1.6 times the stream kept (bergdb 028-66 has the figures).
     * 
     * No order of the deletes on the device is assumed: a power loss can keep any of the
     * deletes of a batch whose force has not returned and lose the others. A gap that this
     * leaves is taken at the open (the class's Javadoc, "A gap in the files"). What the
     * argument needs is that a file is deleted only after the record of the cut that took it
     * off is on the device: before a batch, the thread has the stream forced up to its length
     * at the latest cut (2026-11-04, bergdb 005-47), a no-op with per-append forcing on; every
     * file of the batch ends before that length, and the record is before it, as Reclaim
     * cuts only when the durable length has passed its decision (Reclaim,
     * pendingCutDurableAt); with forcing off that length means written. Deletes are issued
     * oldest first for a copy of the files in the order of their names (the class's Javadoc,
     * "A backup"), which sees the directory as the deletes leave it, not as the device has
     * it. A crash before a file is deleted leaves it, and the next start cuts again (Reclaim).
     * It ends when nothing is left to delete, or at a failure, which it keeps as the
     * stream's: the files of the batch that it has not deleted stay on the queue, and
     * close() closes them.
     */
    private void runCuts() {
        try {
            while (true) {
                int batch;
                long forceTo;
                synchronized (this) {
                    batch = cutFiles.size();
                    if (batch == 0 || ioException != null) {
                        cutThread = null;
                        notifyAll();
                        return;
                    }
                    forceTo = cutForceTo;
                }
                
                try {
                    forceTo(forceTo);
                    // Cuts add files at the end only, so the batch is the first 'batch' files.
                    // A file leaves the queue once deleted: close() needs only those that are
                    // not, to close them after a failure.
                    for (int i = 0; i < batch; i++) {
                        DbFile k;
                        synchronized (this) {
                            k = cutFiles.peekFirst();
                        }
                        k.delete();
                        synchronized (this) {
                            cutFiles.removeFirst();
                        }
                    }
                    forceDirectory(dir);
                } catch (IOException e) {
                    ioException = e;
                } catch (RuntimeException | Error e) {
                    // Recorded with nothing allocated (2026-11-06, bergdb 019-39): a new
                    // IOException could throw too, and the thread ended with no failure.
                    // At most once: no cut follows a failure.
                    cutFailure.initCause(e);
                    ioException = cutFailure;
                }
            }
        } finally {
            // Also when the thread dies (2026-11-06, bergdb 019-39): close() waits for it.
            synchronized (this) {
                if (cutThread == Thread.currentThread()) {
                    cutThread = null;
                    notifyAll();
                }
            }
        }
    }

    /**
     * Has every byte before 'pos' forced (bergdb 005-47). Every file before the last is
     * whole and forced, by the force before a new file (SWITCH); so only the last file can
     * hold unforced bytes, and only if it starts before 'pos'. The cut's thread.
     */
    private void forceTo(long pos) throws IOException {
        DbFile last = findLastFile();
        if (last.spos < pos) {
            last.forceWritten(FileStreamIo.Force.CUT);
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
     * Whether 'dir' holds a stream file (*.bergdb) with at least one byte (2026-11-03,
     * bergdb 015-01): false for a directory that does not exist, holds none, or holds only
     * empty ones. It opens nothing and takes no lock; a running stream always has a file with
     * bytes once its database is created, and a cut never removes the last file. For the
     * Pub API's start, which refuses a directory that held a database (created.txt) and has
     * no stream byte.
     *
     * @throws IOException  If 'dir' is a directory that cannot be listed: an I/O error, or no
     *         permission to read it (bergdb 020-20). Until 020-20 that was false, and the Pub
     *         API's start called such a directory one whose stream is missing.
     */
    public static boolean hasStreamBytes(File dir) throws IOException {
        if (!dir.isDirectory()) {
            return false;
        }
        for (File f : listFiles(dir, null)) {
            if (f.getName().endsWith(SUFFIX) && f.isFile() && f.length() > 0) {
                return true;
            }
        }
        return false;
    }

    /**
     * @throws IOException  If directory does not exist and cannot be created, or exists and
     *      is not a directory.
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
            if (!dir.isDirectory()) {
                // 2026-11-09 (bergdb 020-24-08, U8-11): lockDir() threw "Not a directory",
                // without the path.
                throw new IOException("Directory " + dir.getPath() + " could not be opened: "
                        + "it exists and is not a directory.");
            }
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
            // 2026-11-09 (bergdb 020-24-10, U10-5): mkdirs() returns false when another
            // thread or process made the directory meanwhile, and the start threw this,
            // not the lock's refusal (DirectoryInUseException), which lockDir() gives.
            if (!created && !dir.isDirectory()) {
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
     * this JVM holds the directory, of this copy of the class or of another (bergdb 015-24),
     * or holds the directory's path (pathKey(), bergdb 021-20), after if another process
     * holds the lock. Not interruptible, as the rest of this class.
     */
    private void lockDir() throws IOException {
        Object key = lockKey(dir);
        Object pathKey = pathKey(dir);
        synchronized (LOCKED_DIRS) {
            if (LOCKED_DIRS.contains(key)) {
                throw new DirectoryInUseException("Directory " + dir.getPath() 
                        + " is in use by another BergDB database in this JVM (" + LOCK_NAME 
                        + " is locked).");
            }
            if (LOCKED_DIRS.contains(pathKey)) {
                throw new DirectoryInUseException(pathInUse());
            }
            LOCKED_DIRS.add(key);
            LOCKED_DIRS.add(pathKey);
        }
        
        boolean interrupted = Thread.interrupted();
        boolean locked = false;
        try {
            // A FileStream of another copy of the class holds it (bergdb 015-24). This copy's
            // own value, which a program that puts back older system properties can leave, is
            // no holder: LOCKED_DIRS has none.
            Object holder = System.getProperties().putIfAbsent(PROPERTY_PREFIX + key, COPY);
            if (holder != null && !holder.equals(COPY)) {
                throw new DirectoryInUseException("Directory " + dir.getPath() 
                        + " is in use by another BergDB database in this JVM, in another class"
                        + " loader (" + LOCK_NAME + " is locked).");
            }
            holder = System.getProperties().putIfAbsent(PROPERTY_PREFIX + pathKey, COPY);
            if (holder != null && !holder.equals(COPY)) {
                throw new DirectoryInUseException(pathInUse());
            }
            
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
                    // Held in this JVM, not by a FileStream of it, of any copy of the class.
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
                    lockPathKey = pathKey;
                }
                dirKey = key;
                locked = true;
                return;
            }
        } finally {
            if (!locked) {
                System.getProperties().remove(PROPERTY_PREFIX + key, COPY);
                System.getProperties().remove(PROPERTY_PREFIX + pathKey, COPY);
                LOCKED_DIRS.remove(key);
                LOCKED_DIRS.remove(pathKey);
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
     * The directory's path key in LOCKED_DIRS and the system properties, beside its
     * lockKey() (2026-11-09, bergdb 021-20, from 020-24-10, U10-1): "path " and its real
     * path. A start at a path is refused while a FileStream of this JVM that opened the
     * directory at that path is open, also when that directory was deleted, moved or
     * replaced since. The lock in the directory, and the file key, refused only a start in
     * the same directory: a new database at the path of one that was deleted while it ran,
     * or after stop() while it closed, started beside it.
     */
    private static Object pathKey(File dir) throws IOException {
        return "path " + dir.toPath().toRealPath();
    }
    
    private String pathInUse() {
        return "Directory " + dir.getPath() + " is in use by another BergDB database in this"
                + " JVM: one started on the directory that was at this path, deleted, moved or"
                + " replaced since, is still open or closing.";
    }
    
    /**
     * Throws, and fails the stream, if the directory at the stream's path is no longer the
     * one that it locked, by lockKey() (2026-11-09, bergdb 021-20, from 020-24-10, U10-1): it
     * was deleted, moved or replaced while the stream had it. A stream file is made, deleted
     * and opened again by its name in the directory's path; so a stream whose directory was
     * deleted made its next files in a new database's directory at the path, and broke it,
     * or deleted that database's files at a cut. Where the key is the path (Windows), a
     * replacement is not seen, but there a directory with open files cannot be deleted.
     * 
     * Called right before each of these steps, with nothing that waits in between, and again
     * after it (2026-11-09, bergdb 021-24). newFile() checked before its force of the last
     * file (Force.SWITCH, with per-append forcing off), which can take seconds, so a
     * directory replaced during that force got the new file, and the stream went on without
     * an error; a cut's delete checked before closing the file, which waits for the reads in
     * progress. Left: a replacement in the short window between the check and the step,
     * usually microseconds, longer if the thread is paused, as by a GC, as the step opens or
     * deletes the file by its path. The check after the step then fails the stream before it
     * writes a byte there, but the step is done: a new, empty stream file in the
     * replacement, or, at a cut, the replacement's file of that name deleted. A database's
     * start there is refused until the empty file is removed, with an exception that
     * depends on what else is in the directory: BadDirStateException beside stream files of
     * its own; in a directory without others, StreamFormatException ("Could not find *any*
     * valid meta block") from create(), DatabaseMissingException from open() (bergdb 020-23,
     * reviewer v2's EmptyFileProbe). A directory replaced and put back between the two
     * checks is not seen. SecureDirectoryStream (macOS and Linux), which opens and deletes
     * relative to an open directory, could close the window; not used here.
     * 
     * The invariant that the check relies on (bergdb 020-23, section 5, V5-1): while the
     * stream holds bergdb.lock open, from lockDir() until unlockDir(), which close() calls
     * after its last file step, the old directory's inode cannot be reused, so a new
     * directory at the path has another file key. Without an open file in it, a deleted
     * directory's inode number is reused at once on Linux ext4: on s1, rm -rf and then mkdir
     * gave the same inode 50 of 50 times, and 0 of 30 with a file of it open. So the lock
     * file must stay open until the stream has made, deleted and opened its last file; do
     * not close it earlier.
     */
    private void checkDirectory() throws IOException {
        Object now;
        try {
            now = lockKey(dir);
        } catch (IOException e) {
            now = null;     // Gone.
        }
        if (now == null || !now.equals(dirKey)) {
            IOException e = new IOException("Directory " + dir.getPath() + " is no longer the"
                    + " database's directory: it was deleted, moved or replaced while the"
                    + " database had it open. Nothing more is written there.");
            ioException = e;
            throw e;
        }
    }
    
    /**
     * Releases the directory's lock, if this stream holds it; the file stays (bergdb 005-63).
     * The lock file is closed before the directory leaves the system properties and
     * LOCKED_DIRS, all in one hold of LOCKED_DIRS's monitor, under which lockDir() checks
     * (2026-11-12, bergdb 024-36, OT2). So a start in this copy of the class sees the
     * directory either before the close, still held, or after it, gone from LOCKED_DIRS,
     * never the lock file closed and the keys still listed.
     *
     * Why that matters: closing the lock file closes the last open file of a directory that
     * was deleted while the stream closed, and Linux ext4 then gives the directory's inode at
     * once to the next new directory (see checkDirectory()). Before, a start in such a new,
     * empty directory, in the moment between the close and the removal, found its file key
     * still in LOCKED_DIRS and was refused as in use by another database (s1, JDK 17: 10 in
     * 30,000 runs of a probe; 006-17, section 6.2). The start reads its key before it takes
     * the monitor, but a new directory can have the freed inode only if it was made after
     * the close, so its check, under the monitor, comes after the removal.
     *
     * The file is closed first, as a start in this JVM must not open a second channel of it
     * while it is open (LOCKED_DIRS's comment); the properties go in the same hold, so a
     * start of this copy that has passed LOCKED_DIRS cannot lose its new property to this
     * remove (the value is the copy's, the same for both streams). Left: a start in another copy of the class (another class loader, bergdb 015-24)
     * checks the properties without this monitor and can still, rarely, be refused in that
     * moment. Lock order: this stream's monitor, then LOCKED_DIRS; lockDir() takes them one
     * at a time, not nested.
     */
    private synchronized void unlockDir() throws IOException {
        if (lockFile == null) {
            return;
        }
        synchronized (LOCKED_DIRS) {
            try {
                lockFile.close();       // Releases the lock.
            } finally {
                lockFile = null;
                System.getProperties().remove(PROPERTY_PREFIX + lockKey, COPY);
                System.getProperties().remove(PROPERTY_PREFIX + lockPathKey, COPY);
                LOCKED_DIRS.remove(lockKey);
                LOCKED_DIRS.remove(lockPathKey);
                lockKey = null;
                lockPathKey = null;
            }
        }
    }

    /**
     * Handles initialization based on existing *.bergdb files.
     * 
     * @throws IOException
     * @thrown BadDirStateException
     */
    private void handleExistingFiles() throws IOException, BadDirStateException {
        File[] all = getSortedDbFiles();
        // The stream is the files after the last gap (2026-11-27, bergdb 028-66); those
        // before it are the leftovers, not opened.
        int first = checkDbFiles(all);
        File[] bergdbFiles = Arrays.copyOfRange(all, first, all.length);
        if (first > 0) {
            leftovers = new DbFile[first];
            for (int i = 0; i < first; i++) {
                leftovers[i] = new DbFile(fileSpos(all[i]), all[i], all[i].length());
            }
            long end = leftovers[first - 1].spos + leftovers[first - 1].maxSize;
            gap = "At its open the stream's directory " + dir.getPath() + " had a gap in its"
                    + " files: none held the bytes from " + end + " to " + fileSpos(all[first])
                    + ", so the stream is the files from " + all[first].getName() + " on, and"
                    + (first == 1 ? " the file before the gap, " + all[0].getName() + ", is"
                    : " the " + first + " files before the gap, " + all[0].getName() + " to "
                    + all[first - 1].getName() + ", are") + " not read (bergdb 028-66).";
        }
        determineFileSizeIndexFromFiles(bergdbFiles);
        createDbFileObjects(bergdbFiles, 0);
        if (zeroTailRemoved > 0) {
            // The last file's size from its length without the zeros (bergdb 028-60).
            DbFile[] files = dbFiles;
            long before = files.length > 1 ? files[files.length - 2].fileLength : 0;
            determineFileSizeIndexFromLengths(findLastFile().fileLength, before);
            findLastFile().maxSize = FILE_SIZES[fileSizeIndex];
        }
    }

    private void createDbFileObjects(File[] bergdbFiles, long currentSpos) throws IOException,
            BadDirStateException {
        // Creates this.dbFiles. Sets this.length.
        
        dbFiles = new DbFile[bergdbFiles.length];
        
        if (bergdbFiles.length == 0) {
            // No file: the first append creates the first (2026-11-06, bergdb 015-06). The
            // constructor created it, and a start refused after the open left it empty, which
            // breaks the restore in place of a database whose first file has another name.
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
                // The tail of zeros goes before anything reads the stream (bergdb 028-60).
                dbFiles[i] = openForRw(currentSpos, f, FILE_SIZES[fileSizeIndex], true,
                        bergdbFiles.length == 1);
            } else {
                dbFiles[i] = openForR(currentSpos, f);
            }
            
            currentSpos += dbFiles[i].fileLength;
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
            determineFileSizeIndexFromLengths(bergdbFiles[bergdbFiles.length - 1].length(),
                    bergdbFiles.length > 1 ? bergdbFiles[bergdbFiles.length - 2].length() : 0);
        }
    }
    
    /**
     * Computes and sets this.fileSizeIndex from the lengths of the last file and the one
     * before it, 0 if none: the smallest size that holds both. The last file's length is the
     * stream's part of it, without a tail of zeros that the open left out (bergdb 028-60).
     */
    private void determineFileSizeIndexFromLengths(long last, long beforeLast) {
        long fileSize = Math.max(last, beforeLast);
        
        this.fileSizeIndex = FILE_SIZES.length - 1;    // max
        
        for (int i = FILE_SIZES.length - 1; i >= 0; i--) {
            long s0 = FILE_SIZES[i];
            if (s0 < fileSize) {
                break;
            }
            this.fileSizeIndex = i;
        }
    }

    /**
     * Checks the names and lengths of the files, in the order of their names, and returns the
     * index of the first file after the last gap, 0 if there is none: a file that begins after
     * the end of the one before it (2026-11-27, bergdb 028-66; before, refused). Refused: a
     * bad name, a file that begins before the end of the one before it, and a file but the
     * last whose length is not a multiple of BYTES_PER_INDEX_UNIT.
     */
    private int checkDbFiles(File[] bergdbFiles) throws BadDirStateException {
        long currentSpos = 0;
        int first = 0;
        
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
            } else if (currentSpos < fileSpos) {
                first = i;      // A gap (bergdb 028-66).
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
        return first;
    }
    
    /** The first stream position of a file with a checked name (checkDbFiles). */
    private long fileSpos(File f) throws BadDirStateException {
        String name = f.getName();
        try {
            return stringToIndex(name.substring(0, name.length() - SUFFIX.length()))
                    * BYTES_PER_INDEX_UNIT;
        } catch (BadFormatException e) {
            throw new BadDirStateException("Bad name of bergdb file: " + f.getPath() + ".");
        }
    }
    
    /**
     * Internal, for testing (bergdb 028-66): the number of files before a gap that the open
     * found, which the first cut at or after the first position has not yet taken off.
     */
    public synchronized int getLeftoverCount() {
        return leftovers.length;
    }

    /**
     * Returns berg *.bergdb file in this.dir.
     */
    private File[] getSortedDbFiles() throws IOException {
        File[] bergdbFiles = listFiles(dir, new FilenameFilter() {
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
    
    /**
     * dir.listFiles(filter), or dir.listFiles() for a null filter; an IOException if 'dir'
     * cannot be listed: an I/O error, or no permission to read it (SpotBugs, bergdb 020-20).
     * File.listFiles() gives null then, which getSortedDbFiles dereferenced (a
     * NullPointerException from the constructor) and hasStreamBytes took for a directory
     * without a stream byte.
     */
    private static File[] listFiles(File dir, FilenameFilter filter) throws IOException {
        File[] files = filter == null ? dir.listFiles() : dir.listFiles(filter);
        if (files == null) {
            throw new IOException("Cannot list the directory " + dir.getPath()
                    + ": an I/O error, or no permission to read it.");
        }
        return files;
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
            for (DbFile k : leftovers) {
                k.delete();
                forceDirectory(dir);
            }
            leftovers = new DbFile[0];
            gap = null;
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
     * Makes a new last file; the writer's (append's, seekFirstPos'). It
     * creates and forces the file and the directory before it takes the stream's monitor, and
     * takes it only to publish the new list (2026-10-27, bergdb 005-46): every read waited for
     * the forces. No read needs the new file before an append to it has returned.
     * 
     * With per-append forcing off, it forces the old last file first (2026-11-04, bergdb
     * 005-47): a power loss must not leave a short file before a newer one, which the
     * constructor refuses (BadDirStateException). With forcing on, it is forced already.
     * 
     * openForRw() checks the directory (checkDirectory()), after that force (2026-11-09,
     * bergdb 021-24): the check came first, and a directory replaced while the force waited
     * got the new file.
     */
    private void newFile() throws IOException {
        if (this.length % BYTES_PER_INDEX_UNIT != 0) {
            throw new Bug("Illegal state, length = " + length);
        }
        
        DbFile[] files = dbFiles;
        if (files.length > 0) {
            // The last file takes no more appends; its read channel stays.
            files[files.length - 1].forceWritten(FileStreamIo.Force.SWITCH);
            files[files.length - 1].closeWriter();
        }
        
        long index = this.length / BYTES_PER_INDEX_UNIT;
        File file = new File(dir, indexToString(index) + SUFFIX);
        
        applyFileSizeChangeRules();
        
        DbFile newFile = openForRw(length, file, FILE_SIZES[fileSizeIndex], false, false);
        
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
    
    /**
     * The size of the next file (2026-11-26, bergdb 028-62): the largest of FILE_SIZES that
     * is at most a tenth of 'streamSize', the stream that the files hold, from the first
     * file's start to the length; FILE_SIZES[0] if none is. A larger size than the current
     * one begins only at a length that is a multiple of the next larger size; a smaller one
     * at once. Until 2026-11-26 the rule took a quarter: an emptied database kept the file
     * that its first available position was in, up to a quarter of the stream when the file
     * was made (bergdb 033, RB-011).
     */
    private int determineFileSizeIndex(int currentFileSizeIndex, long streamLength, long streamSize) {
        long currentSize = FILE_SIZES[this.fileSizeIndex];
        long size = streamSize / 10;    // a quarter until 2026-11-26 (bergdb 028-62)
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
        
        // The result is capped, not the current index (2026-11-05, bergdb 015-33): a start
        // chooses the size from the last two files, so a small current size could jump to
        // the rule's size, such as 10 GB, past the cap.
        if (max2G && result > INDEX_2G) {
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
    
    /**
     * Opens a file for appends, and makes it if it is not there: the last file at a start,
     * and newFile()'s. The directory is checked right before the open, with nothing that
     * waits in between, and again after the steps by name (2026-11-09, bergdb 021-24; see
     * checkDirectory()). With 'zeroTail', the last file at a start, a tail of zeros is left
     * out of the stream, and cut from the file at its first append (zeroTailLength(); bergdb
     * 028-60); 'onlyFile' says that the file is the stream's only one.
     */
    private DbFile openForRw(long spos, File file, long maxSize, boolean zeroTail,
            boolean onlyFile) throws IOException {
        DbFile k = new DbFile(spos, file, maxSize);
        checkDirectory();
        k.rfile = io.open(file);
        try {
            // Read only; the file is not changed here (bergdb 028-60).
            final long zeros = zeroTail ? zeroTailLength(k.rfile, onlyFile) : 0;
            // Persist both the file and its directory entry before it can
            // contribute to StorageManager's confirmed (durable) length.
            k.force(FileStreamIo.Force.OPEN);
            forceDirectory(dir);
            k.fileLength = k.rfile.length() - zeros;
            k.zeroTail = zeros;
            if (zeroTail) {
                zeroTailRemoved = zeros;
            }
            k.forcedLength = k.fileLength;
            k.channel = io.openRead(file);
            checkDirectory();
        } catch (IOException | RuntimeException | Error e) {
            // The file is closed whatever is thrown (2026-11-05, bergdb 015-32): it stayed open
            // after an unchecked exception or an Error, as 'k' is in no list that a close or
            // closeAfterFailedOpen() reaches.
            try {
                k.rfile.close();
            } catch (IOException closeFailure) {
                e.addSuppressed(closeFailure);
            }
            if (k.channel != null) {
                try {
                    k.channel.close();
                } catch (IOException closeFailure) {
                    e.addSuppressed(closeFailure);
                }
            }
            if (e instanceof IOException) {
                ioException = (IOException) e;
            }
            throw e;
        }
        k.isRw = true;
        k.maxSize = maxSize;
        synchronized (k) {}
        return k;
    }
    
    /**
     * The length of the tail of zeros of the last file that the open leaves out of the stream
     * (2026-11-26, bergdb 028-60): the run of zero bytes at the file's end when it is at most
     * ZERO_TAIL_MAX, 8 MB, else 0; 0 too for a run that is the whole stream, the only file all
     * zeros, which is not a stream that a start can take as a cut one (a repair never empties
     * a stream, so open() of DatabaseBuilder never creates a database in its place). It reads
     * the file and changes nothing. The stream's length then ends where the run starts, and
     * reads stop there; the file keeps the zeros until the stream's first append, which
     * truncates it there and forces it before it writes, or a cut that deletes files before
     * it (DbFile.cutZeroTail()). So an open
     * that is closed, or a start refused, before anything is appended leaves the files as they
     * were. Runs in the constructor, after the directory's lock and the check of the files'
     * names and lengths, before anything reads the stream; the same on every operating system
     * and file system, with no detection of either.
     * 
     * Why. After a kill of the process during an append, APFS (macOS) can leave the last file
     * with zeros within its length, from a page boundary on, where the bytes of the cut write
     * should be (bergdb 031-02, F1; 035-01): not a prefix of what was appended, which the
     * storage contract asks for (AppendOnlyStream, "CRASHES"; bergdb 014-01, section 7).
     * Without the zeros it is one, and the layers above see a stream cut short, which the
     * start's recovery completes and aborts as a torn last record. It is safe for BergDB's
     * stream format: a committed record and a valid meta block end in the byte 10, so zeros
     * at the end of the last file are the system's, or bytes of a torn record that was never
     * synced, or a recovery's zeros of an aborted record (completed again by the next
     * recovery); none holds a committed transaction. The bound limits a silent repair in the
     * case outside the contract, a power loss that destroyed forced bytes and left zeros in
     * their place. Stale bytes that are not zero (bergdb 028-67) are not removed.
     */
    private static long zeroTailLength(RandomAccessFile handle, boolean onlyFile)
            throws IOException {
        final long fileLength = handle.length();
        final long limit = Math.min(fileLength, ZERO_TAIL_MAX + 1);
        if (limit == 0) {
            return 0;
        }
        final byte[] buffer = new byte[(int) Math.min(limit, 64 * 1024)];
        long zeros = 0;         // the zero bytes at the file's end, so far
        while (zeros < limit) {
            int n = (int) Math.min(buffer.length, limit - zeros);
            handle.seek(fileLength - zeros - n);
            handle.readFully(buffer, 0, n);
            int i = n;
            while (i > 0 && buffer[i - 1] == 0) {
                i--;
            }
            zeros += n - i;
            if (i > 0) {
                break;
            }
        }
        if (zeros > ZERO_TAIL_MAX || (onlyFile && zeros == fileLength)) {
            return 0;
        }
        return zeros;
    }
    
    /**
     * The number of zero bytes at the end of the last file that the open left out of the
     * stream, 0 if none (zeroTailLength(); 2026-11-26, bergdb 028-60); the stream's length is
     * where they begin. For tests and tools: the layers above see the stream as cut short
     * there. The file keeps them until the first append.
     */
    public long getZeroTailRemoved() {
        return zeroTailRemoved;
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
        private long forcedLength = 0;      // its bytes forced so far (bergdb 005-47); under this
        private long zeroTail = 0;          // zeros after fileLength, cut at the 1st append (028-60)
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
            
            // Right before the delete, after close(), which waits for the reads in progress
            // (bergdb 021-20; 2026-11-09, bergdb 021-24: it came before close()).
            checkDirectory();
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
            checkDirectory();       // A replacement since the check fails the stream.
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
                throw closedException();
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
                    throw closedException();
                }
                if (channel == closed) {
                    // Before and after the open; no read gets the channel before the second
                    // check (bergdb 021-20, 021-24).
                    checkDirectory();
                    FileChannel reopened = io.openRead(file);
                    try {
                        checkDirectory();
                    } catch (IOException e) {
                        try {
                            reopened.close();
                        } catch (IOException closeFailure) {
                            e.addSuppressed(closeFailure);
                        }
                        throw e;
                    }
                    channel = reopened;
                }
            }
        }
        
        private ReadBelowFirstPosException deletedException(long spos) {
            return new ReadBelowFirstPosException("Cannot read at spos " + spos
                    + ", the file " + file.getPath() + " has been deleted by pretruncate.");
        }
        
        /**
         * The failure of a read of this file after close() has closed it (2026-11-03, bergdb
         * 015-17): only that read fails, as one of a deleted file does, and the stream has not
         * failed. It was kept as the stream's failure, 'ioException', and the second close()
         * of a BufferedStream's close, after its thread's close, threw it: Db.close() reported
         * a get that ran during the close as a failed close (InterruptStress).
         */
        private IOException closedException() {
            return new IOException("File closed, " + file.getPath() + ".");
        }
        
        /**
         * Forces the file through FileStreamIo; under this object's monitor. Not
         * interruptible (bergdb 005-46): it clears the thread's interrupt flag first and sets
         * it again after. If an interrupt during the force closes the channel anyway, which
         * closes 'rfile' too, its parent, it opens the file again and forces again.
         */
        void force(FileStreamIo.Force why) throws IOException {
            boolean interrupted = Thread.interrupted();
            try {
                while (true) {
                    try {
                        io.forceFile(file, rfile, why);
                        return;
                    } catch (ClosedByInterruptException e) {
                        Thread.interrupted();
                        interrupted = true;
                        checkDirectory();       // Bergdb 021-20, 021-24: before and after.
                        rfile = io.open(file);
                        checkDirectory();       // close() closes the handle.
                    }
                }
            } finally {
                if (interrupted) {
                    Thread.currentThread().interrupt();
                }
            }
        }
        
        /**
         * Forces what the writer has written and not forced (bergdb 005-47); nothing with
         * per-append forcing on, or when the writer is done with the file: it was forced
         * before (SWITCH). A failure is the stream's.
         */
        synchronized void forceWritten(FileStreamIo.Force why) throws IOException {
            if (rfile == null || forcedLength == fileLength) {
                return;
            }
            try {
                force(why);
            } catch (IOException e) {
                ioException = e;
                throw e;
            }
            forcedLength = fileLength;
        }
        
        /**
         * Cuts the tail of zeros that the open left out of the stream from the file (bergdb
         * 028-60, FileStream.zeroTailLength()): truncates the file to the stream's part of it
         * and forces it (ZERO_TAIL), also with per-append forcing off. At the first append to
         * the file, before its check of the file's length and its write, or at a cut that
         * deletes files (pretruncate()); not at close() or at an append of nothing. A failure
         * is the stream's, and the file keeps the zeros or a part of them: the next open
         * leaves them out again.
         */
        synchronized void cutZeroTailIfPending() throws IOException {
            if (zeroTail > 0 && rfile != null && !isClosed) {
                cutZeroTail();
            }
        }
        
        private void cutZeroTail() throws IOException {
            try {
                io.truncate(file, rfile, fileLength);
                force(FileStreamIo.Force.ZERO_TAIL);
            } catch (IOException e) {
                ioException = e;
                throw e;
            }
            zeroTail = 0;
        }
        
        /**
         * Appends bytes to the file, returns actual number of bytes appended. With per-append
         * forcing on, the bytes are forced before it returns; off, only written (bergdb
         * 005-47).
         */
        synchronized int append(byte[] bytes, int offset, int len) throws IOException {
            if (!isRw) {
                throw new Bug("Cannot append to file opened in read-only mode.");
            }
            
            if (isClosed) {
                ioException = new IOException("File closed, " + file.getPath() + ".");
                throw ioException;
            }
            
            if (zeroTail > 0) {
                cutZeroTail();      // Before the check of the file's length (bergdb 028-60).
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
                            + " is not of expected length (" + this.fileLength + "), "
                            + "but " + rfileLength + " bytes."
                            + " Was it modified by someone else?");
                }
                
                rfile.seek(this.fileLength);
                if (toAppend > 0) {
                    io.write(file, rfile, bytes, offset, toAppend);
                    if (forceAppends) {
                        force(FileStreamIo.Force.APPEND);
                    }
                }
                // Published to reads after the force, or the write (volatile).
                fileLength += toAppend;
                if (forceAppends) {
                    forcedLength = fileLength;
                }
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
    static void test0(TestEnvironment c) throws IOException {
        // Simple sanity test.
        File dir = c.createTempDir();
        assert dir != null : "dir is null";
        FileStream f = new FileStream(dir);
        Assert.assertEquals(0, f.getFirstPos());
        Assert.assertEquals(0, f.getLength());
        f.close();
    }
    
    @Nano
    static void test1(TestEnvironment c) throws IOException {
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
    
    /**
     * bergdb 015-06: a new stream has no file until its first append, and reads as an empty
     * one: 0 bytes at 0, and an EOFException past the end, which leaves the stream usable.
     * An empty append makes no file. Before, the constructor made an empty first file.
     */
    @Nano
    static void testNoFileUntilFirstAppend(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir);
        byte[] b = new byte[1];
        f.read(0, b, 0, 0);
        try {
            f.read(0, b, 0, 1);
            throw new AssertionError("read a byte of an empty stream");
        } catch (EOFException e) {
            // Expected.
        }
        f.append(b, 0, 0);
        Assert.assertEquals("[bergdb.lock]", Arrays.toString(dir.list()));
        f.close();
        Assert.assertEquals("[bergdb.lock]", Arrays.toString(dir.list()));
        
        f = new FileStream(dir);
        f.append(new byte[] {7}, 0, 1);
        f.read(0, b, 0, 1);
        Assert.assertEquals(7, b[0]);
        f.close();
        String[] names = dir.list();
        Arrays.sort(names);
        Assert.assertEquals("[00000000000000.bergdb, bergdb.lock]", Arrays.toString(names));
    }
    
    /**
     * A directory that cannot be listed, here one without read permission (SpotBugs, bergdb
     * 020-20): the constructor and hasStreamBytes throw an IOException that says so, and the
     * constructor releases the directory's lock. Before, File.listFiles()'s null for it was
     * dereferenced in getSortedDbFiles (a NullPointerException), and hasStreamBytes took it
     * for a directory without a stream byte. Skipped where the permission does not stop the
     * listing (root).
     */
    @Nano
    static void testUnlistableDirectory(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir);
        f.append(new byte[] {7}, 0, 1);
        f.close();
        Assert.assertTrue(hasStreamBytes(dir));
        Assert.assertFalse("a missing directory", hasStreamBytes(new File(dir, "missing")));
        
        Assert.assertTrue(dir.setReadable(false, false));
        try {
            if (dir.listFiles() != null) {
                System.out.println("FileStream.testUnlistableDirectory: skipped, the "
                        + "directory can be listed without read permission");
                return;
            }
            try {
                new FileStream(dir).close();
                throw new AssertionError("opened a directory that cannot be listed");
            } catch (IOException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("Cannot list"));
            }
            try {
                boolean has = hasStreamBytes(dir);
                throw new AssertionError("hasStreamBytes of a directory that cannot be listed: "
                        + has);
            } catch (Exception e) {
                Assert.assertTrue(e.toString(), e instanceof IOException
                        && e.getMessage().contains("Cannot list"));
            }
        } finally {
            dir.setReadable(true, false);
        }
        
        f = new FileStream(dir);        // the lock was released
        byte[] b = new byte[1];
        f.read(0, b, 0, 1);
        f.close();
        Assert.assertEquals(7, b[0]);
    }
    
    @Nano
    static void testFileSizeRules0(TestEnvironment c) throws IOException {
        int newIndex;
        long size;
        File dir = c.createTempDir();
        assert dir != null : "dir is null";
        FileStream f = new FileStream(dir);
        
        // A tenth of the stream (2026-11-26, bergdb 028-62; a quarter before: 5 MB gave 1 MB).
        size = 10 * 1000000L;
        newIndex = f.determineFileSizeIndex(0, size, size);
        Assert.assertEquals(1, newIndex);
        
        size = 9 * 1000000L;
        newIndex = f.determineFileSizeIndex(0, size, size);
        Assert.assertEquals(0, newIndex);
        
        size = 5 * 1000000L;
        newIndex = f.determineFileSizeIndex(0, size, size);
        Assert.assertEquals(0, newIndex);
        
        // The rule reads the current size from the field, as applyFileSizeChangeRules passes it.
        size = 50 * 1000000L;
        f.fileSizeIndex = 1;
        newIndex = f.determineFileSizeIndex(1, size, size);
        Assert.assertEquals(2, newIndex);
        
        size = 200 * 1000000L;
        f.fileSizeIndex = 2;
        newIndex = f.determineFileSizeIndex(2, size, size);
        Assert.assertEquals(3, newIndex);
        
        // Smaller at once: 20 MB of stream kept after 20 MB files, at any length.
        size = 20 * 1000000L;
        f.fileSizeIndex = 3;
        newIndex = f.determineFileSizeIndex(3, 310 * 1000000L, size);
        Assert.assertEquals(1, newIndex);
        f.fileSizeIndex = 0;
        
        f.close();
    }
    
    @Nano
    static void testFileSizeRules1(TestEnvironment c) throws IOException {
        // Tests the max2G setting.
        // Sizes: .., 500*M, 2*G, 10*G, 50*G, ...
        
        int newIndex;
        long size;
        File dir = c.createTempDir();
        assert dir != null : "dir is null";
        FileStream f = new FileStream(dir);
        
        size = 100*G;       // a tenth is 10 G (bergdb 028-62; 50 G with the quarter)
        
        f.setMax2G(false);
        newIndex = f.determineFileSizeIndex(INDEX_2G, size, size);
        Assert.assertEquals(INDEX_2G + 1, newIndex);
        
        f.setMax2G(true);
        newIndex = f.determineFileSizeIndex(INDEX_2G, size, size);
        Assert.assertEquals(INDEX_2G, newIndex);
        
        f.close();
    }
    
    /**
     * A start accepts files of the quarter rule (until 2026-11-26) beside files of the tenth
     * (bergdb 028-62): 200 kB files, then 1 MB files from 4 MB on, as the quarter made them
     * (the tenth makes 1 MB files from 10 MB on), the last half full. The stream is opened,
     * cut, written on into files of the tenth, and opened again, twice; every byte is read
     * back each time. Without forces, for the test's time: the forces of a new file are
     * most of it on macOS.
     */
    @Nano
    static void testMixedFileSizes(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        long pos = 0;
        for (int i = 0; i < 20; i++) {              // 200 kB files to 4 MB
            writePatternFile(dir, pos, SMALLEST_FILE_SIZE);
            pos += SMALLEST_FILE_SIZE;
        }
        for (int i = 0; i < 6; i++) {               // 1 MB files to 10 MB, the quarter's
            writePatternFile(dir, pos, M);
            pos += M;
        }
        writePatternFile(dir, pos, M / 2);          // the last, half full
        pos += M / 2;
        
        FileStream f = new FileStream(dir, new StreamContract.NoForceIo());
        Assert.assertEquals(0L, f.getFirstPos());
        Assert.assertEquals(pos, f.getLength());
        checkPattern(f, 0, pos);
        f.pretruncate(9500 * 1000L);                // the files before 9 MB go
        f.awaitDeletes();
        Assert.assertEquals(9 * M, f.getFirstPos());
        appendPattern(f, 1500 * 1000);              // fills the last 1 MB file; then 200 kB
        Assert.assertEquals(12 * M, f.getLength());
        checkPattern(f, 9 * M, 12 * M);
        f.close();
        
        long[] layout = {9 * M, M, 10 * M, M, 11 * M, 200 * 1000, 11200 * 1000, 200 * 1000,
                11400 * 1000, 200 * 1000, 11600 * 1000, 200 * 1000, 11800 * 1000, 200 * 1000};
        checkLayout(dir, layout);
        
        f = new FileStream(dir, new StreamContract.NoForceIo());
        Assert.assertEquals(9 * M, f.getFirstPos());
        Assert.assertEquals(12 * M, f.getLength());
        checkPattern(f, 9 * M, 12 * M);
        appendPattern(f, 300 * 1000);               // a 200 kB file and part of the next
        f.close();
        
        f = new FileStream(dir, new StreamContract.NoForceIo());
        Assert.assertEquals(12300 * 1000L, f.getLength());
        checkPattern(f, 9 * M, 12300 * 1000L);
        f.close();
        long[] tail = {12 * M, 200 * 1000, 12200 * 1000, 100 * 1000};
        long[] all = Arrays.copyOf(layout, layout.length + tail.length);
        System.arraycopy(tail, 0, all, layout.length, tail.length);
        checkLayout(dir, all);
    }
    
    private static byte patternByte(long pos) {
        return (byte) (pos * 131 + (pos >>> 13));
    }
    
    /**
     * Bergdb 028-60: the open leaves a run of zero bytes of at most ZERO_TAIL_MAX, 8 MB, at
     * the end of the last file out of the stream, and a longer one in; zeros before the last
     * non-zero byte stay. Runs of 0, 1, 4,095 and 8 MB bytes are left out, one of 8 MB + 1 is
     * not. The stream's length ends where the run starts and a read past it fails, while the
     * file keeps its length through an append of nothing, a close and a second open; the
     * first append truncates it and writes there, and a third open has nothing to leave out.
     */
    @Nano
    static void testZeroTailRemoved(TestEnvironment c) throws IOException {
        for (long zeros : new long[] {0, 1, 4095, ZERO_TAIL_MAX, ZERO_TAIL_MAX + 1}) {
            String what = zeros + " zeros";
            File dir = c.createTempDir();
            FileStream f = new FileStream(dir, new StreamContract.NoForceIo());
            byte[] bytes = new byte[] {7, 0, 0, 10};      // a zero inside stays
            f.append(bytes, 0, bytes.length);
            f.close();
            File file = new File(dir, "00000000000000.bergdb");
            try (RandomAccessFile raf = new RandomAccessFile(file, "rw")) {
                raf.setLength(4 + zeros);
            }
            boolean removed = zeros <= ZERO_TAIL_MAX;
            for (int open = 0; open < 2; open++) {
                f = new FileStream(dir, new StreamContract.NoForceIo());
                Assert.assertEquals(what, removed ? zeros : 0, f.getZeroTailRemoved());
                Assert.assertEquals(what, removed ? 4 : 4 + zeros, f.getLength());
                byte[] b = new byte[4];
                f.read(0, b, 0, 4);
                Assert.assertArrayEquals(what, bytes, b);
                if (removed) {
                    try {
                        f.read(4, new byte[1], 0, 1);
                        throw new AssertionError(what + ": read past the end");
                    } catch (EOFException e) {
                        // Expected: the zeros are not in the stream.
                    }
                }
                f.append(new byte[1], 0, 0);
                Assert.assertEquals(what, 4 + zeros, file.length());
                if (open == 0) {
                    f.close();
                    Assert.assertEquals(what, 4 + zeros, file.length());
                }
            }
            f.append(new byte[] {5}, 0, 1);
            long length = f.getLength();
            Assert.assertEquals(what, removed ? 5 : 5 + zeros, length);
            Assert.assertEquals(what, length, file.length());
            byte[] b = new byte[1];
            f.read(length - 1, b, 0, 1);
            Assert.assertEquals(what, 5, b[0]);
            f.close();
            f = new FileStream(dir, new StreamContract.NoForceIo());
            Assert.assertEquals(what, 0, f.getZeroTailRemoved());
            Assert.assertEquals(what, length, f.getLength());
            f.close();
        }
    }
    
    /**
     * Bergdb 028-60: only the last file's zeros are left out; a last file of zeros only is
     * left out whole and cut to 0 bytes at the first append, and a file before it keeps its
     * zeros at its end; and the only file of a stream, all zeros, is left in (a repair never
     * empties a stream).
     */
    @Nano
    static void testZeroTailLastFileOnly(TestEnvironment c) throws IOException {
        // A first file of 200 kB that ends in zeros, a second of zeros only.
        File dir = c.createTempDir();
        byte[] first = new byte[(int) SMALLEST_FILE_SIZE];
        first[1000] = 10;
        writeFile(new File(dir, "00000000000000.bergdb"), first);
        File second = new File(dir, "00000000000002.bergdb");
        writeFile(second, new byte[3000]);
        FileStream f = new FileStream(dir, new StreamContract.NoForceIo());
        Assert.assertEquals(3000, f.getZeroTailRemoved());
        Assert.assertEquals(SMALLEST_FILE_SIZE, f.getLength());
        Assert.assertEquals(3000L, second.length());
        f.append(new byte[] {10}, 0, 1);
        Assert.assertEquals(1L, second.length());
        f.close();
        f = new FileStream(dir, new StreamContract.NoForceIo());
        Assert.assertEquals(SMALLEST_FILE_SIZE + 1, f.getLength());
        f.close();
        Assert.assertEquals(SMALLEST_FILE_SIZE,
                new File(dir, "00000000000000.bergdb").length());
        
        // The only file, all zeros: left.
        dir = c.createTempDir();
        writeFile(new File(dir, "00000000000000.bergdb"), new byte[5000]);
        f = new FileStream(dir, new StreamContract.NoForceIo());
        Assert.assertEquals(0, f.getZeroTailRemoved());
        Assert.assertEquals(5000, f.getLength());
        f.close();
    }
    
    /**
     * Bergdb 028-60: the open changes no file; the first append truncates the last file and
     * forces it (ZERO_TAIL) before it writes, also with per-append forcing off, and a close
     * after it forces the write (CLOSE). A truncation that fails fails the append and the
     * stream, with the file as it was; the next open leaves the zeros out again.
     */
    @Nano
    static void testZeroTailCutAtFirstAppend(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        File file = new File(dir, "00000000000000.bergdb");
        writeFile(file, new byte[] {10, 0, 0, 0});
        final List<String> events = new ArrayList<String>();
        FileStreamIo failing = new FileStreamIo() {
            @Override protected void truncate(File file, RandomAccessFile handle, long length)
                    throws IOException {
                events.add("truncate " + length);
                throw new IOException("planted");
            }
        };
        FileStream f = new FileStream(dir, failing);
        Assert.assertEquals(1L, f.getLength());
        try {
            f.append(new byte[] {10}, 0, 1);
            throw new AssertionError("appended");
        } catch (IOException e) {
            Assert.assertEquals("planted", e.getMessage());
        }
        Assert.assertEquals(4L, file.length());
        try {
            f.append(new byte[] {10}, 0, 1);
            throw new AssertionError("appended after the failure");
        } catch (IOException e) {
            Assert.assertEquals("planted", e.getMessage());
        }
        try {
            f.close();
            throw new AssertionError("closed without the failure");
        } catch (IOException e) {
            Assert.assertEquals("planted", e.getMessage());
        }
        Assert.assertEquals("[truncate 1]", events.toString());
        Assert.assertEquals(4L, file.length());
        
        events.clear();
        FileStreamIo counting = new FileStreamIo() {
            @Override protected void truncate(File file, RandomAccessFile handle, long length)
                    throws IOException {
                events.add("truncate " + length);
                super.truncate(file, handle, length);
            }
            @Override protected void forceFile(File file, RandomAccessFile handle,
                    FileStreamIo.Force why) throws IOException {
                events.add("force " + why);
            }
        };
        f = new FileStream(dir, counting, false);
        Assert.assertEquals(3L, f.getZeroTailRemoved());
        Assert.assertEquals(1L, f.getLength());
        Assert.assertEquals(4L, file.length());
        f.append(new byte[] {10}, 0, 1);
        Assert.assertEquals(2L, f.getLength());
        Assert.assertEquals(2L, file.length());
        f.close();
        Assert.assertEquals("[force OPEN, truncate 1, force ZERO_TAIL, force CLOSE]",
                events.toString());
    }
    
    /**
     * Bergdb 028-60: the last file's size, its capacity for appends, is computed from its
     * length without the zeros that the open left out. A file of 150,000 bytes and 100,000
     * zeros takes 50,000 bytes more, to 200,000, the smallest size, not the 1 MB of its
     * length with the zeros; one of 200,000 bytes and 50,000 zeros is full, and the append
     * cuts it and goes on in a new file. Both are opened again with every byte.
     */
    @Nano
    static void testZeroTailFileSize(TestEnvironment c) throws IOException {
        for (int stream : new int[] {150 * 1000, 200 * 1000}) {
            String what = stream + " bytes";
            File dir = c.createTempDir();
            File file = new File(dir, "00000000000000.bergdb");
            byte[] bytes = new byte[250 * 1000];
            Arrays.fill(bytes, 0, stream, (byte) 7);
            bytes[stream - 1] = 10;
            writeFile(file, bytes);
            FileStream f = new FileStream(dir, new StreamContract.NoForceIo());
            Assert.assertEquals(what, 250 * 1000 - stream, f.getZeroTailRemoved());
            byte[] more = new byte[100 * 1000];
            Arrays.fill(more, (byte) 8);
            f.append(more, 0, more.length);
            f.close();
            File next = new File(dir, "00000000000002.bergdb");
            Assert.assertEquals(what, SMALLEST_FILE_SIZE, file.length());
            Assert.assertEquals(what, stream + more.length - SMALLEST_FILE_SIZE, next.length());
            f = new FileStream(dir, new StreamContract.NoForceIo());
            Assert.assertEquals(what, 0, f.getZeroTailRemoved());
            Assert.assertEquals(what, stream + more.length, f.getLength());
            byte[] all = new byte[stream + more.length];
            f.read(0, all, 0, all.length);
            Assert.assertArrayEquals(what, Arrays.copyOf(bytes, stream),
                    Arrays.copyOf(all, stream));
            Assert.assertArrayEquals(what, more, Arrays.copyOfRange(all, stream, all.length));
            f.close();
        }
    }
    
    /**
     * Bergdb 028-60, Codex's second review of part 2 (2026-11-26, its LogicalProbe): a cut
     * that deletes files before the first append cuts the zeros that the open left out
     * first. A first file of 200,000 bytes and a last one of 3,000 zeros: the open shows
     * 200,000; pretruncate(200,000) deletes the first file, and the last one, now the only
     * one, is 0 bytes, so the next open shows 200,000 too (on af26333d it showed 203,000,
     * the only file all zeros taken whole). With 1,000 bytes before 2,000 zeros, 201,000
     * both times. A cut that deletes nothing leaves the zeros in the file.
     */
    @Nano
    static void testZeroTailCutBeforeFirstAppend(TestEnvironment c) throws IOException {
        for (int prefix : new int[] {0, 1000}) {
            String what = prefix + " bytes before the zeros";
            File dir = c.createTempDir();
            byte[] first = new byte[(int) SMALLEST_FILE_SIZE];
            Arrays.fill(first, (byte) 7);
            first[first.length - 1] = 10;
            writeFile(new File(dir, "00000000000000.bergdb"), first);
            byte[] last = new byte[3000];
            Arrays.fill(last, 0, prefix, (byte) 7);
            if (prefix > 0) {
                last[prefix - 1] = 10;
            }
            File lastFile = new File(dir, "00000000000002.bergdb");
            writeFile(lastFile, last);
            long end = SMALLEST_FILE_SIZE + prefix;
            
            FileStream f = new FileStream(dir, new StreamContract.NoForceIo());
            Assert.assertEquals(what, end, f.getLength());
            f.pretruncate(1000);        // in the first file: deletes nothing
            f.awaitDeletes();
            Assert.assertEquals(what, 3000L, lastFile.length());
            f.pretruncate(SMALLEST_FILE_SIZE);
            f.awaitDeletes();
            Assert.assertEquals(what, SMALLEST_FILE_SIZE, f.getFirstPos());
            Assert.assertEquals(what, end, f.getLength());
            Assert.assertEquals(what, (long) prefix, lastFile.length());
            f.close();
            
            f = new FileStream(dir, new StreamContract.NoForceIo());
            Assert.assertEquals(what, SMALLEST_FILE_SIZE, f.getFirstPos());
            Assert.assertEquals(what, end, f.getLength());
            f.append(new byte[] {10}, 0, 1);
            f.close();
            f = new FileStream(dir, new StreamContract.NoForceIo());
            Assert.assertEquals(what, end + 1, f.getLength());
            f.close();
        }
    }
    
    private static void writeFile(File file, byte[] bytes) throws IOException {
        try (FileOutputStream out = new FileOutputStream(file)) {
            out.write(bytes);
        }
    }
    
    /** A stream file of the bytes of 'pattern' from 'spos', as a stream would have made it. */
    private static void writePatternFile(File dir, long spos, long length) throws IOException {
        byte[] bytes = new byte[(int) length];
        for (int i = 0; i < bytes.length; i++) {
            bytes[i] = patternByte(spos + i);
        }
        File file = new File(dir, indexToString(spos / BYTES_PER_INDEX_UNIT) + SUFFIX);
        try (FileOutputStream out = new FileOutputStream(file)) {
            out.write(bytes);
        }
    }
    
    private static void appendPattern(FileStream f, int length) throws IOException {
        long spos = f.getLength();
        byte[] bytes = new byte[length];
        for (int i = 0; i < bytes.length; i++) {
            bytes[i] = patternByte(spos + i);
        }
        f.append(bytes, 0, bytes.length);
    }
    
    private static void checkPattern(FileStream f, long from, long to) throws IOException {
        byte[] b = new byte[64 * 1000];
        for (long p = from; p < to; p += b.length) {
            int n = (int) Math.min(b.length, to - p);
            f.read(p, b, 0, n);
            for (int i = 0; i < n; i++) {
                if (b[i] != patternByte(p + i)) {
                    Assert.assertTrue("byte at " + (p + i) + ": " + b[i], false);
                }
            }
        }
    }
    
    /** The directory's stream files, by name: their first positions and lengths, in pairs. */
    private static void checkLayout(File dir, long[] layout) {
        File[] files = dir.listFiles((d, name) -> name.endsWith(SUFFIX));
        Arrays.sort(files, Comparator.comparing(File::getName));
        Assert.assertEquals(layout.length / 2, files.length);
        for (int i = 0; i < files.length; i++) {
            Assert.assertEquals(indexToString(layout[2 * i] / BYTES_PER_INDEX_UNIT) + SUFFIX,
                    files[i].getName());
            Assert.assertEquals(layout[2 * i + 1], files[i].length());
        }
    }
    
    @Nano
    static void testRestart0(TestEnvironment c) throws IOException {
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
    
    /**
     * bergdb 028-66: a stream whose second file of three is missing opens from the third, the
     * file after the gap, and keeps the first, a leftover, unread; until 2026-11-27 the open
     * refused it (BadDirStateException). A read below the first position names the gap. A cut
     * before the first position deletes nothing; one at it deletes the leftover, and the
     * stream then opens without a gap.
     */
    @Nano
    static void testRestartMissingFile(TestEnvironment c) throws IOException {
        byte[] bytes = new byte[500*1000];     // 3 stream files
        new Random(66).nextBytes(bytes);
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
        
        FileStream f2 = new FileStream(dir);
        try {
            Assert.assertEquals(400 * 1000L, f2.getFirstPos());
            Assert.assertEquals(500 * 1000L, f2.getLength());
            Assert.assertEquals(1, f2.getLeftoverCount());
            readAndCheck(f2, 400 * 1000, 100 * 1000, bytes);
            try {
                f2.read(400 * 1000 - 1, new byte[1], 0, 1);
                throw new AssertionError("read below the gap");
            } catch (ReadBelowFirstPosException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("gap")
                        && e.getMessage().contains(fileName(0))
                        && e.getMessage().contains("from 200000 to 400000"));
            }
            f2.pretruncate(400 * 1000 - 1);       // Before the first position: nothing.
            f2.awaitDeletes();
            Assert.assertEquals(1, f2.getLeftoverCount());
            Assert.assertTrue(new File(dir, fileName(0)).exists());
            f2.pretruncate(400 * 1000);
            f2.awaitDeletes();
            Assert.assertEquals(0, f2.getLeftoverCount());
            Assert.assertFalse(new File(dir, fileName(0)).exists());
        } finally {
            f2.close();
        }
        
        FileStream f3 = new FileStream(dir);
        try {
            Assert.assertEquals(0, f3.getLeftoverCount());
            Assert.assertEquals(400 * 1000L, f3.getFirstPos());
            readAndCheck(f3, 400 * 1000, 100 * 1000, bytes);
        } finally {
            f3.close();
        }
    }
    
    /**
     * bergdb 028-66: what the open still refuses (BadDirStateException), and the refused open
     * releases the directory's lock (bergdb 005-63): a file that begins before the end of the
     * one before it, and a file before a gap whose length is not a multiple of 100,000.
     */
    @Nano
    static void testRestartRefusedOverlap(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir);
        f.append(new byte[500*1000], 0, 500*1000);      // 0, 200,000, 400,000
        f.close();
        
        File overlap = new File(dir, indexToString(1) + SUFFIX);       // At 100,000.
        Files.write(overlap.toPath(), new byte[100*1000]);
        for (int i = 0; i < 2; i++) {
            try {
                new FileStream(dir).close();
                throw new AssertionError("opened with an overlap");
            } catch (BadDirStateException e) {
                // Expected; the second time too: the lock was released.
            }
        }
        Assert.assertTrue(overlap.delete());
        
        // The first file, before a gap, 150,000 bytes long.
        Assert.assertTrue(new File(dir, indexToString(2) + SUFFIX).delete());
        try (RandomAccessFile raf = new RandomAccessFile(new File(dir, fileName(0)), "rw")) {
            raf.setLength(150 * 1000);
        }
        try {
            new FileStream(dir).close();
            throw new AssertionError("opened with a bad size before the gap");
        } catch (BadDirStateException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("Bad size"));
        }
    }
    
    /**
     * bergdb 028-66: two gaps; the stream is the files after the last one. A cut deletes the
     * leftovers, oldest first, before the files that it takes off, in one batch with one
     * force of the directory. A stream of one file after a gap is the stream's only file for
     * the tail of zeros (bergdb 028-60): its zeros are not left out, as the leftovers go at
     * the next cut and the open after it must find the same stream.
     */
    @Nano
    static void testGapsAtOpen(TestEnvironment c) throws Exception {
        final List<String> log = Collections.synchronizedList(new ArrayList<String>());
        FileStreamIo io = new FileStreamIo() {
            protected void forceDirectory(File directory) throws IOException {
                super.forceDirectory(directory);
                log.add("force");
            }
            
            protected boolean delete(File file) throws IOException {
                boolean ok = super.delete(file);
                log.add("delete " + file.getName());
                return ok;
            }
        };
        File dir = c.createTempDir();
        byte[] bytes = new byte[1600 * 1000];
        new Random(28066).nextBytes(bytes);
        // Files at 0, 200,000, 600,000, 1,000,000 and 1,200,000 (the last, 150,000 bytes):
        // gaps at 400,000 and at 800,000.
        long[] starts = {0, 200 * 1000, 600 * 1000, 1000 * 1000, 1200 * 1000};
        for (long start : starts) {
            int n = start == 1200 * 1000 ? 150 * 1000 : 200 * 1000;
            Files.write(new File(dir, fileName(start)).toPath(),
                    Arrays.copyOfRange(bytes, (int) start, (int) start + n));
        }
        FileStream f = new FileStream(dir, io);
        try {
            Assert.assertEquals(1000 * 1000L, f.getFirstPos());
            Assert.assertEquals(1350 * 1000L, f.getLength());
            Assert.assertEquals(3, f.getLeftoverCount());
            readAndCheck(f, 1000 * 1000, 350 * 1000, bytes);
            log.clear();
            f.pretruncate(1300 * 1000);
            f.awaitDeletes();
            Assert.assertEquals(Arrays.asList("delete " + fileName(0),
                    "delete " + fileName(200 * 1000), "delete " + fileName(600 * 1000),
                    "delete " + fileName(1000 * 1000), "force"), log);
            Assert.assertEquals(1200 * 1000L, f.getFirstPos());
            f.append(bytes, 1350 * 1000, 10);
        } finally {
            f.close();
        }
        Assert.assertEquals(Arrays.asList(fileName(1200 * 1000)),
                Arrays.asList(dir.list((d, name) -> name.endsWith(SUFFIX))));
        
        // One file of zeros after a gap: in the stream, not left out.
        File dir2 = c.createTempDir();
        Files.write(new File(dir2, fileName(0)).toPath(), Arrays.copyOf(bytes, 200 * 1000));
        Files.write(new File(dir2, fileName(400 * 1000)).toPath(), new byte[1000]);
        FileStream g = new FileStream(dir2);
        try {
            Assert.assertEquals(400 * 1000L, g.getFirstPos());
            Assert.assertEquals(401 * 1000L, g.getLength());
            Assert.assertEquals(0L, g.getZeroTailRemoved());
        } finally {
            g.close();
        }
    }
    
    @Nano
    static void testBigAppend0(TestEnvironment c) throws IOException {
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
    static void testConstants() {
        Assert.assertTrue(SMALLEST_FILE_SIZE % BYTES_PER_INDEX_UNIT == 0);
        Assert.assertEquals(2L*1000*1000000, FILE_SIZES[INDEX_2G]);
        
        for (int i = 0; i < FACTOR_UP.length; i++) {
            Assert.assertEquals(FILE_SIZES[i + 1], FILE_SIZES[i] * FACTOR_UP[i]);
        }
    }
    
    @Nano
    static void testSeekFirstPos0(TestEnvironment c) throws IOException {
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
    static void testReopenPast214TB(TestEnvironment c) throws IOException {
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
    static void testSeekFirstPos1(TestEnvironment c) throws IOException {
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
    static void testPretruncate0(TestEnvironment c) throws Exception {
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
     * bergdb 019-39 (review R6 of 006-13, B2): a cut whose thread cannot start, as at an
     * OutOfMemoryError, throws the Error, and close() returns. Before, cutThread stayed set,
     * and close() waited for it for ever.
     */
    @Nano
    static void testCutThreadThatCannotStart(TestEnvironment c) throws Exception {
        final FileStream f = new FileStream(c.createTempDir());
        byte[] bytes = new byte[500*1000];
        f.append(bytes, 0, bytes.length);
        final OutOfMemoryError oom = new OutOfMemoryError("test: no cut thread");
        Util.testHookStart = t -> {
            if (t.getName().equals("FileStream-cut")) throw oom;
        };
        Throwable thrown = null;
        try {
            f.pretruncate(200*1000);
        } catch (OutOfMemoryError e) {
            thrown = e;
        } finally {
            Util.testHookStart = null;
        }
        Assert.assertTrue("pretruncate() throws the Error: " + thrown, thrown == oom);
        Thread closer = new Thread(() -> {
            try {
                f.close();
            } catch (IOException e) {
                // Not this test's concern.
            }
        });
        closer.setDaemon(true);
        closer.start();
        closer.join(10000);
        Assert.assertFalse("close() still waits", closer.isAlive());
    }
    
    /**
     * bergdb 019-39 (review R6 of 006-13, B3; review R7, B1): an Error of a cut's delete is
     * recorded as the IOException made with the stream, with the Error as its cause: the
     * cut's thread makes none, so that it records the failure also when the heap is full.
     * Before, a new IOException that threw too ended the thread with nothing recorded, and
     * close() waited for ever (review R7, R7CutOomProbe).
     */
    @Nano
    static void testCutErrorRecordedAsMadeBefore(TestEnvironment c) throws Exception {
        final Error error = new Error("test: a delete's Error");
        FileStream f = new FileStream(c.createTempDir(), new FileStreamIo() {
            protected boolean delete(File file) throws IOException {
                throw error;
            }
        });
        try {
            byte[] bytes = new byte[500*1000];
            f.append(bytes, 0, bytes.length);
            f.pretruncate(200*1000);
            IOException thrown = null;
            try {
                f.awaitDeletes();
            } catch (IOException e) {
                thrown = e;
            }
            Assert.assertTrue("made before: " + thrown, thrown == f.cutFailure);
            Assert.assertTrue("the cause", thrown.getCause() == error);
        } finally {
            try {
                f.close();
            } catch (IOException e) {
                // The cut's failure.
            }
        }
    }
    
    /**
     * 2026-10-13 (bergdb 011-04, W1). A read of bytes that pretruncate()
     * removed used to store a permanent IOException: after it, every read and append failed.
     * Now only the read fails.
     */
    @Nano
    static void testReadBelowFirstPosDoesNotBreakStream(TestEnvironment c)
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
    static void testReadPastEnd(TestEnvironment c) throws Exception {
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
    static void testReadOfFileDeletedMeanwhileDoesNotBreakStream(TestEnvironment c)
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
    static void testMultiFileRead0(TestEnvironment c) throws IOException {
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
    static void testMultiFileRead1(TestEnvironment c) throws IOException {
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
        
        // 11 MB: 200 kB files to 10 MB, then a 1 MB file, a tenth (2026-11-26, bergdb 028-62;
        // with a quarter, 5 MB gave 200 kB files to 4 MB and a 1 MB file).
        for (int i = 0; i < 110; i++) {
            f.append(bytes, 0, bytes.length);
        }
        
        Assert.assertEquals(51, f.dbFiles.length);
        Assert.assertEquals(200*1000, f.dbFiles[0].fileLength);
        Assert.assertEquals(1000*1000, f.dbFiles[f.dbFiles.length - 1].fileLength);
        
        f.close();
    }
    
    /**
     * Regression test for bergdb 015-32 (review R2-F3): a new stream whose open of its first
     * file fails closes that file and releases the directory, whatever it throws. Before, an
     * unchecked exception left the file open (only an IOException closed it), and an Error
     * left the directory locked within the JVM: a new FileStream on it was refused with a
     * DirectoryInUseException until the JVM ended.
     */
    @Nano
    static void testFailedOpenClosesFileAndUnlocks(TestEnvironment c) throws IOException {
        String[] kinds = {"an IOException", "an unchecked exception", "an Error"};
        for (int kind = 0; kind < kinds.length; kind++) {
            final int k = kind;
            final RandomAccessFile[] opened = new RandomAccessFile[1];
            FileStreamIo io = new FileStreamIo() {
                protected RandomAccessFile open(File file) throws IOException {
                    return opened[0] = super.open(file);
                }
                protected void forceFile(File file, RandomAccessFile handle,
                        FileStreamIo.Force why) throws IOException {
                    if (why == FileStreamIo.Force.OPEN) {
                        if (k == 0) throw new IOException("injected");
                        if (k == 1) throw new IllegalStateException("injected");
                        throw new AssertionError("injected");
                    }
                    super.forceFile(file, handle, why);
                }
            };
            File dir = c.createTempDir();
            FileStream written = new FileStream(dir);     // A file to open: a new stream
            written.append(new byte[1], 0, 1);           // opens none (bergdb 015-06).
            written.close();
            Throwable thrown = null;
            try {
                new FileStream(dir, io).close();
            } catch (IOException | RuntimeException | Error e) {
                thrown = e;
            }
            Assert.assertTrue("the open throws " + kinds[k] + ": " + thrown,
                    thrown != null && "injected".equals(thrown.getMessage()));
            Assert.assertTrue("a file was opened", opened[0] != null);
            boolean open = opened[0].getFD().valid();
            opened[0].close();
            Assert.assertFalse("the file is closed after " + kinds[k], open);
            try {
                new FileStream(dir).close();
            } catch (DirectoryInUseException e) {
                throw new AssertionError("the directory is locked after " + kinds[k], e);
            }
        }
    }
    
    // ---- bergdb 005-47: per-append forcing off ----
    
    /**
     * A FileStreamIo that logs, in order, the file forces with their reason, the file and its
     * length, and the opens and deletes (bergdb 005-47).
     */
    static final class ForceLogIo extends FileStreamIo {
        final List<String> log = Collections.synchronizedList(new ArrayList<String>());
        
        protected void forceFile(File file, RandomAccessFile handle, FileStreamIo.Force why)
                throws IOException {
            log.add(why + " " + file.getName() + " " + handle.length());
            super.forceFile(file, handle, why);
        }
        
        protected RandomAccessFile open(File file) throws IOException {
            log.add("open " + file.getName());
            return super.open(file);
        }
        
        protected boolean delete(File file) throws IOException {
            log.add("delete " + file.getName());
            return super.delete(file);
        }
        
        /** The log's entries that start with 'prefix'. */
        List<String> starting(String prefix) {
            List<String> result = new ArrayList<String>();
            synchronized (log) {
                for (String entry : log) {
                    if (entry.startsWith(prefix + " ")) result.add(entry);
                }
            }
            return result;
        }
        
        int indexOf(String entry) {
            return log.indexOf(entry);
        }
    }
    
    private static String fileName(long spos) {
        return indexToString(spos / BYTES_PER_INDEX_UNIT) + SUFFIX;
    }
    
    /**
     * Forcing on, the default, is today's hard sync: one force per append, and none at a new
     * file's predecessor, a cut or close(), where nothing is left unforced (bergdb 005-47).
     */
    @Nano
    static void testForcingOnForcesEveryAppend(TestEnvironment c) throws IOException {
        FileStream plain = new FileStream(c.createTempDir());
        Assert.assertTrue("forcing on by default", plain.forcesAppends());
        plain.close();
        
        ForceLogIo io = new ForceLogIo();
        FileStream f = new FileStream(c.createTempDir(), io, true);
        Assert.assertTrue(f.forcesAppends());
        f.append(new byte[100], 0, 100);
        f.append(new byte[100], 0, 100);
        f.append(new byte[250 * 1000], 0, 250 * 1000);     // 199,800 to the first file, 50,200 to the next.
        f.pretruncate(200 * 1000);
        f.awaitDeletes();
        f.close();
        Assert.assertEquals(Arrays.asList("APPEND " + fileName(0) + " 100", 
                "APPEND " + fileName(0) + " 200", "APPEND " + fileName(0) + " 200000", 
                "APPEND " + fileName(200000) + " 50200"), io.starting("APPEND"));
        Assert.assertEquals(2, io.starting("OPEN").size());
        Assert.assertEquals(0, io.starting("SWITCH").size());
        Assert.assertEquals(0, io.starting("CUT").size());
        Assert.assertEquals(0, io.starting("CLOSE").size());
    }
    
    /**
     * Forcing off (bergdb 005-47): an append is written, not forced. The bytes are in the file,
     * where another reader, after a crash of the process, finds them; reads see them at once.
     */
    @Nano
    static void testForcingOffWritesAppends(TestEnvironment c) throws IOException {
        ForceLogIo io = new ForceLogIo();
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir, io, false);
        try {
            Assert.assertTrue(!f.forcesAppends());
            byte[] bytes = new byte[300];
            new Random(47).nextBytes(bytes);
            f.append(bytes, 0, 100);
            f.append(bytes, 100, 200);
            Assert.assertEquals(0, io.starting("APPEND").size());
            Assert.assertEquals(Arrays.asList("OPEN " + fileName(0) + " 0"), io.starting("OPEN"));
            Assert.assertTrue("written to the file", 
                    Arrays.equals(bytes, Files.readAllBytes(new File(dir, fileName(0)).toPath())));
            byte[] read = new byte[300];
            f.read(0, read, 0, 300);
            Assert.assertTrue(Arrays.equals(bytes, read));
        } finally {
            f.close();
        }
    }
    
    /**
     * Forcing off (bergdb 005-47): the stream forces its last file before it moves to a new
     * one, before the new file is opened, so that a power loss leaves no short file before a
     * newer one.
     */
    @Nano
    static void testForcingOffForcesTheFileBeforeANewFile(TestEnvironment c) 
            throws IOException {
        ForceLogIo io = new ForceLogIo();
        FileStream f = new FileStream(c.createTempDir(), io, false);
        try {
            f.append(new byte[250 * 1000], 0, 250 * 1000);
            String sw = "SWITCH " + fileName(0) + " 200000";
            Assert.assertEquals(Arrays.asList(sw), io.starting("SWITCH"));
            Assert.assertTrue("forced before the new file is opened", 
                    io.indexOf(sw) < io.indexOf("open " + fileName(200000)));
            Assert.assertEquals(0, io.starting("APPEND").size());
        } finally {
            f.close();
        }
    }
    
    /**
     * Forcing off (bergdb 005-47): the cut's thread forces the last file, which holds the
     * cut's decision, before it deletes the first file of the cut; once, as nothing is left
     * unforced for the next delete.
     */
    @Nano
    static void testForcingOffForcesBeforeACutDeletes(TestEnvironment c) 
            throws IOException {
        ForceLogIo io = new ForceLogIo();
        FileStream f = new FileStream(c.createTempDir(), io, false);
        try {
            f.append(new byte[1000 * 1000], 0, 1000 * 1000);    // Five files of 200,000 bytes.
            f.append(new byte[100], 0, 100);                    // A sixth, at 1,000,000.
            Assert.assertEquals(5, io.starting("SWITCH").size());
            f.pretruncate(800 * 1000);
            f.awaitDeletes();
            String cut = "CUT " + fileName(1000 * 1000) + " 100";
            Assert.assertEquals(Arrays.asList(cut), io.starting("CUT"));
            Assert.assertEquals(4, io.starting("delete").size());
            Assert.assertTrue("forced before the deletes", 
                    io.indexOf(cut) < io.indexOf("delete " + fileName(0)));
            
            // A cut with nothing unforced forces nothing.
            f.pretruncate(1000 * 1000);
            f.awaitDeletes();
            Assert.assertEquals(5, io.starting("delete").size());
            Assert.assertEquals(1, io.starting("CUT").size());
        } finally {
            f.close();
        }
    }
    
    /**
     * Forcing off (bergdb 005-47): close() forces the last file, so that a clean stop is
     * durable; a second close() forces nothing, and a restart reads the bytes.
     */
    @Nano
    static void testForcingOffForcesAtClose(TestEnvironment c) throws IOException {
        ForceLogIo io = new ForceLogIo();
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir, io, false);
        byte[] bytes = new byte[] {4, 7};
        f.append(bytes, 0, 2);
        Assert.assertEquals(0, io.starting("CLOSE").size());
        f.close();
        String close = "CLOSE " + fileName(0) + " 2";
        Assert.assertEquals(Arrays.asList(close), io.starting("CLOSE"));
        f.close();
        Assert.assertEquals(1, io.starting("CLOSE").size());
        
        FileStream again = new FileStream(dir, false);
        try {
            byte[] read = new byte[2];
            again.read(0, read, 0, 2);
            Assert.assertTrue(Arrays.equals(bytes, read));
        } finally {
            again.close();
        }
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
        
        void hold(java.util.concurrent.CountDownLatch latch) throws IOException {
            if (latch == null) return;
            held.countDown();
            try {
                if (!latch.await(30, java.util.concurrent.TimeUnit.SECONDS)) {
                    throw new IOException("held for 30 s");
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
    
    /**
     * A HeldIo whose read channels hold their next positional read, when 'holdRead' is set,
     * on that latch before it reads (bergdb 015-17): a read stopped after its checks of the
     * file, and before the channel reads.
     */
    static final class HeldReadIo extends HeldIo {
        volatile java.util.concurrent.CountDownLatch holdRead;
        
        protected FileChannel openRead(File file) throws IOException {
            return new HeldChannel(super.openRead(file));
        }
        
        /** Reads through 'ch'; the first read after 'holdRead' is set waits on it. */
        final class HeldChannel extends FileChannel {
            private final FileChannel ch;
            
            HeldChannel(FileChannel ch) {
                this.ch = ch;
            }
            
            public int read(ByteBuffer dst, long position) throws IOException {
                final java.util.concurrent.CountDownLatch latch = holdRead;
                if (latch != null) {
                    holdRead = null;
                    hold(latch);
                }
                return ch.read(dst, position);
            }
            
            public int read(ByteBuffer dst) throws IOException { return ch.read(dst); }
            public long read(ByteBuffer[] dsts, int offset, int length) throws IOException {
                return ch.read(dsts, offset, length);
            }
            public int write(ByteBuffer src) throws IOException { return ch.write(src); }
            public long write(ByteBuffer[] srcs, int offset, int length) throws IOException {
                return ch.write(srcs, offset, length);
            }
            public int write(ByteBuffer src, long position) throws IOException {
                return ch.write(src, position);
            }
            public long position() throws IOException { return ch.position(); }
            public FileChannel position(long p) throws IOException {
                ch.position(p);
                return this;
            }
            public long size() throws IOException { return ch.size(); }
            public FileChannel truncate(long size) throws IOException {
                ch.truncate(size);
                return this;
            }
            public void force(boolean metaData) throws IOException { ch.force(metaData); }
            public long transferTo(long position, long count,
                    java.nio.channels.WritableByteChannel target) throws IOException {
                return ch.transferTo(position, count, target);
            }
            public long transferFrom(java.nio.channels.ReadableByteChannel src, long position,
                    long count) throws IOException {
                return ch.transferFrom(src, position, count);
            }
            public java.nio.MappedByteBuffer map(MapMode mode, long position, long size)
                    throws IOException {
                return ch.map(mode, position, size);
            }
            public FileLock lock(long position, long size, boolean shared) throws IOException {
                return ch.lock(position, size, shared);
            }
            public FileLock tryLock(long position, long size, boolean shared)
                    throws IOException {
                return ch.tryLock(position, size, shared);
            }
            protected void implCloseChannel() throws IOException {
                ch.close();
            }
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
    static void testReadOfLastFileDuringForce(TestEnvironment c) throws Exception {
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
        Assert.assertTrue("the read waited", System.nanoTime() - t0 < 10000000000L);
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
    static void testReadDuringNewFile(TestEnvironment c) throws Exception {
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
        Assert.assertTrue("the read waited", System.nanoTime() - t0 < 10000000000L);
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
    static void testCutOnItsOwnThread(TestEnvironment c) throws Exception {
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
        Assert.assertTrue("the cut or the read waited", System.nanoTime() - t0 < 10000000000L);
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
    static void testFailedDeleteOfACut(TestEnvironment c) throws Exception {
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
     * bergdb 028-66: the cut's thread deletes the files that the cuts so far took off as one
     * batch, oldest first, and forces the directory once after it, not after each file;
     * files that a cut takes off while it deletes are the next batch, with a force of their
     * own. The stream reads the same, and a restart opens it.
     */
    @Nano
    static void testCutDeletesABatchWithOneDirectoryForce(TestEnvironment c) throws Exception {
        final List<String> log = Collections.synchronizedList(new ArrayList<String>());
        HeldIo io = new HeldIo() {
            protected void forceDirectory(File directory) throws IOException {
                super.forceDirectory(directory);
                log.add("force");
            }
            
            protected boolean delete(File file) throws IOException {
                boolean ok = super.delete(file);
                log.add("delete " + file.getName());
                return ok;
            }
        };
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir, io);
        byte[] bytes = new byte[1400 * 1000 + 100];
        new Random(28066).nextBytes(bytes);
        try {
            f.append(bytes, 0, 1400 * 1000);        // Seven files of 200,000 bytes.
            f.append(bytes, 1400 * 1000, 100);      // An eighth, at 1,400,000.
            log.clear();
            
            // The thread holds in its first delete while a second cut takes off three files.
            io.holdDelete = new java.util.concurrent.CountDownLatch(1);
            f.pretruncate(400 * 1000);
            Assert.assertTrue(io.held.await(10, java.util.concurrent.TimeUnit.SECONDS));
            f.pretruncate(1000 * 1000);
            io.holdDelete.countDown();
            f.awaitDeletes();
            
            Assert.assertEquals(Arrays.asList(
                    "delete " + fileName(0), "delete " + fileName(200 * 1000), "force",
                    "delete " + fileName(400 * 1000), "delete " + fileName(600 * 1000),
                    "delete " + fileName(800 * 1000), "force"), log);
            Assert.assertEquals(1000 * 1000, f.getFirstPos());
            readAndCheck(f, 1000 * 1000, 400 * 1000 + 100, bytes);
            
            // A cut that takes every file but the last: one batch of two, one force.
            log.clear();
            f.pretruncate(1400 * 1000 + 50);
            f.awaitDeletes();
            Assert.assertEquals(Arrays.asList(
                    "delete " + fileName(1000 * 1000), "delete " + fileName(1200 * 1000),
                    "force"), log);
        } finally {
            f.close();
        }
        Assert.assertEquals(Arrays.asList(fileName(1400 * 1000)),
                Arrays.asList(dir.list((d, name) -> name.endsWith(SUFFIX))));
        FileStream again = new FileStream(dir);
        try {
            Assert.assertEquals(1400 * 1000, again.getFirstPos());
            readAndCheck(again, 1400 * 1000, 100, bytes);
        } finally {
            again.close();
        }
    }
    
    /**
     * bergdb 005-46: a read by a thread whose interrupt flag is set reads, and leaves the
     * flag set; a FileChannel would have closed itself. And a read that finds the channel
     * closed, as an interrupt during a read of another thread closes it, opens it again.
     */
    @Nano
    static void testReadsAndInterrupts(TestEnvironment c) throws Exception {
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
     * Regression test for bergdb 015-17: a read of a file that close() has closed fails alone,
     * as one of a file that a cut deleted does, and the stream has not failed: a second
     * close(), as BufferedStream.close() makes one after its thread's, does not throw the
     * read's exception. It did, and Db.close() threw it as a failed close (InterruptStress,
     * 016-08). Both ways a read meets the close: it begins after it (the read's check of
     * isClosed), or it is under way when the close closes its channel (the check after the
     * ClosedChannelException, reopenChannel()); a held channel stops the read between the two.
     */
    @Nano
    static void testReadOfClosedFileFailsAlone(TestEnvironment c) throws Exception {
        for (int i = 0; i < 2; i++) {
            final boolean underWay = i == 1;
            HeldReadIo io = new HeldReadIo();
            final FileStream f = new FileStream(c.createTempDir(), io);
            byte[] bytes = new byte[100 * 1000];
            f.append(bytes, 0, bytes.length);
            Run reader = null;
            final java.util.concurrent.CountDownLatch hold =
                    new java.util.concurrent.CountDownLatch(1);
            if (underWay) {
                io.holdRead = hold;
                reader = new Run(() -> f.read(1000, new byte[10], 0, 10));
                Assert.assertTrue(io.held.await(10, java.util.concurrent.TimeUnit.SECONDS));
            }
            f.close();      // The storage thread's close, the first.
            Throwable failed = null;
            if (underWay) {
                hold.countDown();
                reader.join(10000);
                Assert.assertTrue("the read still runs after 10 s", !reader.isAlive());
                failed = reader.failure;
            } else {
                try {
                    f.read(1000, new byte[10], 0, 10);
                } catch (IOException e) {
                    failed = e;
                }
            }
            Assert.assertTrue("the read of the closed file fails: " + failed,
                    failed instanceof IOException && !(failed instanceof ReadBelowFirstPosException)
                    && failed.getMessage().startsWith("File closed"));
            f.close();      // BufferedStream.close()'s, the second: nothing failed.
        }
    }
    
    /**
     * bergdb 005-46: a cut and a new FileStream by a thread whose interrupt flag is set work,
     * and leave the flag set. Their directory forces closed their FileChannel, and the
     * stream failed with ClosedByInterruptException; the cut failed the database.
     */
    @Nano
    static void testCutAndOpenByInterruptedThread(TestEnvironment c) throws Exception {
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
    static void testReadersBesideWriterAndCuts(TestEnvironment c) throws Exception {
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
     * bergdb 024-36 (OT2): a start never finds a directory still in LOCKED_DIRS after the
     * close has closed its lock file. The test holds the monitor of the system properties, so
     * that the closing thread stops in unlockDir() at the removal of its property, right
     * after the lock file's close; a second thread then checks LOCKED_DIRS as lockDir() does,
     * under its monitor. Before, the check went through at once and found the key listed,
     * with the lock file closed: on Linux, a new directory that got the deleted directory's
     * inode in that moment was refused as in use. Now the check waits until the close has
     * removed the keys. Does not need a reused inode, so it fails before the fix on every
     * system.
     */
    @Nano
    static void testNoStartSeesAClosedLockStillListed(TestEnvironment c) throws Exception {
        File dir = c.createTempDir();
        FileStream f = new FileStream(dir);
        Object key = lockKey(dir);
        IOException[] closeError = new IOException[1];
        boolean[] listed = new boolean[1];
        Thread closer = new Thread(() -> {
            try {
                f.close();
            } catch (IOException e) {
                closeError[0] = e;
            }
        }, "closer");
        Thread checker = new Thread(() -> {
            synchronized (LOCKED_DIRS) {
                listed[0] = LOCKED_DIRS.contains(key);
            }
        }, "checker");
        boolean fileClosed;
        synchronized (System.getProperties()) {
            closer.start();
            awaitState(closer, Thread.State.BLOCKED, null);
            try (RandomAccessFile other = new RandomAccessFile(new File(dir, LOCK_NAME), "rw")) {
                // The lock file is closed: a new channel in this JVM gets its lock.
                fileClosed = other.getChannel().tryLock(LOCK_POS, 1, false) != null;
            }
            checker.start();
            awaitState(checker, Thread.State.BLOCKED, Thread.State.TERMINATED);
        }
        closer.join(60_000);
        Assert.assertFalse("the closer thread did not end within 60 s", closer.isAlive());
        checker.join(60_000);
        Assert.assertFalse("the checker thread did not end within 60 s", checker.isAlive());
        if (closeError[0] != null) {
            throw closeError[0];
        }
        Assert.assertTrue("the closer stopped before the lock file's close", fileClosed);
        Assert.assertFalse("a start found the directory listed after its lock file was closed",
                listed[0]);
        new FileStream(dir).close();
    }
    
    /** Waits, at most 10 s, until the thread is in one of the states (the second may be null). */
    private static void awaitState(Thread t, Thread.State a, Thread.State b) 
            throws InterruptedException {
        long end = System.nanoTime() + 10_000_000_000L;
        while (t.getState() != a && t.getState() != b) {
            if (t.getState() == Thread.State.TERMINATED || System.nanoTime() > end) {
                throw new AssertionError(t.getName() + " is " + t.getState() + ", not " + a);
            }
            Thread.sleep(1);
        }
    }
    
    /**
     * bergdb 005-63: a second FileStream on the directory in the same JVM is refused, also by
     * another path to it, and the first goes on; after the first's close(), a new one opens.
     */
    @Nano
    static void testSecondStreamRefused(TestEnvironment c) throws IOException {
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
     * bergdb 015-24: a directory that another copy of the class holds, by its system property,
     * is refused before the lock file is opened, or made, and the property stays. This copy's
     * own value, as a program that puts back older system properties can leave it, refuses
     * nothing; the close removes it.
     */
    @Nano
    static void testOtherCopyRefusedFirst(TestEnvironment c) throws IOException {
        File dir = c.createTempDir();
        String name = PROPERTY_PREFIX + lockKey(dir);
        System.getProperties().put(name, "another copy");
        try {
            try {
                new FileStream(dir).close();
                throw new AssertionError("opened a directory that another copy holds");
            } catch (DirectoryInUseException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("another class loader"));
            }
            Assert.assertFalse("the lock file was made", new File(dir, LOCK_NAME).exists());
            Assert.assertEquals("another copy", System.getProperty(name));
            
            System.getProperties().put(name, COPY);
            FileStream f = new FileStream(dir);
            Assert.assertEquals(COPY, System.getProperty(name));
            f.close();
            Assert.assertNull(System.getProperty(name));
        } finally {
            System.getProperties().remove(name);
        }
    }
    
    /**
     * bergdb 005-63: bergdb.lock holds its text, is not a stream file, and stays as it is
     * through appends, a cut, a close, a new open and seekFirstPos(). A directory without it,
     * as from 2026.1, opens and gets one.
     */
    @Nano
    static void testLockFile(TestEnvironment c) throws IOException {
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
    static void testLockAcrossProcesses(TestEnvironment c) throws Exception {
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
    
    /**
     * bergdb 015-24: two copies of FileStream in one JVM, from two class loaders (two
     * applications that each bring bergdb.jar, or a redeploy; here a URLClassLoader over this
     * class's jar). Each refuses a directory that the other holds, and the refusal leaves the
     * lock for other processes: a child's open is refused. Before, the other copy's LOCKED_DIRS
     * was empty: it opened bergdb.lock, was refused by OverlappingFileLockException, and the
     * close of its channel released this JVM's lock on macOS and Linux; the child opened.
     */
    @Nano("f")
    static void testLockAcrossClassLoaders(TestEnvironment c) throws Exception {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = c.createTempDir();
        java.net.URL code = FileStream.class.getProtectionDomain().getCodeSource().getLocation();
        try (java.net.URLClassLoader loader = new java.net.URLClassLoader(
                new java.net.URL[] {code}, ClassLoader.getPlatformClassLoader())) {
            Class<?> other = Class.forName(FileStream.class.getName(), true, loader);
            Assert.assertTrue("another copy of the class", other != FileStream.class);
            java.lang.reflect.Constructor<?> open = other.getConstructor(File.class);
            
            FileStream f = new FileStream(dir);
            try {
                try {
                    other.getMethod("close").invoke(open.newInstance(dir));
                    throw new AssertionError("the other copy opened a directory held here");
                } catch (java.lang.reflect.InvocationTargetException e) {
                    Assert.assertEquals(DirectoryInUseException.class.getName(), 
                            e.getCause().getClass().getName());
                }
                Assert.assertEquals("refused", runLockChild(dir));
                byte[] bytes = new byte[] {1, 2, 3};
                f.append(bytes, 0, bytes.length);
            } finally {
                f.close();
            }
            
            Object g = open.newInstance(dir);
            try {
                Assert.assertEquals(3L, other.getMethod("getLength").invoke(g));
                try {
                    new FileStream(dir).close();
                    throw new AssertionError("this copy opened a directory that the other holds");
                } catch (DirectoryInUseException e) {
                    // Expected.
                }
                Assert.assertEquals("refused", runLockChild(dir));
            } finally {
                other.getMethod("close").invoke(g);
            }
        }
        FileStream f2 = new FileStream(dir);
        Assert.assertEquals(3, f2.getLength());
        f2.close();
    }
    
    private static Process startLockChild(String mode, File dir) throws IOException {
        String javaBin = System.getProperty("java.home") + "/bin/java";
        String cp = System.getProperty("java.class.path");
        return new ProcessBuilder(javaBin, "-cp", cp, LockChild.class.getName(), mode, 
                dir.getPath()).redirectErrorStream(true).start();
    }
    
    // ---- bergdb 021-20: the directory deleted or replaced while the stream has it ----
    
    /**
     * bergdb 021-20 (020-24-10, U10-1): the stream's directory deleted, and a new one made at
     * its path, while the stream is open, as when a database's directory is deleted and a new
     * database is created there. A FileStream at the path is refused while this one is open,
     * and this one's next file is refused, and the stream fails: nothing is made in the new
     * directory. Before, the second FileStream opened, and this one made its next file in the
     * new directory, by name: a new database there was broken.
     */
    @Nano
    static void testNoNewFileInAReplacedDirectory(TestEnvironment c) throws IOException {
        File dir = new File(c.createTempDir(), "db");
        FileStream f = new FileStream(dir);
        byte[] bytes = new byte[100 * 1000];
        f.append(bytes, 0, bytes.length);
        deleteTree(dir);
        Assert.assertTrue("made again", dir.mkdir());
        try {
            new FileStream(dir).close();
            throw new AssertionError("a second FileStream at the path");
        } catch (DirectoryInUseException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("deleted"));
        }
        f.append(bytes, 0, bytes.length);       // The first file is full: 200,000 bytes.
        try {
            f.append(bytes, 0, 1);
            throw new AssertionError("a new file in the replaced directory");
        } catch (IOException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("no longer"));
        }
        Assert.assertEquals(0, dir.list().length);
        try {
            f.close();
            throw new AssertionError("close() of the failed stream did not throw");
        } catch (IOException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("no longer"));
        }
        FileStream f2 = new FileStream(dir);    // The path is free.
        Assert.assertEquals(0L, f2.getLength());
        f2.close();
    }
    
    /**
     * bergdb 021-20: a cut after the directory was replaced deletes nothing in the new one,
     * and the stream fails. It deleted the new directory's file of the same name.
     */
    @Nano
    static void testNoDeleteInAReplacedDirectory(TestEnvironment c) throws Exception {
        File dir = new File(c.createTempDir(), "db");
        FileStream f = new FileStream(dir);
        byte[] bytes = new byte[1000 * 1000];
        f.append(bytes, 0, bytes.length);
        deleteTree(dir);
        Assert.assertTrue("made again", dir.mkdir());
        File other = new File(dir, indexToString(0) + SUFFIX);
        Files.write(other.toPath(), new byte[] {1, 2, 3});
        f.pretruncate(800 * 1000);
        try {
            f.awaitDeletes();
            throw new AssertionError("a cut in the replaced directory");
        } catch (IOException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("no longer"));
        }
        Assert.assertTrue("the new directory's file is there", other.exists());
        try {
            f.close();
            throw new AssertionError("close() of the failed stream did not throw");
        } catch (IOException e) {
            // Expected: the stream's failure.
        }
    }
    
    /**
     * bergdb 020-24-10, U10-5: FileStreams opened at once by several threads on a directory
     * that does not exist: one opens it, the others are refused as in use. Those whose
     * mkdirs() found the directory made by another thread threw "Directory ... could not be
     * created.", though it was there.
     */
    @Nano
    static void testConcurrentOpensOfANewDirectory(TestEnvironment c) throws Exception {
        File root = c.createTempDir();
        final int threads = 8;
        for (int round = 0; round < 10; round++) {
            final File dir = new File(root, "r" + round + "/a/b");
            final java.util.concurrent.CyclicBarrier barrier = 
                    new java.util.concurrent.CyclicBarrier(threads);
            final List<Throwable> failures = Collections.synchronizedList(new ArrayList<Throwable>());
            final java.util.concurrent.atomic.AtomicInteger opened = 
                    new java.util.concurrent.atomic.AtomicInteger();
            Thread[] ts = new Thread[threads];
            for (int i = 0; i < threads; i++) {
                ts[i] = new Thread(() -> {
                    try {
                        barrier.await();
                        FileStream f = new FileStream(dir);
                        opened.incrementAndGet();
                        f.close();
                    } catch (DirectoryInUseException e) {
                        // Expected: another thread has it.
                    } catch (Throwable e) {
                        failures.add(e);
                    }
                });
                ts[i].start();
            }
            for (Thread t : ts) {
                t.join(60_000);
                Assert.assertFalse("an opening thread did not end within 60 s", t.isAlive());
            }
            if (!failures.isEmpty()) {
                throw new AssertionError("round " + round + ": " + failures, failures.get(0));
            }
            Assert.assertTrue("opened", opened.get() >= 1);
        }
    }
    
    /**
     * bergdb 021-24 (a review of 021-20): the directory replaced by another stream's while
     * newFile() forces the last file (Force.SWITCH, per-append forcing off). 021-20's check
     * came before that force, so the stream made its next file in the replacement: its
     * append and close() returned, and the replacement no longer opened (BadDirStateException).
     * Now the check comes after the force, right before the file is made: the append fails,
     * the stream with it, and the replacement opens with its own bytes.
     */
    @Nano
    public static void testNoNewFileWhenReplacedDuringTheSwitch(TestEnvironment c)
            throws Exception {
        File root = c.createTempDir();
        File dir = new File(root, "db");
        File replacement = new File(root, "replacement");
        final byte[] bytes = new byte[200 * 1000];
        FileStream other = new FileStream(replacement);
        other.append(bytes, 0, 1000);
        other.close();
        
        final java.util.concurrent.CountDownLatch inSwitch = 
                new java.util.concurrent.CountDownLatch(1);
        final java.util.concurrent.CountDownLatch resume = 
                new java.util.concurrent.CountDownLatch(1);
        FileStreamIo io = new FileStreamIo() {
            @Override
            protected void forceFile(File file, RandomAccessFile handle, Force why)
                    throws IOException {
                if (why == Force.SWITCH) {
                    inSwitch.countDown();
                    try {
                        if (!resume.await(10, java.util.concurrent.TimeUnit.SECONDS)) {
                            throw new IOException("test: not resumed");
                        }
                    } catch (InterruptedException e) {
                        throw new IOException(e);
                    }
                }
                super.forceFile(file, handle, why);
            }
        };
        final FileStream f = new FileStream(dir, io, false);
        f.append(bytes, 0, bytes.length);       // The first file is full: 200,000 bytes.
        final Throwable[] thrown = new Throwable[1];
        Thread appender = new Thread(() -> {
            try {
                f.append(bytes, 0, 1);      // A new file, after the SWITCH force.
            } catch (Throwable e) {
                thrown[0] = e;
            }
        });
        appender.start();
        try {
            Assert.assertTrue("in the switch", 
                    inSwitch.await(10, java.util.concurrent.TimeUnit.SECONDS));
            Files.move(dir.toPath(), new File(root, "moved").toPath());
            Files.move(replacement.toPath(), dir.toPath());
        } finally {
            resume.countDown();
            appender.join(60_000);
            Assert.assertFalse("the appender thread did not end within 60 s", appender.isAlive());
        }
        IOException closeFailure = null;
        try {
            f.close();
        } catch (IOException e) {
            closeFailure = e;
        }
        
        Assert.assertFalse("a new file in the replacement", 
                new File(dir, indexToString(2) + SUFFIX).exists());
        Assert.assertTrue("the append threw: " + thrown[0], thrown[0] instanceof IOException
                && thrown[0].getMessage().contains("no longer"));
        Assert.assertTrue("close() threw the failure: " + closeFailure, closeFailure != null
                && closeFailure.getMessage().contains("no longer"));
        FileStream f2 = new FileStream(dir);    // The replacement, with its own bytes.
        try {
            Assert.assertEquals(1000L, f2.getLength());
        } finally {
            f2.close();
        }
    }
    
    /**
     * bergdb 021-24: what is left, a replacement right before the new file is made, after
     * the check (here inside FileStreamIo.open()). The check after the open fails the
     * stream before it writes a byte: the append and close() throw. The new file, empty, is
     * in the replacement, which a stream refuses beside the replacement's own files
     * (BadDirStateException) until it is removed: since 2026-11-27 (bergdb 028-66) for the
     * replacement's file, before the last and not a multiple of 100,000 bytes long, as the
     * open takes a gap in the files.
     */
    @Nano
    public static void testReplacedRightBeforeTheOpen(TestEnvironment c) throws Exception {
        final File root = c.createTempDir();
        final File dir = new File(root, "db");
        final File replacement = new File(root, "replacement");
        final byte[] bytes = new byte[200 * 1000];
        FileStream other = new FileStream(replacement);
        other.append(bytes, 0, 1000);
        other.close();
        
        FileStreamIo io = new FileStreamIo() {
            boolean replaced = false;
            
            @Override
            protected RandomAccessFile open(File file) throws IOException {
                if (file.getName().equals(indexToString(2) + SUFFIX) && !replaced) {
                    replaced = true;
                    Files.move(dir.toPath(), new File(root, "moved").toPath());
                    Files.move(replacement.toPath(), dir.toPath());
                }
                return super.open(file);
            }
        };
        FileStream f = new FileStream(dir, io, false);
        f.append(bytes, 0, bytes.length);
        try {
            f.append(bytes, 0, 1);
            throw new AssertionError("the stream went on in the replacement");
        } catch (IOException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("no longer"));
        } finally {
            try {
                f.close();
                throw new AssertionError("close() of the failed stream did not throw");
            } catch (IOException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("no longer"));
            }
        }
        
        File made = new File(dir, indexToString(2) + SUFFIX);
        Assert.assertEquals(0L, made.length());
        try {
            new FileStream(dir).close();
            throw new AssertionError("opened with the empty file");
        } catch (BadDirStateException e) {
            // Expected.
        }
        Assert.assertTrue(made.delete());
        FileStream f2 = new FileStream(dir);
        try {
            Assert.assertEquals(1000L, f2.getLength());
        } finally {
            f2.close();
        }
    }
    
    /** Deletes 'dir' and everything in it. */
    private static void deleteTree(File dir) throws IOException {
        try (java.util.stream.Stream<Path> paths = Files.walk(dir.toPath())) {
            for (Path p : paths.sorted(Comparator.reverseOrder()).toArray(Path[]::new)) {
                Files.delete(p);
            }
        }
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
