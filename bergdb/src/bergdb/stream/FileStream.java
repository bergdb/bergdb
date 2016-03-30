package bergdb.stream;

import java.io.EOFException;
import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Random;

import bergdb.common.Bug;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.util.BadFormatException;

/**
 * An object of this class is an AppendOnlyStream that stores the stream data 
 * in one directory in the filesystem.
 * Multiple files are used to be able pretruncate the stream and reclaim disk space.
 * 
 * Files of sizes 200*1000, 1*M, 5*M, 20*M, 100*M, 500*M, 2*G, 10*G, 50*G, 200*G
 * are used to store the stream (4-5 factor log factor). Decimal factors, M = 1,000,000 bytes.
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
    
    private final File dir;
    private long firstPos = 0;
    private long length = 0;
    private int fileSizeIndex = 0;
    private boolean renameAsDelete = false;
    private boolean max2G = false;
    
    /** First spos of each file in 'files'. Protected by this. */
    private long[] dbFilePositions;
    
    /** The .bergdb files of the directory. Protected by this. */
    private DbFile[] dbFiles;
    
    /** If not null, this stream should be considered faulty and not used any further. */
    private volatile IOException ioException = null;
    
    /**
     * Creates a new stream if it does not exist or opens an existing one if it exists.
     * If the directory 'dir' does not exist an attempt to create it is made.
     * 
     * @param dir
     *      The directory to use.
     * @throws IOException
     *      If existing directory cannot be read from / written to, or if 
     *      'dir' does not exist and cannot be created.
     * @throws BadDirStateException
     *      If the directory exists but the files in the directory
     *      are not in a valid state. The files in the directory were modified by some other software.
     */
    public FileStream(File dir) throws IOException {
        if (dir == null) {
            throw new IllegalArgumentException("dir == null not allowed");
        }
        
        this.dir = dir;
        createDirIfNeeded();
        handleExistingFiles();
    }
    
    public void read(long spos, byte[] dest, int destOffset, int length) throws IOException {
        //
        // Sync comments. Multiple concurrent reads are allowed, but only if made from different
        // files (needed since we use RandomAccessFile.seek()).
        //
        checkIOException();
        
        int actuallyRead;
        int leftToRead;
        
        while (true) {
            DbFile k = findFile(spos);
            if (k == null) {
                this.ioException = new IOException("No file found for reading at spos " + spos + ".");
                throw ioException;
            }
    
            actuallyRead = k.read(spos, dest, destOffset, length);
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

    public synchronized long getLength() {
        return length;
    }

    public void close() throws IOException {
        checkIOException();
        
        synchronized (this) {
            for (int i = 0; i < dbFiles.length; i++) {
                dbFiles[i].close();
            }
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
    
    /**
     * Call this method with "true" to disable file deletes.
     * Instead of actually deleting a stream file, the file will instead be renamed
     * by adding the suffix ".deleted" to its filename.
     */
    public void setRenameAsDelete(boolean b) {
        synchronized (this) {
            this.renameAsDelete = b;
        }
    }
    
    public synchronized long getFirstPos() {
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
        
        deleteAllFiles();
        
        this.length = pos;
        this.firstPos = pos;
        
        dbFiles = new DbFile[0];
        dbFilePositions = new long[0];
        newFile();
    }

    public synchronized void pretruncate(long pos) throws IOException {
        checkIOException();
        
        int index = -1;      // index of last file to delete
        
        long len = getLength();
        if (pos > len) {
            throw new IllegalArgumentException("pos > length of stream (" + len + ").");
        }
        
        for (int i = 0; i < dbFiles.length; i++) {
            DbFile k = dbFiles[i];
            if (k.spos + k.fileLength - 1 < pos) {
                index = i;
            } else {
                break;
            }
        }
        
        if (index != -1) {
            for (int i = 0; i <= index; i++) {
                dbFiles[i].delete();
            }
            
            int newSize = dbFiles.length - (index + 1);
            if (newSize < 1) {
                throw new Bug("Unexpected newSize: " + newSize + ". pos=" + pos 
                        + ", kfiles.length=" + dbFiles.length);
            }
            
            DbFile[] newFiles = new DbFile[newSize];
            long[] newPositions = new long[newSize];
            
            System.arraycopy(dbFiles, index + 1, newFiles, 0, newSize);
            System.arraycopy(dbFilePositions, index + 1, newPositions, 0, newSize);
            
            this.dbFiles = newFiles;
            this.dbFilePositions = newPositions;
            this.firstPos = dbFiles[0].spos;
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
            return;
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
        // Creates this.dbFiles, this.dbFilePositions. Sets this.length.
        
        dbFiles = new DbFile[bergdbFiles.length];
        dbFilePositions = new long[bergdbFiles.length];
        
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
                
                int index;
                try {
                    index = this.stringToIndex(name);
                } catch (BadFormatException e) {
                    throw new BadDirStateException("Bad name of bergdb file: " + f.getPath() + ".");
                }
                
                currentSpos = index * BYTES_PER_INDEX_UNIT;
                this.firstPos = currentSpos;
            }
            
            dbFilePositions[i] = currentSpos;
            
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
            
            int index;
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
     * @throws BadFormatException If not correctly formatted.
     */
    private int stringToIndex(String s) {
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
        
        int result = 0;
        try {
            result = Integer.parseInt(s);
        } catch (NumberFormatException e) {
            throw new BadFormatException("Not an int, '" + s + "'.");
        }
        return result;
    }
    
    private synchronized void deleteAllFiles() throws IOException {
        try {
            for (int i = 0; i < dbFiles.length; i++) {
                dbFiles[i].delete();
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

    private void newFile() throws IOException {
        synchronized (this) {
            if (this.length % BYTES_PER_INDEX_UNIT != 0) {
                throw new Bug("Illegal state, length = " + length);
            }
            
            if (dbFiles.length > 0) {
                // last file is opened for RW, close and reopen for read only.
                DbFile k = dbFiles[dbFiles.length - 1];
                reopenForReadOnly(k);
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
            
            DbFile[] newKFiles = new DbFile[dbFiles.length + 1];
            System.arraycopy(dbFiles, 0, newKFiles, 0, dbFiles.length);
            newKFiles[newKFiles.length - 1] = newFile;
            dbFiles = newKFiles;
            
            long[] newPositions = new long[dbFiles.length];
            System.arraycopy(dbFilePositions, 0, newPositions, 0, dbFilePositions.length);
            newPositions[newPositions.length - 1] = length;
            this.dbFilePositions = newPositions;
            
            assert dbFilePositions.length == dbFiles.length : dbFilePositions.length + " != " + dbFiles.length;
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
        
        DbFile result = null;
        assert dbFilePositions.length == dbFiles.length :
                dbFilePositions.length + " != " + dbFiles.length;
        
        synchronized (this) {
            for (int i = 0; i < dbFilePositions.length; i++) {
                long p = dbFilePositions[i];
                if (p <= spos) {
                    result = dbFiles[i];
                } else {
                    break;
                }
            }
        }
        
        return result;
    }
    
    private DbFile findLastFile() {        
        synchronized (this) {
            assert dbFiles.length > 0;
            return dbFiles[dbFiles.length - 1];
        }
    }
    
    private DbFile openForR(long spos, File file) throws IOException {
        DbFile k = new DbFile(spos, file, 0);
        k.rfile = new RandomAccessFile(file, "r");
        k.fileLength = k.rfile.length();
        k.isRw = false;
        synchronized (k) {}
        return k;
    }
    
    private DbFile openForRw(long spos, File file, long maxSize) throws IOException {
        DbFile k = new DbFile(spos, file, maxSize);
        k.rfile = new RandomAccessFile(file, "rws");
        k.fileLength = k.rfile.length();
        k.isRw = true;
        k.maxSize = maxSize;
        synchronized (k) {}
        return k;
    }
    
    private void reopenForReadOnly(DbFile dbFile) throws IOException {
        synchronized (dbFile) {
            dbFile.close();
            dbFile.rfile = new RandomAccessFile(dbFile.file, "r");
            dbFile.isRw = false;
            dbFile.isClosed = false;
        }
    }
    
    /**
     * Cached information about a particular *.bergdb file.
     * This class is not thread-safe.
     */
    private class DbFile {
        private File file;
        private RandomAccessFile rfile = null;
        private long fileLength;   // current length of the file
        private boolean isRw = false;
        private long spos;    // spos of first byte in file
        private long maxSize;
        private volatile boolean isClosed = false;
        
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
        
        synchronized void close() throws IOException {
            if (rfile == null) {
                throw new Bug("Cannot close file, not open, " + file.getPath());
            }
            
            try {
                rfile.close();
            } catch (IOException e) {
                ioException = e;
                throw e;
            }
            
            isClosed = true;
        }
        
        /**
         * Closes and deletes a file. 
         * If option renameAsDelete has been set, the file will be renamed instead of deleted.
         * 
         * @throws IOException
         */
        synchronized void delete() throws IOException {
            close();
            
            if (renameAsDelete) {
                boolean ok = file.renameTo(new File(dir, file.getName() + ".deleted"));
                if (!ok) {
                    ioException = new IOException("Could not rename file " + file.getPath() + ".");
                    throw ioException;
                }
            } else {
                boolean ok = file.delete();
                if (!ok) {
                    ioException = new IOException("Cound not delete file " + file.getPath() + ".");
                    throw ioException;
                }
            }
        }
        
        /**
         * Reads bytes from the file, returns number of bytes actually read.
         */
        synchronized int read(long spos, byte[] dest, int destOffset, int lengthToRead) throws IOException {
            if (isClosed) {
                ioException = new IOException("File closed, " + file.getPath() + ".");
                throw ioException;
            }
            
            if (spos < this.spos || spos > spos + fileLength) {
                throw new IllegalArgumentException("Cannot read from spos " + spos 
                        + ", this.spos=" + this.spos + ", length=" + fileLength);
            }
            
            long fileOffset = spos - this.spos;
            long actualLengthToRead = lengthToRead > fileLength - fileOffset ? fileLength - fileOffset : lengthToRead;
            assert actualLengthToRead <= Integer.MAX_VALUE;
            int actualLengthToReadInt = (int) actualLengthToRead;
            
            try {
                rfile.seek(fileOffset);
                rfile.readFully(dest, destOffset, actualLengthToReadInt);
            } catch (EOFException e) {          
                String message = "EOF when reading from " + file.getPath() 
                        + ". fileOffset: " + fileOffset 
                        + ". destOffset: " + destOffset
                        + ". lengthToRead: " + lengthToRead
                        + ". file.length(): " + file.length()
                        + ". rfile.length(): " + rfile.length()
                        + ". dest.length: " + dest.length
                        + ". Original EOFException message: " + e.getMessage();
                ioException = new EOFException(message);
                throw ioException;
            } catch (IOException e) {
                ioException = e;
                throw e;
            }
            
            return actualLengthToReadInt;
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
                rfile.write(bytes, offset, toAppend);
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
}
