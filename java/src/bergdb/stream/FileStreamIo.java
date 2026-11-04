package bergdb.stream;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.channels.FileChannel;
import java.nio.file.StandardOpenOption;

/**
 * The persistence boundary of FileStream. Tests replace the physical
 * operations through it while exercising the production code.
 * This class is public for use by bergdb.core.FileStreamPowerLossTester.
 * 
 * @author Frans Lundberg
 */
public class FileStreamIo {
    //
    // Created for bergdb.core.FileStreamPowerLossTester, 2026-10-14.
    // Needed for testing.
    //
    protected RandomAccessFile open(File file) throws IOException {
        return new RandomAccessFile(file, "rw");
    }

    protected void write(File file, RandomAccessFile handle, byte[] bytes, int offset, int length)
            throws IOException {
        handle.write(bytes, offset, length);
    }

    /**
     * Why FileStream forces a file (2026-11-04, bergdb 005-47). With per-append forcing off,
     * APPEND never occurs and the others keep the database whole after a power loss; with it
     * on, SWITCH, CUT and CLOSE find nothing unforced and do not occur.
     */
    public enum Force {
        /** An append, with per-append forcing on. */
        APPEND,
        /** A file opened for appends, new or the last file at a start, before its directory. */
        OPEN,
        /** The last file, before the stream moves to a new file. */
        SWITCH,
        /** The last file, before the files of a cut are deleted. */
        CUT,
        /** The last file, at close(). */
        CLOSE
    }

    /**
     * The force that FileStream calls: forceFile(file, handle). A test can count the forces
     * by their reason, or leave one kind out.
     */
    protected void forceFile(File file, RandomAccessFile handle, Force why) throws IOException {
        forceFile(file, handle);
    }

    protected void forceFile(File file, RandomAccessFile handle) throws IOException {
        // On the tested macOS JDK this reaches F_FULLFSYNC; getFD().sync()
        // reaches fsync instead. On Linux force(true) reaches fsync.
        handle.getChannel().force(true);
    }

    /**
     * Opens a file's read channel; reads are positional reads on it (bergdb 005-46). A test
     * can give a channel that is slow, fails, or is closed under its readers.
     */
    protected FileChannel openRead(File file) throws IOException {
        return FileChannel.open(file.toPath(), StandardOpenOption.READ);
    }

    protected void forceDirectory(File directory) throws IOException {
        try (FileChannel channel = FileChannel.open(directory.toPath(), StandardOpenOption.READ)) {
            channel.force(true);
        }
    }

    protected boolean delete(File file) throws IOException {
        return file.delete();
    }

    protected boolean rename(File file, File destination) throws IOException {
        return file.renameTo(destination);
    }
}
