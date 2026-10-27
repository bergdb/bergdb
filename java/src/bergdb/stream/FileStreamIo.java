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

    protected void forceFile(File file, RandomAccessFile handle) throws IOException {
        // On the tested macOS JDK this reaches F_FULLFSYNC; getFD().sync()
        // reaches fsync instead. On Linux force(true) reaches fsync.
        handle.getChannel().force(true);
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
