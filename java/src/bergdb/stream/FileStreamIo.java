package bergdb.stream;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.channels.FileChannel;
import java.nio.file.StandardOpenOption;

/**
 * The persistence boundary of FileStream. Package-private so fault tests can
 * replace the physical operations while exercising the production ordering.
 * A completed append means forced bytes, not merely readable bytes.
 */
class FileStreamIo {
    RandomAccessFile open(File file) throws IOException {
        return new RandomAccessFile(file, "rw");
    }

    void write(File file, RandomAccessFile handle, byte[] bytes, int offset, int length)
            throws IOException {
        handle.write(bytes, offset, length);
    }

    void forceFile(File file, RandomAccessFile handle) throws IOException {
        // On the tested macOS JDK this reaches F_FULLFSYNC; getFD().sync()
        // reaches fsync instead. On Linux force(true) reaches fsync.
        handle.getChannel().force(true);
    }

    void forceDirectory(File directory) throws IOException {
        try (FileChannel channel = FileChannel.open(directory.toPath(), StandardOpenOption.READ)) {
            channel.force(true);
        }
    }

    boolean delete(File file) throws IOException {
        return file.delete();
    }

    boolean rename(File file, File destination) throws IOException {
        return file.renameTo(destination);
    }
}
