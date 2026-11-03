package bergdb.core;

import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.Comparator;

/** Tests file rotation with sparse zero data, without writing gigabytes to the device. */
public final class Max2GProbe {
    private static final class SparseIo extends FileStreamIo {
        protected void write(File file, RandomAccessFile handle, byte[] bytes,
                int offset, int length) throws IOException {
            long end = handle.getFilePointer() + length;
            handle.setLength(end);
            handle.seek(end);
        }
        // File-size selection is the subject, not power-loss persistence.
        protected void forceFile(File file, RandomAccessFile handle) {}
        protected void forceDirectory(File dir) {}
    }

    public static void main(String[] args) throws Exception {
        File dir = Files.createTempDirectory(new File(args[0]).toPath(), "max-2g-").toFile();
        FileStream stream = null;
        try {
            // Generate the entire prefix through the public stream API. A restart
            // after each 100 MB keeps the final two files short: reopening chooses
            // its capacity from their actual lengths, not the retained prefix size.
            byte[] fourMB = new byte[4_000_000];
            for (int round = 0; round < 400; round++) {
                stream = new FileStream(dir, new SparseIo());
                stream.setMax2G(true);
                for (int i = 0; i < 25; i++) stream.append(fourMB, 0, fourMB.length);
                stream.close();
                stream = null;
            }
            stream = new FileStream(dir, new SparseIo());
            stream.setMax2G(true);
            File[] before = dir.listFiles(f -> f.getName().endsWith(".bergdb"));
            long largestBefore = 0;
            for (File file : before) largestBefore = Math.max(largestBefore, file.length());
            System.out.println("After 400 public-API write/reopen rounds: files=" + before.length
                    + "; largest=" + largestBefore + "; length=" + stream.getLength());
            byte[] zeros = new byte[1_000_000];
            for (int i = 0; i < 2001; i++) stream.append(zeros, 0, zeros.length);
            File[] files = dir.listFiles(f -> f.getName().endsWith(".bergdb"));
            long max = 0;
            for (File file : files) max = Math.max(max, file.length());
            System.out.println("After setMax2G(true): largest=" + max + "; files=" + files.length);
            System.out.println("Cap respected: " + (max <= 2_000_000_000L));
        } finally {
            if (stream != null) stream.close();
            try (java.util.stream.Stream<java.nio.file.Path> paths = Files.walk(dir.toPath())) {
                for (java.nio.file.Path p : paths.sorted(Comparator.reverseOrder()).toList()) {
                    Files.delete(p);
                }
            }
        }
    }
}
