package bergdb.core;

import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.Comparator;

/** Injects failures at the same production boundary as the power-loss tests. */
public final class FailedOpenProbe {
    private static final class FailIo extends FileStreamIo {
        final int kind;
        RandomAccessFile opened;
        FailIo(int kind) { this.kind = kind; }
        protected RandomAccessFile open(File f) throws IOException {
            return opened = super.open(f);
        }
        protected void forceFile(File f, RandomAccessFile handle) throws IOException {
            if (kind == 0) throw new IOException("injected checked failure");
            if (kind == 1) throw new IllegalStateException("injected unchecked failure");
            throw new AssertionError("injected error");
        }
    }

    public static void main(String[] args) throws Exception {
        String[] kinds = {"IOException", "RuntimeException", "Error"};
        for (int kind = 0; kind < kinds.length; kind++) {
            File dir = Files.createTempDirectory(new File(args[0]).toPath(), "failed-open-").toFile();
            FailIo io = new FailIo(kind);
            try {
                try {
                    new FileStream(dir, io).close();
                    throw new AssertionError("failure injection did not run");
                } catch (IOException | RuntimeException | Error expected) {
                    System.out.println(kinds[kind] + ": " + expected.getClass().getSimpleName());
                }
                System.out.println("  data handle still valid: " + io.opened.getFD().valid());
                try {
                    FileStream recovered = new FileStream(dir);
                    recovered.close();
                    System.out.println("  reopen: succeeded");
                } catch (IOException failure) {
                    System.out.println("  reopen: " + failure.getClass().getSimpleName());
                }
            } finally {
                // No Db was started. The failed constructor has no returned stream to close.
                // Close the captured data handle; the leaked directory lock dies at JVM exit.
                if (io.opened != null) io.opened.close();
                try (java.util.stream.Stream<java.nio.file.Path> paths = Files.walk(dir.toPath())) {
                    for (java.nio.file.Path p : paths.sorted(Comparator.reverseOrder()).toList()) {
                        Files.delete(p);
                    }
                }
            }
        }
    }
}
