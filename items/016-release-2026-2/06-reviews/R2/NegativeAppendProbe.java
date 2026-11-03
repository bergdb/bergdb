package bergdb.core;

import bergdb.stream.FileStream;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Comparator;

public final class NegativeAppendProbe {
    public static void main(String[] args) throws Exception {
        File dir = Files.createTempDirectory(new File(args[0]).toPath(), "negative-append-").toFile();
        FileStream f = new FileStream(dir);
        try {
            f.append(new byte[] {1, 2, 3}, 0, 3);
            System.out.println("Assertions enabled: " + NegativeAppendProbe.class.desiredAssertionStatus());
            try {
                f.append(new byte[1], 0, -1);
                System.out.println("Negative append: returned normally");
            } catch (Throwable failure) {
                System.out.println("Negative append: " + failure.getClass().getSimpleName());
            }
            System.out.println("Reported length: " + f.getLength());
            try {
                byte[] tail = new byte[1];
                f.read(2, tail, 0, 1);
                System.out.println("Previously committed last byte: " + tail[0]);
            } catch (IOException failure) {
                System.out.println("Previously committed last byte: " + failure.getClass().getSimpleName());
            }
            try {
                f.append(new byte[] {4}, 0, 1);
                System.out.println("Next append: succeeded");
            } catch (IOException failure) {
                System.out.println("Next append: " + failure.getClass().getSimpleName());
            }
        } finally {
            try { f.close(); } catch (IOException expected) { /* still releases handles */ }
            try (java.util.stream.Stream<java.nio.file.Path> paths = Files.walk(dir.toPath())) {
                for (java.nio.file.Path p : paths.sorted(Comparator.reverseOrder()).toList()) Files.delete(p);
            }
        }
    }
}
