package bergdb.core;

import bergdb.stream.FileStream;
import java.io.File;
import java.nio.file.Files;
import java.util.Comparator;

public final class CutEndProbe {
    public static void main(String[] args) throws Exception {
        File dir = Files.createTempDirectory(new File(args[0]).toPath(), "cut-end-").toFile();
        FileStream fs = new FileStream(dir);
        try {
            for (int n : new int[] {0, 3}) {
                if (n != 0) fs.append(new byte[n], 0, n);
                try {
                    fs.pretruncate(fs.getLength());
                    System.out.println("cut at length " + fs.getLength() + ": accepted");
                } catch (Throwable failure) {
                    System.out.println("cut at length " + fs.getLength() + ": " + failure);
                }
            }
            fs.append(new byte[] {7}, 0, 1);
            byte[] b = new byte[1];
            fs.read(3, b, 0, 1);
            System.out.println("Stream remains usable: length=" + fs.getLength() + ", last=" + b[0]);
        } finally {
            fs.close();
            try (java.util.stream.Stream<java.nio.file.Path> paths = Files.walk(dir.toPath())) {
                for (java.nio.file.Path p : paths.sorted(Comparator.reverseOrder()).toList()) {
                    Files.delete(p);
                }
            }
        }
    }
}
