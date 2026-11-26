import bergdb.stream.FileStream;
import java.io.File;
/**
 * bergdb 028-62 (2026-11-26): the time of FileStream's cut thread per deleted file. Appends
 * MB megabytes to a new FileStream in DIR (hard sync, the default), cuts at the length and
 * waits for the deletes. Kind: timing (the number is the result).
 *
 * Usage, from the repository's root, after java/build.sh:
 *   javac -d CLASSES -cp java/build/bergdb.jar PROBES/DelRate.java
 *   java -cp CLASSES:java/build/bergdb.jar DelRate DIR MB
 */
public class DelRate {
    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        int mb = Integer.parseInt(a[1]);
        dir.mkdirs();
        FileStream f = new FileStream(dir, true);
        byte[] b = new byte[1000 * 1000];
        long t0 = System.nanoTime();
        for (int i = 0; i < mb; i++) f.append(b, 0, b.length);
        long t1 = System.nanoTime();
        int files = dir.listFiles((d, n) -> n.endsWith(".bergdb")).length;
        f.pretruncate(f.getLength());
        f.awaitDeletes();
        long t2 = System.nanoTime();
        int left = dir.listFiles((d, n) -> n.endsWith(".bergdb")).length;
        System.out.printf("%d MB in %d files: append %.0f ms; deletes of %d files %.0f ms, %.1f ms a file%n",
                mb, files, (t1 - t0) / 1e6, files - left, (t2 - t1) / 1e6, (t2 - t1) / 1e6 / (files - left));
        f.close();
        for (File x : dir.listFiles()) x.delete();
        dir.delete();
    }
}
