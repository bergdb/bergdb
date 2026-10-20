import java.io.File;
import java.io.RandomAccessFile;
import java.util.Arrays;
import java.util.Locale;

import bergdb.stream.FileStream;

/**
 * 005-13, question 3: what one force costs on this machine. Appends of a given size to a
 * FileStream, each forced as FileStream forces it (FileChannel.force(true): F_FULLFSYNC on
 * macOS), and for comparison the same writes to a RandomAccessFile with getFD().sync()
 * (fsync, which on macOS does not empty the drive's cache). Prints the time per append.
 *
 * Usage: java -cp bergdb.jar:. ForceProbe DIR [COUNT]
 * DIR is emptied of its *.bergdb files and of probe.bin.
 */
public class ForceProbe {
    static final int[] SIZES = {100, 4096, 65536, 1 << 20, 4 << 20};

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        int count = args.length > 1 ? Integer.parseInt(args[1]) : 200;
        dir.mkdirs();
        clean(dir);
        System.out.println("kind      size_bytes  count   mean_ms    p50_ms    p90_ms    p99_ms    max_ms   MB_per_s");
        for (int size : SIZES) {
            int c = size >= (1 << 20) ? Math.max(20, count / 5) : count;
            byte[] b = new byte[size];
            for (int i = 0; i < size; i++) b[i] = (byte) (i * 31);
            FileStream s = new FileStream(dir);
            for (int i = 0; i < 5; i++) s.append(b, 0, size);              // Warm-up.
            long[] t = new long[c];
            for (int i = 0; i < c; i++) {
                long t0 = System.nanoTime();
                s.append(b, 0, size);
                t[i] = System.nanoTime() - t0;
            }
            s.close();
            print("fullfsync", size, t);
            clean(dir);

            File f = new File(dir, "probe.bin");
            RandomAccessFile r = new RandomAccessFile(f, "rw");
            for (int i = 0; i < 5; i++) { r.write(b, 0, size); r.getFD().sync(); }
            for (int i = 0; i < c; i++) {
                long t0 = System.nanoTime();
                r.write(b, 0, size);
                r.getFD().sync();
                t[i] = System.nanoTime() - t0;
            }
            r.close();
            print("fsync", size, t);
            clean(dir);
        }
    }

    static void print(String kind, int size, long[] t) {
        long[] s = t.clone();
        Arrays.sort(s);
        double sum = 0;
        for (long x : s) sum += x;
        double mean = sum / s.length;
        System.out.printf(Locale.ROOT, "%-9s %11d %6d %9.3f %9.3f %9.3f %9.3f %9.3f %10.1f%n", kind, size, s.length,
                mean / 1e6, p(s, 50) / 1e6, p(s, 90) / 1e6, p(s, 99) / 1e6, s[s.length - 1] / 1e6, size / mean * 1e3);
    }

    static long p(long[] s, double q) {
        return s[Math.min(s.length - 1, (int) Math.ceil(q / 100 * s.length) - 1)];
    }

    static void clean(File dir) {
        File[] fs = dir.listFiles();
        if (fs == null) return;
        for (File f : fs) if (f.getName().endsWith(".bergdb") || f.getName().equals("probe.bin")) f.delete();
    }
}
