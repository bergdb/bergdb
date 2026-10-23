import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.Arrays;
import java.util.Locale;
import java.util.SplittableRandom;

import com.sun.nio.file.ExtendedOpenOption;

/**
 * Random reads that bypass the OS file cache, for bergdb item 004 (004-02, part C): what the
 * device gives, to read the from-the-device runs of ScaleBench against. Not BergDB's code.
 *
 * Makes FILE of GB gigabytes of random bytes (written with ExtendedOpenOption.DIRECT: O_DIRECT
 * on Linux, F_NOCACHE on macOS) unless it already has that size. Then, for blocks of 4 and 16
 * KiB and 1 and 8 threads (a queue depth of 1 and 8), each thread with its own channel:
 * random aligned reads with DIRECT for SECONDS each, the reads a second and their latency.
 * Last, for comparison, 4 KiB reads through the OS cache from a 64 MiB region read twice
 * before.
 *
 * Usage: java DiskBaseline FILE GB [SECONDS (default 15)]
 */
public final class DiskBaseline {
    static final int MAX_SAMPLES = 4000000;

    public static void main(String[] args) throws Exception {
        Path f = Paths.get(args[0]).toAbsolutePath();
        long size = (long) (Double.parseDouble(args[1]) * 1e9) >> 20 << 20;
        double sec = args.length > 2 ? Double.parseDouble(args[2]) : 15;
        int align = (int) Files.getFileStore(f.getParent()).getBlockSize();
        if (!Files.exists(f) || Files.size(f) != size) create(f, size, align);
        System.out.printf(Locale.ROOT, "DiskBaseline: %s, %.1f GB, block size %d, %s %s, %s%n", f, size / 1e9,
                align, System.getProperty("os.name"), System.getProperty("os.arch"), System.getProperty("java.version"));
        for (int bs : new int[] {4096, 16384}) {
            for (int qd : new int[] {1, 8}) {
                run(f, size, bs, qd, sec, align, true);
            }
        }
        cached(f, align, Math.min(sec, 5));
    }

    static void create(Path f, long size, int align) throws Exception {
        long s = System.nanoTime();
        ByteBuffer buf = ByteBuffer.allocateDirect((1 << 20) + align).alignedSlice(align);
        SplittableRandom rnd = new SplittableRandom(5);
        try (FileChannel ch = FileChannel.open(f, StandardOpenOption.CREATE, StandardOpenOption.WRITE,
                StandardOpenOption.TRUNCATE_EXISTING, ExtendedOpenOption.DIRECT)) {
            for (long pos = 0; pos < size; pos += 1 << 20) {
                buf.clear();
                while (buf.remaining() >= 8) buf.putLong(rnd.nextLong());
                buf.flip();
                buf.limit(1 << 20);
                while (buf.hasRemaining()) ch.write(buf, pos + buf.position());
            }
            ch.force(true);
        }
        System.out.printf(Locale.ROOT, "made %s: %.1f GB in %.1f s%n", f, size / 1e9, (System.nanoTime() - s) / 1e9);
    }

    static void run(final Path f, final long size, final int bs, int qd, final double sec, final int align,
            final boolean direct) throws Exception {
        final long[][] lat = new long[qd][];
        final int[] counts = new int[qd];
        final long[] reads = new long[qd];
        Thread[] ts = new Thread[qd];
        final long stop = System.nanoTime() + (long) (sec * 1e9);
        for (int t = 0; t < qd; t++) {
            final int tt = t;
            ts[t] = new Thread(new Runnable() {
                public void run() {
                    long[] l = new long[MAX_SAMPLES / 8];
                    int n = 0;
                    long r = 0;
                    SplittableRandom rnd = new SplittableRandom(100 + tt);
                    ByteBuffer buf = ByteBuffer.allocateDirect(bs + align).alignedSlice(align);
                    try (FileChannel ch = direct ? FileChannel.open(f, StandardOpenOption.READ, ExtendedOpenOption.DIRECT)
                            : FileChannel.open(f, StandardOpenOption.READ)) {
                        do {
                            long pos = rnd.nextLong(size / bs) * bs;
                            buf.clear();
                            buf.limit(bs);
                            long t0 = System.nanoTime();
                            while (buf.hasRemaining()) {
                                if (ch.read(buf, pos + buf.position()) < 0) throw new IllegalStateException("eof");
                            }
                            long dt = System.nanoTime() - t0;
                            if (n == l.length) l = Arrays.copyOf(l, Math.min(MAX_SAMPLES, l.length * 2));
                            if (n < l.length) l[n++] = dt;
                            r++;
                        } while (System.nanoTime() < stop);
                    } catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                    lat[tt] = l;
                    counts[tt] = n;
                    reads[tt] = r;
                }
            });
            ts[t].start();
        }
        long s = System.nanoTime();
        for (Thread t : ts) t.join();
        double el = (System.nanoTime() - s) / 1e9;
        int total = 0;
        long totalReads = 0;
        for (int t = 0; t < qd; t++) {
            total += counts[t];
            totalReads += reads[t];
        }
        long[] all = new long[total];
        int k = 0;
        for (int t = 0; t < qd; t++) {
            System.arraycopy(lat[t], 0, all, k, counts[t]);
            k += counts[t];
        }
        Arrays.sort(all);
        double mean = 0;
        for (long x : all) mean += x;
        mean /= Math.max(1, all.length);
        System.out.printf(Locale.ROOT, "%s %5d B, %d thread%s: %8d reads in %.1f s, %8.0f reads/s, %7.1f MB/s; latency us: mean %.1f, p50 %.1f, p90 %.1f, p99 %.1f, p99.9 %.1f, max %.1f%n",
                direct ? "direct" : "cached", bs, qd, qd == 1 ? " " : "s", totalReads, el, totalReads / el,
                totalReads * (double) bs / el / 1e6, mean / 1000, pct(all, 50), pct(all, 90), pct(all, 99),
                pct(all, 99.9), all.length == 0 ? 0 : all[all.length - 1] / 1000.0);
    }

    static double pct(long[] sorted, double p) {
        if (sorted.length == 0) return 0;
        int i = (int) Math.min(sorted.length - 1, Math.max(0, Math.ceil(p / 100 * sorted.length) - 1));
        return sorted[i] / 1000.0;
    }

    /** 4 KiB reads through the OS cache, within a 64 MiB region read twice before. */
    static void cached(Path f, int align, double sec) throws Exception {
        long region = 64L << 20;
        try (FileChannel ch = FileChannel.open(f, StandardOpenOption.READ)) {
            ByteBuffer b = ByteBuffer.allocate(1 << 20);
            for (int pass = 0; pass < 2; pass++) {
                for (long pos = 0; pos < region; pos += b.capacity()) {
                    b.clear();
                    ch.read(b, pos);
                }
            }
        }
        run(f, region, 4096, 1, sec, align, false);
    }
}
