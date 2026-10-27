import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.Arrays;
import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;
import bergdb.stream.SalsaStream;

/**
 * Probe for bergdb 005-46: what a reader of a FileStream waits for, on the code of today.
 * FileStream is used directly, with a FileStreamIo that times the physical operations and can
 * make the forces slower, as on a slow disk.
 *
 * Usage: java -cp bergdb.jar:. StreamWaitProbe MODE DIR ..., with MODE one of
 *   append DIR SECONDS CHUNK INTERVAL_MS [FORCE_DELAY_MS [EVERY [DIR_FORCE_DELAY_MS]]]
 *       After 3 MB of stream, a writer appends CHUNK bytes every INTERVAL_MS ms for SECONDS s;
 *       each append is written and forced (FileStream's hard sync). FORCE_DELAY_MS adds that
 *       much to every EVERY-th force (default every force), DIR_FORCE_DELAY_MS to each
 *       directory force, which a new file makes. Reader "last" reads 100 bytes at random
 *       positions in the last 64 KB written, that is in the file the writer appends to;
 *       reader "first" in the first file, which the writer never touches.
 *   salsa DIR SECONDS CHUNK INTERVAL_MS [FORCE_DELAY_MS [EVERY [DIR_FORCE_DELAY_MS]]]
 *       As append, through a SalsaStream over the FileStream, as an encrypted database has.
 *   cut DIR STREAM_MB [DIR_FORCE_DELAY_MS]
 *       Writes STREAM_MB MB in appends of 1 MB, then cuts every file but the last two
 *       (pretruncate) while reader "last" reads the last file and reader "kept" the file
 *       before it. DIR_FORCE_DELAY_MS adds that much to each directory force of the cut.
 *   interrupt DIR
 *       A thread whose interrupt flag is set makes a cut; then another thread reads and
 *       appends.
 * DIR must not exist or be empty; the probe deletes its files at the end.
 */
public class StreamWaitProbe {
    public static void main(String[] args) throws Exception {
        String mode = args[0];
        File dir = new File(args[1]);
        System.out.println("StreamWaitProbe " + String.join(" ", args) + "; Java "
                + System.getProperty("java.version") + ", " + System.getProperty("os.name"));
        try {
            if (mode.equals("append") || mode.equals("salsa")) {
                append(mode.equals("salsa"), dir, Integer.parseInt(args[2]), Integer.parseInt(args[3]),
                        Integer.parseInt(args[4]), args.length > 5 ? Long.parseLong(args[5]) : 0,
                        args.length > 6 ? Integer.parseInt(args[6]) : 1,
                        args.length > 7 ? Long.parseLong(args[7]) : 0);
            } else if (mode.equals("cut")) {
                cut(dir, Integer.parseInt(args[2]), args.length > 3 ? Long.parseLong(args[3]) : 0);
            } else if (mode.equals("interrupt")) {
                interrupt(dir);
            } else {
                throw new IllegalArgumentException("unknown mode " + mode);
            }
        } finally {
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) f.delete();
            dir.delete();
        }
    }

    static void append(boolean salsa, File dir, int seconds, int chunk, int intervalMs,
            long forceDelayMs, int every, long dirForceDelayMs) throws Exception {
        TimedIo io = new TimedIo();
        FileStream fs = new FileStream(dir, io);
        AppendOnlyStream s = salsa ? new SalsaStream(fs, new byte[8], new byte[32]) : fs;
        byte[] b = new byte[100 * 1000];
        new Random(1).nextBytes(b);
        for (int i = 0; i < 30; i++) s.append(b, 0, b.length);
        final AtomicLong published = new AtomicLong(s.getLength());
        io.forceDelayMs = forceDelayMs;
        io.every = every;
        io.dirForceDelayMs = dirForceDelayMs;
        io.reset();

        Reader last = new Reader("last", s) {
            long lo() { return Math.max(0, published.get() - 65536); }
            long hi() { return published.get(); }
        };
        Reader first = new Reader("first", s) {
            long lo() { return 0; }
            long hi() { return 100 * 1000; }
        };
        last.start();
        first.start();
        Stat appends = new Stat();
        byte[] data = new byte[chunk];
        Random r = new Random(2);
        long end = System.nanoTime() + seconds * 1000000000L;
        while (System.nanoTime() < end) {
            r.nextBytes(data);
            long t0 = System.nanoTime();
            s.append(data, 0, data.length);
            appends.add(System.nanoTime() - t0);
            published.set(s.getLength());
            if (intervalMs > 0) Thread.sleep(intervalMs);
        }
        last.finish();
        first.finish();
        System.out.println(appends.line("writer, append (write and force)"));
        System.out.println(io.write.line("  of it the write"));
        System.out.println(io.force.line("  of it the force"));
        System.out.println(io.dirForce.line("  of it the directory forces of " + io.opens
                + " new files"));
        System.out.println(last.stat.line("reader last, read of 100 bytes"));
        System.out.println(first.stat.line("reader first, read of 100 bytes"));
        s.close();
    }

    static void cut(File dir, int streamMb, long dirForceDelayMs) throws Exception {
        TimedIo io = new TimedIo();
        FileStream s = new FileStream(dir, io);
        byte[] b = new byte[1000 * 1000];
        new Random(1).nextBytes(b);
        for (int i = 0; i < streamMb; i++) s.append(b, 0, b.length);
        final long length = s.getLength();
        long[] starts = starts(dir);
        final long pos = starts[starts.length - 2];
        final long lastStart = starts[starts.length - 1];
        System.out.println("stream " + length + " bytes in " + starts.length
                + " files; the cut at " + pos + " deletes " + (starts.length - 2) + " of them");

        Reader last = new Reader("last", s) {
            long lo() { return lastStart; }
            long hi() { return length; }
        };
        Reader kept = new Reader("kept", s) {
            long lo() { return pos; }
            long hi() { return lastStart; }
        };
        last.start();
        kept.start();
        Thread.sleep(500);
        io.dirForceDelayMs = dirForceDelayMs;
        io.reset();
        long t0 = System.nanoTime();
        s.pretruncate(pos);
        long cutNs = System.nanoTime() - t0;
        Thread.sleep(500);
        last.finish();
        kept.finish();
        System.out.println(String.format("the cut (pretruncate) took %.3f ms; files left %d",
                cutNs / 1e6, starts(dir).length));
        System.out.println(io.delete.line("  its deletes"));
        System.out.println(io.dirForce.line("  its directory forces"));
        System.out.println(last.stat.line("reader last, read of 100 bytes"));
        System.out.println(kept.stat.line("reader kept, read of 100 bytes"));
        s.close();
    }

    static void interrupt(File dir) throws Exception {
        final FileStream s = new FileStream(dir, new FileStreamIo());
        byte[] b = new byte[1000 * 1000];
        s.append(b, 0, b.length);
        System.out.println("stream of " + s.getLength() + " bytes in " + starts(dir).length + " files");
        Thread t = new Thread() {
            public void run() {
                Thread.currentThread().interrupt();
                try {
                    s.pretruncate(400 * 1000);
                    System.out.println("the cut by an interrupted thread: OK");
                } catch (Throwable e) {
                    System.out.println("the cut by an interrupted thread threw " + e);
                }
            }
        };
        t.start();
        t.join();
        System.out.println("files left " + starts(dir).length + ", first position " + s.getFirstPos());
        try {
            s.read(900 * 1000, new byte[10], 0, 10);
            System.out.println("then a read by another thread: OK");
        } catch (Throwable e) {
            System.out.println("then a read by another thread threw " + e);
        }
        try {
            s.append(new byte[10], 0, 10);
            System.out.println("then an append: OK");
        } catch (Throwable e) {
            System.out.println("then an append threw " + e);
        }
        try {
            s.close();
        } catch (Throwable e) {
            System.out.println("close threw " + e);
        }
    }

    /** The first stream positions of the .bergdb files of dir, sorted. */
    static long[] starts(File dir) {
        File[] fs = dir.listFiles();
        long[] r = new long[fs.length];
        int n = 0;
        for (File f : fs) {
            if (f.getName().endsWith(".bergdb")) {
                r[n++] = Long.parseLong(f.getName().substring(0, 14)) * 100000;
            }
        }
        r = Arrays.copyOf(r, n);
        Arrays.sort(r);
        return r;
    }

    /** Reads 100 bytes at random positions in [lo(), hi() - 100) until finish(), each timed. */
    abstract static class Reader extends Thread {
        final AppendOnlyStream s;
        final Stat stat = new Stat();
        volatile boolean stop = false;
        volatile Throwable failure = null;

        Reader(String name, AppendOnlyStream s) {
            super(name);
            this.s = s;
        }

        abstract long lo();
        abstract long hi();

        public void run() {
            Random r = new Random(getName().hashCode());
            byte[] dest = new byte[100];
            try {
                while (!stop) {
                    long a = lo(), b = hi() - dest.length;
                    if (b <= a) continue;
                    long pos = a + (long) (r.nextDouble() * (b - a));
                    long t0 = System.nanoTime();
                    s.read(pos, dest, 0, dest.length);
                    stat.add(System.nanoTime() - t0);
                }
            } catch (Throwable e) {
                failure = e;
            }
        }

        void finish() throws Exception {
            stop = true;
            join();
            if (failure != null) throw new RuntimeException("reader " + getName() + " failed", failure);
        }
    }

    /** FileStreamIo that times its operations; a force can be made slower. */
    static final class TimedIo extends FileStreamIo {
        volatile long forceDelayMs = 0, dirForceDelayMs = 0;
        volatile int every = 1;
        int forces = 0, opens = 0;
        final Stat write = new Stat(), force = new Stat(), dirForce = new Stat(), delete = new Stat();

        void reset() {
            write.reset();
            force.reset();
            dirForce.reset();
            delete.reset();
            opens = 0;
        }

        protected RandomAccessFile open(File file) throws IOException {
            opens++;
            return super.open(file);
        }

        protected void write(File file, RandomAccessFile h, byte[] b, int off, int len) throws IOException {
            long t0 = System.nanoTime();
            super.write(file, h, b, off, len);
            write.add(System.nanoTime() - t0);
        }

        protected void forceFile(File file, RandomAccessFile h) throws IOException {
            long t0 = System.nanoTime();
            if (forceDelayMs > 0 && ++forces % every == 0) sleep(forceDelayMs);
            super.forceFile(file, h);
            force.add(System.nanoTime() - t0);
        }

        protected void forceDirectory(File d) throws IOException {
            long t0 = System.nanoTime();
            sleep(dirForceDelayMs);
            super.forceDirectory(d);
            dirForce.add(System.nanoTime() - t0);
        }

        protected boolean delete(File file) throws IOException {
            long t0 = System.nanoTime();
            boolean ok = super.delete(file);
            delete.add(System.nanoTime() - t0);
            return ok;
        }

        static void sleep(long ms) {
            if (ms <= 0) return;
            try {
                Thread.sleep(ms);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
    }

    /** Count, mean and longest of durations, and how many took more than 1, 10 and 100 ms. */
    static final class Stat {
        long count, total, max, over1, over5, over10, over100;

        synchronized void add(long ns) {
            count++;
            total += ns;
            max = Math.max(max, ns);
            if (ns > 1000000) over1++;
            if (ns > 5000000) over5++;
            if (ns > 10000000) over10++;
            if (ns > 100000000) over100++;
        }

        synchronized void reset() {
            count = total = max = over1 = over5 = over10 = over100 = 0;
        }

        synchronized String line(String name) {
            return String.format("%s: %d, mean %.3f ms, longest %.3f ms; over 1 ms %d, over 5 ms %d,"
                    + " over 10 ms %d, over 100 ms %d", name, count, count == 0 ? 0 : total / 1e6 / count, max / 1e6,
                    over1, over5, over10, over100);
        }
    }
}
