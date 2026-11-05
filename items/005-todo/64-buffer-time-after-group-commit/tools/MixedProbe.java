import java.io.File;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.util.Arrays;
import java.util.Locale;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.locks.LockSupport;

import bergdb.core.Db;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StorageManager;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;

/**
 * bergdb 005-64, question 3: mixed writers, some that sync after each transaction and some
 * that do not, at a given buffer time. Perf has no such scenario (a run's threads all sync,
 * commit=durable, or none do), so this probe. Written 2026-10-28 by Claude (Opus 5.5, Claude
 * Code).
 *
 * <p>A database on a FileStream in DIR, the main stream at BUFFERMS ms (the default buffer
 * size, 10 MB), as Perf builds it (noEvict, retainForever; the system clock). SYNC_THREADS
 * threads each execute a transaction of one put and then db.sync(ORDINARY), as Perf's
 * commit=durable; PLAIN_THREADS threads execute transactions of one put and never sync. A
 * rate is transactions a second per thread, paced on a schedule as Perf's rate=; 0 means as
 * fast as possible. Each thread puts to keys of its own (KEYS of them, in turn), values of
 * VALSIZE bytes. WARMUP_S seconds of writes, then SECONDS measured, then a final sync, close,
 * and a reopen that checks the last value of each key.
 *
 * <p>Prints one line, then MIXED OK:
 * MIXED buffer_ms= sync_threads= sync_rate= plain_threads= plain_rate= valsize= seconds=
 *   sync_commits_per_s= sync_p50_ms= sync_p99_ms= sync_max_ms= plain_puts_per_s=
 *   plain_mb_per_s= plain_append_p50_us= plain_append_p999_us= plain_append_max_ms=
 *   forces_per_s= bytes_per_force= force_ms_mean= force_busy= process_cpu_ms_per_s=
 *   consumer_cpu_ms_per_s=
 * The force counts are the appends that reach the FileStream (each one forced, F_FULLFSYNC on
 * macOS, fsync on Linux), as Perf counts them. The CPU is the process's and the consumer
 * thread's (BufferedStream-consumer) over the measured seconds.
 *
 * <p>Usage: java -cp bergdb.jar:CLASSES MixedProbe DIR BUFFERMS SYNC_THREADS SYNC_RATE
 *        PLAIN_THREADS PLAIN_RATE VALSIZE SECONDS WARMUP_S
 */
public class MixedProbe {
    static final int KEYS = 50000;

    /** The stream under the buffer: counts the appends (forces) and their bytes and time. */
    static final class CountingStream implements AppendOnlyStream {
        final FileStream s;
        final AtomicLong appends = new AtomicLong(), bytes = new AtomicLong(), nanos = new AtomicLong();

        CountingStream(FileStream s) { this.s = s; }

        public long getLength() { return s.getLength(); }
        public long getFirstPos() { return s.getFirstPos(); }
        public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
            s.read(position, dest, destOffset, length);
        }
        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            long t0 = System.nanoTime();
            s.append(source, sourceOffset, length);
            nanos.addAndGet(System.nanoTime() - t0);
            appends.incrementAndGet();
            bytes.addAndGet(length);
        }
        public void pretruncate(long position) throws IOException { s.pretruncate(position); }
        // Kept so that the tool compiles against older jars, whose AppendOnlyStream has it;
        // main's has not (bergdb 019-04). No layer of BergDB calls it.
        public void seekFirstPos(long position) { throw new UnsupportedOperationException(); }
        public void close() throws IOException { s.close(); }
    }

    /** Latencies in ns, growing. */
    static final class Lat {
        long[] v = new long[1 << 14];
        int n;

        void add(long x) {
            if (n == v.length) v = Arrays.copyOf(v, n * 2);
            v[n++] = x;
        }

        void addAll(Lat o) {
            for (int i = 0; i < o.n; i++) add(o.v[i]);
        }

        double pct(double p) {
            if (n == 0) return Double.NaN;
            long[] s = Arrays.copyOf(v, n);
            Arrays.sort(s);
            int i = (int) Math.ceil(p / 100.0 * n) - 1;
            return s[Math.max(0, Math.min(n - 1, i))];
        }
    }

    static volatile boolean measuring, stop;
    static Db db;

    static final class Writer extends Thread {
        final int id;
        final boolean sync;
        final int rate;
        final int valsize;
        final Lat lat = new Lat();
        long done;              // transactions in the measured window
        final int[] last = new int[KEYS];
        Throwable error;

        Writer(int id, boolean sync, int rate, int valsize) {
            super((sync ? "mixed-sync-" : "mixed-plain-") + id);
            this.id = id;
            this.sync = sync;
            this.rate = rate;
            this.valsize = valsize;
        }

        public void run() {
            try {
                long interval = rate > 0 ? 1000000000L / rate : 0;
                long start = System.nanoTime();
                for (long i = 0; !stop; i++) {
                    if (interval > 0) {
                        long intended = start + i * interval;
                        long now;
                        while ((now = System.nanoTime()) < intended && !stop) {
                            LockSupport.parkNanos(intended - now);
                        }
                        if (stop) break;
                    }
                    int k = (int) (i % KEYS);
                    int version = (int) (i / KEYS) + 1;
                    byte[] value = new byte[valsize];
                    putInt(value, 0, version);
                    putInt(value, 4, k);
                    boolean m = measuring;
                    long s = System.nanoTime();
                    db.execute(db.trans().put(key(id, k), value));
                    if (sync) db.sync(SyncLevel.ORDINARY);
                    long e = System.nanoTime();
                    last[k] = version;
                    if (m && measuring) {
                        lat.add(e - s);
                        done++;
                    }
                }
            } catch (Throwable e) {
                error = e;
            }
        }
    }

    static byte[] key(int thread, int k) {
        byte[] b = new byte[8];
        putInt(b, 0, thread);
        putInt(b, 4, k);
        return b;
    }

    static void putInt(byte[] b, int off, int x) {
        b[off] = (byte) (x >>> 24);
        b[off + 1] = (byte) (x >>> 16);
        b[off + 2] = (byte) (x >>> 8);
        b[off + 3] = (byte) x;
    }

    static int getInt(byte[] b, int off) {
        return ((b[off] & 0xff) << 24) | ((b[off + 1] & 0xff) << 16) | ((b[off + 2] & 0xff) << 8) | (b[off + 3] & 0xff);
    }

    static long consumerCpu(ThreadMXBean tmx) {
        long sum = 0;
        long[] ids = tmx.getAllThreadIds();
        ThreadInfo[] infos = tmx.getThreadInfo(ids, 0);
        for (int i = 0; i < ids.length; i++) {
            if (infos[i] != null && infos[i].getThreadName().startsWith("BufferedStream-consumer")) {
                long t = tmx.getThreadCpuTime(ids[i]);
                if (t > 0) sum += t;
            }
        }
        return sum;
    }

    static long processCpu() {
        return ((com.sun.management.OperatingSystemMXBean) ManagementFactory.getOperatingSystemMXBean())
                .getProcessCpuTime();
    }

    static Db open(File dir, int bufferMs, CountingStream[] cs) throws IOException {
        FileStream fs = new FileStream(dir);
        cs[0] = new CountingStream(fs);
        Db d = Db.builder().stream("main", cs[0], StorageManager.DEFAULT_BUFFER_SIZE, bufferMs)
                .noEvict().build();
        d.start();
        return d;
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 9) {
            System.err.println("Usage: MixedProbe DIR BUFFERMS SYNC_THREADS SYNC_RATE PLAIN_THREADS PLAIN_RATE "
                    + "VALSIZE SECONDS WARMUP_S");
            System.exit(2);
        }
        File dir = new File(args[0]);
        int bufferMs = Integer.parseInt(args[1]);
        int syncThreads = Integer.parseInt(args[2]);
        int syncRate = Integer.parseInt(args[3]);
        int plainThreads = Integer.parseInt(args[4]);
        int plainRate = Integer.parseInt(args[5]);
        int valsize = Math.max(8, Integer.parseInt(args[6]));
        double seconds = Double.parseDouble(args[7]);
        double warmup = Double.parseDouble(args[8]);

        if (dir.exists()) throw new IllegalStateException(dir + " exists");
        dir.mkdirs();
        CountingStream[] cs = new CountingStream[1];
        db = open(dir, bufferMs, cs);
        CountingStream counting = cs[0];
        ThreadMXBean tmx = ManagementFactory.getThreadMXBean();

        Writer[] ws = new Writer[syncThreads + plainThreads];
        for (int i = 0; i < ws.length; i++) {
            boolean s = i < syncThreads;
            ws[i] = new Writer(i, s, s ? syncRate : plainRate, valsize);
        }
        for (Writer w : ws) w.start();
        Thread.sleep((long) (warmup * 1000));

        long f0 = counting.appends.get(), b0 = counting.bytes.get(), n0 = counting.nanos.get();
        long p0 = processCpu(), c0 = consumerCpu(tmx);
        long t0 = System.nanoTime();
        measuring = true;
        Thread.sleep((long) (seconds * 1000));
        measuring = false;
        long t1 = System.nanoTime();
        long f1 = counting.appends.get(), b1 = counting.bytes.get(), n1 = counting.nanos.get();
        long p1 = processCpu(), c1 = consumerCpu(tmx);
        stop = true;
        for (Writer w : ws) w.join();
        for (Writer w : ws) {
            if (w.error != null) {
                w.error.printStackTrace();
                throw new RuntimeException("writer " + w.getName() + " failed: " + w.error);
            }
        }

        double sec = (t1 - t0) / 1e9;
        Lat sl = new Lat(), pl = new Lat();
        long sDone = 0, pDone = 0;
        for (Writer w : ws) {
            if (w.sync) { sl.addAll(w.lat); sDone += w.done; }
            else { pl.addAll(w.lat); pDone += w.done; }
        }
        long forces = f1 - f0;
        StringBuilder sb = new StringBuilder("MIXED");
        kv(sb, "buffer_ms", bufferMs);
        kv(sb, "sync_threads", syncThreads);
        kv(sb, "sync_rate", syncRate);
        kv(sb, "plain_threads", plainThreads);
        kv(sb, "plain_rate", plainRate);
        kv(sb, "valsize", valsize);
        kv(sb, "seconds", sec);
        if (syncThreads > 0) {
            kv(sb, "sync_commits_per_s", sDone / sec);
            kv(sb, "sync_p50_ms", sl.pct(50) / 1e6);
            kv(sb, "sync_p99_ms", sl.pct(99) / 1e6);
            kv(sb, "sync_max_ms", sl.pct(100) / 1e6);
        }
        if (plainThreads > 0) {
            kv(sb, "plain_puts_per_s", pDone / sec);
            kv(sb, "plain_mb_per_s", pDone * (8.0 + valsize) / sec / 1e6);
            kv(sb, "plain_append_p50_us", pl.pct(50) / 1e3);
            kv(sb, "plain_append_p999_us", pl.pct(99.9) / 1e3);
            kv(sb, "plain_append_max_ms", pl.pct(100) / 1e6);
        }
        kv(sb, "forces_per_s", forces / sec);
        kv(sb, "bytes_per_force", forces > 0 ? (b1 - b0) / (double) forces : 0.0);
        kv(sb, "force_ms_mean", forces > 0 ? (n1 - n0) / 1e6 / forces : 0.0);
        kv(sb, "force_busy", (n1 - n0) / 1e9 / sec);
        kv(sb, "process_cpu_ms_per_s", (p1 - p0) / 1e6 / sec);
        kv(sb, "consumer_cpu_ms_per_s", (c1 - c0) / 1e6 / sec);
        System.out.println(sb);

        // The end: a final sync, close, reopen, and every key's last value checked.
        db.sync(SyncLevel.ORDINARY);    // STRONG was ORDINARY without a replica (bergdb 005-11)
        db.close();
        db = open(dir, bufferMs, cs);
        GetData gd = db.newGetData();
        for (Writer w : ws) {
            for (int k = 0; k < KEYS; k++) {
                if (w.last[k] == 0) continue;
                byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(key(w.id, k)), gd);
                if (v == null || v.length != valsize || getInt(v, 0) != w.last[k] || getInt(v, 4) != k) {
                    throw new RuntimeException("after the reopen, key " + w.id + "/" + k + " has "
                            + (v == null ? "no value" : "version " + getInt(v, 0)) + ", expected version " + w.last[k]);
                }
            }
        }
        db.close();
        System.out.println("MIXED OK");
    }

    static void kv(StringBuilder sb, String k, double v) {
        sb.append(' ').append(k).append('=').append(String.format(Locale.ROOT, "%.4f", v));
    }

    static void kv(StringBuilder sb, String k, long v) {
        sb.append(' ').append(k).append('=').append(v);
    }
}
