package bergdb.core;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.lang.management.ManagementFactory;
import java.lang.management.MonitorInfo;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.Random;
import java.util.SplittableRandom;
import java.util.TreeMap;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.PointerFollower;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;

/**
 * BergDB's gets as the database grows, for bergdb item 004 (004-02, part D). A tool of the
 * item, not part of BergDB: it uses the Java code as it is (bergdb.jar) and changes nothing.
 *
 * Two modes, one JVM each:
 *
 *   load  makes a database on disk (FileStream) in sb.dir: sb.keys keys in random order,
 *         1,000 puts a transaction, 8-byte values (the key's number and version 0), node size
 *         30, infinite retention, startup distance sb.sd. With sb.budget 0 nothing is evicted
 *         (regime M) and the heap per key is measured after the load. Then the get phases
 *         run in the same JVM. A marker file in sb.dir keeps the keys, the key type and the
 *         last transaction time for mode get, and the keys loaded: all, or (written by hand
 *         for a load that was stopped) the first that many of the load order, the only keys
 *         mode get then asks for.
 *   get   opens the database in sb.dir with the capacity controller's budget sb.budget
 *         (bytes; 0: no eviction) and runs the get phases. With sb.warmos=1 it first reads
 *         the stream's files once, so that the OS file cache holds them (regime C).
 *
 * Key types (sb.keytype): int4, 4-byte big-endian ints (one key segment); key24,
 * "/scale/key/" and the key's number in 13 decimal digits, 24 bytes (four segments: keys
 * differ only in the last two, so no key gets segment nodes of its own); rnd24, 16 bytes of
 * a hash of the number and then the number, 24 bytes (keys differ in the first segment, so
 * every key gets three single-entry segment nodes, as rnd16 got two in 004-01).
 *
 * Get phases (sb.phases, comma-separated, run in the order given):
 *
 *   warm      one thread, uniform keys, windows of 5 s: until, with a budget, the cache has
 *             filled (a sweep or the low watermark reached) and the gets a second of two
 *             windows in a row differ by at most 10 percent; without one, two windows. At
 *             most sb.warmmax seconds. Every window is kept: a cold start's curve.
 *   uniform   one thread, uniform keys: 5 untimed windows of sb.window seconds (the
 *             throughput: median, min, max), then a timed pass of sb.timedgets gets or
 *             sb.timedsec seconds, two System.nanoTime() calls a get (the latency
 *             distribution and the ten slowest gets, later set beside the collector's pauses
 *             and the readers' waits after loads that overlapped them).
 *   hot       the same with 90 percent of the gets on the first 1 percent of the keys.
 *   threads   for each thread count in sb.threads: that many threads for sb.threadsec
 *             seconds, every get timed; then sb.sampled threads for sb.samplesec seconds
 *             while their states are sampled every 100 ms (what they wait for).
 *   variants  (no eviction only) IndexCensus's read-path variants (004-01): as it is,
 *             without the pointer lock and the stamp, with the stamp but no lock, without
 *             readSync; one thread, and the largest of sb.threads; 7 rounds over a pool of a
 *             million keys, the median of the last 5.
 *   census    (no eviction only) the index nodes of the latest tree and their memory, by a
 *             scan at the latest time.
 *
 * Recorded for every phase: gets, time, loads (NodeCollection.loads()), stream reads and
 * their bytes (a counting wrapper around the FileStream), the bytes the process read from
 * the device (Linux: /proc/self/io; macOS: sb.pidio, a tool that prints proc_pid_rusage's
 * ri_diskio_bytesread and ri_diskio_byteswritten), the device's reads (Linux: /proc/diskstats
 * for sb.disk), the capacity controller's sweeps, the readers' time in the controller after
 * their loads (Eviction.afterLoad, timed by a wrapper around the load listener: it includes
 * the sweeps a load starts and the waits for the write lock), collections (MXBeans; pauses
 * from the GC log sb.gclog), steal time (Linux), resident bytes and heap. Every value read is
 * checked. Writes sb.out (JSON) and a summary to stdout; SCALEBENCH OK at the end.
 *
 * Usage: java -Dsb.mode=load|get -Dsb.dir=D [-Dsb.NAME=VALUE ...]
 *            -cp bergdb.jar:CLASSES bergdb.core.ScaleBench
 */
public class ScaleBench {
    static final long SEC = bergdb.pub.util.Clock.UNITS_PER_SEC;
    static final String MARKER = "scalebench.properties";
    static final int VALSIZE = 8;
    static final byte[] PREFIX24 = "/scale/key/".getBytes(StandardCharsets.US_ASCII);

    static String prop(String name, String def) {
        return System.getProperty("sb." + name, def);
    }

    static int[] ints(String s) {
        String[] p = s.split(",");
        int[] r = new int[p.length];
        for (int i = 0; i < p.length; i++) r[i] = Integer.parseInt(p[i].trim());
        return r;
    }

    // ---- Parameters ----

    final String mode = prop("mode", "get");
    final File dir = new File(prop("dir", "build/scale"));
    int keys = Integer.parseInt(prop("keys", "1000000"));
    int loaded = keys;          // keys loaded, the first of the load order (marker; see openExisting)
    BitSet present;             // the loaded keys when not all are (a load that was stopped)
    String keytype = prop("keytype", "key24");
    final long budget = Long.parseLong(prop("budget", "0"));
    final int sd = Integer.parseInt(prop("sd", "10000000"));
    final String phaseList = prop("phases", "warm,uniform,hot,threads");
    final int[] threadCounts = ints(prop("threads", "1,2,4,8"));
    final int sampled = Integer.parseInt(prop("sampled", "4"));
    final double sampleSec = Double.parseDouble(prop("samplesec", "20"));
    final double windowSec = Double.parseDouble(prop("window", "3"));
    final int timedGets = Integer.parseInt(prop("timedgets", "1000000"));
    final double timedSec = Double.parseDouble(prop("timedsec", "60"));
    final double threadSec = Double.parseDouble(prop("threadsec", "30"));
    final double warmMaxSec = Double.parseDouble(prop("warmmax", "600"));
    final int loadLimit = Integer.parseInt(prop("loadlimit", "0"));     // load: stop after so many puts (trials)
    final String outFile = prop("out", "scalebench.json");
    final String gcLogFile = prop("gclog", "");
    final String pidio = prop("pidio", "");
    final String diskName = prop("disk", "sda");
    final boolean warmOs = prop("warmos", "0").equals("1");
    final String label = prop("label", "");

    // ---- State ----

    final CoreTestClock clock = new CoreTestClock();
    final long tstep = SEC / 10000;         // 100 us between transactions, as LargerThanMemory
    long time = SEC;
    Db db;
    CountingStream stream;
    final long nano0 = System.nanoTime();
    final double up0 = ManagementFactory.getRuntimeMXBean().getUptime() / 1000.0;
    final Map<String, Object> result = new LinkedHashMap<String, Object>();
    final List<Object> phaseResults = new ArrayList<Object>();
    final List<long[]> slowGets = new ArrayList<long[]>();      // {start nanos, nanos}, per timed pass
    final Map<String, List<long[]>> slowGetsByPhase = new LinkedHashMap<String, List<long[]>>();

    // The readers' time in the capacity controller after their loads (see wrapLoadListener).
    final LongAdder alCalls = new LongAdder(), alNanos = new LongAdder(), alSlow = new LongAdder();
    final AtomicLong alMax = new AtomicLong();
    final List<long[]> alEvents = Collections.synchronizedList(new ArrayList<long[]>());

    volatile boolean done = false;
    volatile long maxHeap = 0, maxResident = 0, maxRss = 0;

    /** Seconds of JVM uptime at System.nanoTime() value t, to compare with the GC log. */
    double uptime(long t) {
        return up0 + (t - nano0) / 1e9;
    }

    // ---- Keys and values ----

    int keyLength() {
        return keytype.equals("int4") ? 4 : 24;
    }

    static long mix(long z) {
        z = (z ^ (z >>> 30)) * 0xbf58476d1ce4e5b9L;
        z = (z ^ (z >>> 27)) * 0x94d049bb133111ebL;
        return z ^ (z >>> 31);
    }

    /** Writes key k into b (keyLength() bytes; the prefix of key24 is already there). */
    void fillKey(int k, byte[] b) {
        if (keytype.equals("int4")) {
            b[0] = (byte) (k >>> 24); b[1] = (byte) (k >>> 16); b[2] = (byte) (k >>> 8); b[3] = (byte) k;
        } else if (keytype.equals("key24")) {
            long v = k;
            for (int i = 23; i >= PREFIX24.length; i--) {
                b[i] = (byte) ('0' + v % 10);
                v /= 10;
            }
        } else if (keytype.equals("rnd24")) {
            putLong(b, 0, mix(k + 0x9E3779B97F4A7C15L));
            putLong(b, 8, mix(k ^ 0x5DEECE66DL));
            putLong(b, 16, k);
        } else {
            throw new IllegalArgumentException("keytype " + keytype);
        }
    }

    static void putLong(byte[] b, int off, long v) {
        for (int i = 7; i >= 0; i--) {
            b[off + i] = (byte) v;
            v >>>= 8;
        }
    }

    byte[] newKeyBuffer() {
        byte[] b = new byte[keyLength()];
        if (keytype.equals("key24")) System.arraycopy(PREFIX24, 0, b, 0, PREFIX24.length);
        return b;
    }

    byte[] keyBytes(int k) {
        byte[] b = newKeyBuffer();
        fillKey(k, b);
        return b;
    }

    /** Keys.toSegments, into a reused array. */
    static void toSegments(byte[] key, long[] segs) {
        int offset = 0;
        for (int i = 0; i < segs.length; i++) {
            int length = Math.min(Klong.MAX_SIZE, key.length - offset);
            segs[i] = Klong.createCompareValue(key, offset, length);
            offset += Klong.MAX_SIZE;
        }
    }

    /** A thread's key buffer and segments, reused for every get. */
    final class KeyGen {
        final byte[] key = newKeyBuffer();
        final long[] segs = new long[(key.length + Klong.MAX_SIZE) / Klong.MAX_SIZE];

        long[] segments(int k) {
            fillKey(k, key);
            toSegments(key, segs);
            return segs;
        }
    }

    static byte[] value(int k) {
        byte[] b = new byte[VALSIZE];
        b[0] = (byte) (k >>> 24); b[1] = (byte) (k >>> 16); b[2] = (byte) (k >>> 8); b[3] = (byte) k;
        return b;           // the version, 0, in bytes 4 to 7
    }

    static void check(int k, byte[] v) {
        if (v == null || v.length != VALSIZE || v[0] != (byte) (k >>> 24) || v[1] != (byte) (k >>> 16)
                || v[2] != (byte) (k >>> 8) || v[3] != (byte) k || v[4] != 0 || v[5] != 0 || v[6] != 0
                || v[7] != 0) {
            throw new AssertionError("wrong value for key " + k + ": " + (v == null ? "null" : Arrays.toString(v)));
        }
    }

    /** A key: uniform, or hot (90 percent on the first 1 percent); only loaded keys (present). */
    int pick(SplittableRandom rnd, boolean hot) {
        while (true) {
            int k = hot && rnd.nextInt(10) < 9 ? rnd.nextInt(Math.max(1, keys / 100)) : rnd.nextInt(keys);
            if (present == null || present.get(k)) return k;
        }
    }

    /** The load order: 0 to n - 1 shuffled with Random(1) (Fisher-Yates from the end). */
    static int[] shuffled(int n) {
        int[] order = new int[n];
        for (int i = 0; i < n; i++) order[i] = i;
        Random rnd = new Random(1);
        for (int i = n - 1; i > 0; i--) {
            int j = rnd.nextInt(i + 1);
            int x = order[i]; order[i] = order[j]; order[j] = x;
        }
        return order;
    }

    // ---- The stream and the database ----

    /** The FileStream, counting the reads that reach it and their bytes. */
    static final class CountingStream implements AppendOnlyStream {
        final FileStream s;
        final LongAdder reads = new LongAdder(), readBytes = new LongAdder();

        CountingStream(FileStream s) {
            this.s = s;
        }

        public long getLength() { return s.getLength(); }
        public long getFirstPos() { return s.getFirstPos(); }
        public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
            s.read(position, dest, destOffset, length);
            reads.increment();
            readBytes.add(length);
        }
        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            s.append(source, sourceOffset, length);
        }
        public void pretruncate(long position) throws IOException { s.pretruncate(position); }
        public void seekFirstPos(long position) { throw new UnsupportedOperationException(); }  // older jars (019-04)
        public void close() throws IOException { s.close(); }
    }

    Db open() throws IOException {
        stream = new CountingStream(new FileStream(dir));
        DbBuilder b = Db.builder().stream("main", stream).clock(clock).testId()
                .maxNodeSize30();
        if (sd > 0) b.startupDistance(sd);
        if (budget > 0) b.cacheSizeIndicator(budget).evictionSchedule(Eviction.Schedule.BUDGET, 1);
        else b.noEvict();
        Db d = b.build();
        long s = System.nanoTime();
        d.start();
        result.put("startupSec", (System.nanoTime() - s) / 1e9);
        return d;
    }

    /** The load listener of Db, timed: the readers' time in the capacity controller after loads. */
    void wrapLoadListener() {
        final Eviction ev = db.internal().eviction();
        final Db d = db;
        db.internal().nodeCollection().setLoadListener(new NodeCollection.LoadListener() {
            public void loaded() {      // before 005-52
                loaded(true);
            }
            public void loaded(OpData op) {     // since 005-52: a warmup's load is not paced, as Db's listener
                loaded(!op.getClass().getSimpleName().equals("WarmupGetData"));
            }
            void loaded(boolean paced) {
                long t0 = System.nanoTime();
                afterLoad(ev, d, paced);
                long dt = System.nanoTime() - t0;
                alCalls.increment();
                alNanos.add(dt);
                if (dt > alMax.get()) alMax.accumulateAndGet(dt, Math::max);
                if (dt > 10000000L) {
                    alSlow.increment();
                    if (alEvents.size() < 100000) alEvents.add(new long[] {t0, dt});
                }
            }
        });
    }

    /**
     * Eviction.afterLoad, (Db, boolean paced) since 005-52 and (Db) before it, found once so
     * that this compiles against both (bergdb 015-19).
     */
    static final java.lang.invoke.MethodHandle AFTER_LOAD = afterLoadHandle();

    static java.lang.invoke.MethodHandle afterLoadHandle() {
        java.lang.invoke.MethodHandles.Lookup l = java.lang.invoke.MethodHandles.lookup();
        try {
            try {
                return l.findVirtual(Eviction.class, "afterLoad",
                        java.lang.invoke.MethodType.methodType(void.class, Db.class, boolean.class));
            } catch (NoSuchMethodException e) {
                return java.lang.invoke.MethodHandles.dropArguments(l.findVirtual(Eviction.class, "afterLoad",
                        java.lang.invoke.MethodType.methodType(void.class, Db.class)), 2, boolean.class);
            }
        } catch (ReflectiveOperationException e) {
            throw new RuntimeException(e);
        }
    }

    static void afterLoad(Eviction ev, Db d, boolean paced) {
        try {
            AFTER_LOAD.invokeExact(ev, d, paced);
        } catch (RuntimeException | Error e) {
            throw e;
        } catch (Throwable t) {
            throw new RuntimeException(t);
        }
    }

    long streamFilesBytes() {
        long sum = 0;
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) if (!f.getName().equals(MARKER)) sum += f.length();
        return sum;
    }

    // ---- Counters ----

    static final Pattern SWEEPS = Pattern.compile("; (\\d+) sweeps \\(");
    static final Pattern SWEEP_TIME = Pattern.compile("sweep time (\\d+) ms in total, (\\d+) ms at most");

    /** Sweeps, their total time and the longest (ms), from Eviction.stats(). */
    long[] sweeps() {
        String s = db.internal().eviction().stats();
        long[] r = new long[3];
        Matcher m = SWEEPS.matcher(s);
        if (m.find()) r[0] = Long.parseLong(m.group(1));
        m = SWEEP_TIME.matcher(s);
        if (m.find()) {
            r[1] = Long.parseLong(m.group(1));
            r[2] = Long.parseLong(m.group(2));
        }
        return r;
    }

    /** The bytes this process read from the device so far, or -1. */
    long deviceReadBytes() {
        try {
            File io = new File("/proc/self/io");
            if (io.exists()) {
                for (String line : PerfUtil.readFile(io).split("\n")) {
                    if (line.startsWith("read_bytes:")) return Long.parseLong(line.substring(11).trim());
                }
                return -1;
            }
            if (pidio.isEmpty()) return -1;
            Process p = new ProcessBuilder(pidio, Long.toString(PerfUtil.pid())).redirectErrorStream(true).start();
            BufferedReader r = new BufferedReader(new InputStreamReader(p.getInputStream(), StandardCharsets.UTF_8));
            String line = r.readLine();
            p.waitFor();
            return line == null ? -1 : Long.parseLong(line.trim().split("\\s+")[0]);
        } catch (Exception e) {
            return -1;
        }
    }

    /** Linux: reads completed and sectors read of the device sb.disk (/proc/diskstats); else null. */
    long[] diskstats() {
        try {
            File f = new File("/proc/diskstats");
            if (!f.exists()) return null;
            for (String line : PerfUtil.readFile(f).split("\n")) {
                String[] x = line.trim().split("\\s+");
                if (x.length > 5 && x[2].equals(diskName)) return new long[] {Long.parseLong(x[3]), Long.parseLong(x[5])};
            }
        } catch (Exception e) {
            // None.
        }
        return null;
    }

    /** Linux: the total and the steal ticks of /proc/stat's cpu line; else null. */
    long[] cpuStat() {
        try {
            File f = new File("/proc/stat");
            if (!f.exists()) return null;
            String[] x = PerfUtil.readFile(f).split("\n")[0].trim().split("\\s+");
            long total = 0;
            for (int i = 1; i <= 8; i++) total += Long.parseLong(x[i]);
            return new long[] {total, Long.parseLong(x[8])};
        } catch (Exception e) {
            return null;
        }
    }

    long resident() {
        return db.internal().cache().residents().bytes();
    }

    /** The counters at a moment; delta() makes a phase's record from two. */
    final class Snap {
        final long nanos = System.nanoTime();
        final long loads = db.internal().nodeCollection().loads();
        final long sreads = stream.reads.sum(), sbytes = stream.readBytes.sum();
        final long dev = deviceReadBytes();
        final long[] disk = diskstats();
        final long[] cpu = cpuStat();
        final long[] sw = sweeps();
        final long alc = alCalls.sum(), aln = alNanos.sum(), als = alSlow.sum();
        final long[] gc = PerfUtil.gcTotals();
    }

    Map<String, Object> delta(Snap a, Snap b, long gets) {
        Map<String, Object> m = new LinkedHashMap<String, Object>();
        double sec = (b.nanos - a.nanos) / 1e9;
        m.put("seconds", sec);
        m.put("gets", gets);
        if (gets > 0) m.put("getsPerSec", gets / sec);
        double g = Math.max(1, gets);
        m.put("loads", b.loads - a.loads);
        m.put("loadsPerGet", (b.loads - a.loads) / g);
        m.put("streamReads", b.sreads - a.sreads);
        m.put("streamReadsPerGet", (b.sreads - a.sreads) / g);
        m.put("streamReadBytes", b.sbytes - a.sbytes);
        if (a.dev >= 0 && b.dev >= 0) {
            m.put("deviceReadBytes", b.dev - a.dev);
            m.put("deviceReadBytesPerGet", (b.dev - a.dev) / g);
        }
        if (a.disk != null && b.disk != null) {
            m.put("diskReads", b.disk[0] - a.disk[0]);
            m.put("diskReadsPerGet", (b.disk[0] - a.disk[0]) / g);
            m.put("diskReadBytes", (b.disk[1] - a.disk[1]) * 512);
        }
        if (a.cpu != null && b.cpu != null) {
            long t = b.cpu[0] - a.cpu[0];
            m.put("stealPercent", t > 0 ? 100.0 * (b.cpu[1] - a.cpu[1]) / t : 0.0);
        }
        m.put("sweeps", b.sw[0] - a.sw[0]);
        m.put("sweepMs", b.sw[1] - a.sw[1]);
        m.put("sweepMaxMsSoFar", b.sw[2]);
        m.put("afterLoadCalls", b.alc - a.alc);
        m.put("afterLoadMs", (b.aln - a.aln) / 1e6);
        m.put("afterLoadOver10ms", b.als - a.als);
        m.put("gcCount", b.gc[0] - a.gc[0]);
        m.put("gcMs", b.gc[1] - a.gc[1]);
        m.put("residentBytes", resident());
        m.put("heapUsedBytes", Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory());
        m.put("uptimeFrom", uptime(a.nanos));
        m.put("uptimeTo", uptime(b.nanos));
        return m;
    }

    static Map<String, Object> hist(PerfUtil.Hist h) {
        Map<String, Object> m = new LinkedHashMap<String, Object>();
        m.put("count", h.count());
        m.put("meanUs", h.mean() / 1000);
        m.put("p50Us", h.percentile(50) / 1000.0);
        m.put("p90Us", h.percentile(90) / 1000.0);
        m.put("p99Us", h.percentile(99) / 1000.0);
        m.put("p999Us", h.percentile(99.9) / 1000.0);
        m.put("maxUs", h.max() / 1000.0);
        return m;
    }

    static String histLine(PerfUtil.Hist h) {
        return String.format(Locale.ROOT, "mean %.2f, p50 %.2f, p90 %.2f, p99 %.2f, p99.9 %.2f, max %.1f us",
                h.mean() / 1000, h.percentile(50) / 1000.0, h.percentile(90) / 1000.0,
                h.percentile(99) / 1000.0, h.percentile(99.9) / 1000.0, h.max() / 1000.0);
    }

    static String counterLine(Map<String, Object> d) {
        StringBuilder s = new StringBuilder();
        s.append(String.format(Locale.ROOT, "loads/get %.3f, stream reads/get %.3f",
                (Double) d.get("loadsPerGet"), (Double) d.get("streamReadsPerGet")));
        if (d.containsKey("deviceReadBytesPerGet")) {
            s.append(String.format(Locale.ROOT, ", device bytes/get %.0f", (Double) d.get("deviceReadBytesPerGet")));
        }
        if (d.containsKey("diskReadsPerGet")) {
            s.append(String.format(Locale.ROOT, ", disk reads/get %.3f", (Double) d.get("diskReadsPerGet")));
        }
        s.append(String.format(Locale.ROOT, ", sweeps %d (%d ms), after-load waits over 10 ms %d, gc %d (%d ms), resident %d MB",
                (Long) d.get("sweeps"), (Long) d.get("sweepMs"), (Long) d.get("afterLoadOver10ms"),
                (Long) d.get("gcCount"), (Long) d.get("gcMs"), (Long) d.get("residentBytes") / 1000000));
        if (d.containsKey("stealPercent")) s.append(String.format(Locale.ROOT, ", steal %.2f%%", (Double) d.get("stealPercent")));
        return s.toString();
    }

    void say(String s) {
        System.out.printf(Locale.ROOT, "[%7.1f s] %s%n", (System.nanoTime() - nano0) / 1e9, s);
        System.out.flush();
    }

    /** Samples the heap, the resident bytes and the RSS every second (maxima). */
    Thread sampler() {
        Thread t = new Thread(new Runnable() {
            public void run() {
                Runtime rt = Runtime.getRuntime();
                while (!done) {
                    try {
                        Thread.sleep(1000);
                    } catch (InterruptedException e) {
                        return;
                    }
                    long heap = rt.totalMemory() - rt.freeMemory();
                    if (heap > maxHeap) maxHeap = heap;
                    Db d = db;
                    if (d != null) {
                        long r = d.internal().cache().residents().bytes();
                        if (r > maxResident) maxResident = r;
                    }
                    long rss = PerfUtil.rssBytes();
                    if (rss > maxRss) maxRss = rss;
                }
            }
        });
        t.setDaemon(true);
        t.start();
        return t;
    }

    // ---- Load ----

    void load() throws Exception {
        String[] existing = dir.list();
        if (existing != null && existing.length > 0) throw new IllegalStateException("not empty: " + dir);
        dir.mkdirs();
        clock.setTime(time);
        System.gc();
        System.gc();
        long heap0 = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
        db = open();
        wrapLoadListener();
        int[] order = shuffled(keys);
        final int n = loadLimit > 0 ? Math.min(loadLimit, keys) : keys;
        say("load: " + keys + " keys, " + keytype + ", budget " + budget + " bytes, dir " + dir);
        Snap a = new Snap();
        long last = a.nanos;
        for (int i = 0; i < n; i += 1000) {
            Trans.Builder tb = db.trans();
            int e = Math.min(n, i + 1000);
            for (int j = i; j < e; j++) tb.put(keyBytes(order[j]), value(order[j]));
            time += tstep;
            clock.setTime(time);
            db.execute(tb.build());
            long now = System.nanoTime();
            if (now - last > 30000000000L) {
                last = now;
                say(String.format(Locale.ROOT, "  %d puts, %.0f a second; resident %d MB, heap %d MB, stream %d MB",
                        e, e / ((now - a.nanos) / 1e9), resident() / 1000000,
                        (Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()) / 1000000,
                        streamFilesBytes() / 1000000));
            }
        }
        db.sync(SyncLevel.ORDINARY);
        Snap b = new Snap();
        order = null;
        Properties p = new Properties();
        p.setProperty("keys", Integer.toString(keys));
        p.setProperty("loaded", Integer.toString(n));
        p.setProperty("keytype", keytype);
        p.setProperty("valsize", Integer.toString(VALSIZE));
        p.setProperty("time", Long.toString(time));
        FileOutputStream fo = new FileOutputStream(new File(dir, MARKER));
        try {
            p.store(fo, "ScaleBench (bergdb item 004, 004-02)");
        } finally {
            fo.close();
        }
        Map<String, Object> m = delta(a, b, 0);
        double sec = (Double) m.get("seconds");
        m.put("keys", (long) keys);
        m.put("loaded", (long) n);
        m.put("putsPerSec", n / sec);
        long files = streamFilesBytes();
        m.put("streamBytes", db.internal().nodeStream().getNextPos());
        m.put("diskBytes", files);
        m.put("diskBytesPerKey", (double) files / n);
        if (budget == 0) {
            System.gc();
            System.gc();
            long used = Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
            m.put("heapBeforeLoadBytes", heap0);
            m.put("heapAfterFullGcBytes", used);
            m.put("heapBytesPerKey", (double) (used - heap0) / n);
        }
        m.put("eviction", db.internal().eviction().summary());
        result.put("load", m);
        say(String.format(Locale.ROOT, "load done: %.1f s, %.0f puts a second; on disk %d MB, %.1f bytes per key%s; %s",
                sec, n / sec, files / 1000000, (double) files / n,
                budget == 0 ? String.format(Locale.ROOT, "; heap after a full GC %d MB (%d MB before the load), %.1f bytes per key",
                        (Long) m.get("heapAfterFullGcBytes") / 1000000, heap0 / 1000000,
                        (Double) m.get("heapBytesPerKey")) : "",
                m.get("eviction")));
    }

    // ---- Get ----

    void openExisting() throws Exception {
        Properties p = new Properties();
        FileInputStream fi = new FileInputStream(new File(dir, MARKER));
        try {
            p.load(fi);
        } finally {
            fi.close();
        }
        keys = Integer.parseInt(p.getProperty("keys"));
        loaded = Integer.parseInt(p.getProperty("loaded", p.getProperty("keys")));
        if (loaded < keys) {
            int[] order = shuffled(keys);
            present = new BitSet(keys);
            for (int i = 0; i < loaded; i++) present.set(order[i]);
        }
        keytype = p.getProperty("keytype");
        time = Long.parseLong(p.getProperty("time")) + SEC;
        clock.setTime(time);
        if (warmOs) {
            long s = System.nanoTime(), bytes = 0;
            byte[] buf = new byte[1 << 20];
            File[] fs = dir.listFiles();
            Arrays.sort(fs);
            for (File f : fs) {
                InputStream in = new FileInputStream(f);
                try {
                    int n;
                    while ((n = in.read(buf)) > 0) bytes += n;
                } finally {
                    in.close();
                }
            }
            result.put("osWarmBytes", bytes);
            say(String.format(Locale.ROOT, "read the stream's files once: %d MB in %.1f s", bytes / 1000000,
                    (System.nanoTime() - s) / 1e9));
        }
        db = open();
        wrapLoadListener();
        say(String.format(Locale.ROOT, "opened %s: %d keys, %s, budget %d bytes; startup %.2f s, resident %d MB",
                dir, keys, keytype, budget, (Double) result.get("startupSec"), resident() / 1000000));
    }

    void warm() {
        KeyGen g = new KeyGen();
        GetData gd = db.newGetData();
        SplittableRandom rnd = new SplittableRandom(11);
        List<Object> curve = new ArrayList<Object>();
        Snap first = new Snap();
        long end = first.nanos + (long) (warmMaxSec * 1e9);
        double prev = -1;
        long total = 0;
        for (int w = 0; ; w++) {
            Snap a = new Snap();
            long n = 0, stop = a.nanos + 5000000000L;
            do {
                for (int i = 0; i < 64; i++) {
                    int k = pick(rnd, false);
                    check(k, db.getOne(Long.MAX_VALUE, g.segments(k), gd));
                }
                n += 64;
            } while (System.nanoTime() < stop);
            Snap b = new Snap();
            total += n;
            Map<String, Object> d = delta(a, b, n);
            double rate = (Double) d.get("getsPerSec");
            Map<String, Object> c = new LinkedHashMap<String, Object>();
            c.put("window", w);
            c.put("getsPerSec", rate);
            c.put("loadsPerGet", d.get("loadsPerGet"));
            c.put("residentBytes", d.get("residentBytes"));
            c.put("sweeps", d.get("sweeps"));
            if (d.containsKey("deviceReadBytesPerGet")) c.put("deviceReadBytesPerGet", d.get("deviceReadBytesPerGet"));
            curve.add(c);
            say(String.format(Locale.ROOT, "  warm %d: %.0f gets a second; %s", w, rate, counterLine(d)));
            boolean filled = budget == 0 || b.sw[0] > first.sw[0] || resident() >= 0.7 * budget;
            boolean steady = prev > 0 && Math.abs(rate - prev) <= 0.1 * Math.max(rate, prev);
            if (budget == 0 ? w >= 1 : (filled && steady)) break;
            if (b.nanos > end) {
                say("  warm: stopped at sb.warmmax");
                break;
            }
            prev = rate;
        }
        Map<String, Object> m = delta(first, new Snap(), total);
        m.put("phase", "warm");
        m.put("curve", curve);
        phaseResults.add(m);
    }

    /** One thread: untimed windows, then a timed pass. */
    void oneThread(String name, boolean hot) {
        KeyGen g = new KeyGen();
        GetData gd = db.newGetData();
        SplittableRandom rnd = new SplittableRandom(hot ? 23 : 17);
        double[] rates = new double[5];
        Snap a = new Snap();
        long total = 0;
        for (int w = 0; w < rates.length; w++) {
            long s = System.nanoTime(), n = 0, stop = s + (long) (windowSec * 1e9);
            do {
                for (int i = 0; i < 64; i++) {
                    int k = pick(rnd, hot);
                    check(k, db.getOne(Long.MAX_VALUE, g.segments(k), gd));
                }
                n += 64;
            } while (System.nanoTime() < stop);
            rates[w] = n / ((System.nanoTime() - s) / 1e9);
            total += n;
        }
        Snap b = new Snap();
        PerfUtil.Hist h = new PerfUtil.Hist();
        long[][] top = new long[10][2];         // {nanos, start}, the slowest gets
        long stop = b.nanos + (long) (timedSec * 1e9);
        int n = 0;
        while (n < timedGets) {
            int k = pick(rnd, hot);
            long[] segs = g.segments(k);
            long t0 = System.nanoTime();
            byte[] v = db.getOne(Long.MAX_VALUE, segs, gd);
            long dt = System.nanoTime() - t0;
            check(k, v);
            h.record(dt);
            if (dt > top[9][0]) {
                int i = 9;
                while (i > 0 && top[i - 1][0] < dt) {
                    top[i] = top[i - 1];
                    i--;
                }
                top[i] = new long[] {dt, t0};
            }
            n++;
            if ((n & 255) == 0 && System.nanoTime() > stop) break;
        }
        Snap c = new Snap();
        double[] sorted = rates.clone();
        Arrays.sort(sorted);
        Map<String, Object> m = new LinkedHashMap<String, Object>();
        m.put("phase", name);
        Map<String, Object> win = delta(a, b, total);
        win.put("windowsGetsPerSec", Arrays.asList(rates[0], rates[1], rates[2], rates[3], rates[4]));
        win.put("medianGetsPerSec", sorted[2]);
        m.put("untimed", win);
        Map<String, Object> timed = delta(b, c, n);
        timed.put("latency", hist(h));
        m.put("timed", timed);
        List<long[]> slow = new ArrayList<long[]>();
        for (long[] x : top) if (x[0] > 0) slow.add(x);
        slowGetsByPhase.put(name, slow);
        phaseResults.add(m);
        say(String.format(Locale.ROOT, "%s, 1 thread: %.0f gets a second (median of 5 windows, %.0f to %.0f); %s",
                name, sorted[2], sorted[0], sorted[4], counterLine(win)));
        say(String.format(Locale.ROOT, "%s, timed %d gets: %s; %s", name, n, histLine(h), counterLine(timed)));
    }

    /** Reader threads for the threads phases. */
    final class Reader extends Thread {
        final int t;
        final double sec;
        final CyclicBarrier barrier;
        final PerfUtil.Hist h = new PerfUtil.Hist();
        long gets;

        Reader(int t, double sec, CyclicBarrier barrier) {
            this.t = t;
            this.sec = sec;
            this.barrier = barrier;
            setName("reader-" + t);
            setDaemon(true);
        }

        public void run() {
            KeyGen g = new KeyGen();
            GetData gd = db.newGetData();
            SplittableRandom rnd = new SplittableRandom(1000 + 31 * t);
            try {
                barrier.await();
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
            long stop = System.nanoTime() + (long) (sec * 1e9);
            long n = 0;
            do {
                for (int i = 0; i < 64; i++) {
                    int k = pick(rnd, false);
                    long[] segs = g.segments(k);
                    long t0 = System.nanoTime();
                    byte[] v = db.getOne(Long.MAX_VALUE, segs, gd);
                    h.record(System.nanoTime() - t0);
                    check(k, v);
                }
                n += 64;
            } while (System.nanoTime() < stop);
            gets = n;
        }
    }

    void threads() throws Exception {
        for (int threads : threadCounts) {
            CyclicBarrier barrier = new CyclicBarrier(threads + 1);
            Reader[] rs = new Reader[threads];
            for (int t = 0; t < threads; t++) (rs[t] = new Reader(t, threadSec, barrier)).start();
            barrier.await();
            Snap a = new Snap();
            long gets = 0;
            PerfUtil.Hist h = new PerfUtil.Hist();
            for (Reader r : rs) {
                r.join();
                gets += r.gets;
                h.add(r.h);
            }
            Snap b = new Snap();
            Map<String, Object> m = delta(a, b, gets);
            m.put("phase", "threads-" + threads);
            m.put("threads", threads);
            m.put("latency", hist(h));
            phaseResults.add(m);
            say(String.format(Locale.ROOT, "threads %d: %.0f gets a second; %s; %s", threads,
                    (Double) m.get("getsPerSec"), histLine(h), counterLine(m)));
        }
        sampledThreads();
    }

    /** sb.sampled readers while their states are sampled every 100 ms. */
    void sampledThreads() throws Exception {
        int threads = sampled;
        CyclicBarrier barrier = new CyclicBarrier(threads + 1);
        Reader[] rs = new Reader[threads];
        long[] ids = new long[threads];
        for (int t = 0; t < threads; t++) {
            (rs[t] = new Reader(t, sampleSec, barrier)).start();
            ids[t] = rs[t].threadId();
        }
        barrier.await();
        Snap a = new Snap();
        ThreadMXBean mx = ManagementFactory.getThreadMXBean();
        TreeMap<String, Integer> counts = new TreeMap<String, Integer>();
        int samples = 0;
        long stop = a.nanos + (long) (sampleSec * 1e9) - 200000000L;
        while (System.nanoTime() < stop) {
            Thread.sleep(100);
            for (ThreadInfo ti : mx.getThreadInfo(ids, true, false)) {
                if (ti == null) continue;
                String c = classify(ti);
                Integer old = counts.get(c);
                counts.put(c, old == null ? 1 : old + 1);
                samples++;
            }
        }
        long gets = 0;
        for (Reader r : rs) {
            r.join();
            gets += r.gets;
        }
        Snap b = new Snap();
        Map<String, Object> m = delta(a, b, gets);
        m.put("phase", "sampled-" + threads);
        m.put("threads", threads);
        m.put("samples", samples);
        List<Map.Entry<String, Integer>> es = new ArrayList<Map.Entry<String, Integer>>(counts.entrySet());
        Collections.sort(es, (x, y) -> y.getValue() - x.getValue());
        Map<String, Object> states = new LinkedHashMap<String, Object>();
        StringBuilder s = new StringBuilder();
        for (Map.Entry<String, Integer> e : es) {
            double f = 100.0 * e.getValue() / Math.max(1, samples);
            states.put(e.getKey(), f);
            if (s.length() < 600) s.append(String.format(Locale.ROOT, "%n    %5.1f%% %s", f, e.getKey()));
        }
        m.put("statesPercent", states);
        phaseResults.add(m);
        say(String.format(Locale.ROOT, "sampled %d threads: %.0f gets a second, %d samples:%s", threads,
                (Double) m.get("getsPerSec"), samples, s));
    }

    /** A reader's state and where it is, for sampledThreads(). */
    static String classify(ThreadInfo ti) {
        StackTraceElement[] st = ti.getStackTrace();
        boolean reading = false;
        String where = "?";
        for (StackTraceElement e : st) {
            String c = e.getClassName();
            if (c.equals("bergdb.stream.FileStream") && e.getMethodName().equals("read")) reading = true;
            if (where.equals("?") && c.startsWith("bergdb.") && !c.startsWith("bergdb.core.ScaleBench")) {
                where = c.substring(c.lastIndexOf('.') + 1) + "." + e.getMethodName();
            }
        }
        boolean pointerLock = false;
        for (MonitorInfo mi : ti.getLockedMonitors()) {
            StackTraceElement f = mi.getLockedStackFrame();
            if (f != null && f.getClassName().equals("bergdb.core.NodeCollection")
                    && f.getMethodName().equals("followPointer")) {
                pointerLock = true;
            }
        }
        String lock = ti.getLockName() == null ? "" : " on " + ti.getLockName().replaceAll("@.*$", "");
        return ti.getThreadState() + (reading ? " reading the stream" : " in " + where) + lock
                + (pointerLock ? ", holding a pointer lock" : "");
    }

    /** A follower that takes a memory pointer without the lock and the stamp (IndexCensus, 004-01). */
    static final class NoLock implements PointerFollower {
        final PointerFollower real;

        NoLock(PointerFollower real) {
            this.real = real;
        }

        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node c = predecessor.getPointerNode(pointerIndex);
            if (c != null) return c;
            return real.followPointer(predecessor, pointerIndex, op);
        }
    }

    /** A follower that writes the stamp but takes no lock (IndexCensus, 004-01). */
    static final class StampNoLock implements PointerFollower {
        final PointerFollower real;

        StampNoLock(PointerFollower real) {
            this.real = real;
        }

        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node c = predecessor.getPointerNode(pointerIndex);
            if (c != null) {
                if (predecessor instanceof KeyNode) {
                    ((KeyNode) predecessor).setPointerAccessData(pointerIndex, op.accessData);
                }
                return c;
            }
            return real.followPointer(predecessor, pointerIndex, op);
        }
    }

    /** IndexCensus's read-path variants, as in 004-01 (no eviction only). */
    void variants() throws Exception {
        if (budget != 0) throw new IllegalStateException("variants need sb.budget=0");
        final int pool = 1000000;
        final long[][] segs = new long[pool][];
        final int[] ks = new int[pool];
        SplittableRandom rnd = new SplittableRandom(2);
        KeyGen g = new KeyGen();
        for (int i = 0; i < pool; i++) {
            ks[i] = pick(rnd, false);
            segs[i] = g.segments(ks[i]).clone();
        }
        String[] names = {"as it is", "no lock, no stamp", "stamp, no lock", "as it is, no readSync"};
        double[][] ns = new double[names.length][5];
        for (int r = 0; r < 7; r++) {
            for (int f = 0; f < names.length; f++) {
                GetData gd = db.newGetData();
                PointerFollower real = gd.pointerFollower;
                if (f == 1) gd.pointerFollower = new NoLock(real);
                if (f == 2) gd.pointerFollower = new StampNoLock(real);
                long s = System.nanoTime();
                for (int i = 0; i < pool; i++) {
                    byte[] v = f == 3 ? db.getOneInternal(Long.MAX_VALUE, segs[i], gd)
                            : db.getOne(Long.MAX_VALUE, segs[i], gd);
                    if (v[0] != (byte) (ks[i] >>> 24)) check(ks[i], v);
                }
                double t = (double) (System.nanoTime() - s) / pool;
                if (r >= 2) ns[f][r - 2] = t;
            }
        }
        Map<String, Object> m = new LinkedHashMap<String, Object>();
        m.put("phase", "variants");
        Map<String, Object> one = new LinkedHashMap<String, Object>();
        StringBuilder sb = new StringBuilder("variants, 1 thread, ns a get (median of 5 rounds of a million):");
        for (int f = 0; f < names.length; f++) {
            double[] x = ns[f].clone();
            Arrays.sort(x);
            one.put(names[f], x[2]);
            sb.append(String.format(Locale.ROOT, "%n    %-24s %8.1f (best %.1f)", names[f], x[2], x[0]));
        }
        m.put("oneThreadNsPerGet", one);
        say(sb.toString());
        final int threads = threadCounts[threadCounts.length - 1];
        if (threads > 1) {
            String[] tn = {"as it is", "no lock, no stamp", "no lock, no stamp, no readSync"};
            Map<String, Object> many = new LinkedHashMap<String, Object>();
            sb = new StringBuilder("variants, " + threads + " threads, million gets a second (median of 5 rounds):");
            for (int f = 0; f < tn.length; f++) {
                final int ff = f;
                double[] rates = new double[5];
                for (int r = 0; r < 7; r++) {
                    Thread[] ts = new Thread[threads];
                    final CyclicBarrier barrier = new CyclicBarrier(threads + 1);
                    for (int t = 0; t < threads; t++) {
                        final int tt = t;
                        ts[t] = new Thread(new Runnable() {
                            public void run() {
                                GetData gd = db.newGetData();
                                if (ff >= 1) gd.pointerFollower = new NoLock(gd.pointerFollower);
                                try {
                                    barrier.await();
                                } catch (Exception e) {
                                    throw new RuntimeException(e);
                                }
                                for (int i = 0; i < pool; i++) {
                                    int j = (i + tt * 7919) % pool;
                                    byte[] v = ff == 2 ? db.getOneInternal(Long.MAX_VALUE, segs[j], gd)
                                            : db.getOne(Long.MAX_VALUE, segs[j], gd);
                                    if (v[0] != (byte) (ks[j] >>> 24)) check(ks[j], v);
                                }
                            }
                        });
                        ts[t].start();
                    }
                    barrier.await();
                    long s = System.nanoTime();
                    for (Thread t : ts) t.join();
                    double rate = (double) pool * threads / ((System.nanoTime() - s) / 1e9);
                    if (r >= 2) rates[r - 2] = rate;
                }
                Arrays.sort(rates);
                many.put(tn[f], rates[2]);
                sb.append(String.format(Locale.ROOT, "%n    %-32s %6.2f (best %.2f)", tn[f], rates[2] / 1e6, rates[4] / 1e6));
            }
            m.put("threads", threads);
            m.put("threadsGetsPerSec", many);
            say(sb.toString());
        }
        phaseResults.add(m);
    }

    /** The index nodes of the latest tree and their memory, by a scan (no eviction only). */
    void census() {
        if (budget != 0) throw new IllegalStateException("census needs sb.budget=0");
        Snap a = new Snap();
        final HashSet<Long> current = new HashSet<Long>();
        final long[] bytes = new long[3];        // index bytes, values, value bytes
        GetMany g = db.newGetMany();
        final PointerFollower real = g.gd.pointerFollower;
        g.gd.pointerFollower = new PointerFollower() {
            public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
                Node n = real.followPointer(predecessor, pointerIndex, op);
                if (n.isIndexNode()) {
                    if (current.add(n.getId())) bytes[0] += n.getMemSize();
                } else {
                    bytes[1]++;
                    bytes[2] += n.getMemSize();
                }
                return n;
            }
        };
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                return CONTINUE;
            }
            public void eod() {}
        };
        db.getMany(g);
        Map<String, Object> m = delta(a, new Snap(), 0);
        m.put("phase", "census");
        m.put("latestIndexNodes", (long) current.size());
        m.put("latestIndexBytes", bytes[0]);
        m.put("latestIndexBytesPerKey", (double) bytes[0] / keys);
        m.put("keysPerIndexNode", (double) keys / current.size());
        m.put("values", bytes[1]);
        m.put("valueBytes", bytes[2]);
        phaseResults.add(m);
        say(String.format(Locale.ROOT, "census: the latest tree has %d index nodes (%.2f keys a node), %d MB, %.1f bytes a key; %d values, %d MB",
                current.size(), (double) keys / current.size(), bytes[0] / 1000000, (double) bytes[0] / keys,
                bytes[1], bytes[2] / 1000000));
    }

    /** The cost of the two clock reads around a timed get. */
    static double clockPairNs() {
        long sink = 0;
        long s = System.nanoTime();
        for (int i = 0; i < 2000000; i++) sink += System.nanoTime() - System.nanoTime();
        double ns = (System.nanoTime() - s) / 2e6;
        return sink == 42 ? ns + 1e-9 : ns;
    }

    // ---- The run ----

    void finish() throws IOException {
        PerfUtil.GcLog log = null;
        if (!gcLogFile.isEmpty()) log = PerfUtil.GcLog.read(new File(gcLogFile));
        for (Object o : phaseResults) {
            @SuppressWarnings("unchecked")
            Map<String, Object> m = (Map<String, Object>) o;
            List<Map<String, Object>> parts = new ArrayList<Map<String, Object>>();
            if (m.containsKey("untimed")) {
                parts.add(cast(m.get("untimed")));
                parts.add(cast(m.get("timed")));
            } else {
                parts.add(m);
            }
            for (Map<String, Object> p : parts) {
                if (log != null && p.containsKey("uptimeFrom")) {
                    p.put("gcPauses", PerfUtil.GcLog.summarize(log.pauses, (Double) p.get("uptimeFrom"),
                            (Double) p.get("uptimeTo")));
                }
            }
            String name = (String) m.get("phase");
            List<long[]> slow = slowGetsByPhase.get(name);
            if (slow != null) {
                List<Object> l = new ArrayList<Object>();
                for (long[] x : slow) {
                    double from = uptime(x[1]), to = uptime(x[1] + x[0]);
                    Map<String, Object> e = new LinkedHashMap<String, Object>();
                    e.put("us", x[0] / 1000.0);
                    e.put("uptime", from);
                    List<Object> over = new ArrayList<Object>();
                    if (log != null) {
                        for (PerfUtil.GcLog.Event ev : log.pauses) {
                            double end = ev.uptimeSec, start = end - ev.ms / 1000;
                            if (start < to + 0.001 && end > from - 0.001) over.add(ev.what + " " + ev.ms + " ms");
                        }
                    }
                    synchronized (alEvents) {
                        for (long[] al : alEvents) {
                            double s = uptime(al[0]), t = uptime(al[0] + al[1]);
                            if (s < to && t > from) over.add("after-load wait " + al[1] / 1000000 + " ms");
                        }
                    }
                    e.put("overlapping", over);
                    l.add(e);
                }
                m.put("slowestGets", l);
            }
        }
        result.put("phases", phaseResults);
        Map<String, Object> mx = new LinkedHashMap<String, Object>();
        mx.put("heapUsedBytes", maxHeap);
        mx.put("residentBytes", maxResident);
        mx.put("rssBytes", maxRss);
        result.put("maxima", mx);
        if (log != null) result.put("gcLog", log.summary(0, 1e12));
        result.put("eviction", db.internal().eviction().summary());
        Writer w = new OutputStreamWriter(new FileOutputStream(outFile), StandardCharsets.UTF_8);
        try {
            w.write(PerfUtil.Json.write(result));
            w.write("\n");
        } finally {
            w.close();
        }
    }

    @SuppressWarnings("unchecked")
    static Map<String, Object> cast(Object o) {
        return (Map<String, Object>) o;
    }

    void run() throws Exception {
        result.put("tool", "ScaleBench, bergdb item 004 (004-02)");
        result.put("label", label);
        result.put("mode", mode);
        Map<String, Object> props = new TreeMap<String, Object>();
        for (String n : System.getProperties().stringPropertyNames()) {
            if (n.startsWith("sb.")) props.put(n, System.getProperty(n));
        }
        result.put("properties", props);
        result.put("jvm", PerfUtil.jvmInfo());
        result.put("vmFlags", PerfUtil.vmFlags());
        result.put("physicalMemory", PerfUtil.physicalMemory());
        result.put("os", System.getProperty("os.name") + " " + System.getProperty("os.version") + " "
                + System.getProperty("os.arch"));
        result.put("cpus", Runtime.getRuntime().availableProcessors());
        double cp = clockPairNs();
        result.put("clockPairNs", cp);
        Thread sampler = sampler();
        if (mode.equals("load")) load();
        else if (mode.equals("get")) openExisting();
        else throw new IllegalArgumentException("sb.mode " + mode);
        result.put("keys", keys);
        result.put("loaded", loaded);
        result.put("keytype", keytype);
        result.put("budget", budget);
        say(String.format(Locale.ROOT, "two clock reads cost %.1f ns; heap %d MB; %d CPUs", cp,
                Runtime.getRuntime().maxMemory() / 1000000, Runtime.getRuntime().availableProcessors()));
        for (String p : phaseList.split(",")) {
            p = p.trim();
            if (p.isEmpty()) continue;
            if (p.equals("warm")) warm();
            else if (p.equals("uniform")) oneThread("uniform", false);
            else if (p.equals("hot")) oneThread("hot", true);
            else if (p.equals("threads")) threads();
            else if (p.equals("variants")) variants();
            else if (p.equals("census")) census();
            else throw new IllegalArgumentException("phase " + p);
        }
        done = true;
        sampler.join(2000);
        finish();
        say(String.format(Locale.ROOT, "at most: heap used %d MB, resident %d MB, RSS %d MB; %s",
                maxHeap / 1000000, maxResident / 1000000, maxRss / 1000000, db.internal().eviction().summary()));
        db.stop();
    }

    public static void main(String[] args) {
        try {
            new ScaleBench().run();
        } catch (Throwable e) {
            e.printStackTrace(System.out);
            System.out.println("SCALEBENCH FAILED: " + e);
            System.exit(1);
        }
        System.out.println("SCALEBENCH OK");
    }
}
