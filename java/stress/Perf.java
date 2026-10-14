package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicIntegerArray;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.core.PerfUtil.Hist;
import bergdb.core.PerfUtil.Json;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.Clock;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.FileStream;

/**
 * The performance harness of Level 3 (docs/level3-plan.md, task 3), written 2026-10-14.
 * It is run by java/stress/performance.sh, which fixes the JVM, the GC logging and the
 * scenarios (java/stress/performance.suite); PerfTool compares the results.
 *
 * Three modes, each a separate JVM, each writing result.json and hist.json to perf.out:
 *
 *   write    load n keys; warm up with updates; then the measured update phase on a
 *            FileStream on disk, with the commit latency of append commits (execute()
 *            returned: buffered, group commit timing as configured) and of durable commits
 *            (execute() then sync(ORDINARY)), the bytes appended per user byte, store
 *            efficiency and the record attribution of Reclaim.Stats, the sampled storage
 *            and memory, and reclaim over physical cuts when the retention is finite.
 *            Then a restart in this JVM and a check of every key (visible, not measured).
 *            With keep=1 the data directory and the model are kept for mode restart.
 *   read     load, a history of updates, then warm resident reads: latest, historical and
 *            long-key gets, forward and backward scans, and gets from several threads.
 *            Everything is resident (no eviction in Level 3). Windows of untimed bulk
 *            reads give the throughput; a timed pass gives the latency distribution.
 *   restart  in a fresh JVM, on the kept directory of a write run: startup time and what
 *            it reran, the first reads (cold node cache; the OS file cache is as the
 *            runner says, perf.oscache), the same reads again, then mixed reads and
 *            writes, and a check of every key.
 *
 * The workload is a pure function of the parameters (perf.*) and perf.seed: key i of n is a
 * 4-byte big-endian int, the nlong keys after them are long keys ("/perf/long/" + 9 digits
 * + filler, longlen bytes); the value of key k at version v starts with k and v and ends with
 * a check byte; the load order is a seeded shuffle; updates draw keys from a seeded
 * Random. The clock is simulated (CoreTestClock): a transaction is tstep units after the
 * one before, and the retention is R = K * n / tsize transactions, so that the schedule
 * of reclaim does not depend on the speed of the machine. Time per transaction is what
 * is measured, in wall-clock nanoseconds.
 *
 * Every value read is checked; a wrong value fails the run at once (exit code 1). The
 * end check of all keys follows the measured phase and its time is reported separately.
 * In package bergdb.core to reach Db internals (Reclaim.Stats).
 */
public class Perf {
    /** Bumped when the generation of the trace changes (workload ids then differ). */
    static final int TRACE_VERSION = 1;
    static final long SEC = Clock.UNITS_PER_SEC;
    static final String MARKER = "perf-data.marker";

    // ---- Parameters ----

    /** Workload parameters (perf.*): recorded and hashed into the workload id. */
    static final Map<String, Object> W = new TreeMap<String, Object>();
    /** Run parameters: where and how, not what; not part of the workload id. */
    static final Map<String, Object> RUN = new LinkedHashMap<String, Object>();

    static int pi(String k, int d) { int v = Integer.getInteger("perf." + k, d); W.put(k, (long) v); return v; }
    static long pl(String k, long d) { long v = Long.getLong("perf." + k, d); W.put(k, v); return v; }
    static String ps(String k, String d) { String v = System.getProperty("perf." + k, d); W.put(k, v); return v; }
    static String rs(String k, String d) { String v = System.getProperty("perf." + k, d); RUN.put(k, v); return v; }

    final String mode;
    final long seed = pl("seed", 1);
    final int n = pi("n", 100000);
    final int nlong = pi("nlong", 0);
    final int longlen = pi("longlen", 120);
    final int valsize = Math.max(8, pi("valsize", 1000));
    final int batch = pi("batch", 100);
    final String work = ps("work", "uniform");               // uniform | hot | cold
    final int tsize = pi("tsize", 1);
    final int threads = pi("threads", 1);
    final int warmup = pi("warmup", -1);                     // -1: one update per key
    final int ops = pi("ops", 100000);                       // measured transactions
    final int maxOps = pi("maxops", 0);                      // cap when minCuts is not reached (0: 4 * ops)
    final String retain = ps("retain", "inf");               // inf, or K updates per key per retention
    final int minCuts = pi("mincuts", 0);                    // physical cuts wanted (finite retention)
    final String commit = ps("commit", "append");            // append | durable
    final int rate = pi("rate", 0);                          // paced: transactions per second; 0: as fast as possible
    final int sd = pi("sd", 0);                              // startup distance; 0: the default of Db
    final int sampleMs = pi("samplems", 1000);
    // read mode
    final int history = pi("history", -1);                   // update transactions before the reads (-1: n)
    final int windows = pi("windows", 5);
    final int getsPerWindow = pi("gets", 2000000);
    final int timedGets = pi("timedgets", 1000000);
    final int scansPerWindow = pi("scans", 20000);
    final int scanLen = pi("scanlen", 100);
    final int mtThreads = pi("mtthreads", 4);
    final int warmGets = pi("warmgets", 3000000);
    // restart mode
    final int firstGets = pi("firstgets", 300000);
    final int mixOps = pi("mixops", 50000);
    final int mixReaders = pi("mixreaders", 2);
    final boolean halt = pi("halt", 0) != 0;                 // write: end without close (a crash-like stop)

    final String scenario = rs("scenario", "adhoc");
    final String outDir = rs("out", "build/perf/out");
    final String dataDir = rs("dir", "build/perf/data");
    final boolean keep = "1".equals(rs("keep", "0"));
    final String osCache = rs("oscache", "warm");
    final String sourceLabel = rs("source", "unknown");

    final int total = n + nlong;
    final boolean finite = !retain.equals("inf");
    final double kRetain = finite ? Double.parseDouble(retain) : 1.0;
    final boolean durable = commit.equals("durable");
    final int kvSize = 4 + valsize;
    final long rTrans = Math.max(1, Math.round(kRetain * total / tsize));
    final long tstep = Math.max(SEC / 1000, (SEC + rTrans - 1) / rTrans);
    final long rUnits = rTrans * tstep;

    // ---- State ----

    final File dir = new File(dataDir);
    final CoreTestClock clock = new CoreTestClock();
    final Object timeLock = new Object();
    long time = SEC;
    int[] version;
    int[] midVersion;
    long midTime;
    Db db;
    FileStream stream;
    final Stats stats = new Stats();
    final Map<String, Object> metrics = new LinkedHashMap<String, Object>();
    final Map<String, Object> info = new LinkedHashMap<String, Object>();
    final Map<String, Hist> hists = new LinkedHashMap<String, Hist>();
    final Map<String, Object> raw = new LinkedHashMap<String, Object>();
    final Map<String, Object> phases = new LinkedHashMap<String, Object>();
    long gcStartCount, gcStartMs, upStartMs, upEndMs;
    Sampler sampler;
    volatile Writer[] writers;

    Perf(String mode) {
        this.mode = mode;
    }

    static final class PerfFailure extends RuntimeException {
        PerfFailure(String m) { super(m); }
    }

    static void fail(String m) {
        throw new PerfFailure(m);
    }

    /** Index nodes written per transaction, from the transaction listener. */
    static final class Stats implements Trans.Listener {
        long trans, kvBytes, indexNodes, maxIndexNodes;
        long firstPos = -1, lastPos;
        volatile int lastIndex;

        public void transExecuted(Db.ExecuteData x) {
            TransNodes tn = x.transNodes;
            int index = tn.topCount + tn.keyCount;
            trans++;
            kvBytes += tn.kvSize;
            indexNodes += index;
            if (index > maxIndexNodes) maxIndexNodes = index;
            if (firstPos < 0) firstPos = x.trans.tpos;
            lastPos = x.trans.lastPos;
            lastIndex = index;
        }

        public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}

        void reset() {
            trans = kvBytes = indexNodes = maxIndexNodes = 0;
            firstPos = -1;
        }
    }

    // ---- Keys and values ----

    boolean isLong(int k) {
        return k >= n;
    }

    byte[] keyBytes(int k) {
        if (k < n) return KeyFactory.binaryIntKey(k);
        byte[] b = new byte[longlen];
        byte[] prefix = new byte[] {'/', 'p', 'e', 'r', 'f', '/', 'l', 'o', 'n', 'g', '/'};
        System.arraycopy(prefix, 0, b, 0, prefix.length);
        int v = k;
        for (int i = 19; i >= 11; i--) {
            b[i] = (byte) ('0' + v % 10);
            v /= 10;
        }
        b[20] = '/';
        for (int i = 21; i < longlen; i++) b[i] = (byte) ('a' + (k * 7 + i) % 26);
        return b;
    }

    long[] segs(int k) {
        return Keys.toSegments(keyBytes(k));
    }

    /** The index of a key returned by the database, or -1 for a key that is not ours. */
    int decode(long[] seg) {
        byte[] b = Keys.toBytes(seg);
        if (b.length == 4) {
            return ((b[0] & 0xff) << 24) | ((b[1] & 0xff) << 16) | ((b[2] & 0xff) << 8) | (b[3] & 0xff);
        }
        if (b.length == longlen && b[0] == '/' && b[1] == 'p' && b[20] == '/') {
            int v = 0;
            for (int i = 11; i <= 19; i++) v = v * 10 + (b[i] - '0');
            return v;
        }
        return -1;
    }

    byte[] value(int k, int v) {
        byte[] b = new byte[valsize];
        wr(b, 0, k);
        wr(b, 4, v);
        for (int i = 8; i < valsize; i++) b[i] = (byte) (k + v + i);
        return b;
    }

    static void wr(byte[] b, int o, int v) {
        b[o] = (byte) (v >>> 24); b[o + 1] = (byte) (v >>> 16); b[o + 2] = (byte) (v >>> 8); b[o + 3] = (byte) v;
    }

    static int rd(byte[] b, int o) {
        return ((b[o] & 0xff) << 24) | ((b[o + 1] & 0xff) << 16) | ((b[o + 2] & 0xff) << 8) | (b[o + 3] & 0xff);
    }

    /** The cheap check done on every read: size, key, version and the last byte. */
    boolean ok(int k, int v, byte[] got) {
        return got != null && got.length == valsize && rd(got, 0) == k && rd(got, 4) == v
                && (valsize == 8 || got[valsize - 1] == (byte) (k + v + valsize - 1));
    }

    void check(int k, int v, byte[] got, String what) {
        byte[] want = value(k, v);
        if (!Arrays.equals(want, got)) {
            String g = got == null ? "null" : got.length + " bytes, key " + (got.length >= 8 ? rd(got, 0) : -1)
                    + " version " + (got.length >= 8 ? rd(got, 4) : -1);
            int at = -1;
            if (got != null) {
                for (int i = 0; i < Math.min(got.length, want.length); i++) if (got[i] != want[i]) { at = i; break; }
            }
            fail(what + ": wrong value for key " + k + ", expected version " + v + " (" + want.length + " bytes), got " + g
                    + (at >= 0 ? ", first difference at byte " + at : ""));
        }
    }

    // ---- The update trace ----

    int pickIndex(Random rnd, int m) {
        if (work.equals("hot")) {
            return rnd.nextInt(100) < 90 ? rnd.nextInt(Math.max(1, m / 100)) : rnd.nextInt(m);
        } else if (work.equals("cold")) {
            return rnd.nextInt(Math.max(1, m / 10));
        } else if (work.equals("uniform")) {
            return rnd.nextInt(m);
        }
        throw new PerfFailure("unknown work " + work);
    }

    /** The key for thread t of T: keys k with k % T == t, so that threads never share a key. */
    int pickKey(Random rnd, int t, int T) {
        int m = (total - t + T - 1) / T;
        return pickIndex(rnd, m) * T + t;
    }

    // ---- Database ----

    void prepareDir() throws IOException {
        if (dir.exists()) {
            File[] fs = dir.listFiles();
            if (fs != null && fs.length > 0 && !new File(dir, MARKER).exists()) {
                fail("refusing to empty " + dir + ": it has files and no " + MARKER
                        + " (use a disposable directory)");
            }
            if (fs != null) for (File f : fs) f.delete();
        }
        dir.mkdirs();
        PerfUtil.writeFile(new File(dir, MARKER), "disposable benchmark directory of Perf.java\n");
    }

    Db openDb() throws IOException {
        stream = new FileStream(dir);
        // (FileStream ignores the marker file: it reads only its own files.)
        DbBuilder b = Db.builder().stream("main", stream).clock(clock).noEvict().retainForever().testId();
        if (sd > 0) b.startupDistance(sd);
        return b.build();
    }

    /** One transaction at the next time. Returns the index nodes it wrote. */
    int execute(Trans.Builder b) {
        synchronized (timeLock) {
            time += tstep;
            clock.setTime(time);
            Trans t = b.build();
            t.listener = stats;
            db.execute(t);
            return stats.lastIndex;
        }
    }

    // ---- Phases ----

    void phase(String name, long startNanos) {
        double sec = 1e-9 * (System.nanoTime() - startNanos);
        phases.put(name, sec);
        System.out.printf(Locale.ROOT, "PHASE %s %.2f s%n", name, sec);
    }

    void load() {
        long t0 = System.nanoTime();
        int[] perm = new int[total];
        for (int i = 0; i < total; i++) perm[i] = i;
        Random rnd = new Random(seed);
        for (int i = total - 1; i > 0; i--) {
            int j = rnd.nextInt(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        version = new int[total];
        stats.reset();
        for (int i = 0; i < total; i += batch) {
            Trans.Builder b = db.trans();
            for (int j = i; j < Math.min(total, i + batch); j++) {
                int k = perm[j];
                version[k] = 1;
                b.put(keyBytes(k), value(k, 1));
            }
            execute(b);
        }
        db.sync(SyncLevel.ORDINARY);
        phase("load", t0);
        double sec = (double) phases.get("load");
        metrics.put("load.puts_per_s", total / sec);
        metrics.put("load.stream_mb", db.getStreamLength() / 1e6);
    }

    /** Update transactions on one thread, unmeasured: warm-up or history. */
    void updates(int count, long rseed, String name, boolean midSnapshot) {
        long t0 = System.nanoTime();
        Random rnd = new Random(rseed);
        int[] picks = new int[tsize];
        for (int i = 0; i < count; i++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < tsize; j++) {
                int k;
                boolean dup;
                do {
                    k = pickKey(rnd, 0, 1);
                    dup = false;
                    for (int q = 0; q < j; q++) if (picks[q] == k) dup = true;
                } while (dup);
                picks[j] = k;
                version[k]++;
                b.put(keyBytes(k), value(k, version[k]));
            }
            execute(b);
            seTxn(tsize);
            if (midSnapshot && i == count / 2) {
                midVersion = version.clone();
                midTime = time;
            }
        }
        db.sync(SyncLevel.ORDINARY);
        phase(name, t0);
    }

    // ---- The sampler ----

    /** Samples storage, memory and GC of the running process once per sampleMs. */
    final class Sampler extends Thread {
        final long t0 = System.nanoTime();
        final List<double[]> rows = new ArrayList<double[]>();
        volatile boolean stop;
        double heapAfterMax, heapUsedMax, rssMax, dirtyMax, diskMax, filesMax, keptMax, diskRatioSum, keptSum;
        long diskRatioN;
        long firstPosSeen = -1;
        int physicalCuts;
        volatile int physicalCutsNow;
        double maxDiskRatio;

        Sampler() {
            setDaemon(true);
            setName("perf-sampler");
        }

        /** Polls for physical cuts (files deleted) every 20 ms and takes a full sample every sampleMs. */
        public void run() {
            long last = System.nanoTime();
            int i = 1;
            while (!stop) {
                try {
                    Thread.sleep(20);
                } catch (InterruptedException e) {
                    return;
                }
                pollCuts();
                if (System.nanoTime() - last >= sampleMs * 1000000L) {
                    last = System.nanoTime();
                    sample(i++);
                    if (i % 10 == 0) progress();
                }
            }
        }

        /** A line now and then, so that a long run can be followed in its stdout file (approximate counts). */
        void progress() {
            long commits = 0;
            Writer[] ws = writers;
            if (ws != null) for (Writer w : ws) commits += w.done;
            double[] last = rows.get(rows.size() - 1);
            System.out.printf(Locale.ROOT, "PROGRESS %.0f s:%s stream %.0f MB, kept %.0f MB, on disk %.0f MB in %d files, %d physical cuts%n",
                    last[0] / 1000, ws == null ? "" : " " + commits + " commits,", last[5] / 1e6, (last[5] - last[6]) / 1e6, last[8] / 1e6, (int) last[9], physicalCuts);
        }

        /** A physical cut is a move of the first position of the FileStream: whole files were deleted. */
        void pollCuts() {
            long firstPos = stream.getFirstPos();
            if (firstPosSeen >= 0 && firstPos != firstPosSeen) physicalCuts++;
            firstPosSeen = firstPos;
            physicalCutsNow = physicalCuts;
        }

        void sample(int i) {
            double heapAfter = PerfUtil.heapAfterLastGcMB();
            double heapUsed = PerfUtil.heapUsedMB();
            long[] gc = PerfUtil.gcTotals();
            long len = db.getStreamLength();
            long firstAvail = db.getFirstAvailablePos();
            pollCuts();
            long firstPos = firstPosSeen;
            long disk = 0;
            File[] fs = dir.listFiles();
            int files = 0;
            if (fs != null) {
                for (File f : fs) {
                    if (f.getName().endsWith(".bergdb")) { disk += f.length(); files++; }
                }
            }
            double rss = i % 5 == 0 ? PerfUtil.rssBytes() / 1e6 : -1;
            double dirty = -1;
            if (i % 10 == 0) dirty = dirtyCount();
            heapAfterMax = Math.max(heapAfterMax, heapAfter);
            heapUsedMax = Math.max(heapUsedMax, heapUsed);
            rssMax = Math.max(rssMax, rss);
            dirtyMax = Math.max(dirtyMax, dirty);
            diskMax = Math.max(diskMax, disk);
            filesMax = Math.max(filesMax, files);
            long kept = len - firstAvail;
            keptMax = Math.max(keptMax, kept);
            if (finite && kept > 0 && firstAvail > 0) {
                double ratio = (double) disk / kept;
                diskRatioSum += ratio;
                maxDiskRatio = Math.max(maxDiskRatio, ratio);
                diskRatioN++;
                keptSum += kept;
            }
            rows.add(new double[] {1e-6 * (System.nanoTime() - t0), heapUsed, heapAfter, gc[0], gc[1],
                    len, firstAvail, firstPos, disk, files, rss, dirty});
        }

        void finish() {
            stop = true;
            interrupt();
            try { join(); } catch (InterruptedException e) { /* done */ }
            sample(0);                                    // A last sample, with rss and D.
        }
    }

    double dirtyCount() {
        final long[] c = new long[1];
        synchronized (db.internal().getWriteLock()) {
            TransSeq seq = db.internal().transSeq();
            seq.visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
                public void node(bergdb.dag.Node node, long tpos, long lastTpos) { c[0]++; }
            });
        }
        return c[0];
    }

    // ---- Mode write ----

    /** A slow commit: when, how long, what it wrote. */
    static final class Slow {
        long ns, atMs, uptimeMs, index, op, streamLen;
        String thread;
    }

    final class Writer extends Thread {
        final int t, T;
        final long count;
        final Hist append = new Hist(), dur = new Hist(), delay = new Hist();
        final Slow[] slow = new Slow[20];
        long[] second = new long[64];
        long puts;
        long done;
        Throwable error;
        final Random rnd;
        final long startNanos;

        Writer(int t, int T, long count, long startNanos) {
            this.t = t; this.T = T; this.count = count; this.startNanos = startNanos;
            rnd = new Random(seed * 31 + 1000 + t);
            setName("perf-writer-" + t);
        }

        public void run() {
            try {
                loop();
            } catch (Throwable e) {
                error = e;
            }
        }

        void loop() {
            long interval = rate > 0 ? (long) (1e9 * T / rate) : 0;
            int[] picks = new int[tsize];
            long cap = maxOpsEffective() / T;
            for (long i = 0; ; i++) {
                if (i >= count) {
                    if (T > 1 || minCuts == 0 || sampler.physicalCutsNow >= minCuts) break;
                    if (i >= cap) break;
                }
                Trans.Builder b = db.trans();
                for (int j = 0; j < tsize; j++) {
                    int k;
                    boolean dup;
                    do {
                        k = pickKey(rnd, t, T);
                        dup = false;
                        for (int q = 0; q < j; q++) if (picks[q] == k) dup = true;
                    } while (dup);
                    picks[j] = k;
                    version[k]++;
                    b.put(keyBytes(k), value(k, version[k]));
                }
                long intended = startNanos + i * interval;
                if (interval > 0) {
                    long now;
                    while ((now = System.nanoTime()) < intended) {
                        long wait = intended - now;
                        if (wait > 200000) java.util.concurrent.locks.LockSupport.parkNanos(wait - 100000);
                    }
                }
                long s = System.nanoTime();
                int idx = execute(b);
                long e1 = System.nanoTime();
                append.record(e1 - s);
                long end = e1;
                if (durable) {
                    db.sync(SyncLevel.ORDINARY);
                    end = System.nanoTime();
                    dur.record(end - s);
                }
                if (interval > 0) delay.record(end - intended);
                puts += tsize;
                done++;
                int sec = (int) ((end - startNanos) / 1000000000L);
                if (sec >= second.length) second = Arrays.copyOf(second, Math.max(sec + 1, second.length * 2));
                second[sec]++;
                long lat = end - s;
                noteSlow(lat, end, idx, i);
                if (T == 1) {
                    seTxn(tsize);
                    if (finite && i % 1000 == 0) seSample();
                }
            }
        }

        void noteSlow(long lat, long end, int idx, long op) {
            int min = 0;
            for (int q = 0; q < slow.length; q++) {
                if (slow[q] == null) { min = q; break; }
                if (slow[q].ns < slow[min].ns) min = q;
            }
            if (slow[min] != null && slow[min].ns >= lat) return;
            Slow s = new Slow();
            s.ns = lat;
            s.atMs = (end - startNanos) / 1000000;
            s.uptimeMs = ManagementFactory.getRuntimeMXBean().getUptime();
            s.index = idx;
            s.op = op;
            s.streamLen = stats.lastPos;
            s.thread = getName();
            slow[min] = s;
        }
    }

    // Store efficiency (SE, as in ReclaimCost.java): user bytes accessible from now - R, over the
    // stream kept after the cut. With one writer thread only. Every 16th transaction (from the
    // warm-up on) records its time and the puts so far; every 1000th, once a cut was made, samples.
    long[] seTimes = new long[1 << 16], sePuts = new long[1 << 16];
    int seCount;
    long sePutCount, seTxnCount;
    double seSum, seMin = Double.MAX_VALUE, seOffSum, seKeptSum;
    long seSamples;

    void seTxn(int puts) {
        sePutCount += puts;
        if (seTxnCount++ % 16 != 0) return;
        if (seCount == seTimes.length) {
            seTimes = Arrays.copyOf(seTimes, seCount * 2);
            sePuts = Arrays.copyOf(sePuts, seCount * 2);
        }
        seTimes[seCount] = time;
        sePuts[seCount] = sePutCount;
        seCount++;
    }

    /** User bytes accessible from time t: every key's version at t and every put after. */
    double seAccessible(long t) {
        int lo = -1;
        if (seCount > 0 && seTimes[0] <= t) {
            lo = 0;
            int hi = seCount - 1;
            while (lo < hi) {
                int mid = (lo + hi + 1) >>> 1;
                if (seTimes[mid] <= t) lo = mid; else hi = mid - 1;
            }
        }
        long after = sePutCount - (lo < 0 ? 0 : sePuts[lo]);
        return (double) (total + after) * kvSize;
    }

    void seSample() {
        long first = db.getFirstAvailablePos();
        if (first <= 0) return;                                      // Before the first cut.
        long kept = db.getStreamLength() - first;
        if (kept <= 0) return;
        double se = seAccessible(time - rUnits) / kept;
        double off = seAccessible(db.getFirstAvailableLookupTime()) / kept;
        seSum += se;
        seOffSum += off;
        seMin = Math.min(seMin, se);
        seKeptSum += kept;
        seSamples++;
    }

    long maxOpsEffective() {
        return maxOps > 0 ? maxOps : 4L * ops;
    }

    void runWrite() throws Exception {
        prepareDir();
        db = openDb();
        db.start();
        System.out.println("startupDistance " + db.getStartupDistance());
        info.put("startupDistanceBytes", (long) db.getStartupDistance());
        load();
        int warm = warmup >= 0 ? warmup : (int) Math.ceil((double) total / tsize);
        updates(warm, seed + 7, "warmup", false);
        if (threads == 1) {
            // The historical snapshot is the same as in mode restart's model.
            midVersion = null;
        }

        // The measured phase.
        Reclaim.Stats rstats = db.internal().reclaim().enableStats();
        rstats.countTouch = false;
        Reclaim.Stats.Record user0 = rstats.user.copy(), step0 = rstats.step.copy(), table0 = rstats.table.copy();
        if (finite) db.setRetainDuration(rUnits);
        long len0 = stats.lastPos;
        stats.reset();
        long[] gc0 = PerfUtil.gcTotals();
        upStartMs = ManagementFactory.getRuntimeMXBean().getUptime();
        gcStartCount = gc0[0];
        gcStartMs = gc0[1];
        sampler = new Sampler();
        sampler.sample(0);
        sampler.start();
        long startNanos = System.nanoTime();
        long startPuts = 0;
        Writer[] ws = new Writer[threads];
        long perThread = ops / threads;
        for (int t = 0; t < threads; t++) ws[t] = new Writer(t, threads, perThread, startNanos);
        writers = ws;
        long snapLen = db.getStreamLength();
        long snapFirstAvail = db.getFirstAvailablePos();
        for (Writer w : ws) w.start();
        for (Writer w : ws) w.join();
        long endNanos = System.nanoTime();
        upEndMs = ManagementFactory.getRuntimeMXBean().getUptime();
        long[] gc1 = PerfUtil.gcTotals();
        sampler.finish();
        for (Writer w : ws) if (w.error != null) throw new PerfFailure("writer failed: " + w.error);
        double sec = 1e-9 * (endNanos - startNanos);
        phases.put("measure", sec);

        // Results of the measured phase.
        Hist append = new Hist(), dur = new Hist(), delay = new Hist();
        long commits = 0, puts = 0;
        List<Slow> slows = new ArrayList<Slow>();
        long[] tps = new long[1];
        for (Writer w : ws) {
            append.add(w.append);
            dur.add(w.dur);
            delay.add(w.delay);
            commits += w.done;
            puts += w.puts;
            slows.addAll(Arrays.asList(w.slow));
            if (w.second.length > tps.length) tps = Arrays.copyOf(tps, w.second.length);
            for (int i = 0; i < w.second.length; i++) tps[i] += w.second[i];
        }
        long streamEnd = db.getStreamLength();
        long appended = streamEnd - snapLen;
        double userBytes = (double) puts * kvSize;
        metrics.put("commits", commits);
        metrics.put("puts", puts);
        metrics.put("measure.sec", sec);
        metrics.put("commits_per_s", commits / sec);
        metrics.put("puts_per_s", puts / sec);
        metrics.put("user_mb_per_s", userBytes / sec / 1e6);
        hist("commit.append", append);
        if (durable) hist("commit.durable", dur);
        if (rate > 0) hist("delay", delay);
        metrics.put("stream_appended_mb", appended / 1e6);
        metrics.put("bytes_appended_per_put", appended / (double) puts);
        metrics.put("bytes_appended_per_user_byte", appended / userBytes);
        metrics.put("we", userBytes / appended);
        metrics.put("index_nodes_per_commit", (double) stats.indexNodes / Math.max(1, stats.trans));
        metrics.put("max_index_nodes_in_commit", stats.maxIndexNodes);
        // 1-second windows: the slowest second shows a stall that a mean hides.
        int fullSeconds = (int) Math.max(0, Math.floor(sec) - 0);
        long minTps = Long.MAX_VALUE;
        for (int i = 0; i < Math.min(fullSeconds, tps.length); i++) minTps = Math.min(minTps, tps[i]);
        if (minTps != Long.MAX_VALUE && fullSeconds >= 2) metrics.put("commits_per_s.slowest_second", minTps);
        gcMetrics(gc0, gc1);

        // Reclaim: where the stream bytes went (Reclaim.Stats, ReclaimCost.java).
        Reclaim.Stats.Record u = rstats.user.minus(user0), sr = rstats.step.minus(step0), tr = rstats.table.minus(table0);
        metrics.put("rec.user_bytes_per_put", u.bytes / (double) puts);
        metrics.put("rec.user_value_bytes_per_put", u.valueBytes / (double) puts);
        metrics.put("rec.user_index_bytes_per_put", u.indexBytes / (double) puts);
        metrics.put("rec.step_bytes_per_put", sr.bytes / (double) puts);
        metrics.put("rec.table_bytes_per_put", tr.bytes / (double) puts);
        metrics.put("rec.other_bytes_per_put", (appended - u.bytes - sr.bytes - tr.bytes) / (double) puts);
        int iters = 0;
        long steps = 0;
        for (Reclaim.Stats.Iteration it : rstats.iterations) {
            if (it.pEnd >= 0) iters++;
            steps += it.steps;
        }
        metrics.put("reclaim.iterations_done", (long) iters);
        metrics.put("reclaim.steps", steps);
        metrics.put("reclaim.cuts_logical", (long) rstats.cuts.size());
        metrics.put("reclaim.cuts_physical", (long) sampler.physicalCuts);
        if (finite) {
            if (seSamples > 0) {
                metrics.put("se", seSum / seSamples);
                metrics.put("se_min", seMin);
                metrics.put("se_offered", seOffSum / seSamples);
                metrics.put("kept_mb_mean", seKeptSum / seSamples / 1e6);
            }
            metrics.put("kept_mb_max", sampler.keptMax / 1e6);
            if (sampler.diskRatioN > 0) {
                metrics.put("disk_over_kept_mean", sampler.diskRatioSum / sampler.diskRatioN);
                metrics.put("disk_over_kept_max", sampler.maxDiskRatio);
            }
            if (minCuts > 0 && sampler.physicalCuts < minCuts) {
                fail("only " + sampler.physicalCuts + " physical cuts in " + commits + " commits; wanted " + minCuts
                        + " (raise perf.maxops)");
            }
        }
        metrics.put("storage.files_max", (long) sampler.filesMax);
        metrics.put("storage.disk_mb_max", sampler.diskMax / 1e6);
        metrics.put("heap.after_gc_mb_max", sampler.heapAfterMax);
        metrics.put("heap.used_mb_max", sampler.heapUsedMax);
        if (sampler.rssMax > 0) metrics.put("rss_mb_max", sampler.rssMax);
        if (sampler.dirtyMax >= 0) metrics.put("dirty_nodes_max", sampler.dirtyMax);
        raw.put("tps_1s", tps);
        raw.put("samples", samplesJson(sampler.rows));
        raw.put("slowest", slowJson(slows));
        metrics.put("slowest_commit_ms", slowTop(slows) / 1e6);
        System.out.printf(Locale.ROOT, "WRITE %d commits (%d puts) in %.2f s: %.0f commits/s, bytes appended per user byte %.2f, "
                + "append p50 %.1f us p99.9 %.1f us max %.2f ms%n", commits, puts, sec, commits / sec,
                appended / userBytes, append.percentile(50) / 1e3, append.percentile(99.9) / 1e3, append.max() / 1e6);
        if (durable) {
            System.out.printf(Locale.ROOT, "  durable p50 %.1f ms p99 %.1f ms max %.1f ms%n",
                    dur.percentile(50) / 1e6, dur.percentile(99) / 1e6, dur.max() / 1e6);
        }

        // The end: sync, and either keep the directory for mode restart or restart here and check every key.
        long t0 = System.nanoTime();
        db.sync(SyncLevel.ORDINARY);
        metrics.put("final_sync_ms", 1e-6 * (System.nanoTime() - t0));
        metrics.put("durable_len_lag_bytes", (double) (db.getStreamLength() - db.getDurableLength()));
        if (finite) {
            long firstTime = db.getFirstAvailableLookupTime();
            metrics.put("first_available_lookup_age_over_retention", (double) (time - firstTime) / rUnits);
        }
        if (keep) {
            writeModel();
            if (halt) {
                writeResult(true);
                System.out.println("PERF OK (prepare, halt)");
                System.out.flush();
                Runtime.getRuntime().halt(0);
            }
            db.sync(SyncLevel.STRONG);
            db.close();
        } else {
            t0 = System.nanoTime();
            db.sync(SyncLevel.STRONG);
            db.close();
            restartAndVerify();
            phase("verify", t0);
            FileStreamCleanup.deleteDir(dir);
        }
    }

    void restartAndVerify() throws IOException {
        stream = null;
        long t0 = System.nanoTime();
        db = openDb();
        StartInfo si = db.start();
        double startSec = 1e-9 * (System.nanoTime() - t0);
        metrics.put("restart.startup_sec", startSec);
        metrics.put("restart.transactions_rerun", (long) si.transCount);
        metrics.put("restart.read_from_mb", si.startPos / 1e6);
        metrics.put("restart.section_mb", (db.getStreamLength() - si.startPos) / 1e6);
        info.put("restart.firstAvailableLookupTime", db.getFirstAvailableLookupTime());
        verifyAll("after restart");
        db.close();
    }

    void verifyAll(String what) {
        GetData gd = db.newGetData();
        long t0 = System.nanoTime();
        for (int k = 0; k < total; k++) {
            check(k, version[k], db.getOne(Long.MAX_VALUE, segs(k), gd), what);
        }
        System.out.printf(Locale.ROOT, "VERIFY %d keys %s: ok (%.2f s)%n", total, what, 1e-9 * (System.nanoTime() - t0));
        metrics.put("verify.keys", (long) total);
        metrics.put("verify.sec", 1e-9 * (System.nanoTime() - t0));
    }

    void gcMetrics(long[] gc0, long[] gc1) {
        metrics.put("gc.mxbean.count", gc1[0] - gc0[0]);
        metrics.put("gc.mxbean.time_ms", gc1[1] - gc0[1]);
        metrics.put("alloc.uptime_start_ms", upStartMs);
        metrics.put("alloc.uptime_end_ms", upEndMs);
    }

    void hist(String name, Hist h) {
        hists.put(name, h);
        metrics.put(name + ".count", h.count());
        metrics.put(name + ".mean_us", h.mean() / 1e3);
        metrics.put(name + ".p50_us", h.percentile(50) / 1e3);
        metrics.put(name + ".p95_us", h.percentile(95) / 1e3);
        metrics.put(name + ".p99_us", h.percentile(99) / 1e3);
        metrics.put(name + ".p999_us", h.percentile(99.9) / 1e3);
        metrics.put(name + ".max_us", h.max() / 1e3);
    }

    static double slowTop(List<Slow> slows) {
        long m = 0;
        for (Slow s : slows) if (s != null) m = Math.max(m, s.ns);
        return m;
    }

    static List<Object> slowJson(List<Slow> slows) {
        List<Slow> l = new ArrayList<Slow>();
        for (Slow s : slows) if (s != null) l.add(s);
        Collections.sort(l, new Comparator<Slow>() {
            public int compare(Slow a, Slow b) { return Long.compare(b.ns, a.ns); }
        });
        List<Object> out = new ArrayList<Object>();
        for (int i = 0; i < Math.min(20, l.size()); i++) {
            Slow s = l.get(i);
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            m.put("ms", s.ns / 1e6);
            m.put("atMs", s.atMs);
            m.put("uptimeMs", s.uptimeMs);
            m.put("indexNodes", s.index);
            m.put("op", s.op);
            m.put("streamPos", s.streamLen);
            m.put("thread", s.thread);
            out.add(m);
        }
        return out;
    }

    static List<Object> samplesJson(List<double[]> rows) {
        List<Object> out = new ArrayList<Object>();
        for (double[] r : rows) out.add(r);
        return out;
    }

    // ---- The model for mode restart ----

    void writeModel() throws IOException {
        Map<String, Object> m = new LinkedHashMap<String, Object>();
        m.put("time", time);
        m.put("total", (long) total);
        m.put("midTime", midTime);
        m.put("retentionUnits", finite ? rUnits : 0L);
        m.put("firstAvailableLookupTime", db.getFirstAvailableLookupTime());
        PerfUtil.writeFile(new File(dir, "model.json"), Json.write(m));
        java.io.DataOutputStream out = new java.io.DataOutputStream(new java.io.BufferedOutputStream(
                new java.io.FileOutputStream(new File(dir, "versions.bin"))));
        try {
            for (int v : version) out.writeInt(v);
            out.writeInt(midVersion == null ? 0 : 1);
            if (midVersion != null) for (int v : midVersion) out.writeInt(v);
        } finally {
            out.close();
        }
    }

    boolean readModel() throws IOException {
        Map<String, Object> m = Json.parseObject(PerfUtil.readFile(new File(dir, "model.json")));
        time = ((Number) m.get("time")).longValue();
        midTime = ((Number) m.get("midTime")).longValue();
        if (((Number) m.get("total")).intValue() != total) fail("model.json is for another number of keys");
        java.io.DataInputStream in = new java.io.DataInputStream(new java.io.BufferedInputStream(
                new java.io.FileInputStream(new File(dir, "versions.bin"))));
        try {
            version = new int[total];
            for (int i = 0; i < total; i++) version[i] = in.readInt();
            if (in.readInt() == 1) {
                midVersion = new int[total];
                for (int i = 0; i < total; i++) midVersion[i] = in.readInt();
            }
        } finally {
            in.close();
        }
        long r = ((Number) m.get("retentionUnits")).longValue();
        return r > 0;
    }

    // ---- Reads ----

    /** Random keys, their segments, for a fixed trace of reads. */
    final class Pool {
        final int[] keys;
        final long[][] segs;

        Pool(int size, long rseed, int lo, int hi) {
            Random r = new Random(rseed);
            keys = new int[size];
            segs = new long[size][];
            for (int i = 0; i < size; i++) {
                keys[i] = lo + r.nextInt(hi - lo);
                segs[i] = Perf.this.segs(keys[i]);
            }
        }
    }

    /** Gets in untimed windows and a timed pass; returns the mean throughput. */
    void getReads(String name, long lookupTime, int[] versions, Pool pool, int windowCount) {
        GetData gd = db.newGetData();
        double[] rates = new double[windowCount];
        for (int w = -1; w < windowCount; w++) {            // Window -1 warms this kind of read and is not counted.
            long t0 = System.nanoTime();
            for (int i = 0; i < getsPerWindow; i++) {
                int idx = i % pool.keys.length;
                int k = pool.keys[idx];
                byte[] got = db.getOne(lookupTime, pool.segs[idx], gd);
                if (!ok(k, versions[k], got)) check(k, versions[k], got, name);
            }
            if (w >= 0) rates[w] = getsPerWindow / (1e-9 * (System.nanoTime() - t0));
        }
        rateMetrics(name, rates);
        Hist h = new Hist();
        for (int i = 0; i < timedGets; i++) {
            int idx = (i * 7 + 3) % pool.keys.length;
            int k = pool.keys[idx];
            long s = System.nanoTime();
            byte[] got = db.getOne(lookupTime, pool.segs[idx], gd);
            long e = System.nanoTime();
            h.record(e - s);
            if (!ok(k, versions[k], got)) check(k, versions[k], got, name);
        }
        hist(name + ".get", h);
        System.out.printf(Locale.ROOT, "READ %s: %.0f gets/s (median of %d windows, %.0f..%.0f), p50 %.0f ns, p99 %.0f ns, p99.9 %.0f ns%n",
                name, metrics.get(name + ".ops_per_s"), rates.length, min(rates), max(rates), h.percentile(50) * 1.0, h.percentile(99) * 1.0, h.percentile(99.9) * 1.0);
    }

    /** The throughput of a kind of read is the median of its windows (one disturbed window does not count). */
    void rateMetrics(String name, double[] rates) {
        double[] sorted = rates.clone();
        Arrays.sort(sorted);
        double median = sorted.length % 2 == 1 ? sorted[sorted.length / 2] : (sorted[sorted.length / 2 - 1] + sorted[sorted.length / 2]) / 2;
        metrics.put(name + ".ops_per_s", median);
        metrics.put(name + ".ops_per_s_min", min(rates));
        metrics.put(name + ".ops_per_s_max", max(rates));
        metrics.put(name + ".window_cv", rates.length < 2 ? 0.0 : stdev(rates) / mean(rates));
    }

    static double mean(double[] a) { double s = 0; for (double x : a) s += x; return s / a.length; }
    static double min(double[] a) { double s = Double.MAX_VALUE; for (double x : a) s = Math.min(s, x); return s; }
    static double max(double[] a) { double s = -Double.MAX_VALUE; for (double x : a) s = Math.max(s, x); return s; }
    static double stdev(double[] a) { double m = mean(a), s = 0; for (double x : a) s += (x - m) * (x - m); return Math.sqrt(s / (a.length - 1)); }

    /**
     * Scans of scanLen KVs from random starts inside one region (ints or long keys), so that no internal
     * key is met. Forward from s: s, s+1, ...; backward: s, s-1, ... The call is timed; the check is not.
     */
    void scanReads(String name, boolean forward, int[] versions, long lookupTime, int count, boolean verify) {
        Random r = new Random(seed * 77 + (forward ? 1 : 2));
        Hist h = new Hist();
        long kvs = 0;
        double scanNanos = 0;
        int[] starts = new int[count];
        for (int i = 0; i < count; i++) {
            boolean useLong = nlong > scanLen + 1 && r.nextInt(10) == 0;
            int lo = useLong ? n : 0, hi = useLong ? total : n;
            int s = lo + r.nextInt(hi - lo - scanLen);
            starts[i] = forward ? s : s + scanLen - 1;
        }
        for (int i = 0; i < count; i++) {
            int s = starts[i];
            GetMany g = db.newGetMany();
            g.actualLookupTime = -1;
            g.lookupTime = lookupTime;
            g.startKey = segs(s);
            g.inclusive = true;
            g.forward = forward;
            final int[] added = new int[1];
            final int limit = scanLen;
            g.stopCondition = new GetMany.StopCondition() {
                public int handleKvt(Kvt kvt) {
                    return ++added[0] >= limit ? ADD_AND_STOP : ADD;
                }
                public void eod() {}
            };
            long t0 = System.nanoTime();
            db.getMany(g);
            long e = System.nanoTime();
            h.record(e - t0);
            scanNanos += e - t0;
            kvs += g.result.size();
            if (verify || i < 50) verifyScan(name, g, s, forward, versions);
            else if (g.result.size() != scanLen) fail(name + ": " + g.result.size() + " KVs, expected " + scanLen);
        }
        hist(name, h);
        metrics.put(name + ".kvs_per_s", kvs / (scanNanos * 1e-9));
        metrics.put(name + ".scans_per_s", count / (scanNanos * 1e-9));
        System.out.printf(Locale.ROOT, "SCAN %s: %.0f KVs/s, p50 %.1f us, p99 %.1f us%n", name, kvs / (scanNanos * 1e-9),
                h.percentile(50) / 1e3, h.percentile(99) / 1e3);
    }

    void verifyScan(String name, GetMany g, int s, boolean forward, int[] versions) {
        if (g.result.size() != scanLen) fail(name + ": " + g.result.size() + " KVs from key " + s + ", expected " + scanLen);
        int expect = s;
        for (Kvt kvt : g.result) {
            int k = decode(kvt.key);
            if (k != expect) fail(name + ": key " + k + " where " + expect + " was expected (scan from " + s + ")");
            if (!ok(k, versions[k], kvt.value)) check(k, versions[k], kvt.value, name);
            expect += forward ? 1 : -1;
        }
    }

    /** Several threads getting the latest values; the total throughput. */
    void mtReads(String name, Pool pool, int windowCount) throws InterruptedException {
        double[] rates = new double[windowCount];
        for (int w = -1; w < windowCount; w++) {            // Window -1 is a warm-up.
            final AtomicReference<Throwable> err = new AtomicReference<Throwable>();
            Thread[] ts = new Thread[mtThreads];
            final int per = getsPerWindow;
            final CountDownLatchLite go = new CountDownLatchLite(mtThreads + 1);
            for (int t = 0; t < mtThreads; t++) {
                final int tt = t;
                ts[t] = new Thread(new Runnable() {
                    public void run() {
                        try {
                            GetData gd = db.newGetData();
                            go.countDownAndWait();
                            for (int i = 0; i < per; i++) {
                                int idx = (int) (((long) i * 31 + tt * 1000003L) % pool.keys.length);
                                int k = pool.keys[idx];
                                byte[] got = db.getOne(Long.MAX_VALUE, pool.segs[idx], gd);
                                if (!ok(k, version[k], got)) check(k, version[k], got, name);
                            }
                        } catch (Throwable e) {
                            err.set(e);
                        }
                    }
                });
                ts[t].start();
            }
            go.countDownAndWait();
            long t0 = System.nanoTime();
            for (Thread t : ts) t.join();
            double rate = (double) per * mtThreads / (1e-9 * (System.nanoTime() - t0));
            if (err.get() != null) throw new PerfFailure(name + ": " + err.get());
            if (w >= 0) rates[w] = rate;
        }
        rateMetrics(name, rates);
        System.out.printf(Locale.ROOT, "READ %s (%d threads): %.0f gets/s (median of %d windows)%n", name, mtThreads,
                metrics.get(name + ".ops_per_s"), rates.length);
    }

    static final class CountDownLatchLite {
        private int count;
        CountDownLatchLite(int n) { count = n; }
        synchronized void countDownAndWait() throws InterruptedException {
            count--;
            if (count <= 0) { notifyAll(); return; }
            while (count > 0) wait();
        }
    }

    void runRead() throws Exception {
        prepareDir();
        db = openDb();
        db.start();
        load();
        int hist = history >= 0 ? history : n;
        updates(hist, seed + 11, "history", true);
        long len = db.getStreamLength();
        metrics.put("history.stream_mb", len / 1e6);
        info.put("heapAfterBuildMB", heapMB());

        long t0 = System.nanoTime();
        Pool latest = new Pool(1 << 20, seed + 21, 0, total);
        Pool hpool = new Pool(1 << 20, seed + 22, 0, total);
        Pool lpool = nlong > 0 ? new Pool(1 << 18, seed + 23, n, total) : null;
        // Warm-up: the same kinds of reads, unmeasured.
        {
            GetData gd = db.newGetData();
            for (int i = 0; i < warmGets; i++) {
                int idx = i % latest.keys.length;
                int k = latest.keys[idx];
                byte[] got = db.getOne(Long.MAX_VALUE, latest.segs[idx], gd);
                if (!ok(k, version[k], got)) check(k, version[k], got, "warm-up");
                int j = i % hpool.keys.length;
                int kh = hpool.keys[j];
                got = db.getOne(midTime, hpool.segs[j], gd);
                if (!ok(kh, midVersion[kh], got)) check(kh, midVersion[kh], got, "warm-up historical");
            }
        }
        scanReads("warmup.scan_fwd", true, version, Long.MAX_VALUE, 2000, false);
        scanReads("warmup.scan_back", false, version, Long.MAX_VALUE, 2000, false);
        metrics.remove("warmup.scan_fwd.kvs_per_s"); metrics.remove("warmup.scan_fwd.scans_per_s");
        metrics.remove("warmup.scan_back.kvs_per_s"); metrics.remove("warmup.scan_back.scans_per_s");
        for (Iterator<String> it = metrics.keySet().iterator(); it.hasNext();) if (it.next().startsWith("warmup.")) it.remove();
        hists.remove("warmup.scan_fwd"); hists.remove("warmup.scan_back");
        phase("readwarmup", t0);

        long[] gc0 = PerfUtil.gcTotals();
        upStartMs = ManagementFactory.getRuntimeMXBean().getUptime();
        sampler = new Sampler();
        sampler.sample(0);
        sampler.start();
        t0 = System.nanoTime();
        getReads("get_latest", Long.MAX_VALUE, version, latest, windows);
        getReads("get_historical", midTime, midVersion, hpool, windows);
        if (lpool != null) getReads("get_longkey", Long.MAX_VALUE, version, lpool, windows);
        mtReads("get_latest_mt" + mtThreads, latest, Math.max(1, windows / 2));
        scanReads("scan_fwd", true, version, Long.MAX_VALUE, scansPerWindow, false);
        scanReads("scan_back", false, version, Long.MAX_VALUE, scansPerWindow, false);
        scanReads("scan_fwd_hist", true, midVersion, midTime, scansPerWindow / 4, false);
        phase("measure", t0);
        upEndMs = ManagementFactory.getRuntimeMXBean().getUptime();
        long[] gc1 = PerfUtil.gcTotals();
        sampler.finish();
        gcMetrics(gc0, gc1);
        metrics.put("heap.after_gc_mb_max", sampler.heapAfterMax);
        metrics.put("heap.used_mb_max", sampler.heapUsedMax);
        if (sampler.rssMax > 0) metrics.put("rss_mb_max", sampler.rssMax);
        raw.put("samples", samplesJson(sampler.rows));

        t0 = System.nanoTime();
        verifyAll("end of reads");
        db.close();
        phase("verify", t0);
        FileStreamCleanup.deleteDir(dir);
    }

    static double heapMB() {
        Runtime rt = Runtime.getRuntime();
        for (int i = 0; i < 3; i++) {
            System.gc();
            try { Thread.sleep(50); } catch (InterruptedException e) { /* ignore */ }
        }
        return (rt.totalMemory() - rt.freeMemory()) / 1e6;
    }

    // ---- Mode restart ----

    void runRestart() throws Exception {
        if (!new File(dir, "model.json").exists()) fail("no model.json in " + dir + ": run mode write with keep=1 first");
        boolean wasFinite = readModel();
        info.put("oscache", osCache);
        clock.setTime(time + 1);
        long t0 = System.nanoTime();
        db = openDb();
        StartInfo si = db.start();
        double startSec = 1e-9 * (System.nanoTime() - t0);
        metrics.put("startup.sec", startSec);
        metrics.put("startup.transactions_rerun", (long) si.transCount);
        metrics.put("startup.read_from_mb", si.startPos / 1e6);
        metrics.put("startup.section_mb", (db.getStreamLength() - si.startPos) / 1e6);
        metrics.put("startup.stream_mb", db.getStreamLength() / 1e6);
        long firstAvail = db.getFirstAvailableLookupTime();
        metrics.put("startup.first_available_lookup_age_s", (time - firstAvail) / (double) SEC);
        metrics.put("startup.first_available_pos_mb", db.getFirstAvailablePos() / 1e6);
        System.out.printf(Locale.ROOT, "STARTUP %.3f s: %d transactions rerun, read from %.1f MB, stream %.1f MB%n",
                startSec, si.transCount, si.startPos / 1e6, db.getStreamLength() / 1e6);
        if (wasFinite) db.setRetainDuration(rUnits);

        // First reads, then the same reads again.
        Pool pool = new Pool(firstGets, seed + 31, 0, total);
        GetData gd = db.newGetData();
        long[] edges = {1, 10, 100, 1000, 10000, 100000, Long.MAX_VALUE};
        Hist[] block = new Hist[edges.length];
        for (int i = 0; i < block.length; i++) block[i] = new Hist();
        Hist first = new Hist();
        long firstNs = 0;
        int b = 0;
        for (int i = 0; i < firstGets; i++) {
            int k = pool.keys[i];
            long s = System.nanoTime();
            byte[] got = db.getOne(Long.MAX_VALUE, pool.segs[i], gd);
            long e = System.nanoTime();
            while (i >= edges[b]) b++;
            block[b].record(e - s);
            first.record(e - s);
            if (i == 0) firstNs = e - s;
            if (!ok(k, version[k], got)) check(k, version[k], got, "first reads");
        }
        metrics.put("first_get_us", firstNs / 1e3);
        for (int i = 0; i < block.length; i++) {
            if (block[i].count() > 0) {
                metrics.put("first_gets.block" + i + ".mean_us", block[i].mean() / 1e3);
                metrics.put("first_gets.block" + i + ".count", block[i].count());
            }
        }
        hist("first_gets", first);
        Hist again = new Hist();
        for (int i = 0; i < firstGets; i++) {
            int k = pool.keys[i];
            long s = System.nanoTime();
            byte[] got = db.getOne(Long.MAX_VALUE, pool.segs[i], gd);
            long e = System.nanoTime();
            again.record(e - s);
            if (!ok(k, version[k], got)) check(k, version[k], got, "second reads");
        }
        hist("second_gets", again);
        metrics.put("first_over_second_mean", first.mean() / again.mean());
        System.out.printf(Locale.ROOT, "FIRST READS %d: mean %.2f us (first get %.1f us), again %.2f us; p99 %.1f / %.1f us%n",
                firstGets, first.mean() / 1e3, firstNs / 1e3, again.mean() / 1e3, first.percentile(99) / 1e3,
                again.percentile(99) / 1e3);

        // Mixed reads and writes.
        runMixed();

        t0 = System.nanoTime();
        db.sync(SyncLevel.ORDINARY);
        verifyAll("after the mixed phase");
        db.close();
        phase("verify", t0);
        if (!keep) FileStreamCleanup.deleteDir(dir);
    }

    void runMixed() throws Exception {
        final AtomicIntegerArray committed = new AtomicIntegerArray(total), pending = new AtomicIntegerArray(total);
        for (int i = 0; i < total; i++) { committed.set(i, version[i]); pending.set(i, version[i]); }
        final AtomicBoolean stop = new AtomicBoolean();
        final AtomicReference<Throwable> err = new AtomicReference<Throwable>();
        final Hist[] rh = new Hist[mixReaders];
        final long[] reads = new long[mixReaders];
        Thread[] readers = new Thread[mixReaders];
        long[] gc0 = PerfUtil.gcTotals();
        upStartMs = ManagementFactory.getRuntimeMXBean().getUptime();
        sampler = new Sampler();
        sampler.sample(0);
        sampler.start();
        for (int t = 0; t < mixReaders; t++) {
            final int tt = t;
            rh[t] = new Hist();
            readers[t] = new Thread(new Runnable() {
                public void run() {
                    try {
                        Random r = new Random(seed * 13 + tt);
                        GetData gd = db.newGetData();
                        long count = 0;
                        while (!stop.get()) {
                            int k = r.nextInt(total);
                            int lo = committed.get(k);
                            long s = System.nanoTime();
                            byte[] got = db.getOne(Long.MAX_VALUE, segs(k), gd);
                            long e = System.nanoTime();
                            int hi = pending.get(k);
                            rh[tt].record(e - s);
                            count++;
                            if (got == null || got.length != valsize || rd(got, 0) != k) {
                                fail("mixed: bad value for key " + k);
                            }
                            int v = rd(got, 4);
                            if (v < lo || v > hi || got[valsize - 1] != (byte) (k + v + valsize - 1)) {
                                fail("mixed: key " + k + " version " + v + " not between " + lo + " and " + hi);
                            }
                        }
                        reads[tt] = count;
                    } catch (Throwable e) {
                        err.compareAndSet(null, e);
                        stop.set(true);
                    }
                }
            });
            readers[t].setName("perf-reader-" + t);
        }
        for (Thread r : readers) r.start();
        Hist append = new Hist(), dur = new Hist();
        Random rnd = new Random(seed + 41);
        long t0 = System.nanoTime();
        int[] picks = new int[tsize];
        long puts = 0;
        try {
            for (int i = 0; i < mixOps && !stop.get(); i++) {
                Trans.Builder b = db.trans();
                for (int j = 0; j < tsize; j++) {
                    int k;
                    boolean dup;
                    do {
                        k = pickKey(rnd, 0, 1);
                        dup = false;
                        for (int q = 0; q < j; q++) if (picks[q] == k) dup = true;
                    } while (dup);
                    picks[j] = k;
                    version[k]++;
                    pending.set(k, version[k]);
                    b.put(keyBytes(k), value(k, version[k]));
                }
                long s = System.nanoTime();
                execute(b);
                long e = System.nanoTime();
                append.record(e - s);
                if (durable) {
                    db.sync(SyncLevel.ORDINARY);
                    dur.record(System.nanoTime() - s);
                }
                for (int q = 0; q < tsize; q++) committed.set(picks[q], version[picks[q]]);
                puts += tsize;
            }
        } finally {
            stop.set(true);
        }
        double sec = 1e-9 * (System.nanoTime() - t0);
        for (Thread r : readers) r.join();
        upEndMs = ManagementFactory.getRuntimeMXBean().getUptime();
        long[] gc1 = PerfUtil.gcTotals();
        sampler.finish();
        if (err.get() != null) throw new PerfFailure("mixed phase: " + err.get());
        Hist all = new Hist();
        long totalReads = 0;
        for (int t = 0; t < mixReaders; t++) { all.add(rh[t]); totalReads += reads[t]; }
        metrics.put("mix.sec", sec);
        metrics.put("mix.commits_per_s", mixOps / sec);
        metrics.put("mix.puts_per_s", puts / sec);
        metrics.put("mix.gets_per_s", totalReads / sec);
        hist("mix.commit.append", append);
        if (durable) hist("mix.commit.durable", dur);
        hist("mix.get", all);
        gcMetrics(gc0, gc1);
        metrics.put("heap.after_gc_mb_max", sampler.heapAfterMax);
        metrics.put("heap.used_mb_max", sampler.heapUsedMax);
        if (sampler.rssMax > 0) metrics.put("rss_mb_max", sampler.rssMax);
        raw.put("samples", samplesJson(sampler.rows));
        System.out.printf(Locale.ROOT, "MIXED %d commits and %d gets in %.2f s: %.0f commits/s, %.0f gets/s; commit p99 %.1f us, get p99 %.1f us%n",
                mixOps, totalReads, sec, mixOps / sec, totalReads / sec, append.percentile(99) / 1e3, all.percentile(99) / 1e3);
    }

    // ---- Output ----

    static final class FileStreamCleanup {
        static void deleteDir(File d) {
            File[] fs = d.listFiles();
            if (fs != null) for (File f : fs) f.delete();
            d.delete();
        }
    }

    String workloadId() {
        StringBuilder sb = new StringBuilder("traceVersion=" + TRACE_VERSION + ";mode=" + mode + ";");
        for (Map.Entry<String, Object> e : W.entrySet()) sb.append(e.getKey()).append('=').append(e.getValue()).append(';');
        return PerfUtil.sha256(sb.toString()).substring(0, 16);
    }

    void writeResult(boolean ok) throws IOException {
        Map<String, Object> r = new LinkedHashMap<String, Object>();
        r.put("schema", 1L);
        r.put("scenario", scenario);
        r.put("mode", mode);
        r.put("status", ok ? "ok" : "failed");
        r.put("workloadId", workloadId());
        r.put("traceVersion", (long) TRACE_VERSION);
        r.put("workload", new LinkedHashMap<String, Object>(W));
        r.put("run", new LinkedHashMap<String, Object>(RUN));
        r.put("jvm", PerfUtil.jvmInfo());
        r.put("derived", derived());
        r.put("phasesSec", phases);
        r.put("uptimeMs", Arrays.<Object>asList(upStartMs, upEndMs));
        r.put("metrics", metrics);
        r.put("info", info);
        r.put("finishedAt", new Date().toString());
        File out = new File(outDir);
        out.mkdirs();
        PerfUtil.writeFile(new File(out, mode + ".result.json"), Json.write(r));
        Map<String, Object> h = new LinkedHashMap<String, Object>();
        Map<String, Object> hs = new LinkedHashMap<String, Object>();
        for (Map.Entry<String, Hist> e : hists.entrySet()) hs.put(e.getKey(), e.getValue().sparse());
        h.put("histogramsNs", hs);
        h.putAll(raw);
        PerfUtil.writeFile(new File(out, mode + ".raw.json"), Json.writeCompact(h) + "\n");
    }

    Map<String, Object> derived() {
        Map<String, Object> d = new LinkedHashMap<String, Object>();
        d.put("keys", (long) total);
        d.put("kvBytes", (long) kvSize);
        d.put("liveUserBytes", (long) n * kvSize + (long) nlong * (longlen + valsize));
        d.put("retentionUnits", finite ? rUnits : 0L);
        d.put("retentionTransactions", finite ? rTrans : 0L);
        d.put("tstepUnits", tstep);
        d.put("updatesPerKeyPerRetention", finite ? kRetain : 0.0);
        d.put("paced", rate > 0);
        return d;
    }

    void run() throws Exception {
        System.out.println("Perf mode=" + mode + " scenario=" + scenario + " workload=" + workloadId() + " " + W);
        if (mode.equals("write")) runWrite();
        else if (mode.equals("read")) runRead();
        else if (mode.equals("restart")) runRestart();
        else fail("unknown mode " + mode + " (write, read, restart)");
        writeResult(true);
        System.out.println("PERF OK");
    }

    public static void main(String[] args) throws Exception {
        if (args.length < 1) {
            System.err.println("usage: Perf write|read|restart (parameters as -Dperf.name=value)");
            System.exit(2);
        }
        Perf p = new Perf(args[0]);
        try {
            p.run();
        } catch (Throwable t) {
            t.printStackTrace(System.out);
            System.out.println("PERF FAILED: " + t);
            try {
                p.metrics.put("failure", String.valueOf(t));
                p.writeResult(false);
            } catch (Throwable t2) {
                System.out.println("(could not write the result: " + t2 + ")");
            }
            System.exit(1);
        }
        System.exit(0);
    }
}
