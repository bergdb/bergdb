package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.util.*;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicLongArray;
import java.util.concurrent.atomic.AtomicReference;
import java.util.concurrent.atomic.AtomicReferenceArray;
import java.util.concurrent.locks.LockSupport;

import bergdb.core.PerfUtil.GcLog;
import bergdb.core.PerfUtil.Hist;
import bergdb.core.PerfUtil.Json;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.Clock;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.FileStream;
import bergdb.stream.ReadBelowFirstPosException;

/**
 * The Level 3 soak (docs/level3-plan.md, task 2; bergdb item 001, WP P2), written
 * 2026-10-16. Run it with java/stress/soak.sh, which fixes the JVM flags and the GC log and
 * runs "Soak finish" on the result.
 *
 * A FileStream in a disposable directory, the system clock and a retention in wall-clock
 * seconds: reclaim cuts the stream and deletes whole files as time goes by. One writer (the
 * main thread), paced at a fixed rate, and two to four reader threads, paced too. The
 * phases: the load (every key once), the warm-up (the workload, not measured, at least
 * soak.warmup seconds and until the first physical cut), the measured phase (soak.measure
 * seconds of steady running, not counting the restarts and their checks, with soak.restarts
 * cold restarts spread over it; extended, up to soak.extend seconds, until it has
 * soak.mincuts physical cuts), and the end check.
 *
 * The workload. Key i < n is a 4-byte big-endian int; the nlong keys after them are long keys
 * ("/soak/long/" + 9 digits + "/" + filler, longlen bytes). Keys sort by index, with the
 * database's internal keys ("/#i/...") between the two kinds. The value of key k at version
 * v is a function of k and v (valsize bytes), so the model holds versions. A transaction has
 * tsize distinct keys, each from the hot set (hotkeys keys, half of them long keys) with
 * probability hot percent, else uniform; del percent of the keys that are present are
 * deleted, the others get their next version (a deleted key is inserted again).
 *
 * The model is bounded: per key, its versions and deletes with their transaction times,
 * pruned to what a lookup at or after the "keep" time can see. Keep is the older of the
 * first available lookup time less 2 seconds and the latest time less the retention and a
 * minute, and never newer than a lookup time a reader has announced (Reader.announce), so
 * every successful operation is checked at its actual snapshot. Readers do latest and
 * historical gets (also just around the first available lookup time) and forward and backward
 * scans at the latest or a historical time; a scan's result is checked for completeness too.
 * An operation that throws LookupTimeNotAvailableException is counted as expired at admission
 * or expired during (a cut overtook it), provided its lookup time is before the first
 * available lookup time; anything else fails the run. A latest read may see a transaction
 * before the model has it: it waits for the model (as ReclaimReaders does).
 *
 * A restart: the readers pause, the database is synced and closed and opened again from its
 * directory (a cold node cache; the OS file cache is warm), and the check runs: every key at
 * the latest time, and the hot keys and soak.samplekeys random keys at soak.checktimes times
 * from the first available lookup time to the latest; with n at most soak.companion, every
 * key at every one of those times (the exhaustive companion case). The end check is the same.
 *
 * Results: OUT/result.json (soak.out): the parameters, the JVM, the phases and their uptime
 * windows, throughput, latency histograms (append commits, also split by whether reclaim
 * stepped in the commit; durable commits; the pacing delay; gets and scans), the slowest
 * commits, reclaim iterations, cut decisions and physical cuts with their uptimes, the
 * restarts, memory and storage samples, expiries and failures. "Soak finish OUT" (run by
 * soak.sh after the JVM exits) adds the GC log's pauses and safepoints per phase and the
 * pauses that overlap the slowest commits. Exit code 0 if the run met its conditions with no
 * failure.
 *
 * In package bergdb.core to reach Db internals (Reclaim.Stats). Java 8 source.
 */
public class Soak {
    static final long SEC = Clock.UNITS_PER_SEC;
    static final long NS = 1000000000L;
    static final String MARKER = "soak-data.marker";

    // ---- Parameters (soak.*) ----

    /** The workload parameters, recorded in the result. */
    static final Map<String, Object> W = new TreeMap<String, Object>();
    static int pi(String k, int d) { int v = Integer.getInteger("soak." + k, d); W.put(k, (long) v); return v; }
    static long pl(String k, long d) { long v = Long.getLong("soak." + k, d); W.put(k, v); return v; }

    final long seed = pl("seed", 1);
    final int n = pi("n", 1000000);
    final int nlong = pi("nlong", 1000);
    final int longlen = Math.max(21, pi("longlen", 120));
    final int valsize = Math.max(8, pi("valsize", 1000));
    final int retainSec = pi("retain", 300);
    final int rate = pi("rate", 300);                 // writer transactions per second; 0: unpaced
    final int tsize = pi("tsize", 10);
    final int hotKeys = pi("hotkeys", 1000);
    final int hotPct = pi("hot", 30);
    final int delPct = pi("del", 5);
    final int readerCount = pi("readers", 3);
    final int readRate = pi("readrate", 5000);        // operations per second per reader; 0: unpaced
    final int scanLen = pi("scanlen", 50);
    final int warmupSec = pi("warmup", 300);
    final int warmupMaxSec = pi("warmupmax", 3600);   // the wait for the first physical cut ends here
    final int measureSec = pi("measure", 7200);
    final int extendSec = pi("extend", 3600);
    final int restarts = pi("restarts", 3);
    final int minCuts = pi("mincuts", 10);
    final int durableEvery = pi("durable", Math.max(1, rate));   // every k-th measured commit is synced
    final int sampleMs = pi("samplems", 1000);
    final int dirtyEverySec = pi("dirtyevery", 60);   // the dirty nodes are counted (0: never)
    final int sampleKeys = pi("samplekeys", 20000);
    final int checkTimes = Math.max(2, pi("checktimes", 6));
    final int companion = pi("companion", 20000);
    final int sd = pi("sd", 0);
    final int maxnode = pi("maxnode", 0);
    final String outDir = System.getProperty("soak.out", "build/soak/out");
    final String dataDir = System.getProperty("soak.dir", "build/soak/data");

    final int total = n + nlong;
    final int hotSize = Math.max(1, Math.min(hotKeys, total));
    final boolean exhaustive = total <= companion;

    // ---- State ----

    final File dir = new File(dataDir);
    final Object dbLock = new Object();               // the sampler and a restart
    volatile Db db;
    volatile FileStream stream;
    Reclaim.Stats rstats;
    final long jvmStartMs = ManagementFactory.getRuntimeMXBean().getStartTime();
    volatile long loadStartTime;                      // database time of the load's first commit

    final int[] version;                              // the writer's: current version, -v deleted at v
    final AtomicReferenceArray<KeyHist> hist;         // the model, per key
    volatile long lastCompleted = Long.MIN_VALUE;     // the model has every transaction to here
    volatile long modelKeep = Long.MIN_VALUE;         // pruning never goes past this (monotone)
    final AtomicLongArray announced;                  // per reader: the lookup time it will check
    volatile boolean stopReaders, pauseAll;
    final Object pauseLock = new Object();
    int pausedReaders;

    final AtomicReference<String> failure = new AtomicReference<String>();
    final AtomicLong expiredAtAdmission = new AtomicLong(), expiredDuring = new AtomicLong();
    final AtomicLong unverifiable = new AtomicLong();
    final Map<String, Object> metrics = new LinkedHashMap<String, Object>();
    final Map<String, Object> phases = new LinkedHashMap<String, Object>();
    final Map<String, Object> windows = new LinkedHashMap<String, Object>();
    final List<Object> restartInfo = new ArrayList<Object>();
    final List<Object> cutDecisions = new ArrayList<Object>();
    final List<Object> iterations = new ArrayList<Object>();
    final List<Object> checks = new ArrayList<Object>();

    Soak() {
        version = new int[total];
        hist = new AtomicReferenceArray<KeyHist>(total);
        announced = new AtomicLongArray(Math.max(1, readerCount));
        for (int i = 0; i < announced.length(); i++) announced.set(i, Long.MAX_VALUE);
    }

    void fail(String m) {
        if (failure.compareAndSet(null, m)) {
            System.out.println("FAILURE " + m);
            System.out.flush();
        }
    }

    static double uptimeSec() {
        return ManagementFactory.getRuntimeMXBean().getUptime() / 1000.0;
    }

    static final Set<String> HEAP_POOLS = new HashSet<String>();
    static {
        for (java.lang.management.MemoryPoolMXBean p : ManagementFactory.getMemoryPoolMXBeans()) {
            if (p.getType() == java.lang.management.MemoryType.HEAP) HEAP_POOLS.add(p.getName());
        }
    }

    /**
     * The heap in use right after the latest collection of any collector, young ones included
     * (MB; -1 before the first). PerfUtil.heapAfterLastGcMB sums each pool's own last
     * collection, which for G1's old generation waits for a mixed or full collection.
     */
    static double heapAfterLatestGcMB() {
        long latestEnd = -1;
        double used = -1;
        for (java.lang.management.GarbageCollectorMXBean b : ManagementFactory.getGarbageCollectorMXBeans()) {
            if (!(b instanceof com.sun.management.GarbageCollectorMXBean)) continue;
            com.sun.management.GcInfo gi = ((com.sun.management.GarbageCollectorMXBean) b).getLastGcInfo();
            if (gi == null || gi.getEndTime() <= latestEnd) continue;
            long u = 0;
            for (Map.Entry<String, java.lang.management.MemoryUsage> e : gi.getMemoryUsageAfterGc().entrySet()) {
                if (HEAP_POOLS.contains(e.getKey())) u += e.getValue().getUsed();
            }
            latestEnd = gi.getEndTime();
            used = u / 1e6;
        }
        return used;
    }

    /** The JVM uptime (s) of a database time (the system clock: 100 ns units since 1970). */
    double uptimeOf(long dbTime) {
        return (dbTime / 1e4 - jvmStartMs) / 1000.0;
    }

    // ---- Keys and values ----

    byte[] keyBytes(int k) {
        if (k < n) return KeyFactory.binaryIntKey(k);
        byte[] b = new byte[longlen];
        byte[] prefix = {'/', 's', 'o', 'a', 'k', '/', 'l', 'o', 'n', 'g', '/'};
        System.arraycopy(prefix, 0, b, 0, prefix.length);
        int v = k - n;
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

    /** The index of a key returned by the database; -1 for an internal key, -2 for any other. */
    int decode(long[] seg) {
        if (Keys.isPrefix(DbConstants.INTERNAL_PREFIX_SKEY, seg)) return -1;
        byte[] b = Keys.toBytes(seg);
        if (b.length == 4) {
            int k = ((b[0] & 0xff) << 24) | ((b[1] & 0xff) << 16) | ((b[2] & 0xff) << 8) | (b[3] & 0xff);
            return k >= 0 && k < n ? k : -2;
        }
        if (b.length == longlen && b[0] == '/' && b[1] == 's' && b[20] == '/') {
            int v = 0;
            for (int i = 11; i <= 19; i++) v = v * 10 + (b[i] - '0');
            return v < nlong ? n + v : -2;
        }
        return -2;
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

    /** True if 'got' is key k's value at version v (v <= 0: no value); value(k, v) without allocating it. */
    boolean valueOk(int k, int v, byte[] got) {
        if (v <= 0) return got == null;
        if (got == null || got.length != valsize || rd(got, 0) != k || rd(got, 4) != v) return false;
        for (int i = 8; i < valsize; i++) if (got[i] != (byte) (k + v + i)) return false;
        return true;
    }

    static String printable(byte[] b) {
        StringBuilder sb = new StringBuilder();
        for (byte x : b) {
            if (x >= 32 && x < 127) sb.append((char) x);
            else sb.append(String.format(Locale.ROOT, "\\x%02x", x & 0xff));
        }
        return sb.toString();
    }

    static String describe(byte[] got) {
        if (got == null) return "no value";
        if (got.length < 8) return got.length + " bytes";
        return got.length + " bytes, key " + rd(got, 0) + " version " + rd(got, 4);
    }

    /** Hot key j: the first half of the hot set are int keys from 0, the rest long keys from n. */
    int hotKey(int j) {
        int longHot = Math.min(nlong, hotSize / 2);
        return j < hotSize - longHot ? j : n + (j - (hotSize - longHot));
    }

    int pick(Random r) {
        return r.nextInt(100) < hotPct ? hotKey(r.nextInt(hotSize)) : r.nextInt(total);
    }

    // ---- The model ----

    /**
     * A key's history: entries [from, to) of a, each a time and a version (-1: deleted).
     * Immutable once published, except that the writer appends after 'to' of the newest
     * snapshot, which no reader of an older snapshot reads.
     */
    static final class KeyHist {
        final long[] a;
        final int from, to;

        KeyHist(long[] a, int from, int to) {
            this.a = a; this.from = from; this.to = to;
        }
    }

    /** The version of key k at lookup time t (0: no value), from the model. */
    int modelAt(int k, long t) {
        KeyHist h = hist.get(k);
        if (h == null) return 0;
        long[] a = h.a;
        int lo = h.from, hi = h.to - 1, found = -1;
        while (lo <= hi) {
            int mid = (lo + hi) >>> 1;
            if (a[2 * mid] <= t) { found = mid; lo = mid + 1; } else hi = mid - 1;
        }
        if (found < 0) return 0;
        long v = a[2 * found + 1];
        return v < 0 ? 0 : (int) v;
    }

    /** Appends (tt, v) to key k's history, dropping what no lookup at or after 'keep' sees. */
    void modelAdd(int k, long tt, long v, long keep) {
        KeyHist h = hist.get(k);
        long[] a;
        int from, to;
        if (h == null) {
            a = new long[4];
            from = 0;
            to = 0;
        } else {
            a = h.a;
            from = h.from;
            to = h.to;
        }
        while (from + 1 < to && a[2 * (from + 1)] <= keep) from++;
        if (2 * (to + 1) > a.length) {
            int live = to - from;
            long[] na = new long[Math.max(4, 4 * (live + 1))];
            System.arraycopy(a, 2 * from, na, 0, 2 * live);
            a = na;
            from = 0;
            to = live;
        }
        a[2 * to] = tt;
        a[2 * to + 1] = v;
        hist.set(k, new KeyHist(a, from, to + 1));
    }

    /** The keep time for pruning now: what no announced reader and no lookup after needs. */
    long keepNow(long tt) {
        long cand = Math.min(tt - (retainSec + 60) * SEC, db.getFirstAvailableLookupTime() - 2 * SEC);
        if (cand > modelKeep) modelKeep = cand;
        long keep = modelKeep;                        // written before 'announced' is read
        for (int i = 0; i < announced.length(); i++) keep = Math.min(keep, announced.get(i) - 1);
        return keep;
    }

    /** Waits for the model, not the database: a latest read can precede model publication. */
    boolean awaitModel(long actualLookupTime) {
        long deadline = System.nanoTime() + 60 * NS;
        while (actualLookupTime > lastCompleted) {
            if (failure.get() != null) return false;
            if (System.nanoTime() >= deadline) {
                fail("timed out waiting for the model through " + actualLookupTime);
                return false;
            }
            LockSupport.parkNanos(100000);
        }
        return true;
    }

    // ---- The database ----

    void prepareDir() throws IOException {
        if (dir.exists()) {
            File[] fs = dir.listFiles();
            if (fs != null && fs.length > 0 && !new File(dir, MARKER).exists()) {
                throw new IOException("refusing to empty " + dir + ": it has files and no " + MARKER
                        + " (use a disposable directory)");
            }
            if (fs != null) for (File f : fs) f.delete();
        }
        dir.mkdirs();
        PerfUtil.writeFile(new File(dir, MARKER), "disposable directory of Soak.java\n");
    }

    Db openDb() throws IOException {
        FileStream s = new FileStream(dir);    // (FileStream reads its own files only, not the marker.)
        DbBuilder b = Db.builder().stream("main", s).systemClock().noEvict().retainForever().testId();
        if (sd > 0) b.startupDistance(sd);
        if (maxnode == 8) b.maxNodeSize8();
        if (maxnode == 14) b.maxNodeSize14();
        if (maxnode == 30) b.maxNodeSize30();
        if (maxnode == 62) b.maxNodeSize62();
        Db d = b.build();
        stream = s;
        return d;
    }

    void enableStats() {
        rstats = db.internal().reclaim().enableStats();
        rstats.countTouch = false;
    }

    /** Moves the reclaim statistics of this database object to the result (at a restart and the end). */
    void harvestStats(int segment) {
        for (Reclaim.Stats.Cut c : rstats.cuts) {
            cutDecisions.add(Arrays.<Object>asList(uptimeOf(c.decidedTime), (long) segment, c.pos / 1e6,
                    (c.decidedTime - c.tEnd) / (double) SEC, c.decidedAt / 1e6));
        }
        for (Reclaim.Stats.Iteration it : rstats.iterations) {
            iterations.add(Arrays.<Object>asList(uptimeOf(it.tStart), it.tEnd < 0 ? null : (Object) uptimeOf(it.tEnd),
                    (long) segment, it.steps, it.kvs, it.values, it.valueBytes / 1e6, it.recordBytes / 1e6,
                    it.pStart / 1e6));
        }
    }

    void phase(String name, long startNanos, double upFrom) {
        double sec = 1e-9 * (System.nanoTime() - startNanos);
        phases.put(name, sec);
        windows.put(name, Arrays.<Object>asList(upFrom, uptimeSec()));
        System.out.printf(Locale.ROOT, "PHASE %s %.1f s%n", name, sec);
        System.out.flush();
    }

    // ---- The writer ----

    /** The slowest events: [ns, uptime ms, commit index, reclaim stepped, cut decided]. */
    static final class Slowest {
        final int keep;
        final List<long[]> l = new ArrayList<long[]>();
        long floor = -1;                              // after a trim: the slowest kept, at least

        Slowest(int keep) {
            this.keep = keep;
        }

        void note(long ns, long index, boolean stepped, boolean cut) {
            if (ns <= floor) return;
            l.add(new long[] {ns, ManagementFactory.getRuntimeMXBean().getUptime(), index, stepped ? 1 : 0, cut ? 1 : 0});
            if (l.size() >= 4 * keep) trim();
        }

        void trim() {
            Collections.sort(l, new Comparator<long[]>() {
                public int compare(long[] a, long[] b) { return Long.compare(b[0], a[0]); }
            });
            while (l.size() > keep) l.remove(l.size() - 1);
            if (l.size() == keep) floor = l.get(keep - 1)[0];
        }

        List<Object> json() {
            trim();
            List<Object> out = new ArrayList<Object>();
            for (long[] e : l) out.add(Arrays.<Object>asList(e[0] / 1e6, e[1] / 1000.0, e[2], e[3], e[4]));
            return out;
        }
    }

    final Hist commitAppend = new Hist(), commitStep = new Hist(), commitPlain = new Hist();
    final Hist commitDurable = new Hist(), commitDelay = new Hist();
    final Slowest slowAppend = new Slowest(20), slowDurable = new Slowest(10);
    volatile long commits;
    long puts, deletes, measuredCommits, stepCommits, cutCommits;
    long[] perSecond = new long[4096];
    long secondsBase;                                 // System.nanoTime() of the measured start
    final List<long[]> pausedSeconds = new ArrayList<long[]>();   // restarts: [first, last] second

    /** One transaction of tsize distinct keys. */
    void transaction(Random rnd, boolean measure) {
        int[] ks = new int[tsize];
        int[] nv = new int[tsize];
        Trans.Builder b = db.trans();
        for (int j = 0; j < tsize; j++) {
            int k;
            boolean dup;
            do {
                k = pick(rnd);
                dup = false;
                for (int q = 0; q < j; q++) if (ks[q] == k) dup = true;
            } while (dup);
            ks[j] = k;
            int cur = version[k];
            if (cur > 0 && rnd.nextInt(100) < delPct) {
                b.delete(keyBytes(k));
                nv[j] = -cur;
                deletes++;
            } else {
                int v = Math.abs(cur) + 1;
                b.put(keyBytes(k), value(k, v));
                nv[j] = v;
                puts++;
            }
        }
        Trans t = b.build();
        List<Reclaim.Stats.Iteration> its = rstats.iterations;
        int itsBefore = its.size();
        long stepsBefore = itsBefore == 0 ? 0 : its.get(itsBefore - 1).steps;
        int cutsBefore = rstats.cuts.size();
        long s = System.nanoTime();
        db.execute(t);
        long e1 = System.nanoTime();
        boolean stepped = its.size() != itsBefore || (itsBefore > 0 && its.get(itsBefore - 1).steps != stepsBefore);
        boolean cut = rstats.cuts.size() != cutsBefore;
        if (measure) {
            commitAppend.record(e1 - s);
            (stepped ? commitStep : commitPlain).record(e1 - s);
            slowAppend.note(e1 - s, commits, stepped, cut);
            if (durableEvery > 0 && measuredCommits % durableEvery == 0) {
                db.sync(SyncLevel.ORDINARY);
                long e2 = System.nanoTime();
                commitDurable.record(e2 - s);
                slowDurable.note(e2 - s, commits, stepped, cut);
            }
            measuredCommits++;
            if (stepped) stepCommits++;
            if (cut) cutCommits++;
            int sec = (int) ((e1 - secondsBase) / NS);
            if (sec >= perSecond.length) perSecond = Arrays.copyOf(perSecond, Math.max(sec + 1, 2 * perSecond.length));
            if (sec >= 0) perSecond[sec]++;
        }
        commits++;
        long keep = keepNow(t.tt);
        for (int j = 0; j < tsize; j++) {
            version[ks[j]] = nv[j];
            modelAdd(ks[j], t.tt, nv[j] < 0 ? -1 : nv[j], keep);
        }
        lastCompleted = db.lookupTime(Long.MAX_VALUE);   // publishes the model updates above
    }

    void load() {
        long t0 = System.nanoTime();
        double up0 = uptimeSec();
        int[] perm = new int[total];
        for (int i = 0; i < total; i++) perm[i] = i;
        Random rnd = new Random(seed);
        for (int i = total - 1; i > 0; i--) {
            int j = rnd.nextInt(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        int batch = 100;
        for (int i = 0; i < total; i += batch) {
            Trans.Builder b = db.trans();
            int end = Math.min(total, i + batch);
            for (int j = i; j < end; j++) b.put(keyBytes(perm[j]), value(perm[j], 1));
            Trans t = b.build();
            db.execute(t);
            if (i == 0) loadStartTime = t.tt;
            for (int j = i; j < end; j++) {
                version[perm[j]] = 1;
                modelAdd(perm[j], t.tt, 1, Long.MIN_VALUE);
            }
            lastCompleted = db.lookupTime(Long.MAX_VALUE);
        }
        db.sync(SyncLevel.ORDINARY);
        phase("load", t0, up0);
        metrics.put("load.puts_per_s", total / (Double) phases.get("load"));
        metrics.put("load.stream_mb", db.getStreamLength() / 1e6);
    }

    /** The writer's pacing: transaction i at start + i / rate. */
    final class Pacer {
        final long interval = rate > 0 ? NS / rate : 0;
        long start, i;

        Pacer() {
            restartClock();
        }

        void restartClock() {
            start = System.nanoTime();
            i = 0;
        }

        void await(boolean measure) {
            if (interval == 0) return;
            long intended = start + i * interval;
            long now;
            while ((now = System.nanoTime()) < intended) {
                long wait = intended - now;
                if (wait > 200000) LockSupport.parkNanos(wait - 100000);
            }
            if (measure) commitDelay.record(now - intended);
            if (now - intended > NS) restartClock();     // more than a second behind: pace from now
            else i++;
        }
    }

    // ---- The readers ----

    final class Reader extends Thread {
        final int slot;
        final Random rr;
        final Hist latest = new Hist(), historical = new Hist(), fwd = new Hist(), bwd = new Hist();
        long getsOk, scansOk, kvsChecked;

        Reader(int slot, long rseed) {
            this.slot = slot;
            rr = new Random(rseed);
            setName("soak-reader-" + slot);
            setDaemon(true);
        }

        public void run() {
            long interval = readRate > 0 ? NS / readRate : 0;
            long start = System.nanoTime(), i = 0;
            try {
                while (!stopReaders && failure.get() == null) {
                    if (pauseAll) {
                        synchronized (pauseLock) {
                            pausedReaders++;
                            pauseLock.notifyAll();
                            while (pauseAll && !stopReaders) pauseLock.wait(100);
                            pausedReaders--;
                        }
                        start = System.nanoTime();
                        i = 0;
                        continue;
                    }
                    if (interval > 0) {
                        // Parks, never spins (an early wake-up runs early; a late one is caught up).
                        long intended = start + i * interval;
                        long now = System.nanoTime();
                        if (intended - now > 20000) {
                            LockSupport.parkNanos(intended - now);
                            now = System.nanoTime();
                        }
                        if (now - intended > NS) { start = now; i = 0; } else i++;
                    }
                    Db d = db;
                    int r = rr.nextInt(100);
                    if (r < 35) get(d, Long.MAX_VALUE, latest);
                    else if (r < 60) get(d, pickTime(d), historical);
                    else if (r < 65) get(d, edgeTime(d), historical);
                    else if (r < 75) scan(d, true, Long.MAX_VALUE, fwd);
                    else if (r < 85) scan(d, false, Long.MAX_VALUE, bwd);
                    else if (r < 92) scan(d, true, pickTime(d), fwd);
                    else scan(d, false, pickTime(d), bwd);
                }
            } catch (Throwable e) {
                fail("reader " + getName() + ": " + e);
                e.printStackTrace(System.out);
            }
        }

        /** The oldest time worth a lookup: the first available lookup time, or the load. */
        long windowStart(Db d) {
            return Math.max(d.getFirstAvailableLookupTime(), loadStartTime);
        }

        /** A lookup time in the retention window. */
        long pickTime(Db d) {
            long first = windowStart(d);
            long last = lastCompleted;
            if (last <= first) return last;
            return first + (long) (rr.nextDouble() * (last - first));
        }

        /** A lookup time within a second of the first available lookup time (expiry tested). */
        long edgeTime(Db d) {
            long first = d.getFirstAvailableLookupTime();
            if (first <= loadStartTime) return pickTime(d);
            return first - SEC + (long) (rr.nextDouble() * 2 * SEC);
        }

        /**
         * Announces the lookup time this operation will check, so that the writer keeps the
         * model for it. False if the model may already be pruned past it (unverifiable; skipped).
         */
        boolean announce(long t) {
            announced.set(slot, t);
            if (t < modelKeep) {
                announced.set(slot, Long.MAX_VALUE);
                unverifiable.incrementAndGet();
                return false;
            }
            return true;
        }

        void release() {
            announced.set(slot, Long.MAX_VALUE);
        }

        /** Classifies an exception of an operation at 'lookupTime'; false if it is a failure. */
        boolean expired(Db d, long lookupTime, Throwable e, String what) {
            if (!(e instanceof LookupTimeNotAvailableException)) {
                fail(what + " failed: " + e);
                e.printStackTrace(System.out);
                return false;
            }
            boolean during = false;
            for (Throwable c = e; c != null; c = c.getCause() == c ? null : c.getCause()) {
                during |= c instanceof ReadBelowFirstPosException;
            }
            long first = d.getFirstAvailableLookupTime();
            if (lookupTime == Long.MAX_VALUE) {
                fail(what + " expired at admission, which a read of the latest state cannot: " + e);
                return false;
            }
            if (lookupTime >= first) {
                fail(what + " expired although its lookup time " + lookupTime
                        + " is not before the first available lookup time " + first + ": " + e);
                return false;
            }
            (during ? expiredDuring : expiredAtAdmission).incrementAndGet();
            return true;
        }

        void get(Db d, long lookupTime, Hist h) {
            int k = pick(rr);
            if (!announce(lookupTime == Long.MAX_VALUE ? lastCompleted : lookupTime)) return;
            try {
                String what = "get(" + k + ", " + lookupTime + ")";
                GetData gd = d.newGetData();
                gd.actualLookupTime = -1;
                byte[] got;
                long s = System.nanoTime();
                try {
                    got = d.getOne(lookupTime, segs(k), gd);
                } catch (Throwable e) {
                    expired(d, gd.actualLookupTime >= 0 ? gd.actualLookupTime : lookupTime, e, what);
                    return;
                }
                h.record(System.nanoTime() - s);
                long t = gd.actualLookupTime;
                if (!awaitModel(t)) return;
                int v = modelAt(k, t);
                if (!valueOk(k, v, got)) {
                    fail(what + " at " + t + ": expected " + (v <= 0 ? "no value" : "version " + v) + ", got "
                            + describe(got));
                    return;
                }
                getsOk++;
            } finally {
                release();
            }
        }

        void scan(Db d, boolean forward, long lookupTime, Hist h) {
            boolean inLong = nlong > 2 * scanLen && rr.nextInt(10) == 0;
            final int start = inLong ? n + rr.nextInt(nlong) : rr.nextInt(total);
            if (!announce(lookupTime == Long.MAX_VALUE ? lastCompleted : lookupTime)) return;
            try {
                String what = (forward ? "forward" : "backward") + " scan from " + start + " at " + lookupTime;
                GetMany g = d.newGetMany();
                g.actualLookupTime = -1;
                g.lookupTime = lookupTime;
                g.startKey = segs(start);
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
                long s = System.nanoTime();
                try {
                    d.getMany(g);
                } catch (Throwable e) {
                    expired(d, g.actualLookupTime >= 0 ? g.actualLookupTime : lookupTime, e, what);
                    return;
                }
                h.record(System.nanoTime() - s);
                long t = g.actualLookupTime;
                if (!awaitModel(t)) return;
                // In order, each with its value at t, and no key present at t skipped.
                int step = forward ? 1 : -1;
                int prev = start - step;
                for (Kvt kvt : g.result) {
                    int k = decode(kvt.key);
                    if (k == -1) continue;                    // an internal key
                    if (k < 0) {
                        fail(what + " (actual " + t + "): a key that is neither the soak's nor internal: "
                                + printable(Keys.toBytes(kvt.key)));
                        return;
                    }
                    if (forward ? k <= prev : k >= prev) {
                        fail(what + " (actual " + t + "): key " + k + " out of order after " + prev);
                        return;
                    }
                    for (int q = prev + step; q != k; q += step) {
                        if (modelAt(q, t) > 0) {
                            fail(what + " (actual " + t + "): key " + q + " (version " + modelAt(q, t)
                                    + ") is missing before key " + k);
                            return;
                        }
                    }
                    int v = modelAt(k, t);
                    if (!valueOk(k, v, kvt.value)) {
                        fail(what + " (actual " + t + "): key " + k + " expected "
                                + (v <= 0 ? "no value" : "version " + v) + ", got " + describe(kvt.value));
                        return;
                    }
                    prev = k;
                    kvsChecked++;
                }
                if (added[0] < limit) {
                    // The scan reached the end of the keys: none present after the last one.
                    for (int q = prev + step; q >= 0 && q < total; q += step) {
                        if (modelAt(q, t) > 0) {
                            fail(what + " (actual " + t + "): ended before key " + q);
                            return;
                        }
                    }
                }
                scansOk++;
            } finally {
                release();
            }
        }
    }

    List<Reader> startReaders(long rseed) {
        List<Reader> rs = new ArrayList<Reader>();
        for (int i = 0; i < readerCount; i++) rs.add(new Reader(i, rseed * 1000003 + i));
        for (Reader r : rs) r.start();
        return rs;
    }

    void stopReaders(List<Reader> rs) throws InterruptedException {
        stopReaders = true;
        synchronized (pauseLock) {
            pauseLock.notifyAll();
        }
        for (Reader r : rs) {
            r.join(120000);
            if (r.isAlive()) fail("reader " + r.getName() + " did not stop within two minutes");
        }
        stopReaders = false;
    }

    void pauseReaders(List<Reader> rs) throws InterruptedException {
        synchronized (pauseLock) {
            pauseAll = true;
            long deadline = System.currentTimeMillis() + 120000;
            while (pausedReaders < rs.size() && failure.get() == null) {
                pauseLock.wait(100);
                if (System.currentTimeMillis() > deadline) {
                    fail("the readers did not pause within two minutes");
                    return;
                }
            }
        }
    }

    void resumeReaders() {
        synchronized (pauseLock) {
            pauseAll = false;
            pauseLock.notifyAll();
        }
    }

    // ---- Checks, restarts ----

    /**
     * With the readers stopped or paused: every key at the latest time, and the hot keys and
     * a sample (every key if exhaustive) at checkTimes times from the first available lookup
     * time to the latest, both included.
     */
    void check(String what) {
        long t0 = System.nanoTime();
        double up0 = uptimeSec();
        long first = Math.max(db.getFirstAvailableLookupTime(), loadStartTime);
        long last = db.lookupTime(Long.MAX_VALUE);
        long[] times = new long[checkTimes];
        for (int i = 0; i < checkTimes; i++) times[i] = first + (last - first) / (checkTimes - 1) * i;
        times[checkTimes - 1] = last;
        int[] keys;
        if (exhaustive) {
            keys = new int[total];
            for (int k = 0; k < total; k++) keys[k] = k;
        } else {
            keys = new int[hotSize + sampleKeys];
            for (int j = 0; j < hotSize; j++) keys[j] = hotKey(j);
            Random rnd = new Random(seed * 7919 + checks.size());
            for (int i = 0; i < sampleKeys; i++) keys[hotSize + i] = rnd.nextInt(total);
        }
        GetData gd = db.newGetData();
        long gets = 0, present = 0;
        for (int k = 0; k < total; k++) {
            if (!checkOne(what, k, Long.MAX_VALUE, gd)) return;
            gets++;
            if (version[k] > 0) present++;
        }
        double latestSec = 1e-9 * (System.nanoTime() - t0);
        for (long t : times) {
            for (int k : keys) {
                if (!checkOne(what, k, t, gd)) return;
                gets++;
            }
        }
        double sec = 1e-9 * (System.nanoTime() - t0);
        Map<String, Object> m = new LinkedHashMap<String, Object>();
        m.put("what", what);
        m.put("uptime_s", Arrays.<Object>asList(up0, uptimeSec()));
        m.put("gets", gets);
        m.put("keys_present", present);
        m.put("history_keys", (long) keys.length);
        m.put("history_times", (long) checkTimes);
        m.put("window_s", (last - first) / (double) SEC);
        m.put("latest_s", latestSec);
        m.put("sec", sec);
        checks.add(m);
        System.out.printf(Locale.ROOT, "CHECK %s: %d gets (every key at the latest time, %d keys at %d times in a"
                + " window of %.0f s), %.1f s%n", what, gets, keys.length, checkTimes, (last - first) / (double) SEC, sec);
        System.out.flush();
    }

    boolean checkOne(String what, int k, long t, GetData gd) {
        gd.actualLookupTime = -1;
        byte[] got;
        try {
            got = db.getOne(t, segs(k), gd);
        } catch (Throwable e) {
            fail(what + ": get(" + k + ", " + t + ") failed: " + e);
            e.printStackTrace(System.out);
            return false;
        }
        long at = gd.actualLookupTime;
        if (at < modelKeep) {
            fail(what + ": get(" + k + ", " + t + ") at " + at + ", before the model's keep time " + modelKeep);
            return false;
        }
        int v = modelAt(k, at);
        if (!valueOk(k, v, got)) {
            fail(what + ": key " + k + " at " + at + ": expected " + (v <= 0 ? "no value" : "version " + v)
                    + ", got " + describe(got));
            return false;
        }
        return true;
    }

    /** A cold restart: sync, close, open from the directory, start; then the check. */
    void restart(int index) throws IOException {
        Map<String, Object> m = new LinkedHashMap<String, Object>();
        double up0 = uptimeSec();
        long firstBefore = db.getFirstAvailableLookupTime();
        long lastBefore = db.lookupTime(Long.MAX_VALUE);
        double closeSec, startSec;
        StartInfo si;
        synchronized (dbLock) {
            harvestStats(index - 1);
            long t0 = System.nanoTime();
            db.sync(SyncLevel.STRONG);
            db.close();
            closeSec = 1e-9 * (System.nanoTime() - t0);
            long t1 = System.nanoTime();
            db = openDb();
            si = db.start();
            startSec = 1e-9 * (System.nanoTime() - t1);
            db.setRetainDuration(retainSec * SEC);
            enableStats();
        }
        lastCompleted = db.lookupTime(Long.MAX_VALUE);
        long firstAfter = db.getFirstAvailableLookupTime();
        m.put("index", (long) index);
        m.put("uptime_s", up0);
        m.put("close_s", closeSec);
        m.put("startup_s", startSec);
        m.put("transactions_rerun", (long) si.transCount);
        m.put("section_mb", (db.getStreamLength() - si.startPos) / 1e6);
        m.put("stream_mb", db.getStreamLength() / 1e6);
        m.put("first_available_pos_mb", db.getFirstAvailablePos() / 1e6);
        m.put("first_lookup_age_s", firstAfter == 0 ? null : (Object) ((lastCompleted - firstAfter) / (double) SEC));
        m.put("first_lookup_moved_s", (firstAfter - firstBefore) / (double) SEC);
        m.put("last_time_moved_s", (lastCompleted - lastBefore) / (double) SEC);
        restartInfo.add(m);
        System.out.printf(Locale.ROOT, "RESTART %d: closed in %.2f s, started in %.2f s (%d transactions rerun), first"
                + " available lookup time %s%n", index, closeSec, startSec, si.transCount, firstAfter == 0 ? "none (no cut)"
                : String.format(Locale.ROOT, "%.0f s old", (lastCompleted - firstAfter) / (double) SEC));
        System.out.flush();
        if (firstAfter < firstBefore) {
            fail("restart " + index + ": the first available lookup time moved back from " + firstBefore + " to " + firstAfter);
        }
        if (failure.get() == null) check("restart" + index);
        m.put("pause_s", uptimeSec() - up0);
    }

    // ---- The sampler ----

    final class Sampler extends Thread {
        final List<double[]> rows = new ArrayList<double[]>();
        final List<Object> physicalCutTimes = new ArrayList<Object>();
        volatile boolean stop;
        volatile int physicalCuts;
        long firstPosSeen = -1;
        double heapUsedMax, heapAfterMax, rssMax = -1, diskMax, filesMax, keptMax, dirtyMax = -1, dirtyMsMax = -1;
        long lastDirty = System.nanoTime(), lastProgress = System.nanoTime();
        int samples;

        Sampler() {
            setDaemon(true);
            setName("soak-sampler");
        }

        public void run() {
            long last = System.nanoTime();
            while (!stop) {
                try {
                    Thread.sleep(20);
                } catch (InterruptedException e) {
                    return;
                }
                try {
                    synchronized (dbLock) {
                        pollCuts();
                        if (System.nanoTime() - last >= sampleMs * 1000000L) {
                            last = System.nanoTime();
                            sample();
                        }
                    }
                } catch (Throwable e) {
                    fail("sampler: " + e);
                    e.printStackTrace(System.out);
                    return;
                }
                if (System.nanoTime() - lastProgress >= 60 * NS) {
                    lastProgress = System.nanoTime();
                    progress();
                }
            }
        }

        /** A physical cut is a move of the FileStream's first position: whole files were deleted. */
        void pollCuts() {
            long firstPos = stream.getFirstPos();
            if (firstPosSeen >= 0 && firstPos != firstPosSeen) {
                physicalCuts++;
                physicalCutTimes.add(Arrays.<Object>asList(uptimeSec(), firstPos / 1e6));
            }
            firstPosSeen = firstPos;
        }

        void sample() {
            Db d = db;
            double heapUsed = PerfUtil.heapUsedMB();
            double heapAfter = heapAfterLatestGcMB();
            long[] gc = PerfUtil.gcTotals();
            long len = d.getStreamLength();
            long firstAvail = d.getFirstAvailablePos();
            long disk = 0;
            int files = 0;
            File[] fs = dir.listFiles();
            if (fs != null) {
                for (File f : fs) {
                    if (f.getName().endsWith(".bergdb")) { disk += f.length(); files++; }
                }
            }
            double rss = samples % 10 == 0 ? PerfUtil.rssBytes() / 1e6 : -1;
            double dirty = -1, dirtyMs = -1;
            if (dirtyEverySec > 0 && System.nanoTime() - lastDirty >= dirtyEverySec * NS) {
                lastDirty = System.nanoTime();
                dirty = dirtyCount(d);
                dirtyMs = 1e-6 * (System.nanoTime() - lastDirty);
            }
            samples++;
            heapUsedMax = Math.max(heapUsedMax, heapUsed);
            heapAfterMax = Math.max(heapAfterMax, heapAfter);
            rssMax = Math.max(rssMax, rss);
            diskMax = Math.max(diskMax, disk);
            filesMax = Math.max(filesMax, files);
            keptMax = Math.max(keptMax, len - firstAvail);
            dirtyMax = Math.max(dirtyMax, dirty);
            dirtyMsMax = Math.max(dirtyMsMax, dirtyMs);
            rows.add(new double[] {uptimeSec(), heapUsed, heapAfter, gc[0], gc[1], len / 1e6, firstAvail / 1e6,
                    disk / 1e6, files, rss, dirty, dirtyMs, commits});
        }

        double dirtyCount(Db d) {
            final long[] c = new long[1];
            synchronized (d.internal().getWriteLock()) {
                TransSeq seq = d.internal().transSeq();
                seq.visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
                    public void node(bergdb.dag.Node node, long tpos, long lastTpos) { c[0]++; }
                });
            }
            return c[0];
        }

        long commitsAtLastProgress;

        /** A line a minute; the reclaim counts are read without the write lock (approximate). */
        void progress() {
            double[] l;
            long age;
            synchronized (dbLock) {
                if (rows.isEmpty()) return;
                l = rows.get(rows.size() - 1);
                long first = db.getFirstAvailableLookupTime();
                age = first == 0 ? -1 : (lastCompleted - first) / SEC;
            }
            long c = commits;
            Reclaim.Stats rs = rstats;
            System.out.printf(Locale.ROOT, "PROGRESS %.0f s: %d commits (%d in the last minute), stream %.0f MB, kept %.0f MB,"
                    + " on disk %.0f MB in %d files, iterations %d, cut decisions %d, physical cuts %d, first lookup time"
                    + " %d s old, heap after GC %.0f MB, expired %d + %d, unverifiable %d%n",
                    l[0], c, c - commitsAtLastProgress, l[5], l[5] - l[6], l[7], (int) l[8], iterations.size()
                    + rs.iterations.size(), cutDecisions.size() + rs.cuts.size(), physicalCuts, age, l[2],
                    expiredAtAdmission.get(), expiredDuring.get(), unverifiable.get());
            System.out.flush();
            commitsAtLastProgress = c;
        }

        void finish() {
            stop = true;
            interrupt();
            try { join(); } catch (InterruptedException e) { /* done */ }
            synchronized (dbLock) {
                sample();
            }
        }
    }

    // ---- The run ----

    Sampler sampler;

    /** After an exception: what is known, so that a failed run (out of memory, say) can be read. */
    void writePartial() {
        try {
            Map<String, Object> result = new LinkedHashMap<String, Object>();
            result.put("ok", false);
            result.put("failure", failure.get());
            result.put("partial", true);
            result.put("params", W);
            result.put("phases", phases);
            result.put("windows_uptime_s", windows);
            result.put("metrics", metrics);
            result.put("restarts", restartInfo);
            result.put("checks", checks);
            if (sampler != null) {
                sampler.stop = true;
                List<Object> samples = new ArrayList<Object>();
                synchronized (dbLock) {
                    for (double[] row : sampler.rows) {
                        List<Object> l = new ArrayList<Object>();
                        for (double v : row) l.add(v);
                        samples.add(l);
                    }
                    result.put("physical_cuts", new ArrayList<Object>(sampler.physicalCutTimes));
                }
                result.put("samples", samples);
            }
            File out = new File(outDir);
            out.mkdirs();
            PerfUtil.writeFile(new File(out, "result.json"), Json.write(result));
        } catch (Throwable e) {
            System.out.println("could not write the partial result: " + e);
        }
    }

    void run() throws Exception {
        Map<String, Object> info = new LinkedHashMap<String, Object>();
        info.put("jvm", PerfUtil.jvmInfo());
        info.put("jvmStartEpochMs", jvmStartMs);
        System.out.println("SOAK " + W);
        prepareDir();
        db = openDb();
        db.start();
        info.put("startupDistanceBytes", (long) db.getStartupDistance());
        enableStats();
        load();

        db.setRetainDuration(retainSec * SEC);
        sampler = new Sampler();
        sampler.start();

        // The warm-up: the workload, not measured, until the first physical cut.
        long w0 = System.nanoTime();
        double wu0 = uptimeSec();
        List<Reader> readers = startReaders(seed + 1);
        Random rnd = new Random(seed + 17);
        Pacer pacer = new Pacer();
        while (failure.get() == null) {
            long el = System.nanoTime() - w0;
            if (el >= warmupSec * NS && (sampler.physicalCuts > 0 || el >= warmupMaxSec * NS)) break;
            pacer.await(false);
            transaction(rnd, false);
        }
        stopReaders(readers);
        phase("warmup", w0, wu0);
        metrics.put("warmup.physical_cuts", (long) sampler.physicalCuts);

        // The measured phase: new readers (fresh histograms), restarts at fractions of the time.
        int cutsAtStart = sampler.physicalCuts;
        long commitsAtStart = commits, putsAtStart = puts, deletesAtStart = deletes;
        long lenAtStart = db.getStreamLength();
        long appendedBeforeRestarts = 0;
        long[] gc0 = PerfUtil.gcTotals();
        long m0 = System.nanoTime();
        double mu0 = uptimeSec();
        secondsBase = m0;
        readers = startReaders(seed + 2);
        int restartsDone = 0;
        long pausedNs = 0;
        pacer.restartClock();
        while (failure.get() == null) {
            long steady = System.nanoTime() - m0 - pausedNs;
            boolean timeDone = steady >= measureSec * NS;
            boolean cutsDone = sampler.physicalCuts - cutsAtStart >= minCuts;
            if (timeDone && cutsDone && restartsDone >= restarts) break;
            if (steady >= (long) (measureSec + extendSec) * NS) {
                fail("the measured phase reached its extension with " + (sampler.physicalCuts - cutsAtStart)
                        + " physical cuts (wanted " + minCuts + ") and " + restartsDone + " restarts (wanted " + restarts + ")");
                break;
            }
            if (restartsDone < restarts && steady >= measureSec * NS * (restartsDone + 1) / (restarts + 1)) {
                long p0 = System.nanoTime();
                pauseReaders(readers);
                if (failure.get() != null) break;
                appendedBeforeRestarts += db.getStreamLength() - lenAtStart;
                restart(++restartsDone);
                lenAtStart = db.getStreamLength();
                resumeReaders();
                long p1 = System.nanoTime();
                pausedNs += p1 - p0;
                pausedSeconds.add(new long[] {(p0 - m0) / NS, (p1 - m0) / NS});
                pacer.restartClock();
                continue;
            }
            pacer.await(true);
            transaction(rnd, true);
        }
        double measuredWall = 1e-9 * (System.nanoTime() - m0);
        double measuredSteady = measuredWall - 1e-9 * pausedNs;
        phases.put("measured", measuredWall);
        phases.put("measured_steady", measuredSteady);
        windows.put("measured", Arrays.<Object>asList(mu0, uptimeSec()));
        resumeReaders();
        stopReaders(readers);
        long[] gc1 = PerfUtil.gcTotals();
        long appended = appendedBeforeRestarts + db.getStreamLength() - lenAtStart;

        // The end check, with the readers stopped.
        if (failure.get() == null) check("end");
        sampler.finish();
        harvestStats(restartsDone);
        long t0 = System.nanoTime();
        db.sync(SyncLevel.STRONG);
        db.close();
        phases.put("close", 1e-9 * (System.nanoTime() - t0));

        // The result.
        long mCommits = commits - commitsAtStart;
        long mPuts = puts - putsAtStart, mDeletes = deletes - deletesAtStart;
        double userBytes = (double) mPuts * (4 + valsize);
        metrics.put("measured.steady_s", measuredSteady);
        metrics.put("measured.wall_s", measuredWall);
        metrics.put("commits", mCommits);
        metrics.put("commits_per_s", mCommits / measuredSteady);
        metrics.put("puts", mPuts);
        metrics.put("deletes", mDeletes);
        metrics.put("paced", rate > 0);
        metrics.put("updates_per_key_per_retention", (mPuts + mDeletes) / measuredSteady * retainSec / total);
        metrics.put("stream_appended_mb", appended / 1e6);
        metrics.put("bytes_appended_per_user_byte", appended / userBytes);
        metrics.put("commits_with_reclaim_step", stepCommits);
        metrics.put("commits_with_cut_decision", cutCommits);
        metrics.put("physical_cuts", (long) (sampler.physicalCuts - cutsAtStart));
        metrics.put("physical_cuts_total", (long) sampler.physicalCuts);
        metrics.put("cut_decisions_total", (long) cutDecisions.size());
        metrics.put("restarts", (long) restartsDone);
        metrics.put("expired_at_admission", expiredAtAdmission.get());
        metrics.put("expired_during", expiredDuring.get());
        metrics.put("unverifiable_skipped", unverifiable.get());
        metrics.put("gc.mxbean.count", gc1[0] - gc0[0]);
        metrics.put("gc.mxbean.ms", gc1[1] - gc0[1]);
        metrics.put("heap_used_max_mb", sampler.heapUsedMax);
        metrics.put("heap_after_gc_max_mb", sampler.heapAfterMax);
        metrics.put("rss_max_mb", sampler.rssMax);
        metrics.put("disk_max_mb", sampler.diskMax / 1e6);
        metrics.put("files_max", sampler.filesMax);
        metrics.put("kept_max_mb", sampler.keptMax / 1e6);
        metrics.put("dirty_nodes_max", sampler.dirtyMax);
        metrics.put("dirty_count_ms_max", sampler.dirtyMsMax);
        Hist latest = new Hist(), historical = new Hist(), fwd = new Hist(), bwd = new Hist();
        long getsOk = 0, scansOk = 0, kvs = 0;
        for (Reader r : readers) {
            latest.add(r.latest); historical.add(r.historical); fwd.add(r.fwd); bwd.add(r.bwd);
            getsOk += r.getsOk; scansOk += r.scansOk; kvs += r.kvsChecked;
        }
        metrics.put("gets_checked", getsOk);
        metrics.put("scans_checked", scansOk);
        metrics.put("scan_kvs_checked", kvs);
        metrics.put("reads_per_s", (getsOk + scansOk) / measuredSteady);
        Map<String, Object> lat = new LinkedHashMap<String, Object>();
        lat.put("commit_append_ns", commitAppend.summary());
        lat.put("commit_append_reclaim_step_ns", commitStep.summary());
        lat.put("commit_append_no_step_ns", commitPlain.summary());
        lat.put("commit_durable_ns", commitDurable.summary());
        lat.put("pacing_delay_ns", commitDelay.summary());
        lat.put("get_latest_ns", latest.summary());
        lat.put("get_historical_ns", historical.summary());
        lat.put("scan_forward_ns", fwd.summary());
        lat.put("scan_backward_ns", bwd.summary());
        Map<String, Object> hists = new LinkedHashMap<String, Object>();
        hists.put("commit_append_ns", commitAppend.sparse());
        hists.put("commit_durable_ns", commitDurable.sparse());
        hists.put("get_latest_ns", latest.sparse());
        hists.put("get_historical_ns", historical.sparse());
        hists.put("scan_forward_ns", fwd.sparse());
        hists.put("scan_backward_ns", bwd.sparse());
        // Commits per second of the measured phase; the slowest full second outside the restarts.
        int secs = (int) Math.min(perSecond.length, Math.ceil(measuredWall));
        long slowestSecond = Long.MAX_VALUE;
        List<Object> perSec = new ArrayList<Object>();
        for (int i = 0; i < secs; i++) {
            perSec.add(perSecond[i]);
            boolean paused = false;
            for (long[] p : pausedSeconds) paused |= i >= p[0] && i <= p[1];
            if (i < secs - 1 && !paused) slowestSecond = Math.min(slowestSecond, perSecond[i]);
        }
        metrics.put("commits_slowest_second", slowestSecond == Long.MAX_VALUE ? -1 : slowestSecond);
        List<Object> ps = new ArrayList<Object>();
        for (long[] p : pausedSeconds) ps.add(Arrays.<Object>asList(p[0], p[1]));
        metrics.put("restart_seconds", ps);

        Map<String, Object> result = new LinkedHashMap<String, Object>();
        result.put("ok", failure.get() == null);
        result.put("failure", failure.get());
        result.put("params", W);
        result.put("info", info);
        result.put("phases", phases);
        result.put("windows_uptime_s", windows);
        result.put("metrics", metrics);
        result.put("latency", lat);
        result.put("slowest_commits", Arrays.<Object>asList("ms, uptime s, commit, reclaim stepped, cut decided",
                slowAppend.json()));
        result.put("slowest_durable_commits", Arrays.<Object>asList("ms, uptime s, commit, reclaim stepped, cut decided",
                slowDurable.json()));
        result.put("cut_decisions", Arrays.<Object>asList("uptime s, segment, pos MB, age of the new first time s,"
                + " stream length MB", cutDecisions));
        result.put("physical_cuts", Arrays.<Object>asList("uptime s, first pos MB", sampler.physicalCutTimes));
        result.put("reclaim_iterations", Arrays.<Object>asList("start uptime s, end uptime s, segment, steps, kvs,"
                + " values rewritten, value MB, record MB, start pos MB", iterations));
        result.put("restarts", restartInfo);
        result.put("checks", checks);
        result.put("commits_per_second", perSec);
        List<Object> samples = new ArrayList<Object>();
        for (double[] row : sampler.rows) {
            List<Object> l = new ArrayList<Object>();
            for (double v : row) l.add(v);
            samples.add(l);
        }
        result.put("samples", Arrays.<Object>asList("uptime s, heap used MB, heap after GC MB, GC count, GC ms,"
                + " stream MB, first available MB, disk MB, files, rss MB, dirty nodes, dirty count ms, commits", samples));
        result.put("histograms_sparse", hists);
        File out = new File(outDir);
        out.mkdirs();
        PerfUtil.writeFile(new File(out, "result.json"), Json.write(result));
        System.out.printf(Locale.ROOT, "SOAK %s: %.0f s steady, %d commits (%.1f/s), %d gets and %d scans checked,"
                + " %d physical cuts, %d restarts, expired %d at admission and %d during%n",
                failure.get() == null ? "OK" : "FAILED", measuredSteady, mCommits, mCommits / measuredSteady, getsOk,
                scansOk, sampler.physicalCuts - cutsAtStart, restartsDone, expiredAtAdmission.get(), expiredDuring.get());
        System.out.flush();
    }

    // ---- Soak finish OUT: the GC log ----

    @SuppressWarnings("unchecked")
    static void finish(File out) throws IOException {
        File rf = new File(out, "result.json");
        Map<String, Object> r = Json.parseObject(PerfUtil.readFile(rf));
        GcLog g = GcLog.read(new File(out, "gc.log"));
        Map<String, Object> gc = new LinkedHashMap<String, Object>();
        gc.put("whole", g.summary(0, 1e12));
        Map<String, Object> w = (Map<String, Object>) r.get("windows_uptime_s");
        if (w != null) {
            for (Map.Entry<String, Object> e : w.entrySet()) {
                List<Object> l = (List<Object>) e.getValue();
                gc.put(e.getKey(), g.summary(((Number) l.get(0)).doubleValue(), ((Number) l.get(1)).doubleValue()));
            }
        }
        List<Object> rs = (List<Object>) r.get("restarts");
        if (rs != null) {
            for (Object o : rs) {
                Map<String, Object> m = (Map<String, Object>) o;
                double from = ((Number) m.get("uptime_s")).doubleValue();
                Number p = (Number) m.get("pause_s");
                gc.put("restart" + m.get("index"), g.summary(from, from + (p == null ? 0 : p.doubleValue())));
            }
        }
        // The heap after each collection in the measured window: the first and last tenth, the peak.
        List<Object> mw = w == null ? null : (List<Object>) w.get("measured");
        if (mw != null) {
            double from = ((Number) mw.get(0)).doubleValue(), to = ((Number) mw.get(1)).doubleValue();
            double tenth = (to - from) / 10;
            double a = 0, b = 0, peak = 0;
            int na = 0, nb = 0;
            for (double[] h : g.heapAfter) {
                if (h[0] < from || h[0] > to) continue;
                peak = Math.max(peak, h[1]);
                if (h[0] < from + tenth) { a += h[1]; na++; }
                if (h[0] > to - tenth) { b += h[1]; nb++; }
            }
            Map<String, Object> hm = new LinkedHashMap<String, Object>();
            hm.put("first_tenth_mean_mb", na == 0 ? null : (Object) (a / na));
            hm.put("last_tenth_mean_mb", nb == 0 ? null : (Object) (b / nb));
            hm.put("peak_mb", peak);
            gc.put("heap_after_gc_measured", hm);
        }
        r.put("gcLog", gc);
        // The pauses that overlap the slowest commits.
        for (String key : new String[] {"slowest_commits", "slowest_durable_commits"}) {
            List<Object> sl = (List<Object>) r.get(key);
            if (sl == null || sl.size() < 2) continue;
            List<Object> withOverlap = new ArrayList<Object>();
            for (Object o : (List<Object>) sl.get(1)) {
                List<Object> e = new ArrayList<Object>((List<Object>) o);
                double ms = ((Number) e.get(0)).doubleValue();
                double end = ((Number) e.get(1)).doubleValue();
                e.add(overlap(g, end - ms / 1000.0, end));
                withOverlap.add(e);
            }
            r.put(key + "_with_pauses", withOverlap);
        }
        PerfUtil.writeFile(rf, Json.write(r));
        Map<String, Object> sum = (Map<String, Object>) gc.get(mw == null ? "whole" : "measured");
        Map<String, Object> pm = (Map<String, Object>) sum.get("pauses");
        Map<String, Object> sm = (Map<String, Object>) sum.get("safepoints");
        System.out.printf(Locale.ROOT, "FINISH %s: GC pauses in the measured phase: %s, total %.0f ms, max %.1f ms;"
                + " safepoints: %s, max %.1f ms%n", rf, pm.get("count"), ((Number) pm.get("totalMs")).doubleValue(),
                ((Number) pm.get("maxMs")).doubleValue(), sm.get("count"), ((Number) sm.get("maxMs")).doubleValue());
    }

    /** The GC pauses and safepoints (1 ms or more) that overlap [from, to] (uptime, s). */
    static String overlap(GcLog g, double from, double to) {
        StringBuilder sb = new StringBuilder();
        for (GcLog.Event e : g.pauses) {
            if (e.uptimeSec >= from - 0.002 && e.uptimeSec - e.ms / 1000.0 <= to + 0.002) {
                sb.append(String.format(Locale.ROOT, "GC pause %s %.1f ms; ", e.what, e.ms));
            }
        }
        for (GcLog.Event e : g.safepoints) {
            if (e.ms < 1) continue;
            if (e.uptimeSec >= from - 0.002 && e.uptimeSec - e.ms / 1000.0 <= to + 0.002) {
                sb.append(String.format(Locale.ROOT, "safepoint %s %.1f ms; ", e.what, e.ms));
            }
        }
        return sb.length() == 0 ? "none" : sb.toString().trim();
    }

    public static void main(String[] args) throws Exception {
        if (args.length == 2 && args[0].equals("finish")) {
            finish(new File(args[1]));
            return;
        }
        Soak s = new Soak();
        try {
            s.run();
        } catch (Throwable e) {
            s.fail("the run: " + e);
            e.printStackTrace(System.out);
            s.writePartial();
        }
        System.out.flush();
        System.exit(s.failure.get() == null ? 0 : 1);
    }
}
