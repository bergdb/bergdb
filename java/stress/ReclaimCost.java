package bergdb.core;

import java.io.File;
import java.util.*;

import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.pub.util.Clock;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.FileStream;

/**
 * The cost of reclaim (level 3), written 2026-10-13, revised the same day with Frans's
 * measures (bergdb 011-04, "Level 3 cost"):
 *
 *   WE, write efficiency = user bytes written / stream bytes appended, over the
 *       transactions from the first cut to the end. User bytes are key + value, as given
 *       by the user. Reclaim's rewrites count as overhead.
 *   SE, store efficiency = user bytes accessible / stream kept (stream length minus the
 *       first available position, the cut that reclaim decided). Accessible from now - R
 *       (what the user asked for, SE) or from the first available lookup time (what the
 *       database offers, SE offered). With one put per transaction and every key present,
 *       the user bytes accessible from time T are (n + the puts after T) * (key + value).
 *
 * The retention is given as K, the updates per key within the retention duration R: R
 * spans K * n single-put transactions, so the user bytes written during R are K times the
 * live user data. Time is simulated.
 *
 * Phases:
 *   1. Load: n keys in random order, 100 per transaction.
 *   2. Warm-up: n single-put transactions without reclaim.
 *   3. Reclaim on (unless k=0): single-put transactions until `cuts` cuts after the
 *      first, or (30 + 2K) n transactions. With k=0, 4 n transactions (at least 400,000),
 *      measured over the second half (the baseline). SE is sampled every 1000 transactions after the first
 *      cut.
 *   4. Restart, and check every key, and that the first available lookup time is at or
 *      before now - R.
 *
 * In phase 3 it also prints the first 12 user commits that write more than 200 index
 * nodes, with the state of the iteration then (bergdb 011-04, "Level 3 cost": large
 * steps of reclaim caused them, until steps were capped).
 *
 * In package bergdb.core to reach Db internals (Reclaim.Stats).
 *
 * Usage: java -Xmx8g [-Dprop=value ...] -cp bergdb.jar:. bergdb.core.ReclaimCost
 *
 * Properties:
 *   live=N      Live user data in bytes (default 30000000); n = live / (4 + valsize).
 *   valsize=N   Value size in bytes, at least 8 (default 1000). Keys are 4 bytes.
 *   work=W      uniform (default): puts on random keys; hot: 90% of the puts on the first
 *               1% of the keys; cold: all puts on the first 10% of the keys, so 90% of the
 *               data never changes after the load.
 *   k=X         Updates per key within R (default 1); 0: no reclaim (the baseline).
 *   sd=N        Startup distance in bytes (default 0.2 times live).
 *   f=X         internalFraction (default: Reclaim's).
 *   cuts=N      Cuts measured after the first (default 6).
 *   disk=1      A FileStream in dir (default build/reclaimcost-NANOS), instead of a
 *               CutStream in memory. Deleted at the end.
 *   touchstats=0  Do not count the touch (the counting costs time in the writer).
 *   window=N    Print WE over every N transactions of phase 3 (default 0: no).
 */
public class ReclaimCost {
    final int valsize = Math.max(8, Integer.getInteger("valsize", 1000));
    final long liveProp = Long.getLong("live", 30000000L);
    final int n = (int) (liveProp / (4 + valsize));
    final int kvSize = 4 + valsize;
    final long live = (long) n * kvSize;
    final String work = System.getProperty("work", "uniform");
    final String kProp = System.getProperty("k", "1");
    final double k = Double.parseDouble(kProp);
    final int sd = Integer.getInteger("sd", (int) (0.2 * live));
    final String fProp = System.getProperty("f");
    final int cutsWanted = Integer.getInteger("cuts", 6);
    final boolean disk = "1".equals(System.getProperty("disk"));
    final boolean touchStats = !"0".equals(System.getProperty("touchstats"));
    final int window = Integer.getInteger("window", 0);
    final File dir = new File(System.getProperty("dir", "build/reclaimcost-" + System.nanoTime()));

    /** Transactions in R, and the time between transactions; R is at least 1 s. */
    final long rTrans;
    final long tstep;
    final long r;

    /** The tail target (bergdb 011-04, W4.2): index nodes in one user commit. */
    static final long TAIL_TARGET_INDEX_NODES = 200;

    final Random rnd = new Random(1);
    final CoreTestClock clock = new CoreTestClock();
    long time = Clock.UNITS_PER_SEC;
    final int[] version;
    CutStream cutStream;
    AppendOnlyStream stream;
    Db db;

    // User transactions, from the listener: index nodes written.
    long indexNodes, maxIndexNodes;
    int bigCommits;
    Reclaim.Stats statsForDebug;

    // The records of the stream (Reclaim.Stats.Record) when the steady period started (2026-10-13,
    // bergdb 011-04, W4.1), to take the records of the period by subtraction.
    Reclaim.Stats.Record user0, step0, table0;

    void snapshot(Reclaim.Stats stats) {
        user0 = stats.user.copy();
        step0 = stats.step.copy();
        table0 = stats.table.copy();
    }

    // After each single-put transaction (phases 2 and 3): its time, the stream length,
    // and the puts so far.
    long[] times = new long[1 << 20], lens = new long[1 << 20], puts = new long[1 << 20];
    int records;
    long putCount;

    ReclaimCost() {
        version = new int[n];
        rTrans = Math.max(1, Math.round(k * n));
        tstep = Math.max(Clock.UNITS_PER_SEC / 1000, (Clock.UNITS_PER_SEC + rTrans - 1) / rTrans);
        r = k == 0 ? 0 : rTrans * tstep;
    }

    final Trans.Listener listener = new Trans.Listener() {
        public void transExecuted(Db.ExecuteData x) {
            TransNodes tn = x.transNodes;
            int index = tn.topCount + tn.keyCount;
            indexNodes += index;
            if (index > maxIndexNodes) maxIndexNodes = index;
            if (index > 200 && statsForDebug != null && bigCommits++ < 12) {
                Reclaim.Stats st = statsForDebug;
                Reclaim.Stats.Iteration it = st.iterations.isEmpty() ? null
                        : st.iterations.get(st.iterations.size() - 1);
                System.out.printf("  big commit: transaction %d wrote %d index nodes at %.1f MB;"
                        + " iteration from %.1f MB, %d steps%s, cuts %d%n", records, index,
                        x.trans.tpos / 1e6, it == null ? -1.0 : it.pStart / 1e6,
                        it == null ? 0 : it.steps, it != null && it.pEnd >= 0
                        ? String.format(" (done at %.1f MB)", it.pEnd / 1e6) : "",
                        st.cuts.size());
            }
        }

        public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}
    };

    Db start(boolean create) throws java.io.IOException {
        if (disk) {
            if (create) {
                dir.mkdirs();
                for (File f : dir.listFiles()) f.delete();
            }
            stream = new FileStream(dir);
        } else {
            cutStream = cutStream == null ? new CutStream() : cutStream.copy();
            stream = cutStream;
        }
        DbBuilder b = Db.builder().stream("main", stream).clock(clock).noEvict()
                .retainForever().testId().startupDistance(sd);
        return b.build();
    }

    byte[] key(int i) {
        return KeyFactory.binaryIntKey(i);
    }

    byte[] value(int key, int v) {
        byte[] b = new byte[valsize];
        b[0] = (byte) (key >>> 24); b[1] = (byte) (key >>> 16); b[2] = (byte) (key >>> 8); b[3] = (byte) key;
        b[4] = (byte) (v >>> 24); b[5] = (byte) (v >>> 16); b[6] = (byte) (v >>> 8); b[7] = (byte) v;
        for (int i = 8; i < valsize; i++) b[i] = (byte) (key + v + i);
        return b;
    }

    int pick() {
        if (work.equals("hot")) {
            return rnd.nextInt(100) < 90 ? rnd.nextInt(Math.max(1, n / 100)) : rnd.nextInt(n);
        } else if (work.equals("cold")) {
            return rnd.nextInt(Math.max(1, n / 10));
        }
        return rnd.nextInt(n);
    }

    void execute(Trans.Builder b) {
        time += tstep;
        clock.setTime(time);
        Trans t = b.build();
        t.listener = listener;
        db.execute(t);
    }

    /** One single-put transaction; records it. Returns its latency, ns. */
    long update() {
        int key = pick();
        version[key]++;
        Trans.Builder b = db.trans().put(key(key), value(key, version[key]));
        long s = System.nanoTime();
        execute(b);
        long lat = System.nanoTime() - s;
        putCount++;
        if (records == times.length) {
            times = Arrays.copyOf(times, records * 2);
            lens = Arrays.copyOf(lens, records * 2);
            puts = Arrays.copyOf(puts, records * 2);
        }
        times[records] = time;
        lens[records] = db.getStreamLength();
        puts[records] = putCount;
        records++;
        return lat;
    }

    /** Index of the last record at or before time t, or -1. */
    int recordAt(long t) {
        if (records == 0 || times[0] > t) return -1;
        int lo = 0, hi = records - 1;
        while (lo < hi) {
            int mid = (lo + hi + 1) >>> 1;
            if (times[mid] <= t) lo = mid; else hi = mid - 1;
        }
        return lo;
    }

    /** User bytes accessible from time t: every key's version at t and every put after. */
    long accessibleFrom(long t) {
        int i = recordAt(t);
        long after = putCount - (i < 0 ? 0 : puts[i]);
        return (n + after) * kvSize;
    }

    void run() throws java.io.IOException {
        System.out.println("ReclaimCost work=" + work + " valsize=" + valsize + " n=" + n
                + " live=" + live + " k=" + kProp + " sd=" + sd + " f="
                + (fProp == null ? "default" : fProp) + " cuts=" + cutsWanted
                + " disk=" + disk + " touchstats=" + touchStats);
        db = start(true);
        db.start();

        // Phase 1: load.
        int[] perm = new int[n];
        for (int i = 0; i < n; i++) perm[i] = i;
        for (int i = n - 1; i > 0; i--) {
            int j = rnd.nextInt(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < n; i += 100) {
            Trans.Builder b = db.trans();
            for (int j = i; j < Math.min(n, i + 100); j++) {
                version[perm[j]] = 1;
                b.put(key(perm[j]), value(perm[j], 1));
            }
            execute(b);
        }
        System.out.printf("LOAD %d keys, live user data %.1f MB, stream %.1f MB (SE %.3f)%n",
                n, live / 1e6, db.getStreamLength() / 1e6,
                (double) live / db.getStreamLength());

        // Phase 2: warm-up.
        long p0 = db.getStreamLength();
        for (int i = 0; i < n; i++) update();
        System.out.printf("WARM-UP %d transactions: WE %.3f; R = %.1f s, %d transactions%n",
                n, (double) n * kvSize / (db.getStreamLength() - p0), r / 1e7, rTrans);

        // Phase 3.
        Reclaim.Stats stats = db.internal().reclaim().enableStats();     // Also for k = 0: records.
        if (k > 0) {
            if (fProp != null) db.setReclaimInternalFraction(Double.parseDouble(fProp));
            stats.countTouch = touchStats;
            statsForDebug = stats;
            db.setRetainDuration(r);
        }
        final long startTrans = records;
        final long maxTrans = k == 0 ? Math.max(4L * n, 400000) : (long) ((30 + 2 * k) * n);
        long[] lat = new long[1 << 20];
        int latCount = 0;
        int cutsSeen = 0;
        long firstLen = -1, firstPuts = 0, firstNanos = 0, firstTrans = 0, firstIdx = 0;
        double sumSe = 0, sumSeOff = 0, sumKept = 0, minSe = Double.MAX_VALUE;
        double sumDiskRatio = 0, maxDiskRatio = 0;
        long maxKept = 0, samples = 0;
        double sumG = 0;
        int gCount = 0;
        long prevCutPos = -1;
        long winLen = db.getStreamLength(), winPuts = putCount;
        String stop = null;

        while (stop == null) {
            long l = update();
            long done = records - startTrans;
            if (firstLen >= 0) {
                if (latCount == lat.length) lat = Arrays.copyOf(lat, latCount * 2);
                lat[latCount++] = l;
            }
            if (window > 0 && done % window == 0) {
                long len = db.getStreamLength();
                System.out.printf("  at %d: stream %.1f MB, kept %.1f MB, WE %.3f over the "
                        + "last %d transactions%n", done, len / 1e6,
                        (len - db.getFirstAvailablePos()) / 1e6,
                        (double) (putCount - winPuts) * kvSize / (len - winLen), window);
                winLen = len;
                winPuts = putCount;
            }
            if (k == 0) {
                if (done == maxTrans / 2) {
                    firstLen = db.getStreamLength();
                    firstPuts = putCount;
                    firstNanos = System.nanoTime();
                    firstTrans = records;
                    firstIdx = indexNodes;
                    maxIndexNodes = 0;
                    snapshot(stats);
                }
                if (done >= maxTrans) stop = "transactions";
                continue;
            }

            List<Reclaim.Stats.Cut> cuts = stats.cuts;
            while (cutsSeen < cuts.size()) {
                Reclaim.Stats.Cut c = cuts.get(cutsSeen++);
                int ri = recordAt(c.decidedTime - r);
                long windowStart = ri < 0 ? lens[0] : lens[ri];
                String line = String.format("  cut %d at %.1f MB: kept %.1f MB = window %.1f "
                        + "+ slack %.1f", cutsSeen, c.pos / 1e6, (c.decidedAt - c.pos) / 1e6,
                        (c.decidedAt - windowStart) / 1e6, (windowStart - c.pos) / 1e6);
                if (prevCutPos >= 0) {
                    line += String.format(", gap %.1f MB", (c.pos - prevCutPos) / 1e6);
                    sumG += c.pos - prevCutPos;
                    gCount++;
                }
                System.out.println(line);
                prevCutPos = c.pos;
                if (firstLen < 0) {
                    firstLen = db.getStreamLength();
                    firstPuts = putCount;
                    firstNanos = System.nanoTime();
                    firstTrans = records;
                    firstIdx = indexNodes;
                    maxIndexNodes = 0;
                    snapshot(stats);
                }
            }
            if (cutsSeen >= cutsWanted + 1) stop = "cuts";
            if (done >= maxTrans) stop = "transactions";

            if (firstLen >= 0 && (records - firstTrans) % 1000 == 0) {
                long len = db.getStreamLength();
                long kept = len - db.getFirstAvailablePos();
                double se = (double) accessibleFrom(time - r) / kept;
                double seOff = (double) accessibleFrom(db.getFirstAvailableLookupTime()) / kept;
                sumSe += se;
                sumSeOff += seOff;
                minSe = Math.min(minSe, se);
                sumKept += kept;
                maxKept = Math.max(maxKept, kept);
                samples++;
                if (disk) {
                    // FileStream deletes whole files (bergdb 011-04, W5d): the disk
                    // holds the kept stream plus the part of the first file before the cut.
                    long onDisk = 0;
                    for (File f : dir.listFiles()) onDisk += f.length();
                    sumDiskRatio += (double) onDisk / kept;
                    maxDiskRatio = Math.max(maxDiskRatio, (double) onDisk / kept);
                }
            }
        }
        double sec = 1e-9 * (System.nanoTime() - firstNanos);
        long steadyTrans = records - firstTrans;
        long endLen = db.getStreamLength();
        double we = firstLen < 0 ? Double.NaN
                : (double) (putCount - firstPuts) * kvSize / (endLen - firstLen);
        double p999 = Double.NaN;

        System.out.printf("STOP (%s) after %d transactions in phase 3%n", stop,
                records - startTrans);
        if (firstLen < 0) {
            System.out.println("NO CUT");
        } else {
            long[] s = Arrays.copyOf(lat, latCount);
            Arrays.sort(s);
            p999 = s[(int) (s.length * 0.999)] / 1e3;
            System.out.printf("STEADY (%s, %d transactions): WE %.3f, %.0f transactions/s, "
                    + "index nodes per user transaction %.2f (max %d), latency p50 %.1f us, "
                    + "p99.9 %.1f us, max %.2f ms%n",
                    k == 0 ? "second half" : "from the first cut", steadyTrans, we,
                    steadyTrans / sec, (double) (indexNodes - firstIdx) / steadyTrans,
                    maxIndexNodes, s[s.length / 2] / 1e3, p999, s[s.length - 1] / 1e6);
        }
        if (firstLen >= 0) {
            System.out.printf("TAIL TARGET: most index nodes in one user commit %d (target at "
                    + "most %d): %s%n", maxIndexNodes, TAIL_TARGET_INDEX_NODES,
                    maxIndexNodes <= TAIL_TARGET_INDEX_NODES ? "met" : "EXCEEDED");
        }
        if (samples > 0) {
            System.out.printf("STORE: SE %.3f (min %.3f), SE offered %.3f; stream kept mean "
                    + "%.1f MB, max %.1f MB; mean cut gap %.1f MB%n", sumSe / samples, minSe,
                    sumSeOff / samples, sumKept / samples / 1e6, maxKept / 1e6,
                    gCount > 0 ? sumG / gCount / 1e6 : Double.NaN);
            if (disk) {
                System.out.printf("DISK: bytes on disk / stream kept: mean %.3f, max %.3f%n",
                        sumDiskRatio / samples, maxDiskRatio);
            }
        }

        // Where the stream bytes of the steady period went, per user put (2026-10-13, W4.1).
        // Index nodes are counted in the record that writes them, not by who made them dirty.
        double uBytes = Double.NaN, uVal = Double.NaN, uIdx = Double.NaN, sBytes = Double.NaN,
                tBytes = Double.NaN, otherBytes = Double.NaN;
        if (firstLen >= 0 && user0 != null) {
            double puts = putCount - firstPuts;
            Reclaim.Stats.Record u = stats.user.minus(user0);
            Reclaim.Stats.Record sr = stats.step.minus(step0);
            Reclaim.Stats.Record tr = stats.table.minus(table0);
            uBytes = u.bytes / puts;
            uVal = u.valueBytes / puts;
            uIdx = u.indexBytes / puts;
            sBytes = sr.bytes / puts;
            tBytes = tr.bytes / puts;
            double records = u.bytes + sr.bytes + tr.bytes;
            otherBytes = (endLen - firstLen - records) / puts;
            System.out.printf("BYTES per user put (%.0f user bytes), steady period:%n"
                    + "  user records:   %.1f = values %.1f + index %.1f (%.2f nodes) + other %.1f%n"
                    + "  reclaim steps:  %.1f = values %.1f + index %.1f (%.2f nodes) + other %.1f%n"
                    + "  table records:  %.1f = values %.1f + index %.1f (%.2f nodes) + other %.1f%n"
                    + "  meta blocks and the rest: %.1f%n",
                    (double) kvSize, uBytes, uVal, uIdx, u.indexNodes / puts, u.otherBytes() / puts,
                    sBytes, sr.valueBytes / puts, sr.indexBytes / puts, sr.indexNodes / puts,
                    sr.otherBytes() / puts, tBytes, tr.valueBytes / puts, tr.indexBytes / puts,
                    tr.indexNodes / puts, tr.otherBytes() / puts, otherBytes);
        }

        double rewritten = Double.NaN, tableMB = Double.NaN;
        long maxStepDirtied = -1;
        int iters = 0;
        if (stats != null) {
            double kvs = 0, vals = 0, tab = 0, vis = 0, dirt = 0, min = 0, span = 0;
            double stepDirt = 0, stepDirtBytes = 0, steps = 0, valBytes = 0;
            long maxStepDirt = 0;
            for (Reclaim.Stats.Iteration it : stats.iterations) {
                if (it.pEnd < 0) continue;
                iters++;
                span += it.pEnd - it.pStart;
                kvs += it.kvs;
                vals += it.values;
                tab += it.tableBytes;
                vis += it.touch.visited;
                dirt += it.touch.dirtied;
                min += it.touch.minimal;
                stepDirt += it.dirtiedNodes;
                stepDirtBytes += it.dirtiedBytes;
                steps += it.steps;
                valBytes += it.valueBytes + 28 * it.values;
                maxStepDirt = Math.max(maxStepDirt, it.maxStepDirtied);
            }
            if (iters > 0) {
                rewritten = vals / Math.max(1, kvs);
                tableMB = tab / iters / 1e6;
                System.out.printf("ITERATIONS: %d done; per iteration: span %.1f MB, values "
                        + "rewritten %.0f%% of the KVs, table stored %.2f MB; touch: made dirty "
                        + "%.0f of %.0f index nodes visited, old ones and ancestors %.0f%n",
                        iters, span / iters / 1e6, 100 * rewritten, tableMB, dirt / iters,
                        vis / iters, min / iters);
                System.out.printf("  steps: %.0f per iteration; index nodes made dirty per step "
                        + "%.1f (max %d), %.1f MB per iteration, against %.1f MB of value nodes%n",
                        steps / iters, stepDirt / Math.max(1, steps), maxStepDirt,
                        stepDirtBytes / iters / 1e6, valBytes / iters / 1e6);
                maxStepDirtied = maxStepDirt;
            }
        }

        // Phase 4: restart and check.
        db.sync(SyncLevel.STRONG);
        long firstTime = db.getFirstAvailableLookupTime();
        db.close();
        db = start(false);
        db.start();
        GetData gd = db.newGetData();
        for (int i = 0; i < n; i++) {
            byte[] got = db.getOne(Long.MAX_VALUE, Keys.toSegments(key(i)), gd);
            if (!Arrays.equals(value(i, version[i]), got)) {
                throw new AssertionError("wrong value for key " + i + " after restart");
            }
        }
        if (k > 0 && firstTime > time - r) {
            throw new AssertionError("first available lookup time " + firstTime
                    + " is inside the retention window");
        }
        db.close();
        if (disk) {
            for (File f : dir.listFiles()) f.delete();
            dir.delete();
        }

        System.out.printf(Locale.ROOT, "RESULT work=%s valsize=%d k=%s f=%s n=%d stop=%s "
                + "cuts=%d WE=%.4f SE=%.4f SEmin=%.4f SEoff=%.4f keptMB=%.1f tps=%.0f "
                + "p999us=%.0f maxIdx=%d rewritten=%.3f tableMB=%.3f iters=%d maxStepDirtied=%d "
                + "uB=%.1f uVal=%.1f uIdx=%.1f sB=%.1f tB=%.1f otherB=%.1f diskRatio=%.3f%n",
                work, valsize, kProp, fProp == null ? "default" : fProp, n,
                stop, cutsSeen, we, samples > 0 ? sumSe / samples : Double.NaN,
                samples > 0 ? minSe : Double.NaN, samples > 0 ? sumSeOff / samples : Double.NaN,
                samples > 0 ? sumKept / samples / 1e6 : Double.NaN,
                firstLen < 0 ? Double.NaN : steadyTrans / sec, p999, maxIndexNodes,
                rewritten, tableMB, iters, maxStepDirtied,
                uBytes, uVal, uIdx, sBytes, tBytes, otherBytes,
                disk && samples > 0 ? sumDiskRatio / samples : Double.NaN);
        System.out.println("RECLAIMCOST OK");
    }

    public static void main(String[] args) throws Exception {
        new ReclaimCost().run();
    }
}
