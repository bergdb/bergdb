package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.util.*;

import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.PointerFollower;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * Count gates of aims 2 and 3 of release 2026.5 at 1M keys (bergdb 024-30, which defines
 * each quantity; the bounds are 024-05, section 4). Gates on counts (bytes, key nodes), not
 * on times (024-05, QF6). Built from three probes: CleanupRule's counting follower and twin
 * (023-03, sections 2 and 3), PF1's records and drives (024-03) and ReclaimCost's stream
 * kept under reclaim. Each gate prints one line
 *     Gx BDy QUANTITY value V limit L margin M PASS|FAIL
 * where margin is limit / value (above 1 passes); detail lines start with two spaces.
 *
 *   G1 (BD1, a commit's record): keys put in time order with a retain duration R and
 *      reclaim on (a fill in key order, then a FIFO: 100 new keys after every key and 100
 *      deletes of the oldest a transaction; the shape of the last touch, 024-07), then
 *      random overwrites. For every record written, x = its stream bytes minus the bytes
 *      of the value nodes in it (the transaction's own values: the user's puts, or the
 *      values a reclaim step rewrites). Passes when the largest x is at most the larger of
 *      1 MB and 5 times the mean x of the run's records.
 *   G2 (BD13, the reachable index): a random fill, then (a) delete all keys but every
 *      30th, (b) delete the first 90 % of the keys (a mass delete), each on its own
 *      database; overwrites of random live keys until two reclaim iterations that started
 *      after the deletes are complete. Then the key nodes that a scan of every user key
 *      follows, against a twin: a new database with the same live keys put in key order,
 *      100 a transaction, R forever. Passes when both are at most 2 times the twin's.
 *   G3 (BD10, the stream kept): a random fill (L0: the stream length after it, a twin's
 *      fresh stream, as the live keys and value sizes do not change after), then R and
 *      overwrites of random keys, small transactions. From the end of the first reclaim
 *      iteration until the third cut: after each transaction, kept (stream length minus
 *      the first available position) minus H_R, the bytes of the user's records committed
 *      at or after now - R. Passes when the peak is at most 6 times L0.
 *   G4 (back to empty; 023-03's T1, the hello-world convergence test, at n keys): put
 *      "/a.txt", fill n keys in key order and delete them all, 100 a transaction, with R
 *      and a startup distance of 100 kB (the builder's default cache, eviction on); then
 *      a drive of 40 R of overwrites of "/a.txt" (1,000 bytes). Against a twin that skips
 *      the fill and the deletes: kept (the most in the last R), the reachable key nodes,
 *      their dead KEY klongs, the resident index objects, the live handles, the cache
 *      tables' slots (ST6; counted since its fix, 024-33) and the heap after a GC, each
 *      at most 2 times the twin's. KeyAccessPath's arrays (ST7) are
 *      printed, not gated. Needs --add-opens java.base/java.util (the slots are
 *      HashMap's table lengths).
 *   G5 (back to empty by maintain(); bergdb 024-32, 023-03 T1's second drive): G4's
 *      emptied database and twin, each driven by g5drive calls of Db.maintain() (20 R), one
 *      every dt of the test clock, with no writes. Kept (the most in the last R) at most
 *      twice the twin's plus 600,000 bytes (maintain()'s release threshold and a filler,
 *      Reclaim.MAINTAIN_MIN_RELEASE and META_BLOCK_DISTANCE); the last call that returned
 *      true within the first 3/4 of the drive (converged, then quiet); as the twin is tiny,
 *      the key nodes, resident objects and handles at most the larger of twice the twin's
 *      and the twin's plus 10 (023-03's a_n), the dead KEY klongs the larger of twice the
 *      twin's and the twin's plus 30 (023-03's C4: B); the heap at most 2 times the twin's, as
 *      G4; the cache's table slots (ST6) at most the larger of twice the twin's and the
 *      tables' floor since 024-33, 2^MAP_BITS maps of Table.MIN_CAPACITY slots.
 *
 * Every database is a FileStream in dir with the builder's defaults (startup distance 50
 * MB, cache indicator 200 MB), a test clock (dt time units a transaction) and
 * Reclaim.Stats on; each is closed and deleted at the end. In package bergdb.core to reach
 * Db internals (Reclaim.Stats, the maintenance follower).
 *
 * Usage, from java/ after build.sh (count-gates.sh runs it):
 *   java -Xmx4g -cp build/bergdb.jar:build/stress bergdb.core.CountGates [g1|...|g5|all]
 *       [prop=value...]
 * Properties: n=1000000 (keys), valsize=100, retain=1 (seconds of the test clock),
 *   dt=10000 (time units a transaction; R is then 1,000 transactions), dir=build/count-gates-data,
 *   fifo=n*0.06 and overwrites=n*0.02 (G1's transactions), maxdrive=n/20 (G2's most
 *   overwrite transactions a shape), g3batch=10 (puts a G3 transaction), cuts=3 (G3),
 *   g3max=n*2 (G3's most transactions), g4drive=40000 (40 R), g4sd=100000, g4evict=0 (no
 *   eviction in G4 and G5), g4kept, g4nodes, g4slots, g4heap (G4's factors, 2; G5's but
 *   kept), g5drive=20000 (20 R). Exits with status 1 if a gate fails.
 */
public class CountGates {
    static final long SEC = Clock.UNITS_PER_SEC;
    static final long MB = 1000000;

    final Map<String, String> p = new HashMap<String, String>();
    int i(String k, int d) { return p.containsKey(k) ? Integer.parseInt(p.get(k)) : d; }
    long l(String k, long d) { return p.containsKey(k) ? Long.parseLong(p.get(k)) : d; }
    String s(String k, String d) { return p.containsKey(k) ? p.get(k) : d; }

    final long t0 = System.nanoTime();
    int n, vs;
    long dt, retain;
    File base;
    boolean failed;

    static void out(String s) {
        System.out.println(s);
        System.out.flush();
    }

    String el() { return String.format("[%.1fs]", (System.nanoTime() - t0) / 1e9); }

    static String key(int i) { return String.format("/k/%010d", i); }

    static byte[] value(int size, long tag) {
        byte[] v = new byte[size];
        for (int j = 0; j < size; j++) v[j] = (byte) ('a' + (tag + j) % 26);
        for (int j = 0; j < 8 && j < size; j++) v[j] = (byte) (tag >>> (8 * j));
        return v;
    }

    void gate(String name, String quantity, double value, double limit, String fmt) {
        boolean pass = value <= limit;
        if (!pass) failed = true;
        out(String.format(Locale.ROOT, "%s %s value " + fmt + " limit " + fmt
                + " margin %.2f %s", name, quantity, value, limit,
                value == 0 ? Double.POSITIVE_INFINITY : limit / value, pass ? "PASS" : "FAIL"));
    }

    // ======== One database ========

    /** A database on a FileStream in its own directory, a test clock and Reclaim.Stats. */
    final class Run {
        final String label;
        final File dir;
        final CoreTestClock clock = new CoreTestClock();
        long time = 10 * SEC;
        final Db db;
        final Reclaim.Stats stats;

        // Records (Reclaim.Stats.Record, by who wrote them: user, step, table) seen so far,
        // [category][records, bytes, value bytes], and G1's measure over them.
        final long[][] prev = new long[3][3];
        long records, sumX, maxX, together;
        String maxWhere = "";

        Run(String label) {
            this(label, 0);
        }

        /** With sd > 0: that startup distance, no eviction and the test id (G4, T1's). */
        Run(String label, int sd) {
            this.label = label;
            dir = new File(base, label);
            rm(dir);
            dir.mkdirs();
            clock.setTime(time);
            try {
                DbBuilder b = Db.builder().mainStream(new FileStream(dir)).clock(clock);
                if (sd > 0) b.startupDistance(sd).testId();     // G4
                if (sd > 0 && i("g4evict", 1) == 0) b.noEvict();
                db = b.start();
            } catch (IOException e) {
                throw new java.io.UncheckedIOException(e);
            }
            synchronized (db.internal().getWriteLock()) {
                stats = db.internal().reclaim().enableStats();
            }
        }

        /** One transaction at the next time; then its records accounted. */
        void exec(Trans.Builder b, String where) {
            time += dt;
            clock.setTime(time);
            db.execute(b.build());
            account(where);
        }

        /**
         * The records written since the last call, from Reclaim.Stats: for each, x = bytes -
         * value node bytes. If one call saw two or more records of the same writer (user,
         * reclaim step, table), they are counted as one of their summed size, which can only
         * make the largest larger (counted in 'together').
         */
        void account(String where) {
            Reclaim.Stats.Record[] rs = {stats.user, stats.step, stats.table};
            for (int c = 0; c < 3; c++) {
                Reclaim.Stats.Record r = rs[c];
                long dr = r.records - prev[c][0];
                if (dr == 0) continue;
                long x = (r.bytes - prev[c][1]) - (r.valueBytes - prev[c][2]);
                records += dr;
                sumX += x;
                if (dr > 1) together++;
                if (x > maxX) {
                    maxX = x;
                    maxWhere = where + ", " + new String[] {"user", "step", "table"}[c]
                            + (dr > 1 ? " (" + dr + " records together)" : "");
                }
                prev[c][0] = r.records;
                prev[c][1] = r.bytes;
                prev[c][2] = r.valueBytes;
            }
        }

        long kept() { return db.getStreamLength() - db.getFirstAvailablePos(); }

        /** Reclaim iterations complete that started at or after stream position p. */
        int itersDoneFrom(long p) {
            int c = 0;
            for (Reclaim.Stats.Iteration it : stats.iterations) {
                if (it.pStart >= p && it.pEnd >= 0) c++;
            }
            return c;
        }

        String state() {
            return String.format("len=%d kept=%d iters=%d cuts=%d", db.getStreamLength(), kept(),
                    db.getReclaimIterationCount(), stats.cuts.size());
        }

        /** The key nodes and user keys that a scan of every user key follows. */
        long[] scanNodes() {
            synchronized (db.internal().getWriteLock()) {
                Count c = new Count(db.internal().nodeCollection().maintenance());
                GetMany g = db.newGetMany();
                g.gd.pointerFollower = c;
                g.startKey = Keys.toSegments("/k/");
                g.inclusive = true;
                Counter k = new Counter();
                g.stopCondition = k;
                db.getMany(g);
                return new long[] {c.ids.size(), k.keys, c.keyKlongs, c.keyKlongs - c.live};
            }
        }

        void close() {
            db.sync(SyncLevel.ORDINARY);
            db.close();
            rm(dir);
        }
    }

    /** CleanupRule's (023-03) counting follower: key nodes by id, KEY klongs, live ones. */
    static final class Count implements PointerFollower {
        final PointerFollower inner;
        final HashSet<Long> ids = new HashSet<Long>();
        long keyKlongs, live;

        Count(PointerFollower inner) { this.inner = inner; }

        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node r = inner.followPointer(predecessor, pointerIndex, op);
            if (r instanceof KeyNode && ids.add(r.getId())) {
                KeyNode kn = (KeyNode) r;
                int sz = kn.getSize();
                long del = kn.getDeleteBitmapAtTime(Klong.MAX_TIME, sz);
                for (int i = 0; i < sz; i++) {
                    long k = kn.getKlong(i);
                    if (!Klong.isKey(k)) continue;
                    keyKlongs++;
                    if (Klong.isDeleted(del, i)) continue;
                    long cv = Klong.getCompareValue(k);
                    boolean shadowed = false;
                    for (int j = i + 1; j < sz && !shadowed; j++) {
                        long k2 = kn.getKlong(j);
                        shadowed = Klong.isKey(k2) && Klong.getCompareValue(k2) == cv;
                    }
                    if (!shadowed) live++;
                }
            }
            return r;
        }
    }

    /** Counts the KVs of a scan from "/k/" (the user keys; internal ones are "/#..."). */
    static final class Counter implements GetMany.StopCondition {
        long keys;
        public int handleKvt(Kvt kvt) {
            keys++;
            return CONTINUE;
        }
        public void eod() {}
    }

    /** Puts the keys of 'idx' in that order, 'batch' a transaction. */
    void fill(Run r, int[] idx, int batch, String where) {
        for (int k = 0; k < idx.length; ) {
            Trans.Builder b = r.db.trans();
            for (int j = 0; j < batch && k < idx.length; j++, k++) {
                b.put(key(idx[k]), value(vs, idx[k]));
            }
            r.exec(b, where);
        }
    }

    static void shuffle(int[] a, long seed) {
        Random rnd = new Random(seed);
        for (int k = a.length - 1; k > 0; k--) {
            int j = rnd.nextInt(k + 1);
            int t = a[k]; a[k] = a[j]; a[j] = t;
        }
    }

    static int[] range(int from, int to) {
        int[] a = new int[to - from];
        for (int k = 0; k < a.length; k++) a[k] = from + k;
        return a;
    }

    // ======== G1 ========

    void g1() {
        int fifo = i("fifo", (int) (n * 0.06)), ow = i("overwrites", (int) (n * 0.02));
        Run r = new Run("g1");
        r.db.setRetainDuration(retain);
        fill(r, range(0, n), 100, "fill in key order");
        out(el() + "   G1 fill " + r.state());
        // The FIFO: keys in time order, live keys oldest .. next - 1.
        int next = n, oldest = 0;
        for (int k = 0; k < fifo; k++) {
            Trans.Builder b = r.db.trans();
            for (int j = 0; j < 100; j++, next++) b.put(key(next), value(vs, next));
            for (int j = 0; j < 100; j++, oldest++) b.delete(key(oldest));
            r.exec(b, "FIFO transaction " + (k + 1));
        }
        out(el() + "   G1 FIFO " + fifo + " transactions " + r.state());
        Random rnd = new Random(3);
        for (int k = 0; k < ow; k++) {
            Trans.Builder b = r.db.trans();
            for (int j = 0; j < 100; j++) {
                int x = oldest + rnd.nextInt(next - oldest);
                b.put(key(x), value(vs, x + k));
            }
            r.exec(b, "overwrite transaction " + (k + 1));
        }
        r.db.sync(SyncLevel.ORDINARY);
        r.account("the end");
        long[] sc = r.scanNodes();
        out(el() + "   G1 overwrites " + ow + " transactions " + r.state() + " keys=" + sc[1]);
        if (sc[1] != next - oldest) {
            throw new AssertionError("G1: " + sc[1] + " keys, expected " + (next - oldest));
        }
        double mean = (double) r.sumX / r.records;
        out(String.format("  G1 records=%d mean=%.0f largest=%d (%s) together=%d",
                r.records, mean, r.maxX, r.maxWhere, r.together));
        r.close();
        gate("G1", "BD1 largest record without its values, bytes", r.maxX,
                Math.max(1.0 * MB, 5 * mean), "%.0f");
    }

    // ======== G2 ========

    double g2Shape(String shape, int[] live) {
        int maxDrive = i("maxdrive", n / 20);
        Run r = new Run("g2-" + shape);
        r.db.setRetainDuration(retain);
        int[] all = range(0, n);
        shuffle(all, 1);
        fill(r, all, 100, "fill");
        out(el() + "   G2 " + shape + " fill " + r.state());
        boolean[] isLive = new boolean[n];
        for (int x : live) isLive[x] = true;
        Trans.Builder b = r.db.trans();
        int inB = 0;
        for (int k = 0; k < n; k++) {
            if (isLive[k]) continue;
            b.delete(key(k));
            if (++inB == 100) {
                r.exec(b, "delete");
                b = r.db.trans();
                inB = 0;
            }
        }
        if (inB > 0) r.exec(b, "delete");
        long pDel = r.db.getStreamLength();
        long[] before = r.scanNodes();
        out(el() + "   G2 " + shape + " deleted, live=" + live.length + " keyNodes=" + before[0]
                + " " + r.state());
        Random rnd = new Random(11);
        int k;
        for (k = 1; k <= maxDrive && r.itersDoneFrom(pDel) < 2; k++) {
            Trans.Builder d = r.db.trans();
            for (int j = 0; j < 100; j++) {
                int x = live[rnd.nextInt(live.length)];
                d.put(key(x), value(vs, x + k));
            }
            r.exec(d, "drive");
        }
        int iters = r.itersDoneFrom(pDel);
        long[] sc = r.scanNodes();
        out(String.format("%s   G2 %s drive %d transactions, %d iterations after the deletes; %s",
                el(), shape, k - 1, iters, r.state()));
        if (sc[1] != live.length) {
            throw new AssertionError("G2 " + shape + ": " + sc[1] + " keys, expected "
                    + live.length);
        }
        r.close();

        Run t = new Run("g2-" + shape + "-twin");
        fill(t, live, 100, "twin");
        long[] tw = t.scanNodes();
        t.close();
        double ratio = (double) sc[0] / tw[0];
        out(String.format("  G2 %s keyNodes=%d klongs=%d dead=%d twin keyNodes=%d ratio=%.3f%s",
                shape, sc[0], sc[2], sc[3], tw[0], ratio,
                iters < 2 ? " (FEWER THAN 2 ITERATIONS)" : ""));
        return iters < 2 ? Double.POSITIVE_INFINITY : ratio;
    }

    void g2() {
        int keep = 30;
        int[] sparse = new int[(n + keep - 1) / keep];
        for (int k = 0; k < sparse.length; k++) sparse[k] = k * keep;
        double a = g2Shape("sparse", sparse);
        double b = g2Shape("mass", range((int) (n * 0.9), n));
        gate("G2", "BD13 reachable key nodes over the twin's, worst shape", Math.max(a, b), 2,
                "%.3f");
    }

    // ======== G3 ========

    void g3() {
        int batch = i("g3batch", 10), cutsWanted = i("cuts", 3);
        long maxTx = l("g3max", 2L * n);
        Run r = new Run("g3");
        int[] all = range(0, n);
        shuffle(all, 1);
        fill(r, all, 100, "fill");
        r.db.sync(SyncLevel.ORDINARY);
        long l0 = r.db.getStreamLength();
        out(el() + "   G3 fill L0=" + l0 + " " + r.state());
        r.db.setRetainDuration(retain);

        // After transaction k: user record bytes so far and the stream length, in rings of
        // rTx + 2; the records at or after now - R are those of the last rTx + 1 transactions.
        int rTx = (int) (retain / dt);
        int ring = rTx + 2;
        long[] cumUser = new long[ring], lens = new long[ring];
        int[] ver = new int[n];
        Random rnd = new Random(5);
        long peak = -1, peakKept = 0, peakH = 0, peakSpan = 0, peakTx = 0;
        long k;
        for (k = 1; k <= maxTx; k++) {
            Trans.Builder b = r.db.trans();
            for (int j = 0; j < batch; j++) {
                int x = rnd.nextInt(n);
                ver[x]++;
                b.put(key(x), value(vs, x + 7L * ver[x]));
            }
            r.exec(b, "overwrites");
            cumUser[(int) (k % ring)] = r.stats.user.bytes;
            lens[(int) (k % ring)] = r.db.getStreamLength();
            if (k <= rTx + 1) continue;
            Reclaim.Stats.Iteration first =
                    r.stats.iterations.isEmpty() ? null : r.stats.iterations.get(0);
            if (first == null || first.pEnd < 0) continue;
            long older = (k - rTx - 1) % ring;
            long h = cumUser[(int) (k % ring)] - cumUser[(int) older];
            long kept = r.kept();
            if (kept - h > peak) {
                peak = kept - h;
                peakKept = kept;
                peakH = h;
                peakSpan = lens[(int) (k % ring)] - lens[(int) older];
                peakTx = k;
            }
            if (r.stats.cuts.size() >= cutsWanted) break;
        }
        int cuts = r.stats.cuts.size();
        out(String.format("%s   G3 %d transactions of %d puts, R = %d transactions; %s",
                el(), Math.min(k, maxTx), batch, rTx, r.state()));
        for (int c = 0; c < 2000; c++) {
            int x = rnd.nextInt(n);
            byte[] got = r.db.getOne(Long.MAX_VALUE, Keys.toSegments(key(x)), r.db.newGetData());
            byte[] want = ver[x] == 0 ? value(vs, x) : value(vs, x + 7L * ver[x]);
            if (!Arrays.equals(want, got)) throw new AssertionError("G3: wrong value, key " + x);
        }
        out(String.format("  G3 peak at transaction %d: kept=%d H_R=%d (all records within R: "
                + "%d) kept-H_R=%d L0=%d; cuts=%d", peakTx, peakKept, peakH, peakSpan, peak, l0,
                cuts));
        r.close();
        double v = peak < 0 || cuts < cutsWanted ? Double.POSITIVE_INFINITY : (double) peak / l0;
        gate("G3", "BD10 (stream kept - H_R) / L0, peak", v, 6, "%.3f");
    }

    // ======== G4 ========

    static final byte[] HELLO = "Hello world!".getBytes(java.nio.charset.StandardCharsets.UTF_8);

    /** G4's measures of one database at the end of its drive. */
    static final class G4M {
        long keptMax, reach, klongs, dead, objects, handles, slots, heap, userKeys;
        int pathKlongs, pathNodes;
        long firstCut = -1, lag = -1, kept4R = -1;     // drive transactions; kept at 4 R
        // G5: the last call that returned true, the calls that wrote, the most bytes and
        // records of a call, the bytes of the drive.
        long lastMore = -1, writingCalls, maxCallBytes, maxCallRecords, driveBytes;

        String line() {
            return String.format("keptMax=%d reach=%d klongs=%d dead=%d objects=%d handles=%d "
                    + "slots=%d heap=%d pathKlongs=%d pathNodes=%d userKeys=%d", keptMax, reach,
                    klongs, dead, objects, handles, slots, heap, pathKlongs, pathNodes, userKeys);
        }
    }

    /**
     * The heap gates of G4 and G5 compare each heap plus the 10 MB write buffer (2026-11-13,
     * bergdb 026-07): until then every database held the whole buffer from its start, in the
     * twin's heap and the emptied database's alike, and the gates and their factor 2 were set
     * on that. Since 026-07 the buffer grows with use and shrinks after an idle second, and
     * the heap is measured after the shrink; without the constant the emptied database held
     * 2.0 (G4) and 3.7 (G5) times its twin's heap, mostly NodeCollection.idByPos, an LRU of
     * up to 100,000 node ids (026-07, section 6). The lines print the heaps without it.
     */
    static final long BUFFER = bergdb.storage.StorageManager.DEFAULT_BUFFER_SIZE;

    static long usedHeap() {
        Runtime rt = Runtime.getRuntime();
        for (int k = 0; k < 4; k++) System.gc();
        return rt.totalMemory() - rt.freeMemory();
    }

    static Object field(Object o, String name) throws ReflectiveOperationException {
        java.lang.reflect.Field f = o.getClass().getDeclaredField(name);
        f.setAccessible(true);
        return f.get(o);
    }

    /**
     * T1 of 023-03 (section 2) on one database: create, R, put "/a.txt"; fill nn keys in key
     * order and delete them all, 100 a transaction; the drive, overwrites of "/a.txt"; then
     * the measures. heap0 is the heap after a GC before the database was made. twinKept: the
     * twin's M1, to find the lag, the first drive transaction after which kept is at most
     * twice it (0 for the twin itself).
     */
    G4M g4Run(String label, int nn, long heap0, long twinKept)
            throws ReflectiveOperationException {
        return g4Run("G4", label, nn, heap0, twinKept, false);
    }

    /**
     * G4's run (gate "G4"), or G5's (gate "G5", byMaintain): the drive is then maintain()
     * calls, one every dt of the test clock (023-03, T1's second drive; bergdb 024-32), g5drive
     * of them (20 R).
     */
    G4M g4Run(String gate, String label, int nn, long heap0, long twinKept, boolean byMaintain)
            throws ReflectiveOperationException {
        int sd = i("g4sd", 100000), dvs = i("g4dvalsize", 1000);
        int rTx = (int) (retain / dt);
        int drive = byMaintain ? i("g5drive", 20 * rTx) : i("g4drive", 40 * rTx);
        Run r = new Run(label, sd);
        r.db.setRetainDuration(retain);
        r.exec(r.db.trans().put("/a.txt", HELLO), "create");
        if (nn > 0) {
            fill(r, range(0, nn), 100, "fill");
            for (int k = 0; k < nn; ) {
                Trans.Builder b = r.db.trans();
                for (int j = 0; j < 100 && k < nn; j++, k++) b.delete(key(k));
                r.exec(b, "delete");
            }
            out(el() + "   " + gate + " " + label + " filled and deleted " + nn + " keys; "
                    + r.state());
        }
        G4M m = new G4M();
        int cuts0 = r.stats.cuts.size();
        long len0 = r.db.getStreamLength();
        for (int k = 1; k <= drive; k++) {
            if (byMaintain) {
                r.time += dt;
                r.clock.setTime(r.time);
                long len = r.db.getStreamLength();
                long recs = r.stats.user.records + r.stats.step.records + r.stats.table.records;
                if (r.db.maintain()) m.lastMore = k;
                long grown = r.db.getStreamLength() - len;
                if (grown > 0) m.writingCalls++;
                m.maxCallBytes = Math.max(m.maxCallBytes, grown);
                m.maxCallRecords = Math.max(m.maxCallRecords, r.stats.user.records
                        + r.stats.step.records + r.stats.table.records - recs);
            } else {
                r.exec(r.db.trans().put("/a.txt", value(dvs, k)), "drive");
            }
            long kept = r.kept();
            if (k >= drive - rTx) m.keptMax = Math.max(m.keptMax, kept);
            if (k == 4 * rTx) m.kept4R = kept;
            if (m.firstCut < 0 && r.stats.cuts.size() > cuts0) m.firstCut = k;
            if (twinKept > 0 && kept > 2 * twinKept) m.lag = -1;
            else if (twinKept > 0 && m.lag < 0) m.lag = k;
        }
        m.driveBytes = r.db.getStreamLength() - len0;
        out(el() + "   " + gate + " " + label + " drive " + drive
                + (byMaintain ? " maintain() calls; " : " transactions; ") + r.state()
                + " firstCut=" + m.firstCut + " lag=" + m.lag + " kept4R=" + m.kept4R
                + (byMaintain ? " lastTrue=" + m.lastMore + " writingCalls=" + m.writingCalls
                + " maxCallBytes=" + m.maxCallBytes + " maxCallRecords=" + m.maxCallRecords
                + " driveBytes=" + m.driveBytes : ""));
        synchronized (r.db.internal().getWriteLock()) {
            Count c = new Count(r.db.internal().nodeCollection().maintenance());
            GetMany g = r.db.newGetMany();
            g.gd.pointerFollower = c;
            r.db.getMany(g);
            m.reach = c.ids.size();
            m.klongs = c.keyKlongs;
            m.dead = c.keyKlongs - c.live;
            for (Kvt kvt : g.result) {
                if (!Keys.toString(kvt.key).startsWith("/#")) m.userKeys++;
            }
            Cache3 cache = r.db.internal().cache();
            m.objects = cache.residents().objects();
            m.handles = cache.handles().size();
            for (Object t : (Object[]) field(cache, "tables")) {
                Object[] table = (Object[]) field(field(t, "map"), "table");
                if (table != null) m.slots += table.length;
            }
            Object path = r.db.internal().x().putData.keyAccessPath;
            m.pathKlongs = ((long[]) field(path, "klongs")).length;
            m.pathNodes = ((Object[]) field(path, "nodes")).length;
        }
        // The write buffer grows with use and shrinks after a second with nothing to write
        // (2026-11-13, bergdb 026-07): the heap is measured after the shrink, so that the
        // emptied database and its twin are compared without the buffer's transient, as
        // when both held the whole 10 MB from their start. -Dg4heapwait=MS sets the wait, for
        // a class histogram of the database with jcmd during it.
        try {
            Thread.sleep(Long.getLong("g4heapwait", 2000));
        } catch (InterruptedException e) {
            throw new AssertionError(e);
        }
        m.heap = usedHeap() - heap0;
        if (m.userKeys != 1) throw new AssertionError(gate + " " + label + ": " + m.userKeys
                + " user keys, expected 1");
        r.close();
        out("  " + gate + " " + label + " " + m.line());
        return m;
    }

    void g4() throws ReflectiveOperationException {
        G4M t = g4Run("g4-twin", 0, usedHeap(), 0);
        G4M e = g4Run("g4-emptied", n, usedHeap(), t.keptMax);
        out(String.format("  G4 ST7, not gated (closed as negligible by Frans, 2026-11-12): "
                + "KeyAccessPath arrays %d klongs, %d nodes; the twin's %d, %d", e.pathKlongs,
                e.pathNodes, t.pathKlongs, t.pathNodes));
        g4Gate("M1 kept, most in the last R", e.keptMax, t.keptMax, d("g4kept", 2));
        g4Gate("M4 reachable key nodes", e.reach, t.reach, d("g4nodes", 2));
        g4Gate("M5 dead KEY klongs", e.dead, t.dead, d("g4nodes", 2));
        g4Gate("M11 resident index objects", e.objects, t.objects, d("g4nodes", 2));
        g4Gate("M11 live handles", e.handles, t.handles, d("g4nodes", 2));
        g4Gate("ST6 cache table slots", e.slots, t.slots, d("g4slots", 2));
        g4Gate("heap after a GC", e.heap + BUFFER, t.heap + BUFFER, d("g4heap", 2));
    }

    // ======== G5 ========

    /**
     * G5, back to empty by maintain() (bergdb 024-32): G4 with a drive of maintain() calls
     * instead of overwrites, against a twin driven the same way. Kept is held to twice the
     * twin's plus the allowance of maintain()'s design (024-32, section 2.2): the release
     * that an iteration begun by maintain() needs, and a filler; the rest as G4.
     */
    void g5() throws ReflectiveOperationException {
        G4M t = g4Run("G5", "g5-twin", 0, usedHeap(), 0, true);
        G4M e = g4Run("G5", "g5-emptied", n, usedHeap(), 0, true);
        long allowance = Reclaim.MAINTAIN_MIN_RELEASE 
                + bergdb.storage.RecoverableStream.META_BLOCK_DISTANCE;
        gate("G5", "M1 kept, most in the last R, over twice the twin's plus " + allowance
                + " (" + e.keptMax + " / " + t.keptMax + ")",
                (double) e.keptMax / (2 * t.keptMax + allowance), 1, "%.3f");
        gate("G5", "calls returning true, the last of " + i("g5drive", 20 * (int) (retain / dt))
                + " (" + e.lastMore + "), over 3/4 of the drive", 
                (double) e.lastMore / (0.75 * i("g5drive", 20 * (int) (retain / dt))), 1, 
                "%.3f");
        // G5's twin is tiny (4 key nodes, 5 objects): the counts are held to the larger of
        // twice the twin's and the twin's plus a_n = 10 (023-03, section 2.6, the strict
        // allowance of nodes); the dead klongs, of which the twin has none, to the twin's
        // plus B = 30, a leaf's klongs (023-03's C4).
        gateSmall("M4 reachable key nodes", e.reach, t.reach, 10);
        gateSmall("M5 dead KEY klongs", e.dead, t.dead, 30);
        gateSmall("M11 resident index objects", e.objects, t.objects, 10);
        gateSmall("M11 live handles", e.handles, t.handles, 10);
        // ST6: since 024-33 a map's table shrinks to at least Table.MIN_CAPACITY, and a map
        // once used keeps that table; the emptied database has used most of the 2^MAP_BITS
        // maps, the twin 5. So the floor of the tables, 4,096 maps of 16 slots, independent
        // of n, where twice the twin's is less (024-32, section 4).
        long floor = (long) Cache3.maps() * Cache3.Table.MIN_CAPACITY;
        long slotLimit = Math.max(2 * t.slots, floor);
        gate("G5", "ST6 cache table slots over the larger of twice the twin's and the tables' "
                + "floor " + floor + " (" + e.slots + " / " + t.slots + ")",
                (double) e.slots / slotLimit, 1, "%.3f");
        gateTwin("G5", "heap after a GC", e.heap + BUFFER, t.heap + BUFFER, d("g4heap", 2));
    }

    /** G5: emptied at most the larger of twice the twin's and the twin's plus 'plus'. */
    void gateSmall(String what, long emptied, long twin, long plus) {
        long limit = Math.max(2 * twin, twin + plus);
        gate("G5", what + " over the larger of twice the twin's and the twin's plus " + plus
                + " (" + emptied + " / " + twin + ")", (double) emptied / limit, 1, "%.3f");
    }

    void gateTwin(String name, String what, long emptied, long twin, double factor) {
        gate(name, what + " over the twin's (" + emptied + " / " + twin + ")",
                (double) emptied / Math.max(1, twin), factor, "%.3f");
    }

    double d(String k, double d) { return p.containsKey(k) ? Double.parseDouble(p.get(k)) : d; }

    void g4Gate(String what, long emptied, long twin, double factor) {
        gate("G4", what + " over the twin's (" + emptied + " / " + twin + ")",
                (double) emptied / Math.max(1, twin), factor, "%.3f");
    }

    static void rm(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) rm(c);
        f.delete();
    }

    public static void main(String[] args) throws Exception {
        CountGates x = new CountGates();
        String which = args.length > 0 && args[0].indexOf('=') < 0 ? args[0] : "all";
        for (String a : args) {
            int eq = a.indexOf('=');
            if (eq > 0) x.p.put(a.substring(0, eq), a.substring(eq + 1));
        }
        x.n = x.i("n", 1000000);
        x.vs = x.i("valsize", 100);
        x.dt = x.l("dt", 10000);
        x.retain = x.l("retain", 1) * SEC;
        x.base = new File(x.s("dir", "build/count-gates-data"));
        out("CountGates " + which + " n=" + x.n + " valsize=" + x.vs + " retain=" + x.retain
                + " dt=" + x.dt + " " + x.p);
        if (which.equals("all") || which.equals("g1")) x.g1();
        if (which.equals("all") || which.equals("g2")) x.g2();
        if (which.equals("all") || which.equals("g3")) x.g3();
        if (which.equals("all") || which.equals("g4")) x.g4();
        if (which.equals("all") || which.equals("g5")) x.g5();
        rm(x.base);
        out(x.el() + (x.failed ? " COUNT GATES FAILED" : " COUNT GATES OK"));
        System.exit(x.failed ? 1 : 0);
    }
}
