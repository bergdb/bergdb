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
 *
 * Every database is a FileStream in dir with the builder's defaults (startup distance 50
 * MB, cache indicator 200 MB), a test clock (dt time units a transaction) and
 * Reclaim.Stats on; each is closed and deleted at the end. In package bergdb.core to reach
 * Db internals (Reclaim.Stats, the maintenance follower).
 *
 * Usage, from java/ after build.sh (count-gates.sh runs it):
 *   java -Xmx4g -cp build/bergdb.jar:build/stress bergdb.core.CountGates [g1|g2|g3|all]
 *       [prop=value...]
 * Properties: n=1000000 (keys), valsize=100, retain=1 (seconds of the test clock),
 *   dt=10000 (time units a transaction; R is then 1,000 transactions), dir=build/count-gates-data,
 *   fifo=n*0.06 and overwrites=n*0.02 (G1's transactions), maxdrive=n/20 (G2's most
 *   overwrite transactions a shape), g3batch=10 (puts a G3 transaction), cuts=3 (G3),
 *   g3max=n*2 (G3's most transactions). Exits with status 1 if a gate fails.
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
            this.label = label;
            dir = new File(base, label);
            rm(dir);
            dir.mkdirs();
            clock.setTime(time);
            try {
                db = Db.builder().mainStream(new FileStream(dir)).clock(clock).start();
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

    static void rm(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) rm(c);
        f.delete();
    }

    public static void main(String[] args) throws IOException {
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
        rm(x.base);
        out(x.el() + (x.failed ? " COUNT GATES FAILED" : " COUNT GATES OK"));
        System.exit(x.failed ? 1 : 0);
    }
}
