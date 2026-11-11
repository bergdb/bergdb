package bergdb.core;

import java.io.*;
import java.nio.file.*;
import java.util.*;

import bergdb.dag.Dag;
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
 * The probe of bergdb 024-14, written 2026-11-11: the thresholds of merges at the delete at 1M
 * and 10M keys. PF1's setup and fill (024-03): a FileStream with the builder's defaults, a
 * test clock (dt units a transaction), retain 1 s; keys "/k/%010d", values of 100 bytes, 100
 * KVs a transaction; the fill's random order is PF1's, so its counts are 024-03's on the same
 * jar. Compiled apart against each build; the Dag's counters are read by reflection.
 *
 * java -cp classes:JAR bergdb.core.THR run key=value...
 *   n          keys of the fill (keys 0..n-1)
 *   fill       seq | random
 *   shape      over: overwrites of random live keys, phase=TX transactions of 100
 *              keep: all keys deleted but i % keep == 0, order=asc | desc | hashed
 *              mass: keys i < 0.9 n deleted, ascending (024-03, section 4)
 *              churn: phase=TX transactions of 50 deletes of random live keys and 50 puts of
 *                     random keys of 0..2n-1 that are not live
 *   drive      transactions of 100 overwrites of random live keys after the shape (reclaim)
 *   twin=1     a fresh database of the live keys (key order after a seq fill, else random),
 *              then the same drive
 *   thrash     command: a sweep around one key (see thrash())
 */
public class THR {
    static final long SEC = Clock.UNITS_PER_SEC;
    final Map<String, String> p = new HashMap<String, String>();
    int i(String k, int d) { return p.containsKey(k) ? Integer.parseInt(p.get(k)) : d; }
    long l(String k, long d) { return p.containsKey(k) ? Long.parseLong(p.get(k)) : d; }
    String s(String k, String d) { return p.containsKey(k) ? p.get(k) : d; }

    final long t0 = System.nanoTime();
    File dir;
    CoreTestClock clock;
    long time = 10 * SEC;
    Db db;
    long dt = 10000;
    String tag = "";

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

    static long stat(String f) {
        try {
            return Dag.class.getField(f).getLong(null);
        } catch (NoSuchFieldException e) {
            return 0;
        } catch (IllegalAccessException e) {
            throw new RuntimeException(e);
        }
    }

    static String thr() {
        try {
            int[] t = (int[]) Dag.class.getMethod("thresholds", int.class).invoke(null, 30);
            return "m=" + t[0] + " h=" + t[1] + " c=" + t[2] + " merges=" + Dag.class.getField("MERGES").get(null);
        } catch (NoSuchMethodException e) {
            return "main (no merges)";
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    void open(String d) throws IOException {
        dir = new File(d);
        rm(dir);
        dir.mkdirs();
        clock = new CoreTestClock();
        time = 10 * SEC;
        clock.setTime(time);
        db = Db.builder().mainStream(new FileStream(dir)).clock(clock).start();
        db.setRetainDuration(l("retain", 1) * SEC);
    }

    void close() {
        db.sync(SyncLevel.ORDINARY);
        db.close();
        rm(dir);
    }

    long kept() { return db.getStreamLength() - db.getFirstAvailablePos(); }

    // ---- a phase: transactions, ops, bytes, splits, merges ----

    final class Phase {
        final String name;
        long tx, ops, rec, maxRec, len0, ts0, ss0, mg0, mg20, tb0, sl0, ns, it0;
        long[] execNs = new long[1 << 20];
        int execN;
        final long a = System.nanoTime();

        Phase(String name) {
            this.name = name;
            len0 = db.getStreamLength();
            ts0 = stat("statTimeSplits");
            ss0 = stat("statSpaceSplits");
            mg0 = stat("statMerges");
            mg20 = stat("statMergesTwo");
            tb0 = stat("statMergeTaken");
            sl0 = stat("statSiblingLoads");
            it0 = db.getReclaimIterationCount();
        }

        void exec(Trans.Builder b, int ops) {
            time += dt;
            clock.setTime(time);
            Trans t = b.build();
            long x = System.nanoTime();
            db.execute(t);
            long d = System.nanoTime() - x;
            if (execN < execNs.length) execNs[execN++] = d;
            tx++;
            this.ops += ops;
            long r = t.nextPos - t.tpos;
            rec += r;
            maxRec = Math.max(maxRec, r);
        }

        void end() {
            ns = System.nanoTime() - a;
            long[] s = Arrays.copyOf(execNs, execN);
            Arrays.sort(s);
            long p50 = s.length == 0 ? 0 : s[s.length / 2];
            long p999 = s.length == 0 ? 0 : s[(int) Math.min(s.length - 1, (long) (s.length * 0.999))];
            double o = Math.max(1, ops);
            out(String.format("%s %s%s tx=%d ops=%d s=%.1f ops/s=%.0f rec/op=%.1f stream/op=%.1f "
                    + "rec/tx=%d stream/tx=%d maxRec=%d tsplit/op=%.4f ssplit/op=%.4f merge/op=%.4f "
                    + "merge2/op=%.4f taken/op=%.4f sibLoads=%d iters=%d p50=%dus p99.9=%dus kept=%d len=%d",
                    el(), tag, name, tx, ops, ns / 1e9, ops / (ns / 1e9), rec / o,
                    (db.getStreamLength() - len0) / o, tx == 0 ? 0 : rec / tx,
                    tx == 0 ? 0 : (db.getStreamLength() - len0) / tx, maxRec,
                    (stat("statTimeSplits") - ts0) / o, (stat("statSpaceSplits") - ss0) / o,
                    (stat("statMerges") - mg0) / o, (stat("statMergesTwo") - mg20) / o,
                    (stat("statMergeTaken") - tb0) / o, stat("statSiblingLoads") - sl0,
                    db.getReclaimIterationCount() - it0, p50 / 1000, p999 / 1000, kept(),
                    db.getStreamLength()));
        }
    }

    // ---- measures (PF1's, CleanupRule's counting follower) ----

    static final class Count implements PointerFollower {
        final PointerFollower inner;
        final HashSet<Long> ids = new HashSet<Long>();
        long keyKlongs, live;
        int minLive = Integer.MAX_VALUE;
        long under7, under10;

        Count(PointerFollower inner) { this.inner = inner; }

        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node r = inner.followPointer(predecessor, pointerIndex, op);
            if (r instanceof KeyNode && ids.add(r.getId())) {
                KeyNode kn = (KeyNode) r;
                int sz = kn.getSize();
                long del = kn.getDeleteBitmapAtTime(Klong.MAX_TIME, sz);
                int lv = 0;
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
                    if (!shadowed) lv++;
                }
                live += lv;
                // the fill of nodes below a segment leaf's klong: all but roots (approximate:
                // a node followed from a segment leaf is a root and is not counted)
                if (!(predecessor instanceof KeyNode) || !((KeyNode) predecessor).isSegmentLeaf()) {
                    minLive = Math.min(minLive, lv);
                    if (lv < 7) under7++;
                    if (lv < 10) under10++;
                }
            }
            return r;
        }
    }

    static final class Counter implements GetMany.StopCondition {
        long users;
        public int handleKvt(Kvt kvt) { users++; return CONTINUE; }
        public void eod() {}
    }

    String scanTimed(String label) {
        GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments("/k/");
        g.inclusive = true;
        Counter c = new Counter();
        g.stopCondition = c;
        long a = System.nanoTime();
        db.getMany(g);
        long ns = System.nanoTime() - a;
        return String.format("%s keys=%d ms=%.1f ns/key=%d", label, c.users, ns / 1e6,
                c.users == 0 ? 0 : ns / c.users);
    }

    String nodes(String label) {
        synchronized (db.internal().getWriteLock()) {
            Count cn = new Count(db.internal().nodeCollection().maintenance());
            GetMany g = db.newGetMany();
            g.gd.pointerFollower = cn;
            g.startKey = Keys.toSegments("/k/");
            g.inclusive = true;
            Counter c = new Counter();
            g.stopCondition = c;
            db.getMany(g);
            return String.format("%s keys=%d keyNodes=%d klongs=%d dead=%d keys/node=%.2f "
                    + "minLive=%d under7=%d under10=%d", label, c.users, cn.ids.size(),
                    cn.keyKlongs, cn.keyKlongs - cn.live, (double) c.users / cn.ids.size(),
                    cn.minLive, cn.under7, cn.under10);
        }
    }

    void measure(String label) {
        out(el() + " " + tag + "NODES " + nodes(label));
        out(el() + " " + tag + "SCAN " + scanTimed(label));
        out(el() + " " + tag + "SCAN " + scanTimed(label + "-again"));
        out(String.format("%s %sSTATE %s kept=%d len=%d iters=%d", el(), tag, label, kept(),
                db.getStreamLength(), db.getReclaimIterationCount()));
    }

    // ---- the live set: an array of live key indexes with positions, for random picks ----

    int[] liveArr;
    int[] pos;
    int liveN;

    void initLive(int space) {
        liveArr = new int[space];
        pos = new int[space];
        Arrays.fill(pos, -1);
        liveN = 0;
    }

    void addLive(int k) {
        if (pos[k] >= 0) return;
        pos[k] = liveN;
        liveArr[liveN++] = k;
    }

    void removeLive(int k) {
        int x = pos[k];
        if (x < 0) return;
        int last = liveArr[--liveN];
        liveArr[x] = last;
        pos[last] = x;
        pos[k] = -1;
    }

    int[] liveSorted() {
        int[] a = Arrays.copyOf(liveArr, liveN);
        Arrays.sort(a);
        return a;
    }

    // ---- phases ----

    void fill(int[] o, String name) {
        Phase ph = new Phase(name);
        for (int k = 0; k < o.length; ) {
            Trans.Builder b = db.trans();
            int c = 0;
            for (int j = 0; j < 100 && k < o.length; j++, k++, c++) {
                b.put(key(o[k]), value(100, o[k]));
                addLive(o[k]);
            }
            ph.exec(b, c);
        }
        ph.end();
    }

    void overwrites(int txs, String name, long seed) {
        Random r = new Random(seed);
        Phase ph = new Phase(name);
        int report = Math.max(1, txs / 5);
        for (int k = 1; k <= txs; k++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < 100; j++) {
                int x = liveArr[r.nextInt(liveN)];
                b.put(key(x), value(100, x + k));
            }
            ph.exec(b, 100);
            if (k % report == 0) out(String.format("%s %s%s at=%d kept=%d iters=%d", el(), tag,
                    name, k, kept(), db.getReclaimIterationCount()));
        }
        ph.end();
    }

    void deletes(int[] o, String name) {
        Phase ph = new Phase(name);
        for (int k = 0; k < o.length; ) {
            Trans.Builder b = db.trans();
            int c = 0;
            for (int j = 0; j < 100 && k < o.length; j++, k++, c++) {
                b.delete(key(o[k]));
                removeLive(o[k]);
            }
            ph.exec(b, c);
        }
        ph.end();
    }

    void churn(int txs, int space, long seed) {
        Random r = new Random(seed);
        Phase ph = new Phase("CHURN");
        for (int k = 1; k <= txs; k++) {
            Trans.Builder b = db.trans();
            HashSet<Integer> used = new HashSet<Integer>();
            for (int j = 0; j < 50; j++) {
                int x;
                do { x = liveArr[r.nextInt(liveN)]; } while (used.contains(x));
                used.add(x);
                b.delete(key(x));
            }
            for (int j = 0; j < 50; j++) {
                int x;
                do { x = r.nextInt(space); } while (pos[x] >= 0 || used.contains(x));
                used.add(x);
                b.put(key(x), value(100, x + k));
            }
            for (Integer x : used) {
                if (pos[x] >= 0) removeLive(x); else addLive(x);
            }
            ph.exec(b, 100);
        }
        ph.end();
    }

    static void shuffle(int[] o, long seed) {
        Random r = new Random(seed);
        for (int k = o.length - 1; k > 0; k--) {
            int j = r.nextInt(k + 1);
            int t = o[k]; o[k] = o[j]; o[j] = t;
        }
    }

    void run() throws IOException {
        final int n = i("n", 1000000);
        final String fillOrder = s("fill", "random");
        final String shape = s("shape", "over");
        final int drive = i("drive", 20000);
        final int phaseTx = i("phase", 20000);
        out("THR " + p + " " + thr());
        open(s("dir", "data"));
        final int space = shape.equals("churn") ? 2 * n : n;
        initLive(space);
        int[] o = new int[n];
        for (int k = 0; k < n; k++) o[k] = k;
        if (fillOrder.equals("random")) shuffle(o, l("seed", 1));      // PF1's order
        fill(o, "FILL");
        measure("fill");
        boolean shaped = true;
        switch (shape) {
        case "over":
            overwrites(phaseTx, "OVER", 11);
            measure("over");
            shaped = false;
            break;
        case "keep": {
            int keep = i("keep", 2);
            int[] d = new int[n - (n + keep - 1) / keep];
            int c = 0;
            for (int k = 0; k < n; k++) if (k % keep != 0) d[c++] = k;
            String ord = s("order", "asc");
            if (ord.equals("desc")) {
                for (int a = 0, b = d.length - 1; a < b; a++, b--) { int t = d[a]; d[a] = d[b]; d[b] = t; }
            } else if (ord.equals("hashed")) {
                shuffle(d, 7);
            }
            deletes(d, "DELETE");
            break;
        }
        case "mass": {
            int[] d = new int[(int) (0.9 * n)];
            for (int k = 0; k < d.length; k++) d[k] = k;
            deletes(d, "DELETE");
            break;
        }
        case "churn":
            churn(phaseTx, space, 13);
            break;
        case "none":
            shaped = false;
            break;
        default:
            throw new IllegalArgumentException(shape);
        }
        if (shaped) {
            measure("shape");
            if (drive > 0) {
                overwrites(drive, "DRIVE", 11);
                measure("drive");
            }
        }
        int[] live = liveSorted();
        close();
        if (shaped && i("twin", 1) == 1) {
            tag = "TWIN ";
            open(s("dir", "data") + "-twin");
            initLive(space);
            if (!fillOrder.equals("seq")) shuffle(live, 3);
            fill(live, "FILL");
            measure("fill");
            if (drive > 0) {
                overwrites(drive, "DRIVE", 11);
                measure("drive");
            }
            close();
        }
    }

    /**
     * Thrash: a sweep around one key x in a database of n keys at spacing 2 (even keys), put
     * in key order. For d = 1 .. span: one more key next to x is changed (up: an odd key put
     * after x; down: an even key deleted before x), one a transaction; then x is put and
     * deleted in turns, pp transactions of one operation each. Per d: new nodes an operation
     * (splits and merges: a time split makes one node, a space split and a merge into two
     * nodes two, a merge into one node one) and the stream bytes a ping-pong operation.
     */
    void thrash() throws IOException {
        final int n = i("n", 20000), span = i("span", 60), pp = i("pp", 200);
        out("THR thrash " + p + " " + thr());
        open(s("dir", "data"));
        initLive(n);
        int[] o = new int[n / 2];
        for (int k = 0; k < o.length; k++) o[k] = 2 * k;
        fill(o, "FILL");
        double worst = 0;
        String worstAt = "";
        for (String dirn : new String[] {"up", "down"}) {
            int x = n / 2 + (dirn.equals("up") ? -n / 4 : n / 4) + 1;    // odd: not live
            for (int d = 1; d <= span; d++) {
                Trans.Builder b = db.trans();
                if (dirn.equals("up")) b.put(key(x + 2 * d), value(100, d));
                else b.delete(key(x - 1 - 2 * (d - 1)));
                time += dt;
                clock.setTime(time);
                db.execute(b.build());
                long ts = stat("statTimeSplits"), ss = stat("statSpaceSplits");
                long mg = stat("statMerges"), mg2 = stat("statMergesTwo");
                long len = db.getStreamLength();
                for (int k = 0; k < pp; k++) {
                    Trans.Builder c = db.trans();
                    if (k % 2 == 0) c.put(key(x), value(100, k)); else c.delete(key(x));
                    time += dt;
                    clock.setTime(time);
                    db.execute(c.build());
                }
                long dts = stat("statTimeSplits") - ts, dss = stat("statSpaceSplits") - ss;
                long dmg = stat("statMerges") - mg, dmg2 = stat("statMergesTwo") - mg2;
                double nw = (dts + 2.0 * dss + (dmg - dmg2) + 2.0 * dmg2) / pp;
                out(String.format("THRASH %s d=%d new/op=%.3f tsplit=%d ssplit=%d merges=%d two=%d "
                        + "bytes/op=%d", dirn, d, nw, dts, dss, dmg, dmg2,
                        (db.getStreamLength() - len) / pp));
                if (nw > worst) { worst = nw; worstAt = dirn + " d=" + d; }
            }
        }
        out(String.format("THRASH worst new/op=%.3f at %s", worst, worstAt));
        close();
    }

    /**
     * Thrash, a random adversary: a window of w keys (all of them, at spacing 1) in a
     * database of n keys at spacing 2 put in key order; 'bursts' times: the window's live
     * keys are set to a random target count by single puts and deletes of random window keys,
     * then one random key of the window is put and deleted in turns, pp transactions of one
     * operation. Per burst: new nodes an operation (as thrash()); the worst burst and the mean.
     */
    void thrash2() throws IOException {
        final int n = i("n", 20000), w = i("w", 120), bursts = i("bursts", 300), pp = i("pp", 40);
        out("THR thrash2 " + p + " " + thr());
        open(s("dir", "data"));
        initLive(n + w);
        int[] o = new int[n / 2];
        for (int k = 0; k < o.length; k++) o[k] = 2 * k;
        fill(o, "FILL");
        final int lo = n / 2 + 1;
        Random r = new Random(l("seed", 5));
        boolean[] in = new boolean[w];
        for (int k = 0; k < w; k++) in[k] = pos[lo + k] >= 0;
        double worst = 0, sum = 0;
        long ops = 0, allNew = 0, allMerges = 0, allSplits = 0, bytes = 0;
        String worstAt = "";
        for (int b = 0; b < bursts; b++) {
            int target = w / 8 + r.nextInt(w - w / 8);
            int cnt = 0;
            for (boolean x : in) if (x) cnt++;
            while (cnt != target) {
                int k = r.nextInt(w);
                if (cnt < target && !in[k]) {
                    one(lo + k, true); in[k] = true; cnt++;
                } else if (cnt > target && in[k]) {
                    one(lo + k, false); in[k] = false; cnt--;
                }
            }
            int y = r.nextInt(w);
            long ts = stat("statTimeSplits"), ss = stat("statSpaceSplits");
            long mg = stat("statMerges"), mg2 = stat("statMergesTwo");
            long len = db.getStreamLength();
            for (int k = 0; k < pp; k++) {
                in[y] = !in[y];
                one(lo + y, in[y]);
            }
            long dts = stat("statTimeSplits") - ts, dss = stat("statSpaceSplits") - ss;
            long dmg = stat("statMerges") - mg, dmg2 = stat("statMergesTwo") - mg2;
            double nw = (dts + 2.0 * dss + (dmg - dmg2) + 2.0 * dmg2) / pp;
            sum += nw;
            ops += pp;
            allNew += (long) (nw * pp);
            allMerges += dmg;
            allSplits += dss;
            bytes += db.getStreamLength() - len;
            if (nw > worst) {
                worst = nw;
                worstAt = String.format("burst=%d target=%d y=%d tsplit=%d ssplit=%d merges=%d "
                        + "two=%d", b, target, y, dts, dss, dmg, dmg2);
            }
        }
        out(String.format("THRASH2 w=%d bursts=%d pp=%d mean new/op=%.3f worst new/op=%.3f (%s) "
                + "merges/op=%.4f ssplits/op=%.4f bytes/op=%d", w, bursts, pp, sum / bursts, worst,
                worstAt, (double) allMerges / ops, (double) allSplits / ops, bytes / ops));
        close();
    }

    /**
     * Thrash from a fill in key order of one key a transaction (leaves at the split's half):
     * n keys at spacing 1; for each key y of a window of w keys in the middle: y deleted and
     * put in turns, pp transactions of one operation each (pp even: y ends live). Per y: new
     * nodes an operation (as thrash()); the worst y and the mean.
     */
    void thrash3() throws IOException {
        final int n = i("n", 3000), w = i("w", 60), pp = i("pp", 200);
        out("THR thrash3 " + p + " " + thr());
        open(s("dir", "data"));
        initLive(n);
        for (int k = 0; k < n; k++) one(k, true);
        out(el() + " " + nodes("fill1"));
        double worst = 0, sum = 0;
        long merges = 0, splits = 0, bytes = 0;
        String worstAt = "";
        for (int y = n / 2; y < n / 2 + w; y++) {
            long ts = stat("statTimeSplits"), ss = stat("statSpaceSplits");
            long mg = stat("statMerges"), mg2 = stat("statMergesTwo");
            long len = db.getStreamLength();
            for (int k = 0; k < pp; k++) one(y, k % 2 == 1);
            long dts = stat("statTimeSplits") - ts, dss = stat("statSpaceSplits") - ss;
            long dmg = stat("statMerges") - mg, dmg2 = stat("statMergesTwo") - mg2;
            double nw = (dts + 2.0 * dss + (dmg - dmg2) + 2.0 * dmg2) / pp;
            sum += nw;
            merges += dmg;
            splits += dss;
            bytes += db.getStreamLength() - len;
            if (nw > worst) {
                worst = nw;
                worstAt = String.format("y=%d tsplit=%d ssplit=%d merges=%d two=%d bytes/op=%d", y,
                        dts, dss, dmg, dmg2, (db.getStreamLength() - len) / pp);
            }
        }
        out(el() + " " + nodes("end"));
        long ops = (long) w * pp;
        out(String.format("THRASH3 n=%d w=%d pp=%d mean new/op=%.3f worst new/op=%.3f (%s) "
                + "merges/op=%.4f ssplits/op=%.4f bytes/op=%d", n, w, pp, sum / w, worst, worstAt,
                (double) merges / ops, (double) splits / ops, bytes / ops));
        close();
    }

    /**
     * Thrash, a random search near the split's half: 'trials' fresh databases of n even keys
     * put in key order, one a transaction (leaves at the half of a space split); in each, a
     * random e (0 to 7) odd keys put and f (0 to 7) other even keys deleted within 40 of an
     * even key y, one a transaction; then y deleted and put in turns, pp transactions. Per
     * trial: new nodes an operation (as thrash()); the worst trial and the mean.
     */
    void thrash4() throws IOException {
        final int n = i("n", 1000), trials = i("trials", 100), pp = i("pp", 200);
        out("THR thrash4 " + p + " " + thr());
        Random r = new Random(l("seed", 9));
        double worst = 0, sum = 0;
        long merges = 0, splits = 0, bytes = 0, cycles = 0;
        String worstAt = "";
        for (int t = 0; t < trials; t++) {
            open(s("dir", "data"));
            time = 10 * SEC;
            initLive(2 * n);
            for (int k = 0; k < 2 * n; k += 2) one(k, true);
            int y = n + r.nextInt(n / 2);          // even: live, deleted first; odd: put first
            int e = r.nextInt(i("emax", 8)), f = r.nextInt(i("fmax", 8));
            for (int j = 0; j < e; j++) one(y - 41 + 2 * r.nextInt(41), true);
            for (int j = 0; j < f; j++) {
                int z = y - 40 + 2 * r.nextInt(41);
                if (z != y) one(z, false);
            }
            long ts = stat("statTimeSplits"), ss = stat("statSpaceSplits");
            long mg = stat("statMerges"), mg2 = stat("statMergesTwo");
            long len = db.getStreamLength();
            for (int k = 0; k < pp; k++) one(y, (k % 2 == 1) == (y % 2 == 0));
            long dts = stat("statTimeSplits") - ts, dss = stat("statSpaceSplits") - ss;
            long dmg = stat("statMerges") - mg, dmg2 = stat("statMergesTwo") - mg2;
            double nw = (dts + 2.0 * dss + (dmg - dmg2) + 2.0 * dmg2) / pp;
            sum += nw;
            merges += dmg;
            splits += dss;
            if (dmg >= 10 && dss >= 10) cycles++;
            bytes += db.getStreamLength() - len;
            if (nw > worst) {
                worst = nw;
                worstAt = String.format("trial=%d y=%d e=%d f=%d tsplit=%d ssplit=%d merges=%d two=%d "
                        + "bytes/op=%d", t, y, e, f, dts, dss, dmg, dmg2, (db.getStreamLength() - len) / pp);
            }
            close();
        }
        long ops = (long) trials * pp;
        out(String.format("THRASH4 n=%d trials=%d pp=%d mean new/op=%.3f worst new/op=%.3f (%s) "
                + "merges/op=%.4f ssplits/op=%.4f bytes/op=%d cycling trials=%d", n, trials, pp,
                sum / trials, worst, worstAt, (double) merges / ops, (double) splits / ops,
                bytes / ops, cycles));
    }

    /** One put or delete of key k in a transaction of its own. */
    void one(int k, boolean put) {
        Trans.Builder c = db.trans();
        if (put) c.put(key(k), value(100, k)); else c.delete(key(k));
        time += dt;
        clock.setTime(time);
        db.execute(c.build());
    }

    static void rm(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) rm(c);
        f.delete();
    }

    public static void main(String[] args) throws Exception {
        THR x = new THR();
        for (int k = 1; k < args.length; k++) {
            int eq = args[k].indexOf('=');
            x.p.put(args[k].substring(0, eq), args[k].substring(eq + 1));
        }
        switch (args[0]) {
        case "run": x.run(); break;
        case "thrash": x.thrash(); break;
        case "thrash2": x.thrash2(); break;
        case "thrash3": x.thrash3(); break;
        case "thrash4": x.thrash4(); break;
        default: throw new IllegalArgumentException(args[0]);
        }
        out(x.el() + " DONE");
        System.exit(0);
    }
}
