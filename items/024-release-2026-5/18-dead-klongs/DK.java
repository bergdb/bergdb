package bergdb.core;

import java.io.*;
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
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * The probe of bergdb 024-18, written 2026-11-11: dead klongs in live key nodes, counted.
 * 024-14's THR setup (024-03's PF1): a FileStream with the builder's defaults, a test clock of
 * 1 ms a transaction, keys "/k/%010d", values of 100 bytes, 100 operations a transaction.
 *
 * java -cp classes:JAR bergdb.core.DK key=value...
 *   n        keys of the fill
 *   shape    over:   random fill; phase transactions of 100 overwrites of random keys
 *            sparse: fill in key order; all keys but every keep-th deleted in a fixed random
 *                    order; then phase transactions of 100 overwrites of random live keys
 *            fifo:   fill in key order; phase transactions of 50 deletes of the oldest keys
 *                    and 50 puts of new keys at the end (a queue)
 *            sparsecold: sparse's fill and deletes, then phase transactions of 100 overwrites
 *                    of live keys of the hot range only: the rest is never written again
 *            cold:   random fill; phase transactions of 100 overwrites of random keys of the
 *                    hot range, the first hot-th part of the keys (default 100: 1 %)
 *   retain   seconds; 0: forever (reclaim off)
 *   B        the node size: 8, 14, 30 (default) or 62
 *   phase    transactions of the phase; every: a census each so many transactions
 *   iters    1: a census at each reclaim iteration's end too
 *
 * A census walks every key node that a scan of "/k/" reaches at the latest time (CleanupRule's
 * counting follower, as 024-14's THR) and counts, for leaves (segment leaves) and inner nodes
 * apart: klongs by type, live and dead KEY klongs (dead: deleted by the last bitmap, or
 * shadowed by a later KEY klong of the same compare value), the bytes a write of the node
 * stores (32 + 16 a klong, StoredKeyNode), the heap of its arrays (80 + 24 a klong of the
 * array's capacity, KeyNode.getMemSize), a histogram of dead klongs a node, and option 3's
 * set: the nodes that hold a dead klong, their ancestors, and those of them not changed since
 * the census before (cold).
 */
public class DK {
    static final long SEC = CoreTestClock.UNITS_PER_SEC;
    final Map<String, String> p = new HashMap<String, String>();
    int i(String k, int d) { return p.containsKey(k) ? Integer.parseInt(p.get(k)) : d; }
    long l(String k, long d) { return p.containsKey(k) ? Long.parseLong(p.get(k)) : d; }
    String s(String k, String d) { return p.containsKey(k) ? p.get(k) : d; }

    final long t0 = System.nanoTime();
    File dir;
    CoreTestClock clock;
    long time = 10 * SEC;
    Db db;
    final long dt = 10000;
    long lastCensusTime = 0;
    long iterSeen = 0, lenAtIter = 0, recAtIter = 0, recAll = 0, txAtIter = 0, txAll = 0;

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
            return -1;
        } catch (IllegalAccessException e) {
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
        DbBuilder bu = Db.builder().mainStream(new FileStream(dir)).clock(clock);
        switch (i("B", 30)) {
        case 8: bu.maxNodeSize8(); break;
        case 14: bu.maxNodeSize14(); break;
        case 62: bu.maxNodeSize62(); break;
        default: break;
        }
        db = bu.start();
        long r = l("retain", 1);
        if (r > 0) db.setRetainDuration(r * SEC);
    }

    void close() {
        db.sync(SyncLevel.ORDINARY);
        db.close();
        rm(dir);
    }

    long kept() { return db.getStreamLength() - db.getFirstAvailablePos(); }

    // ---- the census ----

    static int cap(int n) {
        for (int c : new int[] {2, 6, 14, 30, 62, 126}) if (c >= n) return c;
        return n;
    }

    static final class Cls {
        long nodes, klongs, key, live, dead, deleted, shadowed, time, del, bytes, liveBytes, heap,
                liveHeap, withDead, coldWithDead, coldWithDeadBytes, set3, set3Bytes, set3Cold;
        long[] hist = new long[8];     // dead: 0, 1, 2, 3-4, 5-8, 9-16, 17-24, 25+

        static int bucket(int d) {
            if (d <= 2) return d;
            if (d <= 4) return 3;
            if (d <= 8) return 4;
            if (d <= 16) return 5;
            if (d <= 24) return 6;
            return 7;
        }

        String fmt(String name) {
            double nn = Math.max(1, nodes);
            return String.format("%s nodes=%d klongs=%d key=%d live=%d dead=%d (deleted=%d shadowed=%d)"
                    + " time=%d del=%d dead/live=%.3f dead/node=%.2f klongs/node=%.2f live/node=%.2f"
                    + " withDead=%d coldWithDead=%d bytes=%d liveBytes=%d deadBytes=%d heap=%d liveHeap=%d"
                    + " set3=%d set3Bytes=%d set3Cold=%d hist=%s",
                    name, nodes, klongs, key, live, dead, deleted, shadowed, time, del,
                    (double) dead / Math.max(1, live), dead / nn, klongs / nn, live / nn, withDead,
                    coldWithDead, bytes, liveBytes, 16 * dead, heap, liveHeap, set3, set3Bytes,
                    set3Cold, Arrays.toString(hist));
        }
    }

    static final class Info {
        long id, parent;
        boolean leaf, dead, cold;
        int liveBytes;
    }

    static final class Census implements PointerFollower {
        final PointerFollower inner;
        final long coldBefore;
        final HashMap<Long, Info> infos = new HashMap<Long, Info>();
        final Cls leaf = new Cls(), innr = new Cls();

        Census(PointerFollower inner, long coldBefore) {
            this.inner = inner;
            this.coldBefore = coldBefore;
        }

        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node r = inner.followPointer(predecessor, pointerIndex, op);
            if (r instanceof KeyNode && !infos.containsKey(r.getId())) {
                KeyNode kn = (KeyNode) r;
                Info in = new Info();
                in.id = kn.getId();
                in.parent = predecessor instanceof KeyNode ? predecessor.getId() : -1;
                in.leaf = kn.isSegmentLeaf();
                infos.put(in.id, in);
                Cls c = in.leaf ? leaf : innr;
                int sz = kn.getSize();
                long delBits = kn.getDeleteBitmapAtTime(Klong.MAX_TIME, sz);
                int lv = 0, dd = 0, dl = 0, sh = 0, tk = 0, dk = 0, kk = 0;
                long lastTime = 0;
                for (int i = 0; i < sz; i++) {
                    long k = kn.getKlong(i);
                    if (Klong.getType(k) == Klong.TYPE_TIME) {
                        tk++;
                        lastTime = Klong.getTime(k);
                        continue;
                    }
                    if (Klong.getType(k) == Klong.TYPE_DELETE_BITMAP) {
                        dk++;
                        continue;
                    }
                    kk++;
                    if (Klong.isDeleted(delBits, i)) {
                        dl++;
                        continue;
                    }
                    long cv = Klong.getCompareValue(k);
                    boolean shadowed = false;
                    for (int j = i + 1; j < sz && !shadowed; j++) {
                        long k2 = kn.getKlong(j);
                        shadowed = Klong.isKey(k2) && Klong.getCompareValue(k2) == cv;
                    }
                    if (shadowed) sh++; else lv++;
                }
                dd = dl + sh;
                c.nodes++;
                c.klongs += sz;
                c.key += kk;
                c.live += lv;
                c.dead += dd;
                c.deleted += dl;
                c.shadowed += sh;
                c.time += tk;
                c.del += dk;
                c.bytes += 32 + 16 * sz;
                in.liveBytes = 32 + 16 * (lv + 1);
                c.liveBytes += in.liveBytes;
                c.heap += 80 + 24 * cap(sz);
                c.liveHeap += 80 + 24 * cap(lv + 1);
                c.hist[Cls.bucket(dd)]++;
                in.cold = lastTime < coldBefore;
                if (dd > 0) {
                    in.dead = true;
                    c.withDead++;
                    if (in.cold) {
                        c.coldWithDead++;
                        c.coldWithDeadBytes += in.liveBytes;
                    }
                }
            }
            return r;
        }

        /** Option 3's set: the nodes with a dead klong and all their ancestors. */
        void set3() {
            HashSet<Long> set = new HashSet<Long>();
            for (Info in : infos.values()) {
                if (!in.dead) continue;
                Info x = in;
                while (x != null && set.add(x.id)) x = infos.get(x.parent);
            }
            for (Long id : set) {
                Info in = infos.get(id);
                Cls c = in.leaf ? leaf : innr;
                c.set3++;
                c.set3Bytes += in.liveBytes;
                if (in.cold) c.set3Cold++;
            }
        }
    }

    static final class Counter implements GetMany.StopCondition {
        long users;
        public int handleKvt(Kvt kvt) { users++; return CONTINUE; }
        public void eod() {}
    }

    void census(String label) {
        synchronized (db.internal().getWriteLock()) {
            Census cn = new Census(db.internal().nodeCollection().maintenance(), lastCensusTime);
            GetMany g = db.newGetMany();
            g.gd.pointerFollower = cn;
            g.startKey = Keys.toSegments("/k/");
            g.inclusive = true;
            Counter c = new Counter();
            g.stopCondition = c;
            db.getMany(g);
            cn.set3();
            out(String.format("%s CENSUS %s keys=%d kept=%d len=%d iters=%d tx=%d", el(), label,
                    c.users, kept(), db.getStreamLength(), db.getReclaimIterationCount(), txAll));
            out(String.format("%s CLEAF %s %s", el(), label, cn.leaf.fmt("leaf")));
            out(String.format("%s CINNER %s %s", el(), label, cn.innr.fmt("inner")));
        }
        lastCensusTime = time;
    }

    // ---- transactions ----

    long phaseRec, phaseOps, phaseTx, phaseLen0, phaseTs0, phaseSs0, phaseMg0, phaseRep0;

    void phaseStart() {
        phaseRec = 0;
        phaseOps = 0;
        phaseTx = 0;
        phaseLen0 = db.getStreamLength();
        phaseTs0 = stat("statTimeSplits");
        phaseSs0 = stat("statSpaceSplits");
        phaseMg0 = stat("statMerges");
        phaseRep0 = stat("statCompactions");
    }

    void phaseEnd(String name) {
        double o = Math.max(1, phaseOps);
        out(String.format("%s PHASE %s tx=%d ops=%d rec/op=%.1f stream/op=%.1f tsplit/op=%.4f "
                + "ssplit/op=%.4f merge/op=%.4f compact/op=%.4f iters=%d kept=%d len=%d", el(), name,
                phaseTx, phaseOps, phaseRec / o, (db.getStreamLength() - phaseLen0) / o,
                (stat("statTimeSplits") - phaseTs0) / o, (stat("statSpaceSplits") - phaseSs0) / o,
                (stat("statMerges") - phaseMg0) / o, (stat("statCompactions") - phaseRep0) / o,
                db.getReclaimIterationCount(), kept(), db.getStreamLength()));
    }

    void exec(Trans.Builder b, int ops) {
        time += dt;
        clock.setTime(time);
        Trans t = b.build();
        db.execute(t);
        long r = t.nextPos - t.tpos;
        phaseRec += r;
        recAll += r;
        phaseOps += ops;
        phaseTx++;
        txAll++;
        if (i("iters", 1) == 1 && db.getReclaimIterationCount() != iterSeen) {
            iterSeen = db.getReclaimIterationCount();
            long len = db.getStreamLength();
            out(String.format("%s ITER %d stream=%d rec=%d tx=%d (since the last iteration's end)",
                    el(), iterSeen, len - lenAtIter, recAll - recAtIter, txAll - txAtIter));
            lenAtIter = len;
            recAtIter = recAll;
            txAtIter = txAll;
            if (iterSeen <= i("maxIterCensus", 1000)) census("iter" + iterSeen);
        }
    }

    // ---- the live set ----

    int[] liveArr;
    int[] pos;
    int liveN;
    long[] expTag;      // the tag of each live key's last value (value(100, tag))

    /** Every live key's value at the latest time, by a scan, against expTag. */
    void verify() {
        final int[] live = Arrays.copyOf(liveArr, liveN);
        Arrays.sort(live);
        final long[] r = new long[3];     // seen, bad, extra
        GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments("/k/");
        g.inclusive = true;
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                int i = (int) r[0]++;
                if (i >= live.length) { r[2]++; return CONTINUE; }
                long tag = 0;
                for (int j = 0; j < 8; j++) tag |= (kvt.value[j] & 0xffL) << (8 * j);
                if (tag != expTag[live[i]] || kvt.value.length != 100) r[1]++;
                return CONTINUE;
            }
            public void eod() {}
        };
        db.getMany(g);
        out(String.format("%s VERIFY live=%d seen=%d bad=%d extra=%d %s", el(), live.length, r[0], r[1],
                r[2], r[0] == live.length && r[1] == 0 && r[2] == 0 ? "OK" : "FAILED"));
    }

    void initLive(int space) {
        liveArr = new int[space];
        pos = new int[space];
        expTag = new long[space];
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

    static void shuffle(int[] o, long seed) {
        Random r = new Random(seed);
        for (int k = o.length - 1; k > 0; k--) {
            int j = r.nextInt(k + 1);
            int t = o[k]; o[k] = o[j]; o[j] = t;
        }
    }

    void fill(int[] o) {
        phaseStart();
        for (int k = 0; k < o.length; ) {
            Trans.Builder b = db.trans();
            int c = 0;
            for (int j = 0; j < 100 && k < o.length; j++, k++, c++) {
                b.put(key(o[k]), value(100, o[k]));
                expTag[o[k]] = o[k];
                addLive(o[k]);
            }
            exec(b, c);
        }
        phaseEnd("FILL");
    }

    void deletes(int[] o) {
        phaseStart();
        for (int k = 0; k < o.length; ) {
            Trans.Builder b = db.trans();
            int c = 0;
            for (int j = 0; j < 100 && k < o.length; j++, k++, c++) {
                b.delete(key(o[k]));
                removeLive(o[k]);
            }
            exec(b, c);
        }
        phaseEnd("DELETE");
    }

    void run() throws IOException {
        final int n = i("n", 1000000);
        final String shape = s("shape", "over");
        final int phase = i("phase", 20000);
        final int every = i("every", Math.max(1, phase / 4));
        out("DK " + p + " thr=" + System.getProperty("bergdb.thr") + " theta="
                + System.getProperty("bergdb.theta") + " rtheta=" + System.getProperty("bergdb.rtheta"));
        open(s("dir", "data"));
        final int space = shape.equals("fifo") ? n + phase * 50 + 1 : n;
        initLive(space);
        int[] o = new int[n];
        for (int k = 0; k < n; k++) o[k] = k;
        boolean random = shape.equals("over") || shape.equals("cold");
        if (random) shuffle(o, 1);
        fill(o);
        census("fill");
        if (shape.equals("sparse") || shape.equals("sparsecold")) {
            int keep = i("keep", 10);
            int[] d = new int[n - (n + keep - 1) / keep];
            int c = 0;
            for (int k = 0; k < n; k++) if (k % keep != 0) d[c++] = k;
            shuffle(d, 7);
            deletes(d);
            census("deleted");
        }
        Random r = new Random(11);
        int hot = Math.max(1, n / i("hot", 100));
        int head = 0, next = n;
        phaseStart();
        for (int t = 1; t <= phase; t++) {
            Trans.Builder b = db.trans();
            if (shape.equals("fifo")) {
                for (int j = 0; j < 50; j++) {
                    b.delete(key(head));
                    removeLive(head++);
                }
                for (int j = 0; j < 50; j++) {
                    b.put(key(next), value(100, next + t));
                    expTag[next] = next + t;
                    addLive(next++);
                }
            } else if (shape.equals("sparsecold")) {
                // the live keys of the hot range (the first hot-th part of the key space)
                HashSet<Integer> u = new HashSet<Integer>();
                int keep = i("keep", 10);
                while (u.size() < Math.min(100, hot / keep)) u.add(keep * r.nextInt(hot / keep));
                for (int x : u) {
                    b.put(key(x), value(100, x + t));
                    expTag[x] = x + t;
                }
            } else if (shape.equals("cold")) {
                HashSet<Integer> u = new HashSet<Integer>();
                while (u.size() < 100) u.add(r.nextInt(hot));
                for (int x : u) {
                    b.put(key(x), value(100, x + t));
                    expTag[x] = x + t;
                }
            } else {
                HashSet<Integer> u = new HashSet<Integer>();
                while (u.size() < 100) u.add(liveArr[r.nextInt(liveN)]);
                for (int x : u) {
                    b.put(key(x), value(100, x + t));
                    expTag[x] = x + t;
                }
            }
            exec(b, 100);
            if (t % every == 0) {
                phaseEnd("RUN-at-" + t);
                census("at" + t);
                phaseStart();
            }
        }
        verify();
        close();
    }

    static void rm(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) rm(c);
        f.delete();
    }

    public static void main(String[] args) throws Exception {
        DK x = new DK();
        for (int k = 0; k < args.length; k++) {
            int eq = args[k].indexOf('=');
            x.p.put(args[k].substring(0, eq), args[k].substring(eq + 1));
        }
        x.run();
        out(x.el() + " DONE");
        System.exit(0);
    }
}
