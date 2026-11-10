package bergdb.core;

import java.io.IOException;
import java.util.*;

import bergdb.dag.GetMany;
import bergdb.dag.GetData;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.PointerFollower;
import bergdb.dag.TopNode;
import bergdb.pub.util.Clock;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;

/**
 * The ratchet test of the dirty top-node window (bergdb 023-06, section 18.6, item 3; 023-08,
 * Q6), written 2026-11-10 from CleanupRule (023-03's T1 and T4, with P7's count of D's top
 * nodes, 023-05 P7, section 1.1). Not a gate: it measures and prints. Compiled apart from
 * the build, against its bergdb.jar; it uses only what main and 023-core both have.
 *
 * Two databases with T1's settings (CutStream, a test clock of 1 ms a transaction, R = 1 s,
 * startup distance 100 kB, node size 30, no eviction), run one after the other:
 *
 *   twin: T4's queue, m transactions (put key i, delete key i - live), with a restart at
 *         every disturbance point;
 *   dist: the same queue, and at every disturbance point (every 'dist' queue transactions,
 *         before the last) a disturbance: n keys put, 100 a transaction, then deleted, 100 a
 *         transaction, in key order, then a restart.
 *
 * Measures, at every checkpoint: D, D's top nodes (tops), the inversions (inv: consecutive
 * dirty top nodes, by ordinal, whose newer node waits in an older got-dirty list), the
 * dirty top nodes with a dirty root (rootDirty), the span of their ordinals, the top nodes
 * made (the super root's ordinal), resident objects, handles, kept bytes, the lag, reclaim
 * iterations and cuts (summed over the restarts). Between checkpoints, D and tops are
 * sampled every 'sample' queue transactions; their most since the last checkpoint is printed.
 *
 * Usage (from a build's java/ directory):
 *   java -ea -Xmx8g -cp CLASSES:build/bergdb.jar bergdb.core.CleanupRatchet [prop=value...]
 * Properties: m=1000000 dist=200000 n=1000000 live=1000 keys=time|hashed work=queue|drive
 *   which=both|twin|dist valsize=100 dvalsize=1000 sd=100000 retain=1 dt=10000
 *   every=10000 sample=100 batch=100 early=1000,2000,5000 fresh=1 seed=1
 *   work=drive replaces the queue by T1's drive (overwrites of "/a.txt" with dvalsize bytes).
 *   fresh=1: each disturbance puts keys of its own range, "/k/" round "/" i; 0: the same keys.
 */
public class CleanupRatchet {
    static final long SEC = Clock.UNITS_PER_SEC;
    static final String A_KEY = "/a.txt";
    static final long[] A_SEG = Keys.toSegments(A_KEY);
    static final byte[] HELLO = "Hello world!".getBytes(java.nio.charset.StandardCharsets.UTF_8);
    static final String INTERNAL = "/#i/";

    final Map<String, String> p = new LinkedHashMap<String, String>();

    CleanupRatchet(String[] args) {
        for (String a : args) {
            int eq = a.indexOf('=');
            p.put(a.substring(0, eq), a.substring(eq + 1));
        }
    }

    int i(String k, int d) { return p.containsKey(k) ? Integer.parseInt(p.get(k)) : d; }
    long l(String k, long d) { return p.containsKey(k) ? Long.parseLong(p.get(k)) : d; }
    String s(String k, String d) { return p.containsKey(k) ? p.get(k) : d; }

    /** Counts the key nodes a read follows, by id (CleanupRule's Count, without the klongs). */
    static final class Count implements PointerFollower {
        final PointerFollower inner;
        final HashSet<Long> ids = new HashSet<Long>();

        Count(PointerFollower inner) {
            this.inner = inner;
        }

        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node r = inner.followPointer(predecessor, pointerIndex, op);
            if (r instanceof KeyNode) ids.add(r.getId());
            return r;
        }
    }

    /** Stops at the first key that is not internal. */
    static final class FirstUser implements GetMany.StopCondition {
        public int handleKvt(Kvt kvt) {
            return Keys.toString(kvt.key).startsWith(INTERNAL) ? CONTINUE : ADD_AND_STOP;
        }

        public void eod() {}
    }

    static final class M {
        long len, kept, lagMs, iters, cuts, reach, qhead, dirty, res, handles, made;
        int[] tops;

        String line() {
            return String.format("D=%d tops=%d inv=%d rootDirty=%d span=%d made=%d res=%d "
                    + "handles=%d kept=%d len=%d lag=%dms iters=%d cuts=%d reach=%d qhead=%d",
                    dirty, tops[0], tops[1], tops[2], tops[3], made, res, handles, kept, len,
                    lagMs, iters, cuts, reach, qhead);
        }
    }

    /** One database: a CutStream, a test clock, a model of the recent keys. */
    final class Run {
        final String label;
        final int sd = i("sd", 100000);
        final long retain = l("retain", 1) * SEC;
        CutStream cut = new CutStream();
        CoreTestClock clock;
        long time = 10 * SEC;
        Db db;
        Reclaim.Stats stats;
        long itersBefore, cutsBefore;   // summed over the earlier starts
        long maxRecord;
        long sMaxD, sMaxTops, sMaxInv;  // the most, sampled since the last checkpoint
        int cutWatch = -1;              // transactions since a disturbance's restart, until a cut
        final HashMap<String, TreeMap<Long, byte[]>> model =
                new HashMap<String, TreeMap<Long, byte[]>>();

        Run(String label) {
            this.label = label;
            start();
            if (retain > 0) db.setRetainDuration(retain);
        }

        void start() {
            clock = new CoreTestClock();
            clock.setTime(time);
            db = Db.builder().testSetup(cut).clock(clock).startupDistance(sd).start();
            stats = db.internal().reclaim().enableStats();
        }

        void restart() {
            itersBefore += stats.iterations.size();
            cutsBefore += stats.cuts.size();
            db.sync(SyncLevel.ORDINARY);
            db.close();
            cut = cut.copy();
            start();
        }

        Trans exec(List<String> keys, List<byte[]> values) {
            time += l("dt", 10000);
            clock.setTime(time);
            Trans.Builder b = db.trans();
            for (int k = 0; k < keys.size(); k++) {
                if (values.get(k) == null) b.delete(keys.get(k));
                else b.put(keys.get(k), values.get(k));
            }
            Trans t = b.build();
            db.execute(t);
            for (int k = 0; k < keys.size(); k++) {
                TreeMap<Long, byte[]> h = model.get(keys.get(k));
                if (h == null) model.put(keys.get(k), h = new TreeMap<Long, byte[]>());
                h.put(t.tt, values.get(k));
                if (h.size() > 64) {
                    // Keep the history from R (and a margin) back: the floor entry and later.
                    Long floor = h.floorKey(time - retain - 100 * l("dt", 10000));
                    if (floor != null) h.headMap(floor, false).clear();
                }
            }
            maxRecord = Math.max(maxRecord, t.nextPos - t.tpos);
            return t;
        }

        long dirty() {
            final Set<Node> d = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
            synchronized (db.internal().getWriteLock()) {
                db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE,
                        (node, tpos, last) -> { if (node.isDirty()) d.add(node); });
            }
            return d.size();
        }

        /** {dirty top nodes, inversions, those with a dirty root, span of ordinals} (P7's). */
        int[] tops() {
            synchronized (db.internal().getWriteLock()) {
                final Map<Node, Long> tposOf = new IdentityHashMap<Node, Long>();
                final List<TopNode> dt = new ArrayList<TopNode>();
                db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE, (node, tpos, last) -> {
                    if (node.isDirty() && node instanceof TopNode && !tposOf.containsKey(node)) {
                        tposOf.put(node, tpos);
                        dt.add((TopNode) node);
                    }
                });
                dt.sort((x1, x2) -> Long.compare(x1.topNodeId, x2.topNodeId));
                int inv = 0, rootDirty = 0;
                for (int k = 0; k < dt.size(); k++) {
                    Node r = dt.get(k).getPointerNode(0);
                    if (r != null && r.isDirty()) rootDirty++;
                    if (k + 1 < dt.size() && tposOf.get(dt.get(k + 1)) < tposOf.get(dt.get(k))) inv++;
                }
                int span = dt.isEmpty() ? 0
                        : (int) (dt.get(dt.size() - 1).topNodeId - dt.get(0).topNodeId + 1);
                return new int[] {dt.size(), inv, rootDirty, span};
            }
        }

        void sample() {
            sMaxD = Math.max(sMaxD, dirty());
            int[] t = tops();
            sMaxTops = Math.max(sMaxTops, t[0]);
            sMaxInv = Math.max(sMaxInv, t[1]);
        }

        M measure() {
            M m = new M();
            m.len = db.getStreamLength();
            m.kept = m.len - db.getFirstAvailablePos();
            m.lagMs = (time - db.getFirstAvailableLookupTime()) / (SEC / 1000);
            m.iters = itersBefore + stats.iterations.size();
            m.cuts = cutsBefore + stats.cuts.size();
            synchronized (db.internal().getWriteLock()) {
                if (i("reach", 1) == 1) {
                    Count c = new Count(db.internal().nodeCollection().maintenance());
                    GetMany g = db.newGetMany();
                    g.gd.pointerFollower = c;
                    g.stopCondition = new GetMany.StopCondition() {
                        public int handleKvt(Kvt kvt) { return CONTINUE; }   // count, keep none
                        public void eod() {}
                    };
                    db.getMany(g);
                    m.reach = c.ids.size();
                }
                Count c3 = new Count(db.internal().nodeCollection().maintenance());
                GetMany h = db.newGetMany();
                h.gd.pointerFollower = c3;
                h.startKey = Keys.toSegments(s("work", "queue").equals("queue") ? "/q/" : "/");
                h.inclusive = true;
                h.stopCondition = new FirstUser();
                db.getMany(h);
                m.qhead = c3.ids.size();
                m.made = db.internal().superRoot().topNodeId;
            }
            m.dirty = dirty();
            m.tops = tops();
            m.res = db.internal().cache().residents().objects();
            m.handles = db.internal().cache().handles().size();
            return m;
        }

        Reclaim.Stats.Iteration inProgress() {
            if (stats.iterations.isEmpty()) return null;
            Reclaim.Stats.Iteration it = stats.iterations.get(stats.iterations.size() - 1);
            return it.pEnd == -1 ? it : null;
        }

        byte[] expected(String k, long t) {
            TreeMap<Long, byte[]> h = model.get(k);
            if (h == null) return null;
            Map.Entry<Long, byte[]> e = h.floorEntry(t);
            return e == null ? null : e.getValue();
        }

        /** CleanupRule's lookups against the model (a sample of keys, three scans). */
        void verify(String where, Random rnd) {
            long now = time;
            long first = db.getFirstAvailableLookupTime();
            if (first > now - retain && first > 10 * SEC + retain) {
                throw new AssertionError(label + " " + where + ": first available time " + first
                        + " is inside the retention window");
            }
            long from = Math.max(first, now - retain);
            List<String> keys = new ArrayList<String>(model.keySet());
            Collections.sort(keys);
            for (int j = 0; j < Math.min(keys.size(), 300); j++) {
                String k = keys.get(rnd.nextInt(keys.size()));
                for (long t : new long[] {Long.MAX_VALUE, from,
                        from + (long) (rnd.nextDouble() * (now - from))}) {
                    byte[] act = db.getOne(t, Keys.toSegments(k), db.newGetData());
                    byte[] exp = expected(k, Math.min(t, now));
                    if (!Arrays.equals(exp, act)) {
                        throw new AssertionError(label + " " + where + ": " + k + " at " + t
                                + ": expected " + (exp == null ? "null" : exp.length + " bytes")
                                + ", got " + (act == null ? "null" : act.length + " bytes"));
                    }
                }
            }
            for (long t : new long[] {from, from + (long) (rnd.nextDouble() * (now - from)),
                    Long.MAX_VALUE}) {
                GetMany g = db.newGetMany();
                g.lookupTime = t;
                g.startKey = Keys.toSegments("/");
                db.getMany(g);
                int act = 0;
                for (Kvt kvt : g.result) {
                    String k = Keys.toString(kvt.key);
                    if (k.startsWith(INTERNAL)) continue;
                    act++;
                    if (!Arrays.equals(expected(k, Math.min(t, now)), kvt.value)) {
                        throw new AssertionError(label + " " + where + ": scan at " + t + ": "
                                + k + " has another value than the model's");
                    }
                }
                int exp = 0;
                for (String k : keys) if (expected(k, Math.min(t, now)) != null) exp++;
                if (exp != act) {
                    throw new AssertionError(label + " " + where + ": scan at " + t + ": "
                            + act + " keys, the model has " + exp);
                }
            }
            if (first > 0) {
                try {
                    db.getOne(first - 1, A_SEG, db.newGetData());
                    throw new AssertionError(label + " " + where + ": a lookup below the first "
                            + "available time was not refused");
                } catch (LookupTimeNotAvailableException e) {
                    // as it must
                }
            }
        }
    }

    static byte[] value(int size, long tag) {
        byte[] v = new byte[size];
        for (int j = 0; j < size; j++) v[j] = (byte) ('a' + (tag + j) % 26);
        for (int j = 0; j < 8 && j < size; j++) v[j] = (byte) (tag >>> (8 * j));
        return v;
    }

    static String qkey(int i, boolean hashed) {
        return hashed ? String.format("/q/%016x", (i * 0x9E3779B97F4A7C15L) >>> 4)
                : String.format("/q/%012d", i);
    }

    String mkey(int round, int i) {
        return i("fresh", 1) == 1 ? String.format("/k/%02d/%010d", round, i)
                : String.format("/k/%010d", i);
    }

    long t0;

    void print(Run run, int q, String phase, M m) {
        System.out.println(String.format("%s q=%d %s: %s maxS: D=%d tops=%d inv=%d maxRecord=%d "
                + "wall=%ds", run.label, q, phase, m.line(), run.sMaxD, run.sMaxTops, run.sMaxInv,
                run.maxRecord, (System.nanoTime() - t0) / 1000000000L));
        run.sMaxD = run.sMaxTops = run.sMaxInv = 0;
        run.maxRecord = 0;
    }

    /** One database through the whole schedule. */
    void run(String label, boolean disturb) throws IOException {
        final int m = i("m", 1000000);
        final int distEvery = i("dist", 200000);
        final int n = i("n", 1000000);
        final int live = i("live", 1000);
        final boolean hashed = "hashed".equals(s("keys", "time"));
        final boolean queue = "queue".equals(s("work", "queue"));
        final int valsize = i("valsize", 100);
        final int dvalsize = i("dvalsize", 1000);
        final int every = i("every", 10000);
        final int sampleEvery = i("sample", 100);
        final int batch = i("batch", 100);
        final Set<Integer> early = new HashSet<Integer>();
        for (String e : s("early", "1000,2000,5000").split(",")) early.add(Integer.parseInt(e));
        final Random rnd = new Random(l("seed", 1));
        t0 = System.nanoTime();

        Run run = new Run(label);
        run.exec(Collections.singletonList(A_KEY), Collections.singletonList(HELLO));
        int lastDist = -1;          // queue index of the last disturbance point
        int round = 0;
        List<String> lastMass = new ArrayList<String>();
        for (int q = 0; q < m; q++) {
            if (q > 0 && q % distEvery == 0) {
                // A disturbance point.
                print(run, q, "pre", run.measure());
                Reclaim.Stats.Iteration spanning = run.inProgress();
                int itersAtStart = run.stats.iterations.size();
                for (String k : lastMass) run.model.remove(k);     // older than R by now
                lastMass.clear();
                long tFill = run.time, tDel = 0;
                if (disturb) {
                    round++;
                    for (int i = 0; i < n; i += batch) {
                        List<String> ks = new ArrayList<String>();
                        List<byte[]> vs = new ArrayList<byte[]>();
                        for (int j = i; j < Math.min(n, i + batch); j++) {
                            ks.add(mkey(round, j));
                            vs.add(value(valsize, j));
                        }
                        run.exec(ks, vs);
                    }
                    print(run, q, "filled", run.measure());
                    tDel = run.time;
                    // h_fill: the most key nodes a get of a key of the fill follows (a sample).
                    int hFill = 0;
                    synchronized (run.db.internal().getWriteLock()) {
                        for (int j = 0; j < Math.min(n, 200); j++) {
                            Count c = new Count(run.db.internal().nodeCollection().maintenance());
                            GetData gd = run.db.newGetData();
                            gd.pointerFollower = c;
                            run.db.getOne(Long.MAX_VALUE, Keys.toSegments(mkey(round,
                                    (int) ((long) j * n / Math.min(n, 200)))), gd);
                            hFill = Math.max(hFill, c.ids.size());
                        }
                    }
                    System.out.println(label + " q=" + q + " hFill=" + hFill);
                    for (int i = 0; i < n; i += batch) {
                        List<String> ks = new ArrayList<String>();
                        List<byte[]> vs = new ArrayList<byte[]>();
                        for (int j = i; j < Math.min(n, i + batch); j++) {
                            ks.add(mkey(round, j));
                            vs.add(null);
                            lastMass.add(mkey(round, j));
                        }
                        run.exec(ks, vs);
                    }
                    print(run, q, "deleted", run.measure());
                    Reclaim.Stats.Iteration open = run.inProgress();
                    System.out.println(String.format("%s q=%d reclaim: at the deletes' end an "
                            + "iteration in progress: %s", label, q, open == null ? "none"
                            : "yes, tStart " + (open.tStart < tFill ? "before the fill"
                            : open.tStart < tDel ? "during the fill (" + (open.tStart - tFill)
                            / l("dt", 10000) + " transactions in)" : "during the deletes ("
                            + (open.tStart - tDel) / l("dt", 10000) + " transactions in)")));
                    run.verify("after the deletes, round " + round, rnd);
                    int started = run.stats.iterations.size() - itersAtStart;
                    int done = 0;
                    for (int k = itersAtStart; k < run.stats.iterations.size(); k++) {
                        if (run.stats.iterations.get(k).pEnd != -1) done++;
                    }
                    System.out.println(String.format("%s q=%d reclaim: an iteration in progress "
                            + "at the fill: %s; it ended %s; iterations started during the "
                            + "disturbance %d, of them done %d", label, q,
                            spanning == null ? "none" : "yes (tStart " + spanning.tStart + ")",
                            spanning == null ? "-" : (spanning.pEnd == -1 ? "not yet"
                                    : "at tEnd " + spanning.tEnd), started, done));
                }
                run.restart();
                if (disturb) run.cutWatch = 0;
                print(run, q, "restarted", run.measure());
                run.verify("after the restart, round " + round, rnd);
                lastDist = q;
            }
            // One transaction of the workload.
            List<String> ks = new ArrayList<String>(2);
            List<byte[]> vs = new ArrayList<byte[]>(2);
            if (queue) {
                ks.add(qkey(q, hashed));
                vs.add(value(valsize, q));
                if (q >= live) {
                    ks.add(qkey(q - live, hashed));
                    vs.add(null);
                }
            } else {
                ks.add(A_KEY);
                vs.add(value(dvalsize, q));
            }
            run.exec(ks, vs);
            if (run.cutWatch >= 0) {
                run.cutWatch++;
                if (!run.stats.cuts.isEmpty()) {
                    System.out.println(String.format("%s q=%d reclaim: the first cut after the "
                            + "restart, %d transactions after it", label, q + 1, run.cutWatch));
                    run.cutWatch = -1;
                } else if (run.cutWatch == distEvery - 1) {
                    System.out.println(String.format("%s q=%d reclaim: no cut since the "
                            + "restart, %d transactions", label, q + 1, run.cutWatch));
                    run.cutWatch = -1;
                }
            }
            // Keys deleted more than R (and a margin) ago leave the model.
            final int keep = (int) (run.retain / l("dt", 10000)) + 100;
            if (queue && q >= live + keep) run.model.remove(qkey(q - live - keep, hashed));
            int done = q + 1;
            if (done % sampleEvery == 0) run.sample();
            if (done % every == 0 || (lastDist >= 0 && early.contains(done - lastDist))) {
                print(run, done, "cp", run.measure());
            }
        }
        run.verify("at the end", rnd);
        run.restart();
        print(run, m, "end-restarted", run.measure());
        run.db.close();
        System.out.println(label + " DONE " + (System.nanoTime() - t0) / 1000000 + " ms");
    }

    public static void main(String[] args) throws Exception {
        CleanupRatchet c = new CleanupRatchet(args);
        System.out.println("CleanupRatchet " + c.p);
        String which = c.s("which", "both");
        if (!which.equals("dist")) c.run("twin", false);
        if (!which.equals("twin")) c.run("dist", true);
    }
}
