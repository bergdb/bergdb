package bergdb.dag;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;

import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * The merges at the delete (bergdb 024-21; 024-11, sections 5 and 6), since record format 8
 * the writer's joins (PeWriter's rebalance; bergdb 026-25), on the Dag alone, in memory: BU1
 * checked after every transaction (Dag.checkFill: V1, V2, V4 and TU2's count), lookups at
 * every time against a model, joins of leaves and inner nodes, cuts and root collapses
 * reached, the shape against a twin (BU2), and thrash at a boundary (TU5). Until format 8 also
 * V8 (no klong names a node taken back) and the cases of prototype P5 (023-05, section 2.4):
 * the writer of format 8 takes no node back.
 *
 * @author Frans Lundberg
 */
public class MergeTester {

    private static final PointerFollower FOLLOWER = new PointerFollower() {
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node result = predecessor.getPointerNode(pointerIndex);
            if (!Pointer.isMem(result)) {
                throw new IllegalStateException("stream pointer");
            }
            op.pointerListener.pointerFollowed(predecessor, pointerIndex, result,
                    Pointer.TYPE_MEMORY);
            return result;
        }
    };

    private static final Comparator<String> BYTES = new Comparator<String>() {
        public int compare(String a, String b) {
            return Keys.compareArrays(Keys.toSegments(a), Keys.toSegments(b));
        }
    };

    /** A Dag with a model of every key's history, and the checks after each transaction. */
    private static final class Run {
        final Dag dag;
        final PutData pd;
        final TreeMap<String, TreeMap<Long, String>> model =
                new TreeMap<String, TreeMap<Long, String>>(BYTES);
        final Set<Node> madeNow = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        final List<Long> times = new ArrayList<Long>();
        long t = 0;
        long newNodes = 0;

        Run(int b) {
            dag = Dag.createEmpty(0, b, FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
            pd = dag.newPutData();
            pd.pointerFollower = FOLLOWER;
            pd.nodeChangeListener = new Dag.NodeChangeListener() {
                public void topNodeCreated(TopNode node) {}
                public void keyNodeCreated(KeyNode node) { madeNow.add(node); newNodes++; }
                public void valueNodeCreated(ValueNode node, long[] key) {}
                public void keyNodeChanged(KeyNode node) {}
            };
        }

        GetData gd() {
            GetData gd = dag.newGetData();
            gd.pointerFollower = FOLLOWER;
            return gd;
        }

        /** One transaction: the keys in key order (as Db sorts them), a null value a delete. */
        void trans(TreeMap<String, String> ops) {
            t += 10;
            pd.tt = t;
            final long[][] keys = new long[ops.size()][];
            final byte[][] values = new byte[ops.size()][];
            int i = 0;
            for (Map.Entry<String, String> e : ops.entrySet()) {
                String v = e.getValue();
                keys[i] = Keys.toSegments(e.getKey());
                values[i++] = v == null ? null : StringUtil.toBytes(v);
            }
            dag.putKvs(keys, values, pd);
            pd.clearFast();
            for (Map.Entry<String, String> e : ops.entrySet()) {
                String v = e.getValue();
                TreeMap<Long, String> h = model.get(e.getKey());
                if (h == null) {
                    h = new TreeMap<Long, String>();
                    model.put(e.getKey(), h);
                }
                h.put(t, v);
            }
            pd.clear();
            madeNow.clear();
            times.add(t);
        }

        /** BU1 at the latest time; returns the walk's counts. */
        Dag.Fill checkFill(String at) {
            Dag.Fill f = dag.checkFill(t, gd());
            Assert.assertTrue(at + ", t " + t + ": " + f, f.error == null);
            return f;
        }

        /** Gets of every key at every time of 'every'-th transaction, and the latest. */
        void checkGets(String at, int every) {
            GetData gd = gd();
            for (int i = times.size() - 1; i >= 0; i -= every) {
                long u = times.get(i);
                for (Map.Entry<String, TreeMap<Long, String>> e : model.entrySet()) {
                    Map.Entry<Long, String> v = e.getValue().floorEntry(u);
                    String exp = v == null ? null : v.getValue();
                    byte[] got = dag.getOne(u, Keys.toSegments(e.getKey()), gd);
                    String act = got == null ? null : StringUtil.toString(got);
                    if (exp == null ? act != null : !exp.equals(act)) {
                        throw new AssertionError(at + ": get " + e.getKey() + " at " + u
                                + ", expected " + exp + ", got " + act);
                    }
                }
            }
        }

        /** A full scan at time u against the model. */
        void checkScan(String at, long u) {
            GetMany g = dag.newGetMany();
            g.gd.pointerFollower = FOLLOWER;
            g.lookupTime = u;
            g.actualLookupTime = u;
            g.forward = true;
            dag.getMany(g);
            List<String> got = new ArrayList<String>();
            for (Kvt kvt : g.result) got.add(Keys.toString(kvt.key));
            List<String> exp = new ArrayList<String>();
            for (Map.Entry<String, TreeMap<Long, String>> e : model.entrySet()) {
                Map.Entry<Long, String> v = e.getValue().floorEntry(u);
                if (v != null && v.getValue() != null) exp.add(e.getKey());
            }
            Assert.assertEquals(at + ": scan at " + u, exp, got);
        }

    }

    private static String key(int i) {
        return "/k/" + String.format("%06d", i);
    }

    private static String longKey(int i) {
        int a = i % 7, b = (i / 7) % 5;
        switch (i % 3) {
        case 0: return "/k/" + i;
        case 1: return "/long/prefix" + a + "/x" + b + "/" + i;
        default: return "/long/prefix" + a + "/y" + i + "/tail/more/" + b;
        }
    }

    /**
     * TU1 and TU2 (bergdb 024-11): random transactions of puts and deletes, most of them
     * deletes in a second phase, keys of one segment and of up to three; after every
     * transaction BU1 (Dag.checkFill), and lookups at every time and scans against the model;
     * reached: joins (merges) of leaves and of inner nodes, cuts of a list into new nodes,
     * appends, and root collapse. Node sizes 8, 14, 30. (Until record format 8: V8 at the
     * end, and the cases of prototype P5, 023-05, section 2.4: merges into one node and into
     * two, a left and a right node made by the transaction, two klongs of one compare value
     * in the parent, nodes taken back.)
     */
    @Nano
    public static void testFillAfterEveryTransaction() {
        final long joins0 = Dag.statJoins, cuts0 = Dag.statCuts, appends0 = Dag.statAppends,
                collapses0 = Dag.statCollapses;
        Random r = new Random(21);
        for (int b : new int[] {8, 14, 30}) {
            for (int shape = 0; shape < 2; shape++) {
                String at = "b " + b + ", shape " + shape;
                Run run = new Run(b);
                int keys = b * 25;
                for (int i = 0; i < 120; i++) {
                    int del = i < 40 ? 15 : 70;
                    int ops = 1 + r.nextInt(i < 40 ? 3 * b : b);
                    TreeMap<String, String> trans = new TreeMap<String, String>(BYTES);
                    while (trans.size() < ops) {
                        int k = r.nextInt(keys);
                        String key = shape == 0 ? key(k) : longKey(k);
                        trans.put(key, r.nextInt(100) < del ? null : "v" + i + "-" + k);
                    }
                    run.trans(trans);
                    run.checkFill(at + ", transaction " + i);
                    if (i % 10 == 9) {
                        run.checkGets(at, 3);
                        run.checkScan(at, run.t);
                    }
                }
                run.checkGets(at, 1);
            }
        }
        Assert.assertTrue("joins", Dag.statJoins > joins0);
        Assert.assertTrue("cuts", Dag.statCuts > cuts0);
        Assert.assertTrue("appends", Dag.statAppends > appends0);
        Assert.assertTrue("root collapses", Dag.statCollapses > collapses0);
    }

    /**
     * TU3 and TU4 at a small size (bergdb 024-11; 023-03, T2's "sparse"): 3,000 keys put in
     * key order, 100 a transaction; then every key but each k-th deleted, 100 a transaction,
     * in ascending, descending or random order. Right after the deletes, with no reclaim (R
     * forever): BU1, the key nodes at most twice the twin's (BU2), a fresh Dag with the kept
     * keys put in key order in transactions of the same size, and a scan of every key against
     * the model. Node sizes 8 and 30; k = 2, 3, 10, 30.
     */
    @Nano
    public static void testSparseAgainstTwin() {
        for (int b : new int[] {8, 30}) {
            for (int k : new int[] {2, 3, 10, 30}) {
                for (int order = 0; order < 3; order++) {
                    String at = "b " + b + ", k " + k + ", order " + order;
                    final int n = 3000;
                    Run run = new Run(b);
                    for (int i = 0; i < n; i += 100) {
                        TreeMap<String, String> tr = new TreeMap<String, String>(BYTES);
                        for (int j = i; j < i + 100; j++) tr.put(key(j), "v" + j);
                        run.trans(tr);
                    }
                    List<Integer> dels = new ArrayList<Integer>();
                    for (int i = 0; i < n; i++) if (i % k != 0) dels.add(i);
                    if (order == 1) Collections.reverse(dels);
                    if (order == 2) Collections.shuffle(dels, new Random(k));
                    for (int i = 0; i < dels.size(); i += 100) {
                        TreeMap<String, String> tr = new TreeMap<String, String>(BYTES);
                        for (int j = i; j < Math.min(dels.size(), i + 100); j++) {
                            tr.put(key(dels.get(j)), null);
                        }
                        run.trans(tr);
                        run.checkFill(at + ", deletes " + i);
                    }
                    Dag.Fill f = run.checkFill(at);
                    run.checkScan(at, run.t);
                    Run twin = new Run(b);
                    for (int i = 0; i < n; i += 100 * k) {
                        TreeMap<String, String> tr = new TreeMap<String, String>(BYTES);
                        for (int j = i; j < Math.min(n, i + 100 * k); j += k) tr.put(key(j), "v" + j);
                        twin.trans(tr);
                    }
                    Dag.Fill ft = twin.checkFill(at + ", twin");
                    Assert.assertEquals(at + ": live keys", ft.liveKeys, f.liveKeys);
                    Assert.assertTrue(at + ": key nodes " + f.keyNodes + ", the twin's "
                            + ft.keyNodes + " (BU2)", f.keyNodes <= 2 * ft.keyNodes);
                }
            }
        }
    }

    /**
     * TU5, thrash (bergdb 024-11, CB4): 2,000 keys put in key order, one a transaction, which
     * leaves the leaves at the halves of their splits; then one key in the middle deleted and
     * put again in turns, and three keys next to it too, 10,000 transactions of one operation:
     * at most 0.5 new key nodes an operation at node sizes 14 and 30, BU1 every 100. Measured
     * on 2026-11-11 (2026.4's in brackets): 0.093 at 30 (0.093), 0.300 at 14 (0.207), 0.750
     * at 8 (0.375), where a merged node of c + 1 = 5 klongs fills in two transactions and a
     * space split's halves hold m = 2: a split and a merge every few operations, so at most
     * 1.0 there (bergdb 024-21, section 5).
     */
    @Nano
    public static void testThrashAtABoundary() {
        for (int b : new int[] {8, 14, 30}) {
            Run run = new Run(b);
            for (int i = 0; i < 2000; i++) {
                TreeMap<String, String> tr = new TreeMap<String, String>(BYTES);
                tr.put(key(i), "v");
                run.trans(tr);
            }
            long nodes0 = run.newNodes;
            int ops = 10000;
            for (int i = 0; i < ops; i++) {
                TreeMap<String, String> tr = new TreeMap<String, String>(BYTES);
                int k = 1000 + (i / 2) % 4;
                tr.put(key(k), i % 2 == 0 ? null : "w" + i);
                run.trans(tr);
                if (i % 100 == 0) run.checkFill("b " + b + ", operation " + i);
            }
            double perOp = (run.newNodes - nodes0) / (double) ops;
            Assert.assertTrue("b " + b + ": new key nodes an operation " + perOp,
                    perOp <= (b == 8 ? 1.0 : 0.5));
            run.checkFill("b " + b);
        }
    }

    /**
     * A delete transaction of every key but the first and the last of a tree of several
     * levels (the chain of single children that 2026.4 left, 023-11, review B, B1): with the
     * merges every node but a root keeps m live klongs, so the two keys end in one leaf under
     * the space root's tree, and the next delete collapses at most one level. Node sizes 8, 14
     * and 30; BU1 after each transaction.
     */
    @Nano
    public static void testNoChainOfSingleChildren() {
        for (int b : new int[] {8, 14, 30}) {
            Run run = new Run(b);
            int n = b * b * 2;
            TreeMap<String, String> tr = new TreeMap<String, String>(BYTES);
            for (int i = 0; i < n; i++) tr.put(key(i), "v");
            run.trans(tr);
            tr = new TreeMap<String, String>(BYTES);
            for (int i = 1; i < n - 1; i++) tr.put(key(i), null);
            run.trans(tr);
            Dag.Fill f = run.checkFill("b " + b);
            Assert.assertTrue("b " + b + ": key nodes " + f, f.keyNodes <= 3);
            long c0 = Dag.statCollapses;
            tr = new TreeMap<String, String>(BYTES);
            tr.put(key(0), null);
            run.trans(tr);
            run.checkFill("b " + b + ", the last delete");
            Assert.assertTrue("b " + b + ": collapses " + (Dag.statCollapses - c0),
                    Dag.statCollapses - c0 <= 1);
            run.checkGets("b " + b, 1);
        }
    }

    /**
     * 024-22's MF1 (its J4): until record format 8, a delete in a full leaf made a rule O first
     * (a time split whose last version has m - 1 live klongs), whose klong could split the
     * parent and make a new root, and then merges and root collapse, in one operation. The
     * model's smallest case at node size 8: twelve keys (the smallest, "/" for the model's
     * empty key, eight of one segment, three under one 7-byte prefix and one under another),
     * each put in its own transaction, all again in one, then a put of the smallest, then its
     * delete. Since format 8 (bergdb 026-25) the delete joins the leaf; after it BU1, every
     * get at every time, and dirtyNodeBound at least the key nodes made dirty.
     */
    @Nano
    public static void testRuleOBeforeAMerge() {
        final String[] keys = {"/", "/a", "/bbbbbb1", "/bbbbbb2", "/bbbbbb3", "/c", "/dddddd4",
                "/e", "/f", "/g", "/h", "/i"};
        Run run = new Run(8);
        for (String k : keys) {
            TreeMap<String, String> tr = new TreeMap<String, String>(BYTES);
            tr.put(k, "v");
            run.trans(tr);
        }
        TreeMap<String, String> all = new TreeMap<String, String>(BYTES);
        for (String k : keys) all.put(k, "w");
        run.trans(all);
        TreeMap<String, String> put = new TreeMap<String, String>(BYTES);
        put.put("/", "x");
        run.trans(put);
        run.checkFill("the put");
        
        // The delete, with dirtyNodeBound before it and the key nodes it makes dirty.
        final Set<Node> dirty = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        long bound = run.dag.dirtyNodeBound(run.t, new long[][] {Keys.toSegments("/")},
                new boolean[] {true}, run.gd());
        final Dag.PointerListener inner = run.pd.pointerListener;
        final Dag.NodeChangeListener changes = run.pd.nodeChangeListener;
        run.pd.pointerListener = new Dag.PointerListener() {
            public void pointerFollowed(Node pred, int i, Node result, int type) {
                if (result instanceof KeyNode) dirty.add(result);
                inner.pointerFollowed(pred, i, result, type);
            }
            public void superRootAccessed(TopNode s) {}
        };
        run.pd.nodeChangeListener = new Dag.NodeChangeListener() {
            public void topNodeCreated(TopNode node) {}
            public void keyNodeCreated(KeyNode node) { dirty.add(node); changes.keyNodeCreated(node); }
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void keyNodeChanged(KeyNode node) { dirty.add(node); }
            public void keyNodeReplaced(KeyNode node) { dirty.remove(node); }
            public void keyNodeOnPath(KeyNode node) { dirty.add(node); }
        };
        final long joins0 = Dag.statJoins;
        TreeMap<String, String> del = new TreeMap<String, String>(BYTES);
        del.put("/", null);
        run.trans(del);
        Assert.assertTrue("a join in the delete", Dag.statJoins > joins0);
        Assert.assertTrue("dirty key nodes " + dirty.size() + ", bound " + bound,
                dirty.size() <= bound);
        run.checkFill("the delete");
        run.checkGets("the delete", 1);
    }
    
    /**
     * The thresholds of format 7 (bergdb 024-21, section 2; 024-14, QT1: 8/17/17 at node size
     * 30, scaled to other node sizes): the values at the database's node sizes, h = B / 2
     * below 8 as in 2026.4, no merges there, and V1's conditions (024-11, section 5.4) for
     * every node size from 8 to 64: a space split's halves and a redistribution's halves hold
     * at least m, a merge into one node fits in c, and h and c leave room in a node.
     */
    @Nano
    public static void testThresholds() {
        int[][] at = {{8, 2, 4, 4}, {14, 3, 7, 7}, {30, 8, 17, 17}, {62, 16, 35, 35}};
        for (int[] x : at) {
            Assert.assertEquals("m at " + x[0], x[1], Dag.minFill(x[0]));
            Assert.assertEquals("h at " + x[0], x[2], Dag.splitAbove(x[0]));
            Assert.assertEquals("c at " + x[0], x[3], Dag.mergeCap(x[0]));
            // The cut of format 8 (bergdb 026-25): a list of more than h entries is cut into
            // parts of at most cutSize = B / 2, at least two, as even as possible; each part
            // holds at least m: the smallest part of a cut into k is of a list of more than
            // (k - 1) cutSize entries, or of more than h for k = 2.
            int b = x[0], m = Dag.minFill(b), cap = Dag.cutSize(b), h = Dag.splitAbove(b);
            Assert.assertEquals("cut size at " + b, b / 2, cap);
            Assert.assertTrue("b " + b + ": a cut's parts", (Math.min(h, cap) + 1) / 2 >= m);
        }
        for (int b = 2; b < 8; b++) {
            Assert.assertEquals("m at " + b, 1, Dag.minFill(b));
            Assert.assertEquals("h at " + b, b / 2, Dag.splitAbove(b));
        }
        for (int b = 8; b <= 64; b++) {
            int m = Dag.minFill(b), h = Dag.splitAbove(b), c = Dag.mergeCap(b);
            Assert.assertTrue("b " + b + ": h and c leave room", h <= b - 2 && c <= b - 2);
            Assert.assertTrue("b " + b + ": a space split's halves", h / 2 >= m);
            Assert.assertTrue("b " + b + ": a redistribution's halves", (c + 1) / 2 >= m);
            Assert.assertTrue("b " + b + ": a merge into one node", 2 * m - 1 <= c);
            Assert.assertTrue("b " + b + ": m >= 2", m >= 2);
        }
    }
}
