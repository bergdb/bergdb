package bergdb.dag;

import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Option 2 of dead klongs, compaction at the write (bergdb 024-23; 024-18, section 4), on the
 * Dag alone, in memory: PE replaces a node whose append would leave more than theta dead
 * KEY klongs by its final live list, in one node if it fits, else cut into parts. Every node
 * holds at most theta dead klongs after every transaction (TP39; bergdb 027-08). The
 * restarts that rerun the compactions are DbTesterMerge's.
 *
 * @author Frans Lundberg
 */
public class DeadKlongTester {

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

    /** A Dag with a model of every key's history. */
    private static final class Run {
        final Dag dag;
        final PutData pd;
        final TreeMap<String, TreeMap<Long, String>> model = new TreeMap<String, TreeMap<Long, String>>();
        long t = 0;

        Run(int b) {
            dag = Dag.createEmpty(0, b, FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
            pd = dag.newPutData();
            pd.pointerFollower = FOLLOWER;
        }

        GetData gd() {
            GetData gd = dag.newGetData();
            gd.pointerFollower = FOLLOWER;
            return gd;
        }

        /** One transaction; the keys are of one length, so the map's order is the key order. */
        void trans(TreeMap<String, String> ops) {
            t += 10;
            pd.tt = t;
            java.util.List<String> keys = new java.util.ArrayList<String>(ops.keySet());
            java.util.List<byte[]> values = new java.util.ArrayList<byte[]>();
            for (String v : ops.values()) {
                values.add(v == null ? null : StringUtil.toBytes(v));
            }
            DagTester.batch(dag, pd, keys, values);
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
        }

        void put(String key, String value) {
            TreeMap<String, String> ops = new TreeMap<String, String>();
            ops.put(key, value);
            trans(ops);
        }

        /** The space root at the latest time. */
        KeyNode root() {
            return dag.getTopDs().findRoot(t, gd());
        }

        /** Every key's get at every time against the model. */
        void checkGets(String at) {
            GetData gd = gd();
            for (long u = 10; u <= t; u += 10) {
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

        /** BU1 and TP39 at the latest time (Dag.checkFill). */
        Dag.Fill checkFill(String at) {
            Dag.Fill f = dag.checkFill(t, gd());
            Assert.assertTrue(at + ", t " + t + ": " + f, f.error == null);
            return f;
        }
    }

    private static String key(int i) {
        return "/k" + String.format("%03d", i);
    }

    /**
     * theta, Dag.THETA_30 scaled as the thresholds are, at least 2 (024-19, Q4: 1 at 8 until
     * 2026-11-12); 0 below node size 8 (024-23, OD2) until 2026-11-20, when such sizes became
     * refused (bergdb 028-38).
     */
    @Nano
    public static void testTheta() {
        Assert.assertEquals(2, Dag.theta(8));
        Assert.assertEquals(3, Dag.theta(14));
        Assert.assertEquals(7, Dag.theta(30));
        Assert.assertEquals(14, Dag.theta(62));
    }

    /**
     * A leaf (the space root) of 10 keys at node size 30 gets 7 overwrites of one key: it holds
     * 7 dead klongs, theta, in 25 klongs, room for more. The 8th overwrite would leave 8: the
     * leaf is replaced by its last version with the put, 11 klongs and none dead; the old one
     * keeps its history for lookups before. dirtyNodeBound counts the replacement.
     */
    @Nano
    public static void testCompactionAtTheta() {
        Run r = new Run(30);
        TreeMap<String, String> ops = new TreeMap<String, String>();
        for (int i = 0; i < 10; i++) ops.put(key(i), "v" + i);
        r.trans(ops);
        final KeyNode leaf = r.root();
        for (int j = 1; j <= 7; j++) {
            r.put(key(0), "w" + j);
            Assert.assertTrue("the same leaf", r.root() == leaf);
            Assert.assertEquals(j, Dag.deadCount(leaf));
        }
        Assert.assertEquals(25, leaf.getSize());
        long bound = r.dag.dirtyNodeBound(r.t, new long[][] {Keys.toSegments(key(0))},
                new boolean[] {false}, r.gd());
        Assert.assertTrue("dirtyNodeBound " + bound, bound >= 2);

        final long compactions0 = Dag.statCompactions;
        r.put(key(0), "w8");
        Assert.assertEquals(compactions0 + 1, Dag.statCompactions);
        KeyNode last = r.root();
        Assert.assertTrue("a new leaf", last != leaf && last.isSegmentLeaf());
        Assert.assertEquals(11, last.getSize());
        Assert.assertEquals(0, Dag.deadCount(last));
        Assert.assertEquals(25, leaf.getSize());
        r.checkGets("after the compaction");
        r.checkFill("after the compaction");
    }

    /**
     * PE's compaction makes one node when the live list fits, even above h: a leaf of 18
     * keys (19 klongs; h = 17 at node size 30) gets 7 overwrites in one transaction (27
     * klongs, 7 dead), then one more: it had room, so it is compacted to one leaf of 19
     * klongs. Until record format 8 rule O of a full node would space split it instead.
     */
    @Nano
    public static void testCompactionIsOneNode() {
        Run r = new Run(30);
        TreeMap<String, String> ops = new TreeMap<String, String>();
        for (int i = 0; i < 18; i++) ops.put(key(i), "v" + i);
        r.trans(ops);
        ops = new TreeMap<String, String>();
        for (int i = 0; i < 7; i++) ops.put(key(i), "w" + i);
        r.trans(ops);
        Assert.assertEquals(27, r.root().getSize());
        Assert.assertEquals(7, Dag.deadCount(r.root()));

        final long compactions0 = Dag.statCompactions;
        r.put(key(7), "w7");
        Assert.assertEquals(compactions0 + 1, Dag.statCompactions);
        KeyNode last = r.root();
        Assert.assertTrue("one leaf", last.isSegmentLeaf());
        Assert.assertEquals(19, last.getSize());
        Assert.assertTrue("above h", last.getSize() > Dag.splitAbove(30));
        Assert.assertEquals(0, Dag.deadCount(last));
        r.checkGets("after the compaction");
    }

    /**
     * A bitmap is a write too: a leaf of 14 keys with 6 dead klongs gets three deletes in one
     * transaction, which would leave it 9 dead klongs, above theta, so the leaf is replaced by
     * one node of its live list, the time klong and 11 keys, none dead. (Until record format 8,
     * whose writer decides a node once from the transaction's whole batch, bergdb 026-25: the
     * first delete made 7, theta; the second would make 8 by the transaction's own bitmap in
     * place, so the leaf was replaced by its last version without the two keys, and the third
     * delete went to that new node, 14 klongs, one dead.)
     */
    @Nano
    public static void testOwnBitmapIsAWrite() {
        Run r = new Run(30);
        TreeMap<String, String> ops = new TreeMap<String, String>();
        for (int i = 0; i < 14; i++) ops.put(key(i), "v" + i);
        r.trans(ops);
        ops = new TreeMap<String, String>();
        for (int i = 0; i < 6; i++) ops.put(key(i), "w" + i);
        r.trans(ops);
        final KeyNode leaf = r.root();
        Assert.assertEquals(6, Dag.deadCount(leaf));

        final long compactions0 = Dag.statCompactions;
        ops = new TreeMap<String, String>();
        for (int i = 10; i < 13; i++) ops.put(key(i), null);
        r.trans(ops);
        Assert.assertEquals(compactions0 + 1, Dag.statCompactions);
        KeyNode last = r.root();
        Assert.assertTrue("a new leaf", last != leaf);
        // T and the 11 keys left.
        Assert.assertEquals(12, last.getSize());
        Assert.assertEquals(0, Dag.deadCount(last));
        r.checkGets("after the deletes");
        r.checkFill("after the deletes");
    }

    /**
     * Random transactions of puts, overwrites and deletes on 300 keys at node sizes 8, 14
     * and 30: after every transaction BU1 and at most theta dead klongs in every reachable
     * node (checkFill), and the most of a node reaches theta: the rule lets a node fill to
     * theta and no further. Every key's get at every time at the end.
     */
    @Nano
    public static void testRandomAtMostTheta() {
        for (int b : new int[] {8, 14, 30}) {
            Run r = new Run(b);
            Random rnd = new Random(b);
            final long compactions0 = Dag.statCompactions;
            long deadMax = 0;
            for (int i = 0; i < 200; i++) {
                TreeMap<String, String> ops = new TreeMap<String, String>();
                int n = 1 + rnd.nextInt(30);
                for (int j = 0; j < n; j++) {
                    String k = key(rnd.nextInt(300));
                    ops.put(k, rnd.nextInt(100) < 25 ? null : "v" + i + "." + j);
                }
                r.trans(ops);
                deadMax = Math.max(deadMax, r.checkFill("node size " + b + ", T" + i).deadMax);
            }
            Assert.assertEquals("node size " + b + ": the most dead klongs a node",
                    Dag.theta(b), deadMax);
            Assert.assertTrue("compactions", Dag.statCompactions > compactions0);
            r.checkGets("node size " + b);
        }
    }
}
