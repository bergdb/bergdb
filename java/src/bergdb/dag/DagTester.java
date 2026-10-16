package bergdb.dag;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

public class DagTester {
    
    private static final int MAX_NODE_SIZE = 30;
    
    private static final PointerFollower DUMMY_POINTER_FOLLOWER = new PointerFollower() {
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node result;
            assert pointerIndex >= 0 : "pointerIndex: " + pointerIndex;
            assert predecessor != null : "predecessor is null";

            Node pointerNode = predecessor.getPointerNode(pointerIndex);
            long pointerPos1 = predecessor.getPointerPos(pointerIndex);

            assert !Pointer.isNull(pointerNode, pointerPos1) : "Pointer is null: " + pointerNode
                    + ", " + pointerPos1;

            if (Pointer.isMem(pointerNode)) {
                result = pointerNode;
                if (op.accessData != AccessData.ZERO) {
                    predecessor.setPointerAccessData(pointerIndex, op.accessData);
                }
                op.pointerListener.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
            
            } else {
                throw new IllegalStateException("This NodeFollower does not support stream pointers.");
            }

            return result;
        }
    };
    
    public static Dag emptyDag(long time) {        
        return Dag.createEmpty(time, MAX_NODE_SIZE, DUMMY_POINTER_FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
    }
    
    private static Dag emptyDag(long time, Dag.PointerCreatedListener listener) {
        return Dag.createEmpty(time, MAX_NODE_SIZE, DUMMY_POINTER_FOLLOWER, listener);
    }
    
    private static GetData gd(Dag dag) {
        GetData gd = dag.newGetData();
        gd.pointerFollower = DUMMY_POINTER_FOLLOWER;
        return gd;
    }
    
    private static PutData pd(Dag dag) {
        PutData pd = dag.newPutData();
        pd.pointerFollower = DUMMY_POINTER_FOLLOWER;
        return pd;
    }
    
    @Nano
    public static void test0() {
        Dag dag = emptyDag(0);
        GetData gd = gd(dag);
        byte[] result = dag.getOne(0, Keys.toSegments("/-k1"), gd);
        Assert.assertTrue(result == null);
    }
    
    @Nano
    public static void test1() {
        // With choices
        Dag dag = emptyDag(0);
        GetData gd = gd(dag);
        final ArrayList<Integer> choices = new ArrayList<Integer>();
        
        gd.pointerListener = new Dag.PointerListener() {
            public void pointerFollowed(Node predecessor, int pointerIndex, Node result, int pointerType) {
                choices.add(pointerIndex);
            }

            public void superRootAccessed(TopNode superRoot) {
            }
        };
        
        byte[] result = dag.getOne(0, Keys.toSegments("/-k1"), gd);
        
        Assert.assertTrue(result == null);
        Assert.assertEquals(1, choices.size());
        Assert.assertEquals(0, choices.get(0).intValue());
    }
    
    @Nano
    public static void testPut0() {
        Dag dag = emptyDag(0);
        PutData pd = pd(dag);
        pd.tt = 10;
        
        dag.putKv(Keys.toSegments("/-key"), StringUtil.toBytes("value"), pd);
        
        //for (int i = 0; i < pd.keyAccessPath.getSize(); i++) {
        //    System.out.println("keyAccessPath: " + Klong.toString(pd.keyAccessPath.getKlong(i)) 
        //            + "->" + pd.keyAccessPath.get(i));
        //}
        
        GetData gd = gd(dag);
        byte[] value = dag.getOne(20, Keys.toSegments("/-key"), gd);
        
        Assert.assertTrue(value != null);
        Assert.assertEquals("value", StringUtil.toString(value));
        
        value = dag.getOne(9, Keys.toSegments("/-key"), gd);
        Assert.assertTrue(value == null);
    }
    
    @Nano
    public static void testPut1() {
        Dag dag = emptyDag(0);
        PutData pd = pd(dag);
        pd.tt = 10;
        
        dag.putKv(Keys.toSegments("/longerKey1"), StringUtil.toBytes("value"), pd);
        
        pd.keyAccessPath.clear();
        
        dag.putKv(Keys.toSegments("/longerKey2"), StringUtil.toBytes("value"), pd);
        
        GetData gd = gd(dag);
        byte[] value = dag.getOne(20, Keys.toSegments("/longerKey1"), gd);
        
        Assert.assertTrue(value != null);
        Assert.assertEquals("value", StringUtil.toString(value));
        
        value = dag.getOne(9, Keys.toSegments("/longerKey"), gd);
        Assert.assertTrue(value == null);
    }
    
    /**
     * Deleting a key that does not exist is a no-op; it must not create or change any
     * node. Keys of 7 bytes or more have more than one key segment.
     * Regression test for a bug found 2026-10-12: the delete created a key node
     * for a missing segment, the rerun at startup did not, so node ids differed after
     * a restart.
     */
    @Nano
    public static void testDeleteMissingKey() {
        Dag dag = emptyDag(0);
        PutData pd = pd(dag);
        pd.tt = 10;
        dag.putKv(Keys.toSegments("/a"), StringUtil.toBytes("value"), pd);
        pd.clearFast();
        dag.putKv(Keys.toSegments("/abcdefXX"), StringUtil.toBytes("value"), pd);
        pd.clearFast();

        final ArrayList<String> changes = new ArrayList<String>();
        pd.nodeChangeListener = new Dag.NodeChangeListener() {
            public void topNodeCreated(TopNode node) { changes.add("topNodeCreated"); }
            public void keyNodeCreated(KeyNode node) { changes.add("keyNodeCreated"); }
            public void valueNodeCreated(ValueNode node, long[] key) { changes.add("valueNodeCreated"); }
            public void keyNodeChanged(KeyNode node) { changes.add("keyNodeChanged"); }
        };

        // One, two and three segments; the first segment of the last key exists.
        String[] keys = {"/k/100", "/k/1000", "/k/10000000", "/abcdefgh12345"};
        pd.tt = 20;

        for (String key : keys) {
            dag.putKv(Keys.toSegments(key), null, pd);
            pd.clearFast();
            Assert.assertEquals("changes when deleting missing key " + key, "[]", changes.toString());
        }

        GetData gd = gd(dag);
        Assert.assertEquals("value", StringUtil.toString(dag.getOne(30, Keys.toSegments("/abcdefXX"), gd)));
    }

    /**
     * Transactions with several keys each, checked against a model at every time.
     * Regression test for a bug found 2026-10-12: when the space root was
     * replaced twice in one transaction (a time split, then a space split), two top
     * nodes got the same time, and TopDs.findSuperRootAtTime() could later return the
     * older one, which misses the rest of the transaction. One failing seed per node
     * size, found with java/stress/DagFuzz.java (same random sequence).
     */
    @Nano
    public static void testTwoNewRootsInOneTransaction() {
        checkRandomTransactions(8, 10, 4, 5, 923);
        checkRandomTransactions(14, 12, 12, 14, 1);
        checkRandomTransactions(30, 20, 20, 11, 37);
    }
    
    private static void checkRandomTransactions(int maxNodeSize, int keyCount, int maxOps, 
            int n, long seed) {
        Random rnd = new Random(seed);
        Dag dag = Dag.createEmpty(0, maxNodeSize, DUMMY_POINTER_FOLLOWER, 
                Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        PutData pd = pd(dag);
        GetData gd = gd(dag);
        Map<String, TreeMap<Long, String>> model = new HashMap<String, TreeMap<Long, String>>();
        
        for (int i = 1; i <= n; i++) {
            long tt = 10 * i;
            pd.tt = tt;
            int ops = 1 + rnd.nextInt(maxOps);
            Set<String> keys = new LinkedHashSet<String>();
            while (keys.size() < ops) {
                keys.add("/k/" + rnd.nextInt(keyCount));
            }
            
            for (String key : keys) {
                String value = rnd.nextInt(4) == 0 ? null : "v" + tt + key;
                dag.putKv(Keys.toSegments(key), value == null ? null : StringUtil.toBytes(value), pd);
                pd.clearFast();
                if (!model.containsKey(key)) {
                    model.put(key, new TreeMap<Long, String>());
                }
                model.get(key).put(tt, value);
            }
            pd.clear();
        }
        
        for (String key : model.keySet()) {
            for (long t = 0; t <= 10 * n; t += 10) {
                Map.Entry<Long, String> e = model.get(key).floorEntry(t);
                Object expected = e == null ? null : e.getValue();
                byte[] bytes = dag.getOne(t, Keys.toSegments(key), gd);
                Object actual = bytes == null ? null : StringUtil.toString(bytes);
                Assert.assertEquals("maxNodeSize " + maxNodeSize + ", seed " + seed + ", key " 
                        + key + " at time " + t, expected, actual);
            }
        }
    }
    
    @Nano
    public static void testSplit0() {
        // Splits space root node. New super root node (top node) needed.
        
        String[] kvs = new String[] {
                "/k1", "v1", "/k2", "v2", "/k3", "v3", "/k4", "v4", "/k0", "v0"
        };
        Dag dag = Dag.createEmpty(0, 6, DUMMY_POINTER_FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        
        PutData pd = pd(dag);
        pd.tt = 10;
        
        for (int i = 0; i < kvs.length; i += 2) {
            dag.putKv(Keys.toSegments(kvs[i]), StringUtil.toBytes(kvs[i + 1]), pd);
            pd.clearFast();
        }
        pd.clear();
        
        Assert.assertEquals(1, pd.spaceSplitCount);
        GetData gd = gd(dag);
        for (int i = 0; i < kvs.length; i += 2) {
            byte[] value = dag.getOne(10, Keys.toSegments(kvs[i]), gd);
            Assert.assertEquals(kvs[i + 1], StringUtil.toString(value));
        }
        
        for (int i = 0; i < kvs.length; i += 2) {
            byte[] value = dag.getOne(9, Keys.toSegments(kvs[i]), gd);
            Assert.assertEquals(null, value);
        }
    }
    
    @Nano
    public static void testTimeSplit1a() {
        // Tests a time-split-1.

        Dag dag = Dag.createEmpty(0, 6, DUMMY_POINTER_FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        PutData pd = pd(dag);
        
        for (int i = 0; i < 4; i++) {
            String keyString = "account-id-0";
            pd.tt = 1 + i;
            dag.putKv(Keys.toSegments(keyString), StringUtil.toBytes("v at " + pd.tt), pd);
            pd.clearFast();
        }
        
        Assert.assertEquals(1, pd.timeSplitCount);
        
        KeyNode node = (KeyNode) dag.findNode(new int[]{0, 3}, gd(dag));
        KlongWithPointer kwi = new KlongWithPointer();
        node.searchEq(Long.MAX_VALUE, Klong.createCompareValue(Keys.toBytes("-id-0")), kwi);
        
        Assert.assertEquals(4, kwi.klongTime);
    }
    
    @Nano
    public static void testVisit0() {
        Dag g = emptyDag(10);
        final int[] counters = new int[3];
        
        g.visitMemoryNodes(new NodeVisitor() {
            public void visit(TopNode node) { counters[0]++; }
            public void visit(KeyNode node) { counters[1]++; }
            public void visit(ValueNode node) { counters[2]++; }
        });
        
        Assert.assertEquals(1, counters[0]);
        Assert.assertEquals(1, counters[1]);
        Assert.assertEquals(0, counters[2]);
    }
    
    @Nano
    public static void testVisit1() {
        Dag dag = emptyDag(10);
        PutData pd = pd(dag);
        pd.tt = 20;
        
        for (int i = 0; i < 4; i++) {
            dag.putKv(Keys.toSegments("/prefix-" + i), StringUtil.toBytes("v" + i), pd);
        }
        
        StatsNodeVisitor v = new StatsNodeVisitor();
        dag.visitMemoryNodes(v);
        
        Assert.assertEquals(1, v.topCount);
        Assert.assertEquals(2, v.keyCount);
        Assert.assertEquals(4, v.valueCount);
    }
    
    @Nano
    private static void testPointerCreationListener1() {
        testPointerCreationListener(200);
    }
    
    @Nano("f")
    private static void testPointerCreationListener2() {
        testPointerCreationListener(10*1000);
    }
    
    /**
     * The last pointer reported for a node is the node's last memory pointer, unless the
     * transaction that reported it replaced the node by a split: a replaced node loses its
     * klongs of that transaction (Dag.handleFullNode, since 2026-10-16), so then its last
     * memory pointer is the last one reported in an earlier transaction.
     */
    @SuppressWarnings("unchecked")
    private static void testPointerCreationListener(int n) {
        final HashMap<Node, Node> map1 = new HashMap<Node, Node>();
        final HashMap<Node, Node> map2 = new HashMap<Node, Node>();
        final HashMap<Node, Node> earlier = new HashMap<Node, Node>();
            // the last pointer reported in an earlier transaction, per node
        final HashMap<Node, Long> timeOfLast = new HashMap<Node, Long>();
        final long[] now = new long[]{10};      // the time of the current transaction
        
        Dag.PointerCreatedListener listener = new Dag.PointerCreatedListener() {
            public void pointerCreated(Node from, int index, Node to) {
                Long t = timeOfLast.get(from);
                if (t != null && t < now[0]) {
                    earlier.put(from, map1.get(from));
                }
                map1.put(from, to);
                timeOfLast.put(from, now[0]);
            }
        };
        
        Dag dag = emptyDag(10, listener);
        PutData pd = pd(dag);
        pd.tt = 20;
        now[0] = pd.tt;
        pd.pointerCreatedListener = listener;
        pd.nodeChangeListener = new Dag.NodeChangeListener() {
            public void topNodeCreated(TopNode node) {}
            public void keyNodeCreated(KeyNode node) {}
            public void keyNodeChanged(KeyNode node) {}
            public void valueNodeCreated(ValueNode node, long[] key) {}
            
            public void keyNodeReplaced(KeyNode node) {
                Long t = timeOfLast.get(node);
                if (t != null && t == now[0]) {
                    Node e = earlier.get(node);
                    if (e == null) {
                        map1.remove(node);
                    } else {
                        map1.put(node, e);
                    }
                }
            }
        };
        
        for (int i = 0; i < n; i++) {
            dag.putKv(Keys.toSegments("/prefix-" + i), StringUtil.toBytes("v" + i), pd);
            if (i % 10 == 9) {
                pd.tt += 10;
                now[0] = pd.tt;
            }
        }
        
        dag.visitMemoryPointersOnce(new PointerVisitor() {
            public void visitNode(Node node) {
            }

            public void visitPointer(Node from, Pointer pointer) {
                map2.put(from, pointer.node);
            }
        });
        
        //printMap("map1", map1);
        //printMap("map2", map2);
        
        HashMap<Node, Node> diff = (HashMap<Node, Node>) map1.clone();
        
        diff.entrySet().removeAll(map2.entrySet());
        
        Assert.assertTrue(map1.size() > 0);
        Assert.assertEquals("map sizes", map1.size(), map2.size());
        Assert.assertEquals("diff size", 0, diff.size());
    }
    
    /**
     * A transaction of 40 sorted puts into an empty tree at node size 8, then one of 40 puts
     * between those keys: every node a transaction creates is reachable at its time, and
     * every node it changed is reachable at its time, or was replaced and has no klong of
     * the time (assumptions A2 and A3 of the Lean model; docs/level2-alignment.md, M1). The
     * root changes several times in the first transaction, which makes one top node: the
     * second root change updates it in place. Before 2026-10-16, 17 of the 39 key nodes that
     * the first transaction created were never reachable (F1-008-10).
     */
    @Nano
    private static void testTransactionLeavesNoUnreachableNode() {
        Dag dag = Dag.createEmpty(10, 8, DUMMY_POINTER_FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        PutData pd = pd(dag);
        final Set<Node> created = identitySet(), changed = identitySet(), replaced = identitySet();
        final int[] topNodes = new int[1];
        pd.nodeChangeListener = new Dag.NodeChangeListener() {
            public void topNodeCreated(TopNode node) { created.add(node); topNodes[0]++; }
            public void keyNodeCreated(KeyNode node) { created.add(node); }
            public void keyNodeChanged(KeyNode node) { changed.add(node); }
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void keyNodeReplaced(KeyNode node) { replaced.add(node); }
        };
        
        for (int round = 0; round < 2; round++) {
            created.clear();
            changed.clear();
            replaced.clear();
            topNodes[0] = 0;
            pd.tt = 20 + 10 * round;
            for (int i = 0; i < 40; i++) {
                String key = "/k/" + (1000 + 2 * i + round);
                dag.putKv(Keys.toSegments(key), StringUtil.toBytes("v" + key), pd);
                pd.clearFast();
            }
            pd.clear();
            
            Set<Node> now = reachableAt(dag, pd.tt);
            for (Node x : created) {
                Assert.assertTrue("round " + round + ": created and not reachable, " + x,
                        now.contains(x));
            }
            for (Node x : changed) {
                if (!now.contains(x)) {
                    Assert.assertTrue("round " + round + ": changed, not reachable, not replaced",
                            replaced.contains(x));
                    Assert.assertTrue("round " + round + ": replaced, with a klong of its time",
                            !hasTimeKlong((KeyNode) x, pd.tt));
                }
            }
            if (round == 0) {
                Assert.assertEquals("top nodes made by the first transaction", 1, topNodes[0]);
            }
        }
        
        GetData gd = gd(dag);
        for (int round = 0; round < 2; round++) {
            for (int i = 0; i < 40; i++) {
                String key = "/k/" + (1000 + 2 * i + round);
                Assert.assertArrayEquals(key, StringUtil.toBytes("v" + key),
                        dag.getOne(30, Keys.toSegments(key), gd));
            }
        }
    }
    
    private static Set<Node> identitySet() {
        return Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
    }
    
    private static boolean hasTimeKlong(KeyNode k, long t) {
        for (int i = 0; i < k.size; i++) {
            if (Klong.isTime(k.klongs[i]) && Klong.getTime(k.klongs[i]) == t) return true;
        }
        return false;
    }
    
    /**
     * The nodes reachable at time t: the super root at t, its root key node, and the live
     * children at t, for each compare value the last key klong up to t that is not deleted.
     */
    private static Set<Node> reachableAt(Dag dag, long t) {
        Set<Node> r = identitySet();
        TopNode top = dag.getTopDs().findSuperRootAtTime(t, gd(dag));
        if (top == null) return r;
        r.add(top);
        Deque<Node> stack = new ArrayDeque<Node>();
        stack.push(top.rootPointer);
        while (!stack.isEmpty()) {
            Node x = stack.pop();
            if (!r.add(x) || !(x instanceof KeyNode)) continue;
            KeyNode k = (KeyNode) x;
            int sz = k.size;
            long del = k.getDeleteBitmapAtTime(t, sz);
            LinkedHashMap<Long, Integer> last = new LinkedHashMap<Long, Integer>();
            for (int i = 0; i < sz; i++) {
                long klong = k.klongs[i];
                if (Klong.isTime(klong)) {
                    if (Klong.getTime(klong) > t) break;
                    continue;
                }
                if (Klong.getType(klong) == Klong.TYPE_KEY && !Klong.isDeleted(del, i)) {
                    last.put(Klong.getCompareValue(klong), i);
                }
            }
            List<Integer> indexes = new ArrayList<Integer>(last.values());
            for (int i : indexes) stack.push(k.pointers[i]);
        }
        return r;
    }
    
    @SuppressWarnings("unused")
    private static void printMap(String name, HashMap<Node, Node> map) {
        System.out.println("---- " + name + " ----");
        for (Map.Entry<Node, Node> en : map.entrySet()) {
            System.out.println(en.getKey() + " --> " + en.getValue());
        }
    }

    public static void main(String[] args) {
        Dag g = emptyDag(10);
        PutData pd = g.newPutData();
        pd.tt = 20;
        
        g.putKv(Keys.toSegments("/-k1"), StringUtil.toBytes("v1"), pd);
        g.putKv(Keys.toSegments("/-k2"), StringUtil.toBytes("v2"), pd);
        
        g.printGraph(System.out);
    }
}
