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
    
    /**
     * The walks of the nodes in memory, loops with a stack of their own since bergdb 021-16,
     * visit the nodes in the order of the recursions they replaced (the references below):
     * visitMemoryNodes() and visitMemoryPointersOnce() each node once, depth first, and
     * DagNodeIterator every path. The graph has replaced nodes, so some nodes have two
     * pointers to them in memory, and deletes.
     */
    @Nano
    public static void testWalksKeepTheirOrder() {
        Dag dag = Dag.createEmpty(10, 8, DUMMY_POINTER_FOLLOWER,
                Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        PutData pd = pd(dag);
        pd.tt = 20;
        Random random = new Random(21016);
        for (int i = 0; i < 400; i++) {
            String key = "/k" + random.nextInt(40) + "/" + random.nextInt(4);
            byte[] value = random.nextInt(8) == 0 ? null : StringUtil.toBytes("v" + i);
            dag.putKv(Keys.toSegments(key), value, pd);
            pd.clearFast();
            if (i % 7 == 6) {
                pd.tt += 10;
            }
        }
        final Node superRoot = dag.getTopDs().getSuperRoot();
        
        final List<Node> visited = new ArrayList<Node>();
        dag.visitMemoryNodes(new NodeVisitor() {
            public void visit(TopNode node) { visited.add(node); }
            public void visit(KeyNode node) { visited.add(node); }
            public void visit(ValueNode node) { visited.add(node); }
        });
        List<Node> expected = new ArrayList<Node>();
        referenceVisit(superRoot, Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>()),
                expected);
        assertSameNodes("visitMemoryNodes()", expected, visited);
        
        final List<Object> events = new ArrayList<Object>();
        dag.visitMemoryPointersOnce(new PointerVisitor() {
            public void visitNode(Node node) {
                events.add(node);
            }
            
            public void visitPointer(Node from, Pointer pointer) {
                events.add(from);
                events.add(pointer.getNode());
            }
        });
        List<Object> expectedEvents = new ArrayList<Object>();
        referencePointers(superRoot,
                Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>()), expectedEvents);
        assertSameNodes("visitMemoryPointersOnce()", expectedEvents, events);
        
        List<Node> iterated = new ArrayList<Node>();
        DagNodeIterator iterator = new DagNodeIterator(dag);
        for (Node n = iterator.next(); n != null; n = iterator.next()) {
            iterated.add(n);
        }
        Assert.assertTrue("next() after the end", iterator.next() == null);
        List<Node> expectedPaths = new ArrayList<Node>();
        referenceIterator(superRoot, Long.MAX_VALUE, expectedPaths);
        assertSameNodes("DagNodeIterator", expectedPaths, iterated);
        Assert.assertTrue("a node met twice", expectedPaths.size() > expected.size());
    }
    
    private static void assertSameNodes(String about, List<?> expected, List<?> actual) {
        Assert.assertTrue(about + ": no nodes", expected.size() > 100);
        Assert.assertEquals(about + ": the count", expected.size(), actual.size());
        for (int i = 0; i < expected.size(); i++) {
            Assert.assertTrue(about + ": the node at " + i, expected.get(i) == actual.get(i));
        }
    }
    
    /** visitMemoryNodes() before bergdb 021-16, a recursion. */
    private static void referenceVisit(Node node, Set<Node> visited, List<Node> out) {
        if (!visited.add(node)) {
            return;
        }
        out.add(node);
        Pointer p = new Pointer();
        int size = node.getSize();
        for (int i = 0; i < size; i++) {
            node.getPointer(i, p);
            if (p.isMem()) {
                referenceVisit(p.getNode(), visited, out);
            }
        }
    }
    
    /** visitMemoryPointersOnce() before bergdb 021-16, a recursion. */
    private static void referencePointers(Node node, Set<Node> visited, List<Object> out) {
        if (!visited.add(node)) {
            return;
        }
        out.add(node);
        Pointer p = new Pointer();
        int size = node.getSize();
        for (int i = 0; i < size; i++) {
            node.getPointer(i, p);
            if (p.isMem()) {
                out.add(node);
                out.add(p.getNode());
                referencePointers(p.getNode(), visited, out);
            }
        }
    }
    
    /** DagNodeIterator before bergdb 021-16, a recursion: every path, depth first. */
    private static void referenceIterator(Node node, long maxLookupTime, List<Node> out) {
        out.add(node);
        int n = node.getSizeAtTime(maxLookupTime);
        Pointer p = new Pointer();
        for (int i = 0; i < n; i++) {
            node.getPointer(i, p);
            if (p.isNull()) {
                continue;
            }
            long childMax = maxLookupTime;
            if (node.isKeyNode()) {
                childMax = Math.min(maxLookupTime, ((KeyNode) node).getMaxValidTime(i));
            }
            referenceIterator(p.getNode(), childMax, out);
        }
    }
    
    /**
     * A key of 400,000 bytes, a level of key nodes per segment of 7 bytes: the walks of the
     * nodes in memory reach every node, with the thread's default stack. Each was a
     * recursion with a frame per level until bergdb 021-16, and threw StackOverflowError.
     */
    @Nano
    public static void testLongKeyWalks() {
        Dag dag = emptyDag(10);
        PutData pd = pd(dag);
        pd.tt = 20;
        byte[] longKey = new byte[400 * 1000];
        java.util.Arrays.fill(longKey, (byte) 'k');
        dag.putKv(Keys.toSegments(longKey), StringUtil.toBytes("long"), pd);
        pd.clearFast();
        dag.putKv(Keys.toSegments("/a"), StringUtil.toBytes("short"), pd);
        pd.clearFast();
        
        StatsNodeVisitor v = new StatsNodeVisitor();
        dag.visitMemoryNodes(v);
        Assert.assertEquals("top nodes", 1, v.topCount);
        Assert.assertTrue("key nodes: " + v.keyCount,
                v.keyCount >= Keys.toSegments(longKey).length);
        Assert.assertEquals("value nodes", 2, v.valueCount);
        final long nodes = v.topCount + v.keyCount + v.valueCount;
        
        final long[] count = new long[1];
        dag.visitMemoryPointersOnce(new PointerVisitor() {
            public void visitNode(Node node) {
                count[0]++;
            }
            
            public void visitPointer(Node from, Pointer pointer) {}
        });
        Assert.assertEquals("visitMemoryPointersOnce()", nodes, count[0]);
        
        long iterated = 0;
        DagNodeIterator iterator = new DagNodeIterator(dag);
        while (iterator.next() != null) {
            iterated++;
        }
        Assert.assertEquals("DagNodeIterator", nodes, iterated);
        
        Assert.assertArrayEquals(StringUtil.toBytes("long"),
                dag.getOne(Long.MAX_VALUE, Keys.toSegments(longKey), gd(dag)));
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
     * the time (assumptions A2 and A3 of the Lean model; bergdb 011-11, M1). The
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
    
    /**
     * Fault 12 (bergdb 023-08, review C; the check of it, sections 3 and 4, ShadowProbe mode
     * 2): one transaction puts z keys after a history of b keys in one segment tree, then
     * deletes every b key, in that order, out of key order, as a Core KeyTransformation could
     * give them to the Dag before Db sorted the transformed keys (023-08, section 7). One
     * operation a key: until 2026-11-10 some z keys were deleted again too (mode 0).
     * The segment root that the transaction made is split in place under a new root, and the
     * deletes empty and take it back. No klong of a node reachable at any time, live, deleted
     * or shadowed, may name a node taken back: such a node is never written. Failed in the
     * first iterations without the in-place repoint of Dag.spaceSplitInPlace, the segment
     * leaf's second klong of tt to the new root shadowing the one that still named the root.
     */
    @Nano
    public static void testNoKlongNamesATakenBackNode() {
        Random r = new Random(1);
        for (int iter = 0; iter < 40; iter++) {
            final int b = 4 + r.nextInt(5);
            Dag dag = Dag.createEmpty(0, b, DUMMY_POINTER_FOLLOWER,
                    Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
            PutData pd = pd(dag);
            final Set<Node> takenBack = identitySet();
            pd.nodeChangeListener = new Dag.NodeChangeListener() {
                public void topNodeCreated(TopNode node) {}
                public void keyNodeCreated(KeyNode node) {}
                public void valueNodeCreated(ValueNode node, long[] key) {}
                public void keyNodeChanged(KeyNode node) {}
                public void keyNodeTakenBack(KeyNode node) { takenBack.add(node); }
            };
            int nb = 1 + r.nextInt(60);
            int hist = 1 + r.nextInt(4);
            long t = 1;
            List<String> keys = new ArrayList<String>();
            List<Boolean> deletes = new ArrayList<Boolean>();
            for (int h = 0; h < hist; h++, t++) {
                keys.clear();
                deletes.clear();
                for (int i = 0; i < nb; i++) {
                    if (h == 0 || r.nextInt(3) == 0) {
                        keys.add(prefixKey("b", i));
                        deletes.add(false);
                    }
                }
                putAll(dag, pd, t, keys, deletes);
            }
            keys.clear();
            deletes.clear();
            int nz = 1 + r.nextInt(120);
            for (int i = 0; i < nz; i++) { keys.add(prefixKey("z", i)); deletes.add(false); }
            for (int i = 0; i < nb; i++) { keys.add(prefixKey("b", i)); deletes.add(true); }
            putAll(dag, pd, t, keys, deletes);
            
            String at = "iter " + iter + ", b " + b + ", nb " + nb + ", hist " + hist + ", nz "
                    + nz + ": ";
            Set<Node> seen = identitySet();
            Deque<KeyNode> todo = new ArrayDeque<KeyNode>();
            for (long u = 0; u <= t; u++) {
                KeyNode root = dag.getTopDs().findRoot(u, gd(dag));
                if (root != null && seen.add(root)) todo.add(root);
            }
            while (!todo.isEmpty()) {
                KeyNode n = todo.poll();
                Assert.assertTrue(at + "a taken-back node is reachable", !takenBack.contains(n));
                for (int i = 0; i < n.size; i++) {
                    if (!Klong.isKey(n.klongs[i])) continue;
                    Node c = n.getPointerNode(i);
                    Assert.assertTrue(at + "klong " + i + " names a taken-back node:\n" + n.print(),
                            c == null || !takenBack.contains(c));
                    if (c instanceof KeyNode && seen.add(c)) todo.add((KeyNode) c);
                }
            }
            GetData gd = gd(dag);
            for (int i = 0; i < keys.size(); i++) {
                boolean deleted = deletes.get(keys.lastIndexOf(keys.get(i)));
                byte[] v = dag.getOne(t, Keys.toSegments(keys.get(i)), gd);
                Assert.assertEquals(at + keys.get(i), deleted, v == null);
            }
        }
    }
    
    /**
     * Every key deleted, after a transaction that split the space root (bergdb 023-07,
     * section 5.1; 023-08, review C, 5.3, item 3): one transaction puts keys between those of
     * an earlier one, so that the space root and its nodes are split by it, and deletes every
     * old key, one operation a key; the next deletes the new keys. Root collapse lowers the
     * space root as it loses its children: at the last time it is a segment leaf, empty, and
     * every key is gone; at the times before, the keys put then are there. Node sizes 4 and
     * 8, keys of one segment and of two.
     */
    @Nano
    public static void testDeleteEveryKeyAfterTheRootSplit() {
        final long collapses0 = Dag.statCollapses;
        for (int b : new int[] {4, 8}) {
            for (String prefix : new String[] {"/k", "/key/prefix/"}) {
                String at = "b " + b + ", prefix " + prefix + ": ";
                Dag dag = Dag.createEmpty(0, b, DUMMY_POINTER_FOLLOWER,
                        Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
                PutData pd = pd(dag);
                List<String> keys = new ArrayList<String>();
                List<Boolean> deletes = new ArrayList<Boolean>();
                for (int i = 0; i < 60; i += 2) {
                    keys.add(prefix + (100 + i));
                    deletes.add(false);
                }
                putAll(dag, pd, 1, keys, deletes);
                List<String> old = new ArrayList<String>(keys);
                keys.clear();
                deletes.clear();
                for (int i = 0; i < 60; i++) {
                    keys.add(prefix + (100 + i));
                    deletes.add(i % 2 == 0);    // the old keys deleted, new ones put
                }
                putAll(dag, pd, 2, keys, deletes);
                keys.clear();
                deletes.clear();
                for (int i = 1; i < 60; i += 2) {
                    keys.add(prefix + (100 + i));
                    deletes.add(true);
                }
                putAll(dag, pd, 3, keys, deletes);
                
                GetData gd = gd(dag);
                KeyNode root = dag.getTopDs().findRoot(3, gd);
                Assert.assertTrue(at + "the root is a segment leaf", root.isSegmentLeaf());
                for (int i = 0; i < 60; i++) {
                    String k = prefix + (100 + i);
                    Assert.assertTrue(at + k, dag.getOne(3, Keys.toSegments(k), gd) == null);
                    Assert.assertEquals(at + k + " at 2", !old.contains(k),
                            dag.getOne(2, Keys.toSegments(k), gd) != null);
                    Assert.assertEquals(at + k + " at 1", old.contains(k),
                            dag.getOne(1, Keys.toSegments(k), gd) != null);
                }
            }
        }
        Assert.assertTrue("root collapses", Dag.statCollapses > collapses0);
    }
    
    /**
     * Dag.dirtyNodeBound for transactions with deletes (bergdb 023-07, section 5.4, K4;
     * 023-08, reviews B and C, 2.5, and C, 5.3, item 4) against the key nodes that the
     * transaction makes dirty: those the writer follows, makes or changes, less those it
     * replaces, unlinks or takes back (review C's BoundProbe2). At node sizes 8, 14 and 30:
     * (1) random histories, thinned out to leave chains of single children, and a transaction
     * of deletes and some puts; (2) a chain that root collapse takes in one delete, several
     * levels, each a klong in the segment leaf above; (3) transactions of 1,000 deletes, and
     * one of 100,000 at node size 30.
     */
    @Nano
    public static void testDirtyNodeBoundOfDeletes() {
        Random r = new Random(5);
        for (int b : new int[] {8, 14, 30}) {
            for (int iter = 0; iter < 40; iter++) {
                BoundCase c = new BoundCase(b);
                int nk = 20 + r.nextInt(b * b * 3);
                int shape = r.nextInt(4);
                String[] keys = new String[nk];
                for (int i = 0; i < nk; i++) {
                    switch (shape) {
                    case 0: keys[i] = "/k/" + String.format("%05d", i); break;
                    case 1: keys[i] = "/prefix/" + (char) ('a' + i % 3) + "/" + String.format("%05d", i); break;
                    case 2: keys[i] = "/p" + String.format("%05d", i % 5) + "/x" + String.format("%05d", i); break;
                    default: keys[i] = "/longprefix/abcdefgh/" + String.format("%05d", i) + (i % 2 == 0 ? "/tail/more" : ""); break;
                    }
                }
                java.util.Arrays.sort(keys, new java.util.Comparator<String>() {
                    public int compare(String x, String y) {
                        return Keys.compareArrays(Keys.toSegments(x), Keys.toSegments(y));
                    }
                });
                Set<Integer> live = new java.util.TreeSet<Integer>();
                int hist = 1 + r.nextInt(4);
                for (int h = 0; h < hist; h++) {
                    List<String> ks = new ArrayList<String>();
                    for (int i = 0; i < nk; i++) {
                        if (h == 0 || r.nextInt(4) == 0) { ks.add(keys[i]); live.add(i); }
                    }
                    c.run(ks, null, false);
                }
                if (r.nextBoolean()) {
                    int k = 2 + r.nextInt(b);
                    List<String> ks = new ArrayList<String>();
                    for (int i = 0; i < nk; i++) {
                        if (i % k != 0 && live.remove(i)) ks.add(keys[i]);
                    }
                    c.run(new ArrayList<String>(), ks, false);
                }
                List<String> puts = new ArrayList<String>(), dels = new ArrayList<String>();
                int lo = r.nextInt(nk), hi = lo + r.nextInt(nk - lo + 1), pdel = r.nextInt(101);
                boolean range = r.nextBoolean();
                for (int i = 0; i < nk; i++) {
                    boolean del = range ? i >= lo && i < hi : r.nextInt(100) < pdel;
                    if (del && live.contains(i)) dels.add(keys[i]);
                    else if (r.nextInt(50) == 0) puts.add(keys[i]);
                }
                c.run(puts, dels, true);
            }
            
            // (2) A chain: keep the first and the last key of a segment tree of three or more
            // levels; then a delete of the first leaves the root one child, a chain of single
            // children down to the last key's leaf, which root collapse takes in one delete.
            BoundCase c = new BoundCase(b);
            List<String> all = new ArrayList<String>();
            int n = b * b * 2;
            for (int i = 0; i < n; i++) all.add("/prefix/" + String.format("%05d", i));
            c.run(all, null, false);
            c.run(new ArrayList<String>(), all.subList(1, n - 1), true);
            long collapses0 = Dag.statCollapses;
            c.run(new ArrayList<String>(), all.subList(0, 1), true);
            Assert.assertTrue("b " + b + ": a collapse of several levels in one delete",
                    Dag.statCollapses - collapses0 >= 2);
            
            // (2b) The same chain below a segment leaf filled with live klongs to one klong
            // short of full, so that the collapses' klongs overflow it.
            for (int extra = 0; extra < 3; extra++) {
                c = new BoundCase(b);
                c.run(all, null, false);
                c.run(new ArrayList<String>(), all.subList(1, n - 1), false);
                KeyNode leaf = c.dag.getTopDs().findRoot(c.t - 1, gd(c.dag));
                Assert.assertTrue("b " + b + ": the space root is a segment leaf", leaf.isSegmentLeaf());
                List<String> fill = new ArrayList<String>();
                for (int i = 0; i < b - 2 - leaf.size + extra && i < 20; i++) {
                    fill.add("/" + (char) ('a' + i) + "aaaaa/x");
                }
                c.run(fill, null, false);
                collapses0 = Dag.statCollapses;
                c.run(new ArrayList<String>(), all.subList(0, 1), true);
                Assert.assertTrue("b " + b + ", extra " + extra + ": collapses of several levels",
                        Dag.statCollapses - collapses0 >= 2);
            }
            
            // (3) 1,000 deletes, of every key and of every third.
            for (int step : new int[] {1, 3}) {
                c = new BoundCase(b);
                all.clear();
                for (int i = 0; i < 1000 * step; i++) all.add("/k/" + String.format("%06d", i));
                c.run(all, null, false);
                List<String> dels = new ArrayList<String>();
                for (int i = 0; i < all.size(); i += step) dels.add(all.get(i));
                c.run(new ArrayList<String>(), dels, true);
            }
        }
        BoundCase c = new BoundCase(30);
        List<String> all = new ArrayList<String>();
        for (int i = 0; i < 100000; i++) all.add("/big/" + String.format("%06d", i));
        c.run(all, null, false);
        c.run(new ArrayList<String>(), all, true);
    }
    
    /** A Dag and the key nodes a transaction makes dirty, for testDirtyNodeBoundOfDeletes. */
    private static final class BoundCase {
        final Dag dag;
        final PutData pd;
        final Set<Node> dirty = identitySet();
        long t = 1;
        
        BoundCase(int b) {
            dag = Dag.createEmpty(0, b, DUMMY_POINTER_FOLLOWER,
                    Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
            pd = pd(dag);
            final Dag.PointerListener inner = pd.pointerListener;
            pd.pointerListener = new Dag.PointerListener() {
                public void pointerFollowed(Node pred, int i, Node result, int type) {
                    if (result instanceof KeyNode) dirty.add(result);
                    inner.pointerFollowed(pred, i, result, type);
                }
                public void superRootAccessed(TopNode s) {}
            };
            pd.nodeChangeListener = new Dag.NodeChangeListener() {
                public void topNodeCreated(TopNode node) {}
                public void keyNodeCreated(KeyNode node) { dirty.add(node); }
                public void valueNodeCreated(ValueNode node, long[] key) {}
                public void keyNodeChanged(KeyNode node) { dirty.add(node); }
                public void keyNodeReplaced(KeyNode node) { dirty.remove(node); }
            };
        }
        
        /** One transaction: the puts, then the deletes; with 'check', against the bound. */
        void run(List<String> puts, List<String> dels, boolean check) {
            List<String> ks = new ArrayList<String>(puts);
            if (dels != null) ks.addAll(dels);
            long bound = -1;
            if (check) {
                long[][] keys = new long[ks.size()][];
                boolean[] deletes = new boolean[ks.size()];
                for (int i = 0; i < ks.size(); i++) {
                    keys[i] = Keys.toSegments(ks.get(i));
                    deletes[i] = i >= puts.size();
                }
                bound = dag.dirtyNodeBound(t - 1, keys, deletes, gd(dag));
            }
            dirty.clear();
            pd.tt = t;
            for (int i = 0; i < ks.size(); i++) {
                byte[] v = i < puts.size() ? StringUtil.toBytes("v" + t) : null;
                dag.putKv(Keys.toSegments(ks.get(i)), v, pd);
                pd.clearFast();
            }
            pd.clear();
            if (check) {
                Assert.assertTrue("t " + t + ", " + puts.size() + " puts, " + ks.size() + " keys: "
                        + dirty.size() + " dirty key nodes, bound " + bound, dirty.size() <= bound);
            }
            t++;
        }
    }
    
    private static String prefixKey(String segment, int i) {
        return "/prefix/" + segment + String.format("%04d", i);
    }
    
    private static void putAll(Dag dag, PutData pd, long tt, List<String> keys,
            List<Boolean> deletes) {
        pd.tt = tt;
        for (int i = 0; i < keys.size(); i++) {
            String k = keys.get(i);
            dag.putKv(Keys.toSegments(k), deletes.get(i) ? null : StringUtil.toBytes("v" + tt + k), pd);
            pd.clearFast();
        }
        pd.clear();
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
        stack.push(top.getPointerNode(0));
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
            for (int i : indexes) stack.push(k.getPointerNode(i));
        }
        return r;
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
