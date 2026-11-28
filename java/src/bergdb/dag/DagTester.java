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
        
        batchOf(dag, pd, "/longerKey1", "value", "/longerKey2", "value");
        
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
        batchOf(dag, pd, "/a", "value", "/abcdefXX", "value");

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
            
            List<String> ks = new ArrayList<String>();
            List<byte[]> vs = new ArrayList<byte[]>();
            for (String key : keys) {
                String value = rnd.nextInt(4) == 0 ? null : "v" + tt + key;
                ks.add(key);
                vs.add(value == null ? null : StringUtil.toBytes(value));
                if (!model.containsKey(key)) {
                    model.put(key, new TreeMap<Long, String>());
                }
                model.get(key).put(tt, value);
            }
            batch(dag, pd, ks, vs);
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
                "/k1", "v1", "/k2", "v2", "/k3", "v3", "/k4", "v4", "/k0", "v0", "/k5", "v5",
                "/k6", "v6", "/k7", "v7", "/k8", "v8", "/k9", "v9"
        };
        Dag dag = Dag.createEmpty(0, 8, DUMMY_POINTER_FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        
        PutData pd = pd(dag);
        pd.tt = 10;
        
        final TopNode top0 = dag.getTopDs().getSuperRoot();
        batchOf(dag, pd, kvs);
        
        // Since record format 8 the transaction's ten keys, more than h = 4 and more than the
        // node with its time klong holds, are cut into leaves under a new root, which a new
        // top node names (bergdb 026-25). Seven keys fill the empty root of node size 8.
        // Node size 6 until 2026-11-20, when sizes below 8 became refused (bergdb 028-38).
        Assert.assertTrue("a new super root", dag.getTopDs().getSuperRoot() != top0);
        Assert.assertTrue("an inner space root",
                !dag.getTopDs().findRoot(10, gd(dag)).isSegmentLeaf());
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
    
    /**
     * A key put again and again, one transaction a time, at node size 8 (6 until 2026-11-20,
     * bergdb 028-38): its segment leaf
     * fills with dead klongs and is replaced by one new node, its live list (until record
     * format 8 a time split, "time-split-1"); every value at its time.
     */
    @Nano
    public static void testTimeSplit1a() {
        Dag dag = Dag.createEmpty(0, 8, DUMMY_POINTER_FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        PutData pd = pd(dag);
        final long replaced0 = Dag.statReplaces + Dag.statCompactions;
        
        for (int i = 0; i < 4; i++) {
            String keyString = "account-id-0";
            pd.tt = 1 + i;
            dag.putKv(Keys.toSegments(keyString), StringUtil.toBytes("v at " + pd.tt), pd);
            pd.clearFast();
        }
        
        Assert.assertTrue("a node replaced by one", Dag.statReplaces + Dag.statCompactions > replaced0);
        GetData gd = gd(dag);
        for (int t = 1; t <= 4; t++) {
            Assert.assertEquals("v at " + t, StringUtil.toString(
                    dag.getOne(t, Keys.toSegments("account-id-0"), gd)));
        }
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
        
        batchOf(dag, pd, "/prefix-0", "v0", "/prefix-1", "v1", "/prefix-2", "v2", "/prefix-3", "v3");
        
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
        List<String> ks = new ArrayList<String>();
        List<byte[]> vs = new ArrayList<byte[]>();
        for (int i = 0; i < 400; i++) {
            String key = "/k" + random.nextInt(40) + "/" + random.nextInt(4);
            byte[] value = random.nextInt(8) == 0 ? null : StringUtil.toBytes("v" + i);
            ks.add(key);
            vs.add(value);
            if (i % 7 == 6) {
                batch(dag, pd, ks, vs);
                ks.clear();
                vs.clear();
                pd.tt += 10;
            }
        }
        batch(dag, pd, ks, vs);
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
     * nodes in memory reach every node, with the thread's default stack, and so does
     * dirtyNodeBound() for a new key of 500,000 bytes with its start (since 2026-11-28, from
     * DbTesterLongKeys). Each was a recursion with a frame per level until bergdb 021-16, and
     * threw StackOverflowError.
     */
    @Nano
    public static void testLongKeyWalks() {
        Dag dag = emptyDag(10);
        PutData pd = pd(dag);
        pd.tt = 20;
        byte[] longKey = new byte[400 * 1000];
        java.util.Arrays.fill(longKey, (byte) 'k');
        long[][] keys = {Keys.toSegments("/a"), Keys.toSegments(longKey)};
        if (Keys.compareArrays(keys[0], keys[1]) > 0) {
            keys = new long[][] {keys[1], keys[0]};
        }
        byte[][] values = new byte[2][];
        for (int i = 0; i < 2; i++) {
            values[i] = StringUtil.toBytes(keys[i].length == 1 ? "short" : "long");
        }
        dag.putKvs(keys, values, pd);
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
        
        // dirtyNodeBound()'s walk of a new key with the long key's start: its path, then the
        // new key's segment trees (freshTreeBound; bergdb 021-16, U5-2). Since L9 (bergdb
        // 024-17, 2026-11-28) no transaction gives the Core a new key this long; the Core's
        // tests (DbTesterLongKeys) walk the longer own keys that a stream may hold.
        byte[] longer = java.util.Arrays.copyOf(longKey, 500 * 1000);
        java.util.Arrays.fill(longer, longKey.length, longer.length, (byte) 'j');
        final long[] longerKey = Keys.toSegments(longer);
        final long bound = dag.dirtyNodeBound(Long.MAX_VALUE, new long[][] {longerKey},
                new boolean[] {false}, gd(dag));
        Assert.assertTrue("dirtyNodeBound(): " + bound, bound >= longerKey.length);
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
     * The last pointer reported for a node is its last memory pointer. PE plans the whole
     * batch and emits each node once; a replaced base receives no klongs or pointers from
     * this transaction (bergdb 027-08). Until record format 8 Dag.handleFullNode could
     * replace a node already written by that transaction and remove its new klongs, so the
     * listener restores the last pointer reported in an earlier transaction in that case.
     * The former key access path was cleared after each put since bergdb 024-23: before
     * that it grew over the test's puts and could give a replaced space root a wrong parent.
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
        
        List<String> ks = new ArrayList<String>();
        List<byte[]> vs = new ArrayList<byte[]>();
        for (int i = 0; i < n; i++) {
            ks.add("/prefix-" + i);
            vs.add(StringUtil.toBytes("v" + i));
            if (i % 10 == 9 || i == n - 1) {
                batch(dag, pd, ks, vs);
                ks.clear();
                vs.clear();
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
            List<String> ks = new ArrayList<String>();
            List<byte[]> vs = new ArrayList<byte[]>();
            for (int i = 0; i < 40; i++) {
                String key = "/k/" + (1000 + 2 * i + round);
                ks.add(key);
                vs.add(StringUtil.toBytes("v" + key));
            }
            batch(dag, pd, ks, vs);
            
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
     * A segment leaf whose keys in a transaction come before and after the keys of a segment
     * tree below it (bergdb 026-25): the operations of /a and /c end in the space root, a
     * segment leaf, and /bbbbbbbX's second segment in the tree below its entry, so in key order
     * the leaf's operations are not consecutive. The writer's short way decided and appended
     * to the leaf once for each run of them, a node written twice in a transaction and, in
     * PubPromiseTester, a node of 31 klongs at node size 30. Every key node is written at
     * most once a transaction (one time klong of each time, and after it one key klong of a
     * compare value), and the values are right.
     */
    @Nano
    public static void testShortWayLeafAroundASegmentTree() {
        Dag dag = emptyDag(0);
        PutData pd = pd(dag);
        final long short0 = Dag.statShort;
        for (int t = 1; t <= 12; t++) {
            pd.tt = 10 * t;
            batchOf(dag, pd, "/a", "a" + t, "/bbbbbbbX", "b" + t, "/c", "c" + t);
            GetData gd = gd(dag);
            for (String k : new String[] {"/a", "/bbbbbbbX", "/c"}) {
                Assert.assertEquals(k.substring(1, 2) + t,
                        StringUtil.toString(dag.getOne(pd.tt, Keys.toSegments(k), gd)));
            }
            for (Node x : reachableAt(dag, pd.tt)) {
                if (!(x instanceof KeyNode)) continue;
                KeyNode k = (KeyNode) x;
                Assert.assertTrue("at most M klongs: " + k.size, k.size <= dag.getMaxNodeSize());
                // One time klong of a time, and after it one key klong of a compare value: a
                // node written twice in a transaction has two.
                Set<Long> times = new java.util.HashSet<Long>();
                Set<Long> cvs = new java.util.HashSet<Long>();
                for (int i = 0; i < k.size; i++) {
                    if (Klong.isTime(k.klongs[i])) {
                        Assert.assertTrue("one time klong of " + Klong.getTime(k.klongs[i]),
                                times.add(Klong.getTime(k.klongs[i])));
                        cvs.clear();
                    } else if (Klong.isKey(k.klongs[i])) {
                        Assert.assertTrue("one klong of a compare value at a time",
                                cvs.add(Klong.getCompareValue(k.klongs[i])));
                    }
                }
            }
        }
        Assert.assertTrue("the short way taken", Dag.statShort > short0);
    }
    
    /**
     * Both ways report and mark in emit's order (bergdb 028-25). At B = 8, 256 keys make
     * three inner levels in one segment tree. Both inner nodes below the space root are
     * clean before one overwrite that appends to its leaf and takes the short way.
     */
    @Nano
    public static void testShortWayMarksInEmitOrder() {
        List<String> keys = new ArrayList<String>();
        for (int i = 0; i < 256; i++) keys.add(String.format("%04d", i));
        MarkRun fast = new MarkRun(keys), plan = new MarkRun(keys);
        KeyNode node = fast.dag.getTopDs().findRoot(1, gd(fast.dag));
        int inner = 0;
        while (!node.isSegmentLeaf()) {
            Assert.assertTrue("inner node clean", !node.isDirty());
            inner++;
            node.searchEq(1, 0, fast.pd.kwi);
            node = (KeyNode) node.getPointerNode(fast.pd.kwi.pointerIndex);
        }
        Assert.assertEquals("three inner levels", 3, inner);
        compareShortMarks(fast, plan, "0000", "new");
        // Siblings and shared ancestors: the parent follows every changed child.
        compareShortMarks(new MarkRun(keys), new MarkRun(keys),
                "0000", "a", "0040", "b", "0255", "c");
        // Later-segment trees precede the entire first tree, including a changed leaf.
        List<String> segmented = java.util.Arrays.asList(
                "/a", "/bbbbbbbX", "/dddddddX", "/dddddddYYYYYYYZ");
        compareShortMarks(new MarkRun(segmented), new MarkRun(segmented),
                "/a", "a", "/bbbbbbbX", "b", "/dddddddYYYYYYYZ", "d");
        // A missing delete reports nothing, even when another operation shares its path.
        compareShortMarks(new MarkRun(keys), new MarkRun(keys),
                "0000", "a", "0000x", null, "0255x", null);
    }

    private static void compareShortMarks(MarkRun fast, MarkRun plan, String... ops) {
        plan.pd.forcePePlan = true;
        long short0 = Dag.statShort;
        fast.pd.tt = plan.pd.tt = 2;
        batchOf(fast.dag, fast.pd, ops);
        Assert.assertEquals("short way taken", short0 + 1, Dag.statShort);
        batchOf(plan.dag, plan.pd, ops);
        Assert.assertEquals("plan forced", short0 + 1, Dag.statShort);
        Assert.assertEquals("listener reports in emit order", plan.reports, fast.reports);
        Assert.assertEquals("marks in emit order", plan.marks, fast.marks);
        Assert.assertEquals("got-dirty order", plan.dirty, fast.dirty);
    }

    /** Listener ids and marks as Db assigns them; every reachable node starts clean. */
    private static final class MarkRun {
        final Dag dag = Dag.createEmpty(0, 8, DUMMY_POINTER_FOLLOWER,
                Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        final PutData pd = pd(dag);
        final List<String> reports = new ArrayList<String>();
        final List<Long> marks = new ArrayList<Long>();
        final List<Long> dirty = new ArrayList<Long>();
        long nextId = 3;

        MarkRun(List<String> keys) {
            TopNode top = dag.getTopDs().findSuperRootAtTime(0, gd(dag));
            top.setId(1);
            top.getPointerNode(0).setId(2);
            pd.pointerListener = new Dag.PointerListener() {
                public void superRootAccessed(TopNode node) { mark(node); }
                public void pointerFollowed(Node from, int i, Node to, int type) {
                    if (to instanceof KeyNode || to instanceof TopNode) mark(to);
                }
            };
            pd.nodeChangeListener = new Dag.NodeChangeListener() {
                public void topNodeCreated(TopNode node) { node.setId(nextId++); mark(node); }
                public void keyNodeCreated(KeyNode node) { node.setId(nextId++); mark(node); }
                public void valueNodeCreated(ValueNode node, long[] key) { node.setId(nextId++); }
                public void keyNodeChanged(KeyNode node) { report("changed", node); }
                public void keyNodeOnPath(KeyNode node) { report("path", node); }
            };
            pd.tt = 1;
            List<byte[]> values = new ArrayList<byte[]>();
            for (String key : keys) values.add(StringUtil.toBytes("old"));
            batch(dag, pd, keys, values);
            for (Node node : reachableAt(dag, 1)) node.setDirty(false);
            reports.clear();
            marks.clear();
            dirty.clear();
        }

        void report(String kind, KeyNode node) {
            reports.add(kind + " " + node.getId());
            mark(node);
        }

        void mark(Node node) {
            if (!marks.contains(node.getId())) marks.add(node.getId());
            if (!node.isDirty()) {
                node.setDirty(true);
                dirty.add(node.getId());
            }
        }
    }

    /**
     * 8 is the smallest node size (Frans, 2026-11-20; bergdb 028-38): a Dag of 7 or less is
     * refused when it is made, by both constructors, with a message that names 8; 8 is taken.
     */
    @Nano
    public static void testNodeSizeBelow8Refused() {
        Assert.assertEquals(8, Dag.MIN_NODE_SIZE);
        Dag.createEmpty(0, 8, DUMMY_POINTER_FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        for (int b : new int[] {7, 6, 4, 1, 0, -1}) {
            try {
                Dag.createEmpty(0, b, DUMMY_POINTER_FOLLOWER,
                        Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
                throw new AssertionError("createEmpty took node size " + b);
            } catch (IllegalArgumentException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains(
                        "The node size " + b + " is below 8, the smallest"));
            }
            try {
                new Dag(null, b);
                throw new AssertionError("new Dag took node size " + b);
            } catch (IllegalArgumentException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("below 8"));
            }
        }
    }
    
    /**
     * 62 is the largest node size (bergdb 024-19, Q6): a Dag of 63 or more is refused when it
     * is made, by both constructors, with a message that names 62; 62 is taken.
     */
    @Nano
    public static void testNodeSizeAbove62Refused() {
        Assert.assertEquals(62, Dag.MAX_NODE_SIZE);
        Assert.assertEquals(Dag.MAX_NODE_SIZE, Klong.DELETE_BITS.length);
        Dag.createEmpty(0, 62, DUMMY_POINTER_FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        for (int b : new int[] {63, 64, 126}) {
            try {
                Dag.createEmpty(0, b, DUMMY_POINTER_FOLLOWER,
                        Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
                throw new AssertionError("createEmpty took node size " + b);
            } catch (IllegalArgumentException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains(
                        "The node size " + b + " is above 62, the largest"));
            }
            try {
                new Dag(null, b);
                throw new AssertionError("new Dag took node size " + b);
            } catch (IllegalArgumentException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("above 62"));
            }
        }
    }
    
    /**
     * Fault 12 (bergdb 023-08, review C; the check of it, sections 3 and 4, ShadowProbe mode
     * 2): one transaction puts z keys after a history of b keys in one segment tree, and
     * deletes every b key. Until record format 8 the Dag got them in that order, out of key
     * order, as a Core KeyTransformation could give them before Db sorted the transformed
     * keys (023-08, section 7): the segment root that the transaction made was split in place
     * under a new root, and the deletes emptied it and took it back, and no klong of a node
     * reachable at any time could name a node taken back (failed without the in-place repoint
     * of the old writer's spaceSplitInPlace). Since format 8 the Dag gets them as one batch in
     * key order (bergdb 026-25) and takes nothing back: every key node that the transaction
     * makes is reachable at its time, and the gets are right.
     */
    @Nano
    public static void testNoKlongNamesATakenBackNode() {
        Random r = new Random(1);
        for (int iter = 0; iter < 40; iter++) {
            final int b = 8 + r.nextInt(5);     // 4 to 8 until 2026-11-20 (bergdb 028-38)
            Dag dag = Dag.createEmpty(0, b, DUMMY_POINTER_FOLLOWER,
                    Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
            PutData pd = pd(dag);
            final Set<Node> made = identitySet();
            pd.nodeChangeListener = new Dag.NodeChangeListener() {
                public void topNodeCreated(TopNode node) {}
                public void keyNodeCreated(KeyNode node) { made.add(node); }
                public void valueNodeCreated(ValueNode node, long[] key) {}
                public void keyNodeChanged(KeyNode node) {}
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
            made.clear();
            putAll(dag, pd, t, keys, deletes);
            
            String at = "iter " + iter + ", b " + b + ", nb " + nb + ", hist " + hist + ", nz "
                    + nz + ": ";
            Set<Node> now = reachableAt(dag, t);
            for (Node x : made) {
                Assert.assertTrue(at + "a key node made and not reachable", now.contains(x));
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
     * every key is gone; at the times before, the keys put then are there. Node sizes 8 and
     * 14 (4 and 8 until 2026-11-20, bergdb 028-38), keys of one segment and of two.
     */
    @Nano
    public static void testDeleteEveryKeyAfterTheRootSplit() {
        final long collapses0 = Dag.statCollapses + Dag.statDropped;
        for (int b : new int[] {8, 14}) {
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
        // Since record format 8 an emptied inner space root is dropped for an empty segment
        // leaf (PeWriter.settleRoot; bergdb 026-25).
        Assert.assertTrue("root collapses", Dag.statCollapses + Dag.statDropped > collapses0);
    }
    
    /**
     * Dag.dirtyNodeBound for transactions with deletes (bergdb 023-07, section 5.4, K4;
     * 023-08, reviews B and C, 2.5, and C, 5.3, item 4) against the key nodes that the
     * transaction makes dirty: those the writer follows, makes or changes, less those it
     * replaces, unlinks or takes back (review C's BoundProbe2). At node sizes 8, 14 and 30:
     * (1) random histories, thinned out to leave chains of single children, and a transaction
     * of deletes and some puts; (3) transactions of 1,000 deletes, and one of 100,000 at node
     * size 30. Since the merges at the delete (bergdb 024-21) every key node but a root holds
     * at least m >= 2 live klongs at node sizes 8 and more, so no chain of single children
     * forms there. (2), a chain that root collapse takes in one delete, several levels, each
     * a klong in the segment leaf above, ran at node size 6, which had no merges, until
     * 2026-11-20, when node sizes below 8 became refused (bergdb 028-38); (1) and (3) at 6
     * too.
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
            
            BoundCase c;
            List<String> all = new ArrayList<String>();
            
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
    
    /**
     * Dag.dirtyNodeBound for the writer PE (bergdb 028-21), against the key nodes that a
     * transaction makes dirty, at node sizes 8, 14, 30 and 62: (1) a new segment tree of 1 to
     * 2 B + 2 keys, which PE cuts into parts from h + 1 keys (until 028-21 counted as the old
     * writer's one node to B - 3 keys: 18 keys at node size 30 made three nodes, counted as
     * one); (2) a parent whose children are each cut into three parts, one more than their
     * overflows and one, at node size 30: the root, 21 klongs and 18 live, gets three klongs
     * a child where the count gave two, and is cut (until 028-21, 12 key nodes and a bound
     * of 10); (2b) a segment tree's root cut into three parts, and a new root above them
     * (until 028-21, 5 key nodes and a bound of 4); (3) random histories and a transaction of runs of puts, new keys and deletes;
     * (4) deletes of most keys under several inner nodes of trees thinned towards m, so that
     * joins happen on several levels, one level down too: at each node size and each case at
     * least ten joins, and a join of inner nodes at height two or more (Dag.statJoinsByHeight),
     * which the proof's Contract.PE.NoHigherJoins leaves out (bergdb 028-46).
     */
    @Nano
    public static void testDirtyNodeBoundOfPe() {
        // (1) New segment trees.
        for (int b : new int[] {8, 14, 30, 62}) {
            for (int n = 1; n <= 2 * b + 2; n++) {
                BoundCase c = new BoundCase(b);
                List<String> ks = new ArrayList<String>();
                for (int i = 0; i < 5; i++) ks.add(String.format("/p%05d/x00000", 2 * i));
                c.run(ks, null, false);
                ks.clear();
                for (int i = 0; i < n; i++) ks.add(String.format("/p00005/x%05d", i));
                c.run(ks, null, true);
            }
        }
        
        // (2) A root of 17 leaves of 15 keys; leaf 0 cut in two (the root: 21 klongs, 18 live,
        // one dead), and four new keys in three leaves (21 klongs, 19 live); then 12 new keys
        // in each of the three, 31 entries, three parts each.
        BoundCase c = new BoundCase(30);
        List<String> ks = new ArrayList<String>();
        for (int i = 0; i < 255; i++) ks.add(String.format("k%05d", i * 100));
        c.run(ks, null, false);
        ks.clear();
        for (int j = 1; j <= 14; j++) ks.add(String.format("k%05d", j));
        for (int l : new int[] {5, 6, 7}) for (int j = 1; j <= 4; j++) ks.add(String.format("k%05d", l * 1500 + j));
        c.run(ks, null, false);
        KeyNode root = c.dag.getTopDs().findRoot(c.t - 1, gd(c.dag));
        Assert.assertEquals("the root's klongs", 21, root.size);
        ks.clear();
        for (int l : new int[] {5, 6, 7}) for (int j = 10; j < 22; j++) ks.add(String.format("k%05d", l * 1500 + j));
        long cuts0 = Dag.statCuts;
        c.run(ks, null, true);
        Assert.assertEquals("three leaves and the root cut", 4, Dag.statCuts - cuts0);
        
        // (2b) A segment tree's root, a leaf of 21 klongs (19 live), gets 12 new keys: three
        // parts and a new root above them, which the segment leaf above names (until 028-21,
        // five key nodes and a bound of 4: the new root was not counted).
        c = new BoundCase(30);
        ks.clear();
        for (int i = 0; i < 15; i++) ks.add(String.format("/p00001x%04d", i * 100));
        ks.add("/p00000x0000");
        ks.add("/p00002x0000");
        c.run(ks, null, false);
        ks.clear();
        for (int j = 1; j <= 4; j++) ks.add(String.format("/p00001x%04d", j));
        c.run(ks, null, false);
        ks.clear();
        for (int j = 10; j < 22; j++) ks.add(String.format("/p00001x%04d", j));
        long newRoots0 = Dag.statNewRoots;
        c.run(ks, null, true);
        Assert.assertEquals("a new root of the segment tree", 1, Dag.statNewRoots - newRoots0);
        
        // (3) Random histories, then runs of puts, new keys and deletes.
        Random r = new Random(28021);
        for (int b : new int[] {8, 14, 30, 62}) {
            for (int iter = 0; iter < 12; iter++) {
                c = new BoundCase(b);
                int nk = 20 + r.nextInt(b * b * 2);
                boolean two = r.nextBoolean();
                Set<Integer> live = new java.util.TreeSet<Integer>();
                for (int h = 1 + r.nextInt(6); h > 0; h--) {
                    List<String> ps = new ArrayList<String>(), ds = new ArrayList<String>();
                    int dens = 1 + r.nextInt(6);
                    for (int i = 0; i < nk; i++) {
                        if (r.nextInt(dens) != 0) continue;
                        if (live.contains(i) && r.nextInt(4) == 0) { ds.add(peKey(two, i)); live.remove(i); }
                        else { ps.add(peKey(two, i)); live.add(i); }
                    }
                    c.run(ps, ds, false);
                }
                List<String> ps = new ArrayList<String>(), ds = new ArrayList<String>();
                for (int cl = 1 + r.nextInt(5); cl > 0; cl--) {
                    int lo = r.nextInt(nk), len = 1 + r.nextInt(3 * b), step = 1 + r.nextInt(3);
                    boolean del = r.nextInt(3) == 0;
                    for (int i = lo; i < Math.min(nk, lo + len); i += step) {
                        if (!del) ps.add(peKey(two, i));
                        else if (live.contains(i)) ds.add(peKey(two, i));
                    }
                }
                int at = r.nextInt(nk);
                for (int i = r.nextInt(4 * b); i > 0; i--) ps.add(peKey(two, at) + "n" + i);
                ps.removeAll(ds);
                c.run(ps, ds, true);
            }
        }
        
        // (4) Deletes of most keys under several inner nodes, the joins counted by the
        // children's height (bergdb 028-46): each case at least ten joins, and one of inner
        // nodes at height two or more (above Contract.PE.NoHigherJoins). At 8 and 14, 6 B^2
        // keys thinned to every third key. At 30 and 62, cap^2 * 2 (m + 2) keys (cap = B / 2):
        // the 2 (m + 2) inner nodes at height one, more than h, are cut into two nodes at height
        // two of m + 2 children each, under a root at height three; every third key deleted,
        // the leaves keep about B / 3 >= m keys, so the thinning joins nothing. Until 028-46
        // 30 too had 6 B^2 keys thinned to every third key: its thinning made 257 joins, and
        // the checked deletes joined at heights 0 and 1 only, as did 62's in a trial.
        for (int b : new int[] {8, 14, 30, 62}) {
            final boolean small = b < 30;
            final int cap = Dag.cutSize(b);
            final int nk = small ? 6 * b * b : cap * cap * 2 * (Dag.minFill(b) + 2);
            for (int keep : new int[] {2, 3, b}) {
                c = new BoundCase(b);
                List<String> all = new ArrayList<String>(), left = new ArrayList<String>();
                for (int i = 0; i < nk; i++) all.add(String.format("k%06d", i));
                c.run(all, null, false);
                List<String> ds = new ArrayList<String>();
                for (int i = 0; i < nk; i++) {
                    if (small ? i % 3 != 0 : i % 3 == 2) ds.add(all.get(i));
                    else left.add(all.get(i));
                }
                c.run(new ArrayList<String>(), ds, false);
                ds.clear();
                for (int i = left.size() / 4; i < 3 * left.size() / 4; i++) {
                    if (i % keep != 0) ds.add(left.get(i));
                }
                long joins0 = Dag.statJoins;
                long[] byHeight0 = Dag.statJoinsByHeight.clone();
                c.run(new ArrayList<String>(), ds, true);
                String at = "b " + b + ", keep " + keep;
                Assert.assertTrue(at + ": joins", Dag.statJoins - joins0 >= 10);
                long high = 0;
                for (int ht = 2; ht < byHeight0.length; ht++) high += Dag.statJoinsByHeight[ht] - byHeight0[ht];
                Assert.assertTrue(at + ": a join at height two or more", high >= 1);
            }
        }
    }
    
    private static String peKey(boolean two, int i) {
        return two ? String.format("/p%05d/x%05d", i / 10, i % 10) : String.format("k%05d", i);
    }
    
    /**
     * Dag.dirtyNodeBound sums the klongs that root collapse gives a segment leaf over the
     * trees below it (bergdb 023-11, review B, B1, its SiblingCollapseProbe): the space root,
     * a segment leaf, names two trees at node size 8, each a root of two leaves (five keys,
     * cut by PE into parts of three and two); a transaction deletes the first and the last
     * key of each, so a leaf of each tree is joined with its sibling and each root collapses:
     * a klong in the space root for each. The count gives the space root at least the
     * collapses and two klongs a delete. The bound also covers the dirty key nodes. Until
     * 2026-11-20 two trees of 1,024 keys at node size 6, which had no merges, thinned to
     * chains of single children that root collapse lowered eight levels each (16 klongs;
     * before the fix of B1 the count took the most of one tree, 2 x 2 + 8 = 12); node sizes
     * below 8 are refused since (bergdb 028-38), and from 8 every key node but a root holds
     * at least m >= 2 live klongs, so no such chain forms.
     */
    @Nano
    public static void testDirtyNodeBoundSumsCollapsesOverTrees() {
        BoundCase c = new BoundCase(8);
        List<String> all = new ArrayList<String>(), dels = new ArrayList<String>();
        for (int m = 0; m < 2; m++) {
            for (int i = 0; i < 5; i++) {
                String k = "/pref0" + m + "/k" + String.format("%04d", i);
                all.add(k);
                if (i == 0 || i == 4) dels.add(k);
            }
        }
        c.run(all, null, false);
        KeyNode leaf = c.dag.getTopDs().findRoot(c.t - 1, gd(c.dag));
        Assert.assertTrue("the space root is a segment leaf", leaf.isSegmentLeaf());
        long[][] keys = new long[dels.size()][];
        boolean[] deletes = new boolean[dels.size()];
        for (int i = 0; i < keys.length; i++) {
            keys[i] = Keys.toSegments(dels.get(i));
            deletes[i] = true;
        }
        java.util.Map<KeyNode, Long> klongs = new IdentityHashMap<KeyNode, Long>();
        c.dag.dirtyNodeBound(c.t - 1, keys, deletes, gd(c.dag), klongs);
        long collapses0 = Dag.statCollapses;
        c.run(new ArrayList<String>(), dels, true);
        long collapses = Dag.statCollapses - collapses0;
        Assert.assertTrue("collapses, one in each tree: " + collapses, collapses >= 2);
        Assert.assertTrue("klongs counted for the space root: " + klongs.get(leaf),
                klongs.get(leaf) >= collapses + 2 * dels.size());
    }
    
    /**
     * The count of 024-17 (sections 5.2 and 5.2a) against Dag.dirtyNodeBound on the worst path
     * (bergdb 028-72, ActionRoomProbe): c (H + 2) S + 14 n nodes for n operations of S
     * segments, c = 14, 10, 8 and 8 nodes a level at node sizes 8, 14, 30 and 62, with H, the
     * most levels of a segment tree less one, at 61, 38, 22 and 16 (024-17, 5.2: a stream of
     * under 2^60 klongs, m = 2, 3, 7 and 16). The worst tree for the count: every segment tree
     * on the keys' paths H + 1 key nodes high, every node of the paths full (B klongs, no
     * room), the paths apart as far as full nodes allow (at most B - 1 children a node); it
     * is made of key nodes directly, in memory, the other klongs of a node KEY klongs that
     * point nowhere and that no search of the walk picks. Deletes, puts and value
     * transformations (a put and a delete of one key) of keys of 1 to 147 segments (6 to
     * 1,022 bytes; 147 is the cap on BergDB's own long keys, 031-06, O1). The count with q
     * is what 024-17 and 031-06 state for a transaction within L1 to L5, and its 7/8 at the
     * release's limits (031-06, section 9): a change that raises Java's count above it fails
     * here, as 028-21's new roots above a cut segment root raised it at node size 14 above 9
     * a level (9.12 on this path). The second check, that the long key's count is above
     * c - 1 a level, keeps the tree the worst one: if a change lowers the count below it, the
     * documents' c can be lowered too.
     */
    @Nano
    public static void testDirtyNodeBoundOfTheWorstPath() {
        final int[][] sizes = {{8, 61, 14}, {14, 38, 10}, {30, 22, 8}, {62, 16, 8}};
        final Random r = new Random(28072);
        for (int[] bhc : sizes) {
            final int b = bhc[0], h = bhc[1], c = bhc[2];
            for (int bytes : new int[] {6, 7, 105, 1022}) {
                final long[][] k = {worstKey(r, bytes)};
                final long n = worstPathCheck(b, h, c, "one delete of " + bytes + " B", k,
                        new boolean[] {true}, 1);
                if (bytes == 1022) {
                    final long below = (c - 1L) * (h + 2) * k[0].length;
                    Assert.assertTrue("B=" + b + ": " + n + " nodes for a delete of "
                            + k[0].length + " segments, not above " + (c - 1) + " a level ("
                            + below + "): the path is not the worst, or the count fell",
                            n > below);
                }
            }
            long[][] k = {worstKey(r, 105)};
            worstPathCheck(b, h, c, "one put of 105 B", k, new boolean[] {false}, 1);
            worstPathCheck(b, h, c, "one value transformation of 105 B",
                    new long[][] {k[0], k[0]}, new boolean[] {false, true}, 1);
            k = new long[8][];
            for (int i = 0; i < k.length; i++) {
                k[i] = worstKey(r, i < 4 ? 119 : 112);
            }
            final boolean[] dels = new boolean[k.length], puts = new boolean[k.length];
            java.util.Arrays.fill(dels, true);
            worstPathCheck(b, h, c, "8 deletes of 119 and 112 B", k, dels, 8);
            worstPathCheck(b, h, c, "8 puts of 119 and 112 B", k, puts, 8);
            final long[][] k2 = new long[2 * k.length][];
            final boolean[] d2 = new boolean[k2.length];
            for (int i = 0; i < k.length; i++) {
                k2[2 * i] = k[i];
                k2[2 * i + 1] = k[i];
                d2[2 * i + 1] = true;
            }
            worstPathCheck(b, h, c, "8 value transformations of 119 and 112 B", k2, d2, 8);
        }
    }

    /** A key of 'bytes' printable bytes at random, as segments. */
    private static long[] worstKey(Random r, int bytes) {
        final byte[] k = new byte[bytes];
        for (int i = 0; i < bytes; i++) {
            k[i] = (byte) (0x21 + r.nextInt(0x5e));
        }
        return Keys.toSegments(k);
    }

    /**
     * Java's count of the operations (keys[i], deletes[i]), 'ops' of them (a value
     * transformation is two entries and one operation), on the worst tree of their keys
     * (testDirtyNodeBoundOfTheWorstPath), checked against c (H + 2) S + 14 n.
     */
    private static long worstPathCheck(int b, int h, int c, String what, long[][] keys,
            boolean[] deletes, int ops) {
        final List<long[]> distinct = new ArrayList<long[]>();
        final Set<String> seen = new java.util.HashSet<String>();
        long s = 0;
        for (long[] k : keys) {
            if (seen.add(java.util.Arrays.toString(k))) {
                distinct.add(k);
                s += k.length;
            }
        }
        final KeyNode root = worstTrie(distinct, 0, h + 1, b);
        final Dag dag = new Dag(new TopNode(0, root, Spos.NULL, 0, Spos.NULL), b);
        final long n = dag.dirtyNodeBound(1, keys, deletes, gd(dag));
        final long bound = c * (h + 2L) * s + 14L * ops;
        Assert.assertTrue("B=" + b + " H=" + h + ", " + what + " (S=" + s + "): Java's count "
                + n + " is above " + c + " (H + 2) S + 14 n = " + bound, n <= bound);
        return n;
    }

    /** The worst tree of segment 'seg' for keys that share their first seg segments. */
    private static KeyNode worstTrie(List<long[]> keys, int seg, int levels, int b) {
        final TreeMap<Long, List<long[]>> by = new TreeMap<Long, List<long[]>>();
        for (long[] k : keys) {
            List<long[]> l = by.get(k[seg]);
            if (l == null) {
                l = new ArrayList<long[]>();
                by.put(k[seg], l);
            }
            l.add(k);
        }
        final long[] vals = new long[by.size()];
        final Node[] targets = new Node[by.size()];
        int i = 0;
        for (Map.Entry<Long, List<long[]>> e : by.entrySet()) {
            vals[i] = e.getKey();
            final List<long[]> sub = new ArrayList<long[]>();
            for (long[] k : e.getValue()) {
                if (k.length > seg + 1) {
                    sub.add(k);
                }
            }
            Assert.assertTrue("a key ends where another goes on",
                    sub.isEmpty() || sub.size() == e.getValue().size());
            targets[i] = sub.isEmpty() ? null : worstTrie(sub, seg + 1, levels, b);
            i++;
        }
        return worstTree(vals, targets, 0, vals.length, levels, b);
    }

    /**
     * A segment tree of 'levels' levels of full key nodes for the sorted values vals[from,
     * to), each pointing to targets[i] (the next segment's tree, or nothing where a key ends):
     * an inner node a KEY klong for each of at most b - 1 groups, a leaf one for each value,
     * each node filled to b klongs with KEY klongs above its values.
     */
    private static KeyNode worstTree(long[] vals, Node[] targets, int from, int to, int levels,
            int b) {
        final KeyNode node = new KeyNode(levels == 1);
        final int n = to - from;
        if (levels == 1) {
            Assert.assertTrue(n + " values in one leaf", n <= b - 1);
            for (int i = from; i < to; i++) {
                node.addKlong(0, Klong.compareValueToKeyKlong(vals[i]), targets[i], Spos.NULL);
            }
        } else {
            final int g = Math.min(n, b - 1);
            for (int j = 0; j < g; j++) {
                final int lo = from + (int) ((long) n * j / g);
                final int hi = from + (int) ((long) n * (j + 1) / g);
                node.addKlong(0, Klong.compareValueToKeyKlong(vals[lo]),
                        worstTree(vals, targets, lo, hi, levels - 1, b), Spos.NULL);
            }
        }
        long cv = vals[to - 1];
        while (node.size < b) {
            cv += 8;
            node.addKlong(0, Klong.compareValueToKeyKlong(cv), null, Spos.NULL);
        }
        return node;
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
                public void keyNodeOnPath(KeyNode node) { dirty.add(node); }
            };
        }
        
        /** One transaction: the puts, then the deletes; with 'check', against the bound. */
        void run(List<String> puts, List<String> dels, boolean check) {
            // The keys in key order, puts and deletes mixed, as Db applies a transaction, so
            // that a put can come after a merge into the node that took its range (bergdb
            // 024-21's review, R6); until then the puts first, then the deletes.
            final Set<String> delSet = new java.util.HashSet<String>();
            if (dels != null) delSet.addAll(dels);
            List<String> ks = new ArrayList<String>(puts);
            if (dels != null) ks.addAll(dels);
            Collections.sort(ks, new java.util.Comparator<String>() {
                public int compare(String x, String y) {
                    return Keys.compareArrays(Keys.toSegments(x), Keys.toSegments(y));
                }
            });
            long bound = -1;
            if (check) {
                long[][] keys = new long[ks.size()][];
                boolean[] deletes = new boolean[ks.size()];
                for (int i = 0; i < ks.size(); i++) {
                    keys[i] = Keys.toSegments(ks.get(i));
                    deletes[i] = delSet.contains(ks.get(i));
                }
                bound = dag.dirtyNodeBound(t - 1, keys, deletes, gd(dag));
            }
            dirty.clear();
            pd.tt = t;
            List<byte[]> vs = new ArrayList<byte[]>();
            for (int i = 0; i < ks.size(); i++) {
                vs.add(delSet.contains(ks.get(i)) ? null : StringUtil.toBytes("v" + t));
            }
            batch(dag, pd, ks, vs);
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
        List<byte[]> vs = new ArrayList<byte[]>();
        for (int i = 0; i < keys.size(); i++) {
            vs.add(deletes.get(i) ? null : StringUtil.toBytes("v" + tt + keys.get(i)));
        }
        batch(dag, pd, keys, vs);
    }
    
    /**
     * One transaction at pd.tt, as Db gives it to the Dag (since record format 8 as one batch,
     * Dag.putKvs; bergdb 026-25): the operations in key order, one a key, the last one of a
     * key; a null value a delete.
     */
    static void batch(Dag dag, PutData pd, List<String> keys, List<byte[]> values) {
        java.util.TreeMap<long[], byte[]> ops = new java.util.TreeMap<long[], byte[]>(
                new java.util.Comparator<long[]>() {
                    public int compare(long[] a, long[] b) { return Keys.compareArrays(a, b); }
                });
        for (int i = 0; i < keys.size(); i++) {
            ops.put(Keys.toSegments(keys.get(i)), values.get(i));
        }
        long[][] k = new long[ops.size()][];
        byte[][] v = new byte[ops.size()][];
        int i = 0;
        for (java.util.Map.Entry<long[], byte[]> e : ops.entrySet()) {
            k[i] = e.getKey();
            v[i++] = e.getValue();
        }
        dag.putKvs(k, v, pd);
        pd.clear();
    }
    
    /** batch() of string values. */
    static void batchOf(Dag dag, PutData pd, String... kvs) {
        List<String> keys = new ArrayList<String>();
        List<byte[]> values = new ArrayList<byte[]>();
        for (int i = 0; i < kvs.length; i += 2) {
            keys.add(kvs[i]);
            values.add(kvs[i + 1] == null ? null : StringUtil.toBytes(kvs[i + 1]));
        }
        batch(dag, pd, keys, values);
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
        
        batchOf(g, pd, "/-k1", "v1", "/-k2", "v2");
        
        g.printGraph(System.out);
    }
}
