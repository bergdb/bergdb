package bergdb.dag;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
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
    
    @SuppressWarnings("unchecked")
    private static void testPointerCreationListener(int n) {
        final HashMap<Node, Node> map1 = new HashMap<Node, Node>();
        final HashMap<Node, Node> map2 = new HashMap<Node, Node>();
        
        Dag.PointerCreatedListener listener = new Dag.PointerCreatedListener() {
            public void pointerCreated(Node from, int index, Node to) {
                map1.put(from, to);
            }
        };
        
        Dag dag = emptyDag(10, listener);
        PutData pd = pd(dag);
        pd.tt = 20;
        pd.pointerCreatedListener = listener;
        
        for (int i = 0; i < n; i++) {
            dag.putKv(Keys.toSegments("/prefix-" + i), StringUtil.toBytes("v" + i), pd);
            if (i % 10 == 9) {
                pd.tt += 10;
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
