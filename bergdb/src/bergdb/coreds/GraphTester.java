package bergdb.coreds;

import java.util.ArrayList;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

public class GraphTester {
    
    @T
    public static void test0() {
        Graph g = Graph.builder().createEmpty(0);
        GetData gd = g.newGetData();
        
        byte[] result = g.getOne(0, Keys.toSegments("/-k1"), gd);
        
        Assert.assertTrue(result == null);
    }
    
    @T
    public static void test1() {
        // With choices
        Graph g = Graph.builder().createEmpty(0);
        GetData gd = g.newGetData();
        final ArrayList<Integer> choices = new ArrayList<Integer>();
        
        gd.pointerListener = new Graph.PointerListener() {
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) {
                choices.add(pointerIndex);
            }

            public void superRootAccessed(TopNode superRoot) {
            }
        };
        
        byte[] result = g.getOne(0, Keys.toSegments("/-k1"), gd);
        
        Assert.assertTrue(result == null);
        Assert.assertEquals(1, choices.size());
        Assert.assertEquals(0, choices.get(0).intValue());
    }
    
    @T
    public static void testPut0() {
        Graph g = Graph.builder().createEmpty(0);
        PutData pd = g.newPutData();
        pd.tt = 10;
        
        g.putKv(Keys.toSegments("/-key"), Util.toBytes("value"), pd);
        
        //for (int i = 0; i < pd.keyAccessPath.getSize(); i++) {
        //    System.out.println("keyAccessPath: " + Klong.toString(pd.keyAccessPath.getKlong(i)) 
        //            + "->" + pd.keyAccessPath.get(i));
        //}
        
        GetData gd = new GetData();
        byte[] value = g.getOne(20, Keys.toSegments("/-key"), gd);
        
        Assert.assertTrue(value != null);
        Assert.assertEquals("value", Util.toString(value));
        
        value = g.getOne(9, Keys.toSegments("/-key"), gd);
        Assert.assertTrue(value == null);
    }
    
    @T
    public static void testPut1() {
        Graph g = Graph.builder().createEmpty(0);
        PutData pd = g.newPutData();
        pd.tt = 10;
        
        g.putKv(Keys.toSegments("/longerKey1"), Util.toBytes("value"), pd);
        
        pd.keyAccessPath.clear();
        
        g.putKv(Keys.toSegments("/longerKey2"), Util.toBytes("value"), pd);
        //for (int i = 0; i < pd.keyAccessPath.getSize(); i++) {
        //    System.out.println("keyAccessPath: " + Klong.toString(pd.keyAccessPath.getKlong(i)) 
        //            + "->" + pd.keyAccessPath.get(i));
        //}
        //
        //System.out.println("Graph:\n");
        //g.printGraph(System.out);
        
        GetData gd = new GetData();
        byte[] value = g.getOne(20, Keys.toSegments("/longerKey1"), gd);
        
        Assert.assertTrue(value != null);
        Assert.assertEquals("value", Util.toString(value));
        
        value = g.getOne(9, Keys.toSegments("/longerKey"), gd);
        Assert.assertTrue(value == null);
    }
    
    @T
    public static void testSplit0() {
        // Splits space root node. New super root node (top node) needed.
        
        String[] kvs = new String[] {
                "/k1", "v1", "/k2", "v2", "/k3", "v3", "/k4", "v4", "/k0", "v0"
        };
        
        Graph g = Graph.builder().maxNodeSize6().createEmpty(0);
        PutData pd = g.newPutData();
        pd.tt = 10;
        
        for (int i = 0; i < kvs.length; i += 2) {
            g.putKv(Keys.toSegments(kvs[i]), Util.toBytes(kvs[i + 1]), pd);
            pd.clearFast();
        }
        pd.clear();
        
        Assert.assertEquals(1, pd.splitCount);
        GetData gd = new GetData();
        for (int i = 0; i < kvs.length; i += 2) {
            byte[] value = g.getOne(10, Keys.toSegments(kvs[i]), gd);
            Assert.assertEquals(kvs[i + 1], Util.toString(value));
        }
        
        for (int i = 0; i < kvs.length; i += 2) {
            byte[] value = g.getOne(9, Keys.toSegments(kvs[i]), gd);
            Assert.assertEquals(null, value);
        }
    }
    
    @T
    public static void testSplit2() {
        // Time split with an ordinary KeyNode as parent.

        Graph g = Graph.builder().maxNodeSize6().createEmpty(0);
        PutData pd = g.newPutData();
        
        for (int i = 0; i < 4; i++) {
            String keyString = "account-id-" + i;
            pd.tt = 1 + i;
            g.putKv(Keys.toSegments(keyString), Util.toBytes("v" + i), pd);
            pd.clearFast();
        }
        
        Assert.assertEquals(1, pd.splitCount);
        pd.clear();
        
        //System.out.println("---- Graph.testSplit2 ----");
        //System.out.println("graph:");
        //g.printGraph(System.out);
        
        byte[] value;
        GetData gd = new GetData();
        
        for (int i = 0; i < 4; i++) {
            String keyString = "account-id-" + i;
            value = g.getOne(100, Keys.toSegments(keyString), gd);
            Assert.assertArrayEquals("i=" + i, Util.toBytes("v" + i), value);
        }
    }
    
    @T
    public static void testVisit0() {
        Graph g = Graph.builder().createEmpty(10);
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
    
    @T
    public static void testVisit1() {
        Graph g = Graph.builder().createEmpty(10);
        PutData pd = g.newPutData();
        pd.tt = 20;
        
        for (int i = 0; i < 4; i++) {
            g.putKv(Keys.toSegments("/prefix-" + i), Util.toBytes("v" + i), pd);
        }
        
        StatsNodeVisitor v = new StatsNodeVisitor();
        g.visitMemoryNodes(v);
        
        Assert.assertEquals(1, v.topCount);
        Assert.assertEquals(2, v.keyCount);
        Assert.assertEquals(4, v.valueCount);
    }
    
    public static void main(String[] args) {
        Graph g = Graph.builder().createEmpty(10);
        PutData pd = g.newPutData();
        pd.tt = 20;
        
        g.putKv(Keys.toSegments("/-k1"), Util.toBytes("v1"), pd);
        g.putKv(Keys.toSegments("/-k2"), Util.toBytes("v2"), pd);
        
        g.printGraph(System.out);
    }
}
