package bergdb.coreds;

import java.util.ArrayList;

import bergdb.common.Util;
import bergdb.coreds.Graph.PutData;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

public class GraphTester {
    
    @T
    public static void test0() {
        Graph g = Graph.builder().createEmpty(0);
        GetData gd = new GetData();
        
        byte[] result = g.getOne(0, Keys.toSegments("/-k1"), gd);
        
        Assert.assertTrue(result == null);
    }
    
    @T
    public static void test1() {
        // With choices
        Graph g = Graph.builder().createEmpty(0);
        GetData gd = new GetData();
        final ArrayList<Integer> choices = new ArrayList<Integer>();
        
        gd.pointerListener = new Graph.PointerListener() {
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) {
                choices.add(pointerIndex);
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
        PutData pd = new PutData();
        pd.tt = 10;
        
        g.putKv(Keys.toSegments("/-key"), Util.toBytes("value"), pd);
        
        for (int i = 0; i < pd.keyAccessPath.getSize(); i++) {
            System.out.println("keyAccessPath: " + Klong.toString(pd.keyAccessPath.getKlong(i)) 
                    + "->" + pd.keyAccessPath.get(i));
        }
        
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
        PutData pd = new PutData();
        pd.tt = 10;
        
        g.putKv(Keys.toSegments("/longerKey1"), Util.toBytes("value"), pd);
        
        pd.keyAccessPath.clear();
        
        g.putKv(Keys.toSegments("/longerKey2"), Util.toBytes("value"), pd);
        for (int i = 0; i < pd.keyAccessPath.getSize(); i++) {
            System.out.println("keyAccessPath: " + Klong.toString(pd.keyAccessPath.getKlong(i)) 
                    + "->" + pd.keyAccessPath.get(i));
        }
        
        System.out.println("Graph:\n");
        g.printGraph(System.out);
        
        GetData gd = new GetData();
        byte[] value = g.getOne(20, Keys.toSegments("/longerKey1"), gd);
        
        Assert.assertTrue(value != null);
        Assert.assertEquals("value", Util.toString(value));
        
        value = g.getOne(9, Keys.toSegments("/longerKey"), gd);
        Assert.assertTrue(value == null);
    }
    
    public static void main(String[] args) {
        Graph g = Graph.builder().createEmpty(10);
        PutData pd = new PutData();
        pd.tt = 20;
        
        g.putKv(Keys.toSegments("/-k1"), Util.toBytes("v1"), pd);
        g.putKv(Keys.toSegments("/-k2"), Util.toBytes("v2"), pd);
        
        g.printGraph(System.out);
    }
}
