package bergdb.dag;

import bergdb.dag.Dag.CachePolicy;
import bergdb.dag.Dag.PointerListener;
import bergdb.dag.TopDs.DagForMe;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Tests TopDB, TopNode.
 */
public class TopTester {
    private KeyNode n1;
    private KeyNode n2;
    private KeyNode n3;
    private KeyNode n4;
    public TopDs ds1;
    private TopDs ds2;
    private TopDs ds3;
    public TopDs ds4;
    
    public void createTestData() {
        Dag.PointerCreatedListener N1 = Dag.DO_NOTHING_POINTER_CREATED_LISTENER;
        Dag.NodeChangeListener N2 = Dag.DO_NOTHING_NODE_CHANGE_LISTENER;
        
        long firstTime = 5;
        n1 = new KeyNode();
        n1.setSpos(100);
        ds1 = TopDs.createFromFirstRoot(firstTime, n1, 0, N1);
        
        n2 = new KeyNode();
        n2.setSpos(200);
        ds2 = TopDs.createFromFirstRoot(firstTime, n1, 0, N1);
        ds2.newSuperRoot(10, n2, 0, N1, N2);
        
        n3 = new KeyNode();
        n3.setSpos(300);
        ds3 = TopDs.createFromFirstRoot(firstTime, n1, 0, N1);
        ds3.newSuperRoot(10, n2, 0, N1, N2);
        ds3.newSuperRoot(20, n3, 0, N1, N2);
        
        n4 = new KeyNode(); 
        n4.setSpos(400);
        ds4 = TopDs.createFromFirstRoot(firstTime, n1, 0, N1);
        ds4.newSuperRoot(10, n2, 0, N1, N2);
        ds4.newSuperRoot(20, n3, 0, N1, N2);
        ds4.newSuperRoot(30, n4, 0, N1, N2);
    }
    
    /**
     * Called by tests.
     */
    private KeyNode findRoot(TopDs topDs, long time) {
        GetData gd = new GetData();
        
        gd.pointerListener = new Dag.PointerListener() {
            public void pointerFollowed(Node predecessor, int pointerIndex, Node result, int pointerType) {
            }

            public void superRootAccessed(TopNode superRoot) {}
        };
        
        gd.cachePolicy = new Dag.CachePolicy() {
            public boolean shouldCache(Node node) {
                return false;
            }
        };
        
        DagForMe g = new DagForMe() {
            public Node followPointer(Node predecessor, int pointerIndex, long accessData,
                    PointerListener walker, CachePolicy cachPolicy) {
                return predecessor.getPointerNode(pointerIndex);
            }
        };
        
        return topDs.findRoot(g, time, gd);
    }
    
    @Nano
    public static void test1() {
        TopTester tt = new TopTester();
        tt.createTestData();
    }
    
    @Nano
    public static void testBeforeFirst() {
        // No space root node before first time.
        
        TopTester t = new TopTester();
        t.createTestData();
        
        //System.out.println("---- TopTester.testBeforeFirst ----");
        //t.printTestData();
        
        Assert.assertEquals(null, t.findRoot(t.ds1, 1));
        Assert.assertEquals(null, t.findRoot(t.ds2, 1));
        Assert.assertEquals(null, t.findRoot(t.ds3, 1));
    }
    
    @Nano
    public static void testFindFirstNode() {
        TopTester t = new TopTester();
        t.createTestData();
        KeyNode root;
        
        root = t.findRoot(t.ds1, 7);
        Assert.assertEquals(t.n1, root);
        
        root = t.findRoot(t.ds2, 7);
        Assert.assertEquals(t.n1, root);
        
        root = t.findRoot(t.ds3, 7);
        Assert.assertEquals(t.n1, root);
    }
    
    @Nano
    public static void testDS3() {
        //
        // ds3: 2-10-20 (n1, n2, n3).
        //
        TopTester t = new TopTester();
        t.createTestData();
        KeyNode p = null;
        
        //p = t.ds3.findRoot(t.db, 99, false, null, 0);
        p = t.findRoot(t.ds3, 99);
        Assert.assertTrue(p != null);
        Assert.assertEquals(t.n3, p);
        
        //p = t.ds3.findRoot(t.db, 10, false, null, 0);
        p = t.findRoot(t.ds3, 10);
        Assert.assertTrue(p != null);
        Assert.assertEquals(t.n2, p);
        
        //p = t.ds3.findRoot(t.db, 19, false, null, 0);
        p = t.findRoot(t.ds3, 19);
        Assert.assertTrue(p != null);
        Assert.assertEquals(t.n2, p);
        
        //p = t.ds3.findRoot(t.db, 20, false, null, 0);
        p = t.findRoot(t.ds3, 20);
        Assert.assertTrue(p != null);
        Assert.assertEquals(t.n3, p);
    }
    
    @Nano
    public static void testDS4() {
        //
        // ds4: t  var id
        //      2  n1  0
        //     10  n2  1
        //     20  n3  2
        //     30  n4  3
        //height
        
        TopTester t = new TopTester();
        t.createTestData();
        
        //System.out.println("---- TopTester.testDS4 ----");
        //System.out.println("ds4 = \n" + t.ds4.print(t.db));
        
        Assert.assertEquals(t.n4, t.findRoot(t.ds4, 99));
        Assert.assertEquals("t=10, n2", t.n2, t.findRoot(t.ds4, 10));
        Assert.assertEquals(t.n2, t.findRoot(t.ds4, 19));
        Assert.assertEquals(t.n3, t.findRoot(t.ds4, 29));
        Assert.assertEquals(t.n4, t.findRoot(t.ds4, 30));
    }
    
    public static void main(String[] args) { 
        testDS3();
    }
}
