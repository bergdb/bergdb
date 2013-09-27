package bergdb.coreds;

import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * Tests TopDB, TopNode.
 */
public class TopTester {
    private TopDs.DbForMe db;
    private KeyNode n1;
    private KeyNode n2;
    private KeyNode n3;
    private KeyNode n4;
    private TopDs ds1;
    private TopDs ds2;
    private TopDs ds3;
    private TopDs ds4;
    
    private void createTestData() {
        db = new TopDs.DbForMe() {
            public INode followPointer(INode predecessor, int index, /*INode node, long pos,*/ 
                    boolean cache, long accessTime, GetData gd) {
                return predecessor.getPointerNode(index);
            }

            public long getAccessData() {
                return 0;
            }
        };
        
        long firstTime = 5;
        n1 = new KeyNode();
        n1.setSpos(100);
        ds1 = TopDs.createFromFirstRoot(firstTime, n1, 0);
        
        n2 = new KeyNode();
        n2.setSpos(200);
        ds2 = TopDs.createFromFirstRoot(firstTime, n1, 0);
        ds2.newSuperRoot(10, n2, 0);
        
        n3 = new KeyNode();
        n3.setSpos(300);
        ds3 = TopDs.createFromFirstRoot(firstTime, n1, 0);
        ds3.newSuperRoot(10, n2, 0);
        ds3.newSuperRoot(20, n3, 0);
        
        n4 = new KeyNode(); 
        n4.setSpos(400);
        ds4 = TopDs.createFromFirstRoot(firstTime, n1, 0);
        ds4.newSuperRoot(10, n2, 0);
        ds4.newSuperRoot(20, n3, 0);
        ds4.newSuperRoot(30, n4, 0);
    }
    
    /**
     * Used internally for testing.
     */
    private static KeyNode findRoot(TopDs topDS, TopDs.DbForMe db, long time) {
        return topDS.findRoot(db, time, false, null, Spos.DEFAULT_ACCESS_DATA, new GetData());
    }
    
    @T
    public static void test1() {
        TopTester tt = new TopTester();
        tt.createTestData();
    }
    
    @T
    public static void testBeforeFirst() {
        // No space root node before first time.
        
        TopTester t = new TopTester();
        t.createTestData();
        
        //System.out.println("---- TopTester.testBeforeFirst ----");
        //t.printTestData();
        
        Assert.assertEquals(null, findRoot(t.ds1, t.db, 1));
        Assert.assertEquals(null, findRoot(t.ds2, t.db, 1));
        Assert.assertEquals(null, findRoot(t.ds3, t.db, 1));
    }
    
    @T
    public static void testFindFirstNode() {
        TopTester t = new TopTester();
        t.createTestData();
        KeyNode root;
        
        root = findRoot(t.ds1, t.db, 7);
        Assert.assertEquals(t.n1, root);
        
        root = findRoot(t.ds2, t.db, 7);
        Assert.assertEquals(t.n1, root);
        
        root = findRoot(t.ds3, t.db, 7);
        Assert.assertEquals(t.n1, root);
    }
    
    @T
    public static void testDS3() {
        //
        // ds3: 2-10-20 (n1, n2, n3).
        //
        TopTester t = new TopTester();
        t.createTestData();
        KeyNode p = null;
        
        //p = t.ds3.findRoot(t.db, 99, false, null, 0);
        p = findRoot(t.ds3, t.db, 99);
        Assert.assertTrue(p != null);
        Assert.assertEquals(t.n3, p);
        
        //p = t.ds3.findRoot(t.db, 10, false, null, 0);
        p = findRoot(t.ds3, t.db, 10);
        Assert.assertTrue(p != null);
        Assert.assertEquals(t.n2, p);
        
        //p = t.ds3.findRoot(t.db, 19, false, null, 0);
        p = findRoot(t.ds3, t.db, 19);
        Assert.assertTrue(p != null);
        Assert.assertEquals(t.n2, p);
        
        //p = t.ds3.findRoot(t.db, 20, false, null, 0);
        p = findRoot(t.ds3, t.db, 20);
        Assert.assertTrue(p != null);
        Assert.assertEquals(t.n3, p);
    }

    void printTestData() {
        System.out.println("-- TestTester test data --");
        System.out.println("ds1 = \n" + ds1.print(db));
        System.out.println("ds2 = \n" + ds2.print(db));
        System.out.println("ds3 = \n" + ds3.print(db));
        System.out.println("ds4 = \n" + ds4.print(db));
    }
    
    @T
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
        
        Assert.assertEquals(t.n4, findRoot(t.ds4, t.db, 99));
        Assert.assertEquals("t=10, n2", t.n2, findRoot(t.ds4, t.db, 10));
        Assert.assertEquals(t.n2, findRoot(t.ds4, t.db, 19));
        Assert.assertEquals(t.n3, findRoot(t.ds4, t.db, 29));
        Assert.assertEquals(t.n4, findRoot(t.ds4, t.db, 30));
    }
    
    @T
    public static void testTopNodeToLongs1() {
        TopTester t = new TopTester();
        t.createTestData();
        TopNode top1 = t.ds1.getSuperRoot();
        int size = top1.getByteSize();
        
        assert size % 8 == 0;
        long[] longs = new long[size / 8];
        
        top1.toLongs(longs, 0);
        byte[] bytes = new byte[longs.length * 8];
        for (int i = 0; i < longs.length; i++) {
            Bytes.longToBytesLE(longs[i], bytes, i * 8);
        }
        
        TopNode top2 = TopNode.fromBytes(bytes, 0, Spos.NULL);
        
        Assert.assertEquals(top1.topNodeId, top2.topNodeId);
        Assert.assertEquals(top1.rootTime, top2.rootTime);
    }
    
    @T
    public static void testTopNodeToLongs2() {
        TopTester t = new TopTester();
        t.createTestData();
        TopNode top1 = t.ds4.getSuperRoot();
        int size = top1.getByteSize();
        assert size % 8 == 0;
        byte[] bytes = new byte[size];
        long[] longs = new long[size / 8];
        top1.toLongs(longs, 0);
        for (int i = 0; i < longs.length; i++) {
            Bytes.longToBytesLE(longs[i], bytes, i * 8);
        }
        TopNode top2 = TopNode.fromBytes(bytes, 0, Spos.NULL);
        
        Assert.assertEquals(top1.topNodeId, top2.topNodeId);
        Assert.assertEquals(top1.rootTime, top2.rootTime);
    }
    
    public static void main(String[] args) { 
        testDS3();
    }
}
