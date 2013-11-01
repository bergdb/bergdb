package bergdb.dag;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;


/**
 * Tests for class KeyNode.
 */
public class KeyNodeTester {
    KeyNode[] t2Pointers;
    
    /**
     * Returns a test key node called T2.
     * 
     * <pre>
     * The T2 supernode graph looks like this:
     * 
     * a  dP gP k  m
     * pP       rP a  dP
     * aP       a  g
     *          mP eP
     *            
     * P = the previous character has a pointer.
     * These are the "keys" that have pointers:
     *   ap    - P0
     *   apa   - P1
     *   d     - P2
     *   g     - P3
     *   kr    - P4
     *   kram  - P5
     *   mage  - P6
     *   md    - P7
     *   
     * </pre>
     */
    public KeyNode createT2() {
        t2Pointers = new KeyNode[8];
        for (int i = 0; i < t2Pointers.length; i++) {
            t2Pointers[i] = new KeyNode();
        }
        
        KeyNode node = new KeyNode();
        String[] keys = new String[] {
                "ap", "apa", "d", "g", "kr", "kram", "mage", "md" };
        
        for (int i = 0; i < keys.length; i++) {
            long klongToAdd = Klong.create(Util.toBytes(keys[i]));
            node.addKlong(1, klongToAdd, t2Pointers[i], AccessData.DEFAULT_ACCESS_DATA);
        }
        
        return node;
    }
    
    @T
    public static void testSanity1() {
        KeyNodeTester t = new KeyNodeTester();
        t.createT2();
    }
    
    @T
    public static void testSanity2() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode t2 = t.createT2();
        long compareValue = createCompareValue(Util.toBytes("ap"));
        
        KlongWithPointer kwi = new KlongWithPointer();
        t2.searchEq(2000, compareValue, kwi);
        
        Assert.assertEquals(true, t2.getPointerNode(kwi.pointerIndex) != null);
        Assert.assertEquals(t.t2Pointers[0], t2.getPointerNode(kwi.pointerIndex));
    }
    
    private static long createCompareValue(byte[] bytes) {
        return Klong.createCompareValue(bytes, 0, bytes.length);
    }
    
    @T
    public static void testEq() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode t2 = t.createT2();
        KlongWithPointer kwi = new KlongWithPointer();
        
        t2.searchEq(2000, createCompareValue(Util.toBytes("ap")), kwi);
        Assert.assertEquals(t.t2Pointers[0], t2.getPointerNode(kwi.pointerIndex));
        
        t2.searchEq(2000, createCompareValue(Util.toBytes("apa")), kwi);
        Assert.assertEquals(true, t2.getPointerNode(kwi.pointerIndex) != null);
        Assert.assertEquals(t.t2Pointers[1], t2.getPointerNode(kwi.pointerIndex));
        
        t2.searchEq(2000, createCompareValue(Util.toBytes("g")), kwi);
        Assert.assertEquals(t.t2Pointers[3], t2.getPointerNode(kwi.pointerIndex));
        
        t2.searchEq(2000, createCompareValue(Util.toBytes("mage")), kwi);
        Assert.assertEquals(t.t2Pointers[6], t2.getPointerNode(kwi.pointerIndex));
        
        t2.searchEq(2000, createCompareValue(Util.toBytes("md")), kwi);
        Assert.assertEquals(t.t2Pointers[7], t2.getPointerNode(kwi.pointerIndex));
    }
    
    @T
    public static void testEqWithVersions() {
        KeyNodeTester t = new KeyNodeTester();
        KlongWithPointer kwi = new KlongWithPointer();
        
        KeyNode t2 = t.createT2();
        
        t2.addKlong(1020, Klong.create(Util.toBytes("a")), t.t2Pointers[7], AccessData.DEFAULT_ACCESS_DATA);
        
        long compareValue = createCompareValue(Util.toBytes("a"));
        t2.searchEq(2000, compareValue, kwi);
        Assert.assertEquals(t.t2Pointers[7], kwi.node);
        
        compareValue = createCompareValue(Util.toBytes("mage"));
        t2.searchEq(2000, compareValue, kwi);
        Assert.assertEquals(t.t2Pointers[6], kwi.node);
    }
    
    @T
    public static void testEqWithVersionsAndDelete() {
        KeyNodeTester t = new KeyNodeTester();
        KlongWithPointer kwi = new KlongWithPointer();
        KeyNode node = t.createT2();
        long klong = node.getDeleteBitmap(Klong.createCompareValue(Util.toBytes("apa")));
        node.addKlong(1020, klong, null, AccessData.DEFAULT_ACCESS_DATA);
        
        long compareValue = createCompareValue(Util.toBytes("apa"));
        node.searchEq(2000, compareValue, kwi);

        //System.out.println("---- NodeTester.testEQWithVersionsAndDelete ----");
        //System.out.println("node: " + node.print());
        //System.out.println("klong: " + Klong.toString(kwi.klong));
        
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("apa"));
        node.searchEq(1010, compareValue, kwi);
        Assert.assertEquals(t.t2Pointers[1], kwi.node);
        
        node.addKlong(1030, Klong.create(Util.toBytes("apa")), t.t2Pointers[5], AccessData.DEFAULT_ACCESS_DATA);
        
        compareValue = createCompareValue(Util.toBytes("apa"));
        node.searchEq(2000, compareValue, kwi);
        Assert.assertEquals(t.t2Pointers[5], kwi.node);
    }
    
    @T
    public static void testEqBeforeFirstVersion() {
        KeyNode n = new KeyNode();
        long klongToAdd = Klong.create(Util.toBytes("first"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        
        n.check();
        KlongWithPointer kwi = new KlongWithPointer();
        long compareValue = createCompareValue(Util.toBytes("first"));
        
        n.searchEq(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong != Klong.NULL);
        
        n.searchEq(5, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong == Klong.NULL);
    }
    
    @T
    public static void testLte1() {
        KeyNode n = new KeyNode();
        long klongToAdd = Klong.create(Util.toBytes("first"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        n.check();
        KlongWithPointer kwi = new KlongWithPointer();
        long compareValue = createCompareValue(Util.toBytes("first"));
        
        n.searchLte(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong != Klong.NULL);
        
        n.searchLte(5, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong == Klong.NULL);
        
        compareValue = createCompareValue(Util.toBytes("fir"));
        n.searchLte(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong == Klong.NULL);
        
        compareValue = createCompareValue(Util.toBytes("g"));
        n.searchLte(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong != Klong.NULL);
    }
    
    @T
    public static void testLte2() {
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.create(Util.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.create(Util.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(Util.toBytes("k20"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k21"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k19"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k09"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        // Tests at time = 15
        
        compareValue = createCompareValue(Util.toBytes("k99"));
        n.searchLte(15, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k10"));
        n.searchLte(15, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k09"));
        n.searchLte(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
    }
    
    @T
    public static void testLte3() {
        //
        // Tests KeyNode.searchLTE() with a delete.
        //
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.create(Util.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.create(Util.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = n.getDeleteBitmap(Klong.createCompareValue(Util.toBytes("k10")));
        n.addKlong(30, klongToAdd, null, AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(Util.toBytes("k20"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k21"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k19"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals("Got: " + Klong.toString(kwi.klong) + ", " + kwi.klongTime, Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k09"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
    }
    
    @T
    public static void testLt1() {
        KeyNode n = new KeyNode();
        long klongToAdd = Klong.create(Util.toBytes("first"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        n.check();
        KlongWithPointer kwi = new KlongWithPointer();
        long compareValue = createCompareValue(Util.toBytes("first"));
        
        n.searchLt(20, compareValue, kwi);
        Assert.assertTrue(kwi.klong == Klong.NULL);
        
        n.searchLt(5, compareValue, kwi);
        Assert.assertTrue(kwi.klong == Klong.NULL);
        
        compareValue = createCompareValue(Util.toBytes("fir"));
        n.searchLt(20, compareValue, kwi);
        Assert.assertTrue(kwi.klong == Klong.NULL);
        
        compareValue = createCompareValue(Util.toBytes("g"));
        n.searchLt(20, compareValue, kwi);
        Assert.assertTrue(kwi.klong != Klong.NULL);
    }
    
    @T
    public static void testLt2() {
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.create(Util.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.create(Util.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(Util.toBytes("k20"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k21"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k19"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k09"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        // Tests at time = 15
        
        compareValue = createCompareValue(Util.toBytes("k99"));
        n.searchLt(15, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k10"));
        n.searchLt(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k09"));
        n.searchLt(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
    }
    
    @T
    public static void testLt3() {
        //
        // Tests KeyNode.searchLt() with a delete.
        //
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.create(Util.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.create(Util.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = n.getDeleteBitmap(Klong.createCompareValue(Util.toBytes("k10")));
        n.addKlong(30, klongToAdd, null, AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(Util.toBytes("k20"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k21"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k19"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals("Got: " + Klong.toString(kwi.klong) + ", " + kwi.klongTime, 
                Klong.NULL, kwi.klong);
    }
    
    @T
    public static void testGt1() {
        KeyNode n = new KeyNode();
        long klongToAdd = Klong.create(Util.toBytes("key"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        n.check();
        KlongWithPointer kwi = new KlongWithPointer();

        long compareValue = createCompareValue(Util.toBytes("a"));
        n.searchGt(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong != Klong.NULL);
        
        n.searchGt(5, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong == Klong.NULL);
        
        compareValue = createCompareValue(Util.toBytes("key"));
        n.searchGt(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong == Klong.NULL);
    }
    
    @T
    public static void testGt2() {
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.create(Util.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.create(Util.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(Util.toBytes("k19"));
        n.searchGt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k10"));
        n.searchGt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k20"));
        n.searchGt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k00"));
        n.searchGt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
        
        // Tests at time = 15
        
        compareValue = createCompareValue(Util.toBytes("k15"));
        n.searchGt(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k10"));
        n.searchGt(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k09"));
        n.searchGt(15, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
    }
    
    
    @T
    public static void testGte() {
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.create(Util.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.create(Util.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(Util.toBytes("k19"));
        n.searchGte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k10"));
        n.searchGte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k20"));
        n.searchGte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k00"));
        n.searchGte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
        
        // Tests at time = 15
        
        compareValue = createCompareValue(Util.toBytes("k15"));
        n.searchGte(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k10"));
        n.searchGte(15, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(Util.toBytes("k09"));
        n.searchGte(15, compareValue, kwi);
        Assert.assertEquals(Klong.create(Util.toBytes("k10")), kwi.klong);
    }
    
    
    @T
    public static void testFirst1() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode t2 = t.createT2();
        KlongWithPointer kwi = new KlongWithPointer();
        
        t2.searchFirst(2000, kwi);
        Assert.assertEquals(false, kwi.klong == Klong.NULL);
        Assert.assertEquals(t.t2Pointers[0], kwi.node);
        Assert.assertEquals(Klong.create(Util.toBytes("ap")), kwi.klong);
    }
    
    @T
    public static void testCheckEmptyNode() {
        // The empty node is allowed, zero klongs.
        new KeyNode().check();
    }
    
    @T
    public static void testCheck1() {
        new KeyNodeTester().createT2().check();
    }
    
    @T
    public static void testCheck2() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode node = t.createT2();
        node.check();
        long klong = node.getDeleteBitmap(Klong.createCompareValue(Util.toBytes("apa")));
        node.addKlong(1020, klong, null, AccessData.DEFAULT_ACCESS_DATA);
        //node.addKlong(1020, Klong.createDelete(Util.toBytes("apa")), null, Spos.DEFAULT_ACCESS_DATA);
        node.check();        
        node.addKlong(1030, Klong.create(Util.toBytes("apa")), t.t2Pointers[5], AccessData.DEFAULT_ACCESS_DATA);
        node.check();
    }
    
    @T
    public static void testGetPointers() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode node = t.createT2();
        int pointerCount = node.getPointerCount();
        Pointer p = new Pointer();

        for (int j = 0; j < pointerCount; j++) {
            node.getPointer(j, p);
            if (p.isNull()) {
                continue;
            }
            Assert.assertEquals("j=" + j, t.t2Pointers[j - 1], p.node);
        }
    }
    
    @T
    public static void testLastVersion1() {
        KeyNode n = new KeyNode();
        
        n.addKlong(10, Klong.create(Util.toBytes("a")), new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.create(Util.toBytes("b")), new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.create(Util.toBytes("c")), new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        
        KeyNode last = n.lastVersion(100);
        NodeInfo info = new NodeInfo();
        last.getInfo(info);
        
        //System.out.println("---- NodeTester.testLastVersion1 ----");
        //System.out.println("n:\n" + n.print());
        //System.out.println("last:\n" + last.print());
        
        Assert.assertEquals(100, info.lastTime);
        Assert.assertEquals(4, info.klongCount);
        Assert.assertEquals(1, info.timeCount);
    }
    
    @T
    public static void testLastVersion3() {
        KeyNode n = new KeyNode();
        ValueNode value = new ValueNode(new byte[0]);
        
        n.addKlong(10, Klong.create(Util.toBytes("a")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.create(Util.toBytes("b")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(25, Klong.create(Util.toBytes("c")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, n.getDeleteBitmap(Klong.createCompareValue(Util.toBytes("b"))), null, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(40, n.getDeleteBitmap(Klong.createCompareValue(Util.toBytes("a"))), null, AccessData.DEFAULT_ACCESS_DATA);
        
        n.addKlong(50, Klong.create(Util.toBytes("b")), value, AccessData.DEFAULT_ACCESS_DATA);
        
        KeyNode last = n.lastVersion(100);
        NodeInfo info = new NodeInfo();
        last.getInfo(info);
        
        //System.out.println("---- NodeTester.testLastVersion3 ----");
        //System.out.println(n.print());
        //System.out.println(last.print());
        
        Assert.assertEquals(100, info.lastTime);
        Assert.assertEquals(3, info.klongCount);
        Assert.assertEquals(1, info.timeCount);
        Assert.assertEquals(Klong.createTime(100), last.klongs[0]);
        Assert.assertEquals(Klong.create(Util.toBytes("b")), last.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("c")), last.klongs[2]);
    }
    
    @T
    public static void testLastVersion4() {
        //
        // Tests adding a delete-all klong.
        //
        
        KeyNode n = new KeyNode();
        ValueNode value = new ValueNode(new byte[0]);
        n.addKlong(10, Klong.create(Util.toBytes("a")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(10, Klong.create(Util.toBytes("b")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.create(Util.toBytes("c")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, n.getDeleteBitmap(Klong.createCompareValue(Util.toBytes("b"))), null, 
                AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(40, Klong.create(Util.toBytes("d")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(50, Klong.DELETE_ALL_BITMAP, null, AccessData.DEFAULT_ACCESS_DATA);
        
        KeyNode last = n.lastVersion(100);
        
        //System.out.println("---- NodeTester.testLastVersion4 ----");
        //System.out.println("last:\n" + last.print());
        
        Assert.assertTrue(last.size <= 1);
    }
    
    @T
    public static void testFirstAndSecond2() {
        KeyNode n = new KeyNode();
        ValueNode v1 = new ValueNode(Util.toBytes("v1"));
        n.addKlong(10, Klong.create(Util.toBytes("10")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.create(Util.toBytes("20")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.create(Util.toBytes("30")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(40, Klong.create(Util.toBytes("40")), v1, AccessData.DEFAULT_ACCESS_DATA);
        
        KeyNode first = new KeyNode();
        KeyNode second = new KeyNode();
        KlongWithPointer[] insert = { new KlongWithPointer() };
        insert[0].klong = Klong.create(Util.toBytes("22"));
        insert[0].node = v1;
        
        n.firstAndSecond(100, n.lastVersion(100), insert, first, second);
        
        //System.out.println("---- NodeTester.testFirstAndSecond2 ----");
        //System.out.println(n.print());
        //System.out.println(first.print());
        //System.out.println(second.print());
        
        Assert.assertEquals(Klong.createTime(100), first.klongs[0]);
        Assert.assertEquals(Klong.create(Util.toBytes("10")), first.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("20")), first.klongs[2]);
        Assert.assertEquals(Klong.create(Util.toBytes("22")), first.klongs[3]);
        Assert.assertEquals(4, first.size);
        
        Assert.assertEquals(Klong.createTime(100), second.klongs[0]);        
        Assert.assertEquals(Klong.create(Util.toBytes("30")), second.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("40")), second.klongs[2]);
        Assert.assertEquals(3, second.size);
    }
    
    @T
    public static void testFirstAndSecond3() {
        KeyNode n = new KeyNode();
        ValueNode v1 = new ValueNode(Util.toBytes("v1"));
        n.addKlong(10, Klong.create(Util.toBytes("10")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.create(Util.toBytes("20")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.create(Util.toBytes("30")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(40, Klong.create(Util.toBytes("40")), v1, AccessData.DEFAULT_ACCESS_DATA);
        
        KeyNode first = new KeyNode();
        KeyNode second = new KeyNode();
        KlongWithPointer[] insert = { new KlongWithPointer(), new KlongWithPointer() };
        insert[1].klong = Klong.create(Util.toBytes("22"));
        insert[1].node = v1;
        insert[0].klong = Klong.create(Util.toBytes("01"));
        insert[0].node = v1;
        
        KeyNode last = n.lastVersion(100);
        n.firstAndSecond(100, last, insert, first, second);
        
        //System.out.println("---- NodeTester.testFirstAndSecond3 ----");
        //System.out.println(n.print());
        //System.out.println(first.print());
        //System.out.println(second.print());
        
        Assert.assertEquals(Klong.createTime(100), first.klongs[0]);
        Assert.assertEquals(Klong.create(Util.toBytes("10")), first.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("20")), first.klongs[2]);
        Assert.assertEquals(Klong.create(Util.toBytes("01")), first.klongs[3]);
        Assert.assertEquals(Klong.create(Util.toBytes("22")), first.klongs[4]);
        Assert.assertEquals(5, first.size);
        
        Assert.assertEquals(Klong.createTime(100), second.klongs[0]);
        Assert.assertEquals(Klong.create(Util.toBytes("30")), second.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("40")), second.klongs[2]);
        Assert.assertEquals(3, second.size);
    }
    
    @T
    public static void testFirstAndSecond4() {
        // Inserts many in the middle. Make sure thay all end up in first.
        //
        
        KeyNode n = new KeyNode();
        ValueNode v1 = new ValueNode(Util.toBytes("v1"));
        n.addKlong(10, Klong.create(Util.toBytes("10")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.create(Util.toBytes("30")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(40, Klong.create(Util.toBytes("40")), v1, AccessData.DEFAULT_ACCESS_DATA);
        
        KeyNode first = new KeyNode();
        KeyNode second = new KeyNode();
        KlongWithPointer[] insert = { new KlongWithPointer(), new KlongWithPointer(),
                new KlongWithPointer()};

        insert[0].klong = Klong.create(Util.toBytes("21"));
        insert[0].node = v1;
        insert[1].klong = Klong.create(Util.toBytes("22"));
        insert[1].node = v1;
        insert[2].klong = Klong.create(Util.toBytes("23"));
        insert[2].node = v1;
        
        KeyNode last = n.lastVersion(100);
        n.firstAndSecond(100, last, insert, first, second);
        
        //System.out.println("---- NodeTester.testFirstAndSecond4 ----");
        //System.out.println(n.print());
        //System.out.println(first.print());
        //System.out.println(second.print());
        
        Assert.assertEquals(5, first.size);
        Assert.assertEquals(Klong.createTime(100), first.klongs[0]);
        Assert.assertEquals(Klong.create(Util.toBytes("10")), first.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("21")), first.klongs[2]);
        Assert.assertEquals(Klong.create(Util.toBytes("22")), first.klongs[3]);
        Assert.assertEquals(Klong.create(Util.toBytes("23")), first.klongs[4]);
        
        Assert.assertEquals(Klong.createTime(100), second.klongs[0]);
        Assert.assertEquals(Klong.create(Util.toBytes("30")), second.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("40")), second.klongs[2]);
        Assert.assertEquals(3, second.size);
    }
    
    @T
    public static void testFirstAndSecond5() {
        // Insert in beginning
        
        KeyNode n = new KeyNode();
        ValueNode v1 = new ValueNode(Util.toBytes("v1"));
        n.addKlong(10, Klong.create(Util.toBytes("10")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(10, Klong.create(Util.toBytes("20")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.create(Util.toBytes("30")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(40, Klong.create(Util.toBytes("40")), v1, AccessData.DEFAULT_ACCESS_DATA);
        
        KeyNode first = new KeyNode();
        KeyNode second = new KeyNode();
        KlongWithPointer[] insert = { new KlongWithPointer(), new KlongWithPointer() };

        insert[0].klong = Klong.create(Util.toBytes("01"));
        insert[0].node = v1;
        insert[1].klong = Klong.create(Util.toBytes("02"));
        insert[1].node = v1;
        
        KeyNode last = n.lastVersion(100);
        n.firstAndSecond(100, last, insert, first, second);
        
        //System.out.println("---- NodeTester.testFirstAndSecond5 ----");
        //System.out.println(n.print());
        //System.out.println(first.print());
        //System.out.println(second.print());
        
        Assert.assertEquals(5, first.size);
        Assert.assertEquals(Klong.createTime(100), first.klongs[0]);
        Assert.assertEquals(Klong.create(Util.toBytes("10")), first.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("20")), first.klongs[2]);
        Assert.assertEquals(Klong.create(Util.toBytes("01")), first.klongs[3]);
        Assert.assertEquals(Klong.create(Util.toBytes("02")), first.klongs[4]);
        
        Assert.assertEquals(Klong.createTime(100), second.klongs[0]);
        Assert.assertEquals(Klong.create(Util.toBytes("30")), second.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("40")), second.klongs[2]);
        Assert.assertEquals(3, second.size);
    }
    
    @T
    public static void testFirstAndSecond6() {
        // Insert more than one at very end.
        
        KeyNode n = new KeyNode();
        ValueNode v1 = new ValueNode(Util.toBytes("v1"));
        n.addKlong(10, Klong.create(Util.toBytes("10")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(10, Klong.create(Util.toBytes("20")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.create(Util.toBytes("30")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(40, Klong.create(Util.toBytes("40")), v1, AccessData.DEFAULT_ACCESS_DATA);
        
        KeyNode first = new KeyNode();
        KeyNode second = new KeyNode();
        KlongWithPointer[] insert = { new KlongWithPointer(), new KlongWithPointer() };

        insert[0].klong = Klong.create(Util.toBytes("41"));
        insert[0].node = v1;
        insert[1].klong = Klong.create(Util.toBytes("42"));
        insert[1].node = v1;
        
        KeyNode last = n.lastVersion(100);
        n.firstAndSecond(100, last, insert, first, second);
        
        //System.out.println("---- NodeTester.testFirstAndSecond6 ----");
        //System.out.println(n.print());
        //System.out.println(first.print());
        //System.out.println(second.print());
        
        Assert.assertEquals(3, first.size);
        Assert.assertEquals(Klong.createTime(100), first.klongs[0]);
        Assert.assertEquals(Klong.create(Util.toBytes("10")), first.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("20")), first.klongs[2]);
        
        Assert.assertEquals(Klong.createTime(100), second.klongs[0]);
        Assert.assertEquals(Klong.create(Util.toBytes("30")), second.klongs[1]);
        Assert.assertEquals(Klong.create(Util.toBytes("40")), second.klongs[2]);
        Assert.assertEquals(Klong.create(Util.toBytes("41")), second.klongs[3]);
        Assert.assertEquals(Klong.create(Util.toBytes("42")), second.klongs[4]);
        Assert.assertEquals(5, second.size);
    }
    
    @T
    public static void testDeleteBitmap1() {
        KeyNode node = new KeyNode();
        ValueNode value = new ValueNode(new byte[0]);
        node.addKlong(10, Klong.create(Util.toBytes("a")), value, AccessData.DEFAULT_ACCESS_DATA);
        node.addKlong(20, Klong.create(Util.toBytes("c")), value, AccessData.DEFAULT_ACCESS_DATA);
        
        long ca = Klong.createCompareValue(Util.toBytes("a"));
        long cb = Klong.createCompareValue(Util.toBytes("b"));
        long cc = Klong.createCompareValue(Util.toBytes("c"));
        long cd = Klong.createCompareValue(Util.toBytes("d"));
        
        Assert.assertTrue(node.getDeleteBitmap(ca) != 0);
        Assert.assertTrue(node.getDeleteBitmap(cb) == 0);
        Assert.assertTrue(node.getDeleteBitmap(cc) != 0);
        Assert.assertTrue(node.getDeleteBitmap(cd) == 0);
        
        long del = Klong.createDeleteBitmap();
        del = Klong.delete(del, 1);
        Assert.assertEquals(del, node.getDeleteBitmap(ca));
        
        del = Klong.createDeleteBitmap();
        del = Klong.delete(del, 3);
        Assert.assertEquals(del, node.getDeleteBitmap(cc));
    }
    
    @T
    public static void testPrint() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode t2 = t.createT2();
        t2.print();
    }
    
    public static void main(String[] args) throws Exception {
        testGt1();
    }
}
