package bergdb.dag;

import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Tests for class KeyNode.
 * 
 * @author Frans Lundberg
 */
public class KeyNodeTester {
    public KeyNode[] t2Pointers;
    
    /**
     * Returns a test key node called T2.
     * 
     * <pre>
     * These are the "keys" that have pointers:
     *   ap    - P0
     *   apa   - P1
     *   d     - P2
     *   g     - P3
     *   kr    - P4
     *   kram  - P5
     *   mage  - P6
     *   md    - P7
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
            long klongToAdd = Klong.createKey(StringUtil.toBytes(keys[i]));
            node.addKlong(1, klongToAdd, t2Pointers[i], AccessData.DEFAULT_ACCESS_DATA);
        }
        
        return node;
    }
    
    @Nano
    public static void testSanity1() {
        KeyNodeTester t = new KeyNodeTester();
        t.createT2();
    }
    
    /**
     * bergdb 021-06: print() shows a key node whose keys have no ikey, as its error messages
     * do (StoredTrans's and KeyNode's checks, the asserts of addKlong; until record format 8 also of the old writer's firstAndSecond). A
     * klong of 7 bytes or less is printed as text when its bytes are printable ASCII, each less
     * 2; the byte 0x31 ('/' + 2), which an index entry's level has, is such a byte, but a bkey
     * with it has no ikey, and Keys.bkey2ikey threw IllegalArgumentException there.
     */
    @Nano
    public static void testPrintKeysWithoutIkey() {
        KeyNode node = new KeyNode();
        byte[][] keys = {{0x63, 0x31, 0x64}, {0x63, 0x31, 0x64, 0x32, 0x00}, {0x65}};
        for (byte[] key : keys) {
            node.addKlong(1, Klong.createKey(key), new KeyNode(), AccessData.DEFAULT_ACCESS_DATA);
        }
        Assert.assertEquals("a/b", KeyNode.getKeyString(new byte[] {0x63, 0x31, 0x64}));
        String printed = node.print();
        Assert.assertTrue(printed, printed.contains("a/b"));
        Assert.assertTrue(printed, printed.contains("c"));
    }
    
    /**
     * bergdb 021-15: the texts of validateStreamNode, which a start refuses a stream with,
     * and of check() name the node by its id and position (Node.name), the same in every
     * run, as a port of the Core matches them byte for byte. They held toString(), with the
     * object's identity hash ("K/44" in one run, "K/ab" in the next), and one the whole node.
     */
    @Nano
    public static void testNodeTextsSameInEveryRun() {
        long key = Klong.createKey(StringUtil.toBytes("a"));
        Assert.assertEquals("Key node 22807 at 36536 with size 0.",
                invalid(streamNode(new long[0], new long[0]), 470));
        // A key klong before every time klong is of the time 0, at or before the startup time.
        Assert.assertEquals("Bad spos of pointer 0 of key node 22807 at 36536: -1, at or before "
                + "the startup time 470.",
                invalid(streamNode(new long[] {key}, new long[] {Spos.NULL}), 470));
        Assert.assertEquals("Bad spos of pointer 1 of key node 22807 at 36536: -5.",
                invalid(streamNode(new long[] {Klong.createTime(480), key},
                        new long[] {Spos.NULL, -5}), 470));
        KeyNode bad = streamNode(new long[] {Klong.createTime(400), key},
                new long[] {Spos.NULL, Spos.NULL});
        Assert.assertEquals("java.lang.AssertionError: Bad spos of pointer 1 of key node 22807 "
                + "at 36536: -1.", bad.checkWithMessage());
        Assert.assertEquals("key node 22807 at 36536", Node.name(bad));
    }
    
    /** The message of validateStreamNode, or null if the node is valid. */
    private static String invalid(KeyNode node, long startupTime) {
        try {
            node.validateStreamNode(startupTime);
            return null;
        } catch (KeyNode.Invalid e) {
            return e.getMessage();
        }
    }
    
    /** A key node as a start reads it: id 22807, at 36536, its pointers stream pointers. */
    private static KeyNode streamNode(long[] klongs, long[] positions) {
        KeyNode node = new KeyNode();
        node.id = 22807;
        node.spos = 36536;
        for (int i = 0; i < klongs.length; i++) {
            node.addToEnd(klongs[i], null, positions[i]);
        }
        return node;
    }
    
    @Nano
    public static void testSanity2() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode t2 = t.createT2();
        long compareValue = createCompareValue(StringUtil.toBytes("ap"));
        
        KlongWithPointer kwi = new KlongWithPointer();
        t2.searchEq(2000, compareValue, kwi);
        
        Assert.assertEquals(true, t2.getPointerNode(kwi.pointerIndex) != null);
        Assert.assertEquals(t.t2Pointers[0], t2.getPointerNode(kwi.pointerIndex));
    }
    
    private static long createCompareValue(byte[] bytes) {
        return Klong.createCompareValue(bytes, 0, bytes.length);
    }
    
    @Nano
    public static void testEq() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode t2 = t.createT2();
        KlongWithPointer kwi = new KlongWithPointer();
        
        t2.searchEq(2000, createCompareValue(StringUtil.toBytes("ap")), kwi);
        Assert.assertEquals(t.t2Pointers[0], t2.getPointerNode(kwi.pointerIndex));
        
        t2.searchEq(2000, createCompareValue(StringUtil.toBytes("apa")), kwi);
        Assert.assertEquals(true, t2.getPointerNode(kwi.pointerIndex) != null);
        Assert.assertEquals(t.t2Pointers[1], t2.getPointerNode(kwi.pointerIndex));
        
        t2.searchEq(2000, createCompareValue(StringUtil.toBytes("g")), kwi);
        Assert.assertEquals(t.t2Pointers[3], t2.getPointerNode(kwi.pointerIndex));
        
        t2.searchEq(2000, createCompareValue(StringUtil.toBytes("mage")), kwi);
        Assert.assertEquals(t.t2Pointers[6], t2.getPointerNode(kwi.pointerIndex));
        
        t2.searchEq(2000, createCompareValue(StringUtil.toBytes("md")), kwi);
        Assert.assertEquals(t.t2Pointers[7], t2.getPointerNode(kwi.pointerIndex));
    }
    
    @Nano
    public static void testEqWithVersions() {
        KeyNodeTester t = new KeyNodeTester();
        KlongWithPointer kwi = new KlongWithPointer();
        
        KeyNode t2 = t.createT2();
        
        t2.addKlong(1020, Klong.createKey(StringUtil.toBytes("a")), t.t2Pointers[7], AccessData.DEFAULT_ACCESS_DATA);
        
        long compareValue = createCompareValue(StringUtil.toBytes("a"));
        t2.searchEq(2000, compareValue, kwi);
        Assert.assertEquals(t.t2Pointers[7], kwi.node);
        
        compareValue = createCompareValue(StringUtil.toBytes("mage"));
        t2.searchEq(2000, compareValue, kwi);
        Assert.assertEquals(t.t2Pointers[6], kwi.node);
    }
    
    @Nano
    public static void testEqWithVersionsAndDelete() {
        KeyNodeTester t = new KeyNodeTester();
        KlongWithPointer kwi = new KlongWithPointer();
        KeyNode node = t.createT2();
        long klong = node.getDeleteBitmap(Klong.createCompareValue(StringUtil.toBytes("apa")));
        node.addKlong(1020, klong, null, AccessData.DEFAULT_ACCESS_DATA);
        
        long compareValue = createCompareValue(StringUtil.toBytes("apa"));
        node.searchEq(2000, compareValue, kwi);

        //System.out.println("---- NodeTester.testEQWithVersionsAndDelete ----");
        //System.out.println("node: " + node.print());
        //System.out.println("klong: " + Klong.toString(kwi.klong));
        
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("apa"));
        node.searchEq(1010, compareValue, kwi);
        Assert.assertEquals(t.t2Pointers[1], kwi.node);
        
        node.addKlong(1030, Klong.createKey(StringUtil.toBytes("apa")), t.t2Pointers[5], AccessData.DEFAULT_ACCESS_DATA);
        
        compareValue = createCompareValue(StringUtil.toBytes("apa"));
        node.searchEq(2000, compareValue, kwi);
        Assert.assertEquals(t.t2Pointers[5], kwi.node);
    }
    
    @Nano
    public static void testEqBeforeFirstVersion() {
        KeyNode n = new KeyNode();
        long klongToAdd = Klong.createKey(StringUtil.toBytes("first"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        
        n.check();
        KlongWithPointer kwi = new KlongWithPointer();
        long compareValue = createCompareValue(StringUtil.toBytes("first"));
        
        n.searchEq(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong != Klong.NULL);
        
        n.searchEq(5, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong == Klong.NULL);
    }
    
    @Nano
    public static void testLte1() {
        KeyNode n = new KeyNode();
        long klongToAdd = Klong.createKey(StringUtil.toBytes("first"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        n.check();
        KlongWithPointer kwi = new KlongWithPointer();
        long compareValue = createCompareValue(StringUtil.toBytes("first"));
        
        n.searchLte(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong != Klong.NULL);
        
        n.searchLte(5, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong == Klong.NULL);
        
        compareValue = createCompareValue(StringUtil.toBytes("fir"));
        n.searchLte(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong == Klong.NULL);
        
        compareValue = createCompareValue(StringUtil.toBytes("g"));
        n.searchLte(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong != Klong.NULL);
    }
    
    @Nano
    public static void testLte2() {
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.createKey(StringUtil.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.createKey(StringUtil.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(StringUtil.toBytes("k20"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k21"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k19"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k09"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        // Tests at time = 15
        
        compareValue = createCompareValue(StringUtil.toBytes("k99"));
        n.searchLte(15, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k10"));
        n.searchLte(15, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k09"));
        n.searchLte(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
    }
    
    @Nano
    public static void testLte3() {
        //
        // Tests KeyNode.searchLTE() with a delete.
        //
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.createKey(StringUtil.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.createKey(StringUtil.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = n.getDeleteBitmap(Klong.createCompareValue(StringUtil.toBytes("k10")));
        n.addKlong(30, klongToAdd, null, AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(StringUtil.toBytes("k20"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k21"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k19"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals("Got: " + Klong.toString(kwi.klong) + ", " + kwi.klongTime, Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k09"));
        n.searchLte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
    }
    
    @Nano
    public static void testLt1() {
        KeyNode n = new KeyNode();
        long klongToAdd = Klong.createKey(StringUtil.toBytes("first"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        n.check();
        KlongWithPointer kwi = new KlongWithPointer();
        long compareValue = createCompareValue(StringUtil.toBytes("first"));
        
        n.searchLt(20, compareValue, kwi);
        Assert.assertTrue(kwi.klong == Klong.NULL);
        
        n.searchLt(5, compareValue, kwi);
        Assert.assertTrue(kwi.klong == Klong.NULL);
        
        compareValue = createCompareValue(StringUtil.toBytes("fir"));
        n.searchLt(20, compareValue, kwi);
        Assert.assertTrue(kwi.klong == Klong.NULL);
        
        compareValue = createCompareValue(StringUtil.toBytes("g"));
        n.searchLt(20, compareValue, kwi);
        Assert.assertTrue(kwi.klong != Klong.NULL);
    }
    
    @Nano
    public static void testLt2() {
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.createKey(StringUtil.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.createKey(StringUtil.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(StringUtil.toBytes("k20"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k21"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k19"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k09"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        // Tests at time = 15
        
        compareValue = createCompareValue(StringUtil.toBytes("k99"));
        n.searchLt(15, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k10"));
        n.searchLt(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k09"));
        n.searchLt(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
    }
    
    @Nano
    public static void testLt3() {
        //
        // Tests KeyNode.searchLt() with a delete.
        //
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.createKey(StringUtil.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.createKey(StringUtil.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = n.getDeleteBitmap(Klong.createCompareValue(StringUtil.toBytes("k10")));
        n.addKlong(30, klongToAdd, null, AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(StringUtil.toBytes("k20"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k21"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k19"));
        n.searchLt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals("Got: " + Klong.toString(kwi.klong) + ", " + kwi.klongTime, 
                Klong.NULL, kwi.klong);
    }
    
    @Nano
    public static void testGt1() {
        KeyNode n = new KeyNode();
        long klongToAdd = Klong.createKey(StringUtil.toBytes("key"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        n.check();
        KlongWithPointer kwi = new KlongWithPointer();

        long compareValue = createCompareValue(StringUtil.toBytes("a"));
        n.searchGt(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong != Klong.NULL);
        
        n.searchGt(5, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong == Klong.NULL);
        
        compareValue = createCompareValue(StringUtil.toBytes("key"));
        n.searchGt(20, compareValue, kwi);
        Assert.assertEquals(true, kwi.klong == Klong.NULL);
    }
    
    @Nano
    public static void testGt2() {
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.createKey(StringUtil.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.createKey(StringUtil.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(StringUtil.toBytes("k19"));
        n.searchGt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k10"));
        n.searchGt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k20"));
        n.searchGt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k00"));
        n.searchGt(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
        
        // Tests at time = 15
        
        compareValue = createCompareValue(StringUtil.toBytes("k15"));
        n.searchGt(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k10"));
        n.searchGt(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k09"));
        n.searchGt(15, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
    }
    
    
    @Nano
    public static void testGte() {
        KeyNode n = new KeyNode();
        long klongToAdd;
        long compareValue;
        KlongWithPointer kwi = new KlongWithPointer();
        
        // Creates KeyNode.
        
        klongToAdd = Klong.createKey(StringUtil.toBytes("k10"));
        n.addKlong(10, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        klongToAdd = Klong.createKey(StringUtil.toBytes("k20"));
        n.addKlong(20, klongToAdd, new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);

        // Tests at time = Long.MAX_VALUE.
        
        compareValue = createCompareValue(StringUtil.toBytes("k19"));
        n.searchGte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k10"));
        n.searchGte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k20"));
        n.searchGte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k20")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k00"));
        n.searchGte(Long.MAX_VALUE, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
        
        // Tests at time = 15
        
        compareValue = createCompareValue(StringUtil.toBytes("k15"));
        n.searchGte(15, compareValue, kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k10"));
        n.searchGte(15, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
        
        compareValue = createCompareValue(StringUtil.toBytes("k09"));
        n.searchGte(15, compareValue, kwi);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("k10")), kwi.klong);
    }
    
    
    @Nano
    public static void testFirst1() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode t2 = t.createT2();
        KlongWithPointer kwi = new KlongWithPointer();
        
        t2.searchFirst(2000, kwi);
        Assert.assertEquals(false, kwi.klong == Klong.NULL);
        Assert.assertEquals(t.t2Pointers[0], kwi.node);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("ap")), kwi.klong);
    }
    
    @Nano
    public static void testCheckEmptyNode() {
        // The empty node is allowed, zero klongs.
        new KeyNode().check();
    }
    
    @Nano
    public static void testCheck1() {
        new KeyNodeTester().createT2().check();
    }
    
    @Nano
    public static void testCheck2() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode node = t.createT2();
        node.check();
        long klong = node.getDeleteBitmap(Klong.createCompareValue(StringUtil.toBytes("apa")));
        node.addKlong(1020, klong, null, AccessData.DEFAULT_ACCESS_DATA);
        //node.addKlong(1020, Klong.createDelete(Util.toBytes("apa")), null, Spos.DEFAULT_ACCESS_DATA);
        node.check();        
        node.addKlong(1030, Klong.createKey(StringUtil.toBytes("apa")), t.t2Pointers[5], AccessData.DEFAULT_ACCESS_DATA);
        node.check();
    }
    
    @Nano
    public static void testGetPointers() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode node = t.createT2();
        int pointerCount = node.getSize();
        Pointer p = new Pointer();

        for (int j = 0; j < pointerCount; j++) {
            node.getPointer(j, p);
            if (p.isNull()) {
                continue;
            }
            Assert.assertEquals("j=" + j, t.t2Pointers[j - 1], p.node);
        }
    }
    
    @Nano
    public static void testLastVersion1() {
        KeyNode n = new KeyNode();
        
        n.addKlong(10, Klong.createKey(StringUtil.toBytes("a")), new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.createKey(StringUtil.toBytes("b")), new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.createKey(StringUtil.toBytes("c")), new ValueNode(new byte[0]), AccessData.DEFAULT_ACCESS_DATA);
        
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
    
    @Nano
    public static void testLastVersion3() {
        KeyNode n = new KeyNode();
        ValueNode value = new ValueNode(new byte[0]);
        
        n.addKlong(10, Klong.createKey(StringUtil.toBytes("a")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.createKey(StringUtil.toBytes("b")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(25, Klong.createKey(StringUtil.toBytes("c")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, n.getDeleteBitmap(Klong.createCompareValue(StringUtil.toBytes("b"))), null, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(40, n.getDeleteBitmap(Klong.createCompareValue(StringUtil.toBytes("a"))), null, AccessData.DEFAULT_ACCESS_DATA);
        
        n.addKlong(50, Klong.createKey(StringUtil.toBytes("b")), value, AccessData.DEFAULT_ACCESS_DATA);
        
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
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("b")), last.klongs[1]);
        Assert.assertEquals(Klong.createKey(StringUtil.toBytes("c")), last.klongs[2]);
    }
    
    @Nano
    public static void testLastVersion4() {
        //
        // Tests adding a delete-all klong.
        //
        
        KeyNode n = new KeyNode();
        ValueNode value = new ValueNode(new byte[0]);
        n.addKlong(10, Klong.createKey(StringUtil.toBytes("a")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(10, Klong.createKey(StringUtil.toBytes("b")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.createKey(StringUtil.toBytes("c")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, n.getDeleteBitmap(Klong.createCompareValue(StringUtil.toBytes("b"))), null, 
                AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(40, Klong.createKey(StringUtil.toBytes("d")), value, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(50, Klong.DELETE_ALL_BITMAP, null, AccessData.DEFAULT_ACCESS_DATA);
        
        KeyNode last = n.lastVersion(100);
        
        //System.out.println("---- NodeTester.testLastVersion4 ----");
        //System.out.println("last:\n" + last.print());
        
        Assert.assertTrue(last.size <= 1);
    }
    
    @Nano
    public static void testDeleteBitmap1() {
        KeyNode node = new KeyNode();
        ValueNode value = new ValueNode(new byte[0]);
        node.addKlong(10, Klong.createKey(StringUtil.toBytes("a")), value, AccessData.DEFAULT_ACCESS_DATA);
        node.addKlong(20, Klong.createKey(StringUtil.toBytes("c")), value, AccessData.DEFAULT_ACCESS_DATA);
        
        long ca = Klong.createCompareValue(StringUtil.toBytes("a"));
        long cb = Klong.createCompareValue(StringUtil.toBytes("b"));
        long cc = Klong.createCompareValue(StringUtil.toBytes("c"));
        long cd = Klong.createCompareValue(StringUtil.toBytes("d"));
        
        Assert.assertTrue(node.getDeleteBitmap(ca) != 0);
        Assert.assertTrue(node.getDeleteBitmap(cb) == 0);
        Assert.assertTrue(node.getDeleteBitmap(cc) != 0);
        Assert.assertTrue(node.getDeleteBitmap(cd) == 0);
        
        long del = Klong.createDelete();
        del = Klong.delete(del, 1);
        Assert.assertEquals(del, node.getDeleteBitmap(ca));
        
        del = Klong.createDelete();
        del = Klong.delete(del, 3);
        Assert.assertEquals(del, node.getDeleteBitmap(cc));
    }
    
    @Nano
    public static void testPrint() {
        KeyNodeTester t = new KeyNodeTester();
        KeyNode t2 = t.createT2();
        t2.print();
    }
    
    /** Changing to state t=15 should remove "c" and keep "a". */
    @Nano private static void testToPreviousState1() {
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");
        addKlong(node, 20, "b");
        
        node.toPreviousState(15);
        
        assertExists(node, "a");
        assertNotExists(node, "b");
    }

    private static void assertNotExists(KeyNode node, String s) {
        KlongWithPointer kwi = new KlongWithPointer();
        node.searchEq(999, Klong.createCompareValue(StringUtil.toBytes(s)), kwi);
        Assert.assertEquals(Klong.NULL, kwi.klong);
    }
    
    private static void assertExists(KeyNode node, String s) {
        KlongWithPointer kwi = new KlongWithPointer();
        node.searchEq(999, Klong.createCompareValue(StringUtil.toBytes(s)), kwi);
        Assert.assertTrue(kwi.klong != Klong.NULL);
    }
    
    private static void addKlong(KeyNode node, long time, String s) {
        ValueNode value = new ValueNode(new byte[0]);
        node.addKlong(time, Klong.createKey(StringUtil.toBytes(s)), value, AccessData.DEFAULT_ACCESS_DATA);
    }
    
    /** Changing to state t=5 should remove "b" and "a". */
    @Nano private static void testToPreviousState2() {
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");
        addKlong(node, 20, "b");
        
        node.toPreviousState(5);
        
        assertNotExists(node, "a");
        assertNotExists(node, "b");
    }
    
    @Nano
    private static void testToPreviousState3() {
        // Changing to state t=40 (in future) should not remove "c", nor "a".
        
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");
        addKlong(node, 20, "b");
        
        node.toPreviousState(40);
        
        assertExists(node, "a");
        assertExists(node, "b");
    }
    
    @Nano private static void testToPreviousState4() {
        // Changing to state t=15 and add klong "c" after that, should work.
        
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");
        addKlong(node, 20, "b");
        
        node.toPreviousState(15);
        addKlong(node, 30, "c");
        
        assertExists(node, "a");
        assertNotExists(node, "b");
        assertExists(node, "c");
    }
    
    @Nano private static void testNewKeyNodeWithTime() {
        KeyNode node = KeyNode.nodeWithTime(123);
        
        Assert.assertEquals(1, node.size);
        Assert.assertEquals(1, node.getSize());
        Pointer p = new Pointer();
        node.getPointer(0, p);
        Assert.assertTrue(p.isNull());
        long klong = node.getKlong(0);
        Assert.assertEquals(Klong.TYPE_TIME, Klong.getType(klong));
        Assert.assertEquals(123, Klong.getTime(klong));
    }
    
    @Nano private static void testGetFirstTime1() {
        KeyNode node = KeyNode.nodeWithTime(123);
        Assert.assertEquals(123, node.getFirstTime());
    }
    
    @Nano private static void testGetFirstTime2() {
        KeyNode node = new KeyNode();
        Assert.assertEquals(-1, node.getFirstTime());
    }
    
    @Nano private static void testGetFirstTime3() {
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");
        addKlong(node, 20, "b");
        Assert.assertEquals(10, node.getFirstTime());
    }
    
    @Nano private static void testGetPointerCount0() {
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");
        Assert.assertEquals(2, node.getSize());
    }
    
    @Nano private static void testGetPointerCount1() {
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");
        addKlong(node, 10, "b");
        Assert.assertEquals(3, node.getSize());
    }
    
    @Nano private static void testGetPointerCount2() {
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");
        addKlong(node, 20, "b");
        Assert.assertEquals(4, node.getSize());
    }
    
    @Nano private static void testGetPointerCount3() {
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");
        addKlong(node, 20, "b");
        Assert.assertEquals(0, node.getSizeAtTime(9));
        Assert.assertEquals(2, node.getSizeAtTime(10));
        Assert.assertEquals(2, node.getSizeAtTime(11));
        Assert.assertEquals(2, node.getSizeAtTime(19));
        Assert.assertEquals(4, node.getSizeAtTime(20));
        Assert.assertEquals(4, node.getSizeAtTime(Long.MAX_VALUE));
    }
    
    @Nano private static void testMaxValidTime0() {
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");
        Assert.assertEquals(Long.MAX_VALUE, node.getMaxValidTime(1));
    }
    
    @Nano private static void testMaxValidTime1() {
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");     // index 1
        addKlong(node, 20, "a");     // index 3
        Assert.assertEquals(19, node.getMaxValidTime(1));
        Assert.assertEquals(Long.MAX_VALUE, node.getMaxValidTime(3));
    }
    
    @Nano private static void testMaxValidTimeWithDelete() {
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");     // index 1
        addKlong(node, 20, "b");     // index 3
        
        long deleteKlong = node.getDeleteBitmap(Klong.createCompareValue(StringUtil.toBytes("a")));
        node.addKlong(30, deleteKlong, null, AccessData.DEFAULT_ACCESS_DATA);
        
        Assert.assertEquals(29, node.getMaxValidTime(1));
        Assert.assertEquals(Long.MAX_VALUE, node.getMaxValidTime(3));
    }
    
    @Nano private static void testAddDeleteKlong() {
        // Checks that pointer corresponding to delete klong is null (Pointer.isNull() == true).
        
        KeyNode node = new KeyNode();
        addKlong(node, 10, "a");                                // index 1
        node.addDeleteKlong(40, Klong.createDelete());    // index 3
        
        Pointer p = new Pointer();
        
        node.getPointer(0, p);
        Assert.assertEquals(true, p.isNull());
        
        node.getPointer(1, p);
        Assert.assertEquals(false, p.isNull());
        
        node.getPointer(2, p);
        Assert.assertEquals(true, p.isNull());
        
        node.getPointer(3, p);
        Assert.assertEquals(true, p.isNull());
    }
    
    @Nano private static void testPointerInPlace() {
        // bergdb 015-14: pointer 0 changed in place as a reader's slow path and the writer
        // change it (raiseRef, swizzle, setPointer), read as the fast path and the searches
        // read it (getPointee, then getPointerPos), before and after a growth copies it.
        KeyNode x = new KeyNode(false);
        Handle a = new Handle(7);
        Handle b = new Handle(7);
        KeyNode v = new KeyNode(true);
        v.setSpos(300);
        b.obj = v;
        x.addToEnd(Klong.createKey(new byte[] {1}), a, 200);
        x.raiseRef(0, 100);
        Assert.assertEquals("never lowered", 200, x.getPointerPos(0));
        x.raiseRef(0, 300);
        Assert.assertEquals("a swizzle expects what it read", false, x.swizzle(0, b, b));
        Assert.assertEquals(true, x.swizzle(0, a, b));
        Assert.assertEquals(true, x.getPointee(0) == b);
        Assert.assertEquals(true, x.getPointerNode(0) == v);
        for (int i = 2; i <= 30; i++) {
            x.addToEnd(Klong.createKey(new byte[] {(byte) i}), null, 8 * i);
        }
        Assert.assertEquals(true, x.pointers.length >= 30);
        Assert.assertEquals(true, x.getPointee(0) == b);
        Assert.assertEquals(300, x.getPointerPos(0));
        Assert.assertEquals(8 * 30, x.getPointerPos(29));
        KlongWithPointer kwi = new KlongWithPointer();
        x.searchEq(Long.MAX_VALUE, Klong.getCompareValue(x.getKlong(0)), kwi);
        Assert.assertEquals(0, kwi.pointerIndex);
        Assert.assertEquals(true, kwi.node == v);
        Assert.assertEquals(300, kwi.pos);
        x.setPointer(0, null, 400);
        Assert.assertEquals(true, x.getPointee(0) == null);
        Assert.assertEquals(400, x.getPointerPos(0));
        Assert.assertEquals(true, x.getPointerNode(0) == null);
        b.obj = null;
        x.setPointee(0, b);
        Assert.assertEquals("no object: the slow path", true, x.getPointerNode(0) == null);
    }
    
    public static void main(String[] args) throws Exception {
        testGt1();
    }
}
