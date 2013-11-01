package bergdb.core;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.TopNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.BadReplicaException;
import bergdb.pub.Clock;
import bergdb.pub.IllegalDbStateException;
import bergdb.storage.RecoverableStream;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * Class for general unit testing of Db.
 * 
 * @author Frans Lundberg
 */
public class DbTester {
    
    @T
    public static void test0() {
        Db db = Db.builder().testSetup().start();
        db.stop();
    }
    
    @T
    public static void test1() {
        Db db = Db.builder().testSetup().start();
        byte[] value = DbUtil.get(db, 99, Util.toBytes("admin1"));
        Assert.assertNull(value);
    }
    
    @T
    public static void test2() {
        Db db = Db.builder().testSetup().start();
        db.execute(Trans.builder().put("admin1", "F").build());
        byte[] value = DbUtil.get(db, 99, Keys.toBytes("admin1"));
        Assert.assertArrayEquals(Util.toBytes("F"), value);
    }
    
    @T
    public static void test3() {
        Db db = Db.builder().testSetup().start();
        db.execute(Trans.builder().put("admin1", "F1")
                .put("admin2", "F2").build());
        
        byte[] value = DbUtil.get(db, 99, Keys.toBytes("admin1"));
        Assert.assertArrayEquals(Util.toBytes("F1"), value);
        value = DbUtil.get(db, 99, Keys.toBytes("admin2"));
        Assert.assertArrayEquals(Util.toBytes("F2"), value);
    }
    
    @T
    public static void test4() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        //db.setTime(100);
        clock.setTime(100);
        db.execute(Trans.builder().put("admin1", "F1").build());
        //db.setTime(200);
        clock.setTime(200);
        db.execute(Trans.builder().put("admin2", "F2").build());
        
        byte[] value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("admin1"));
        Assert.assertArrayEquals(Util.toBytes("F1"), value);
        value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("admin2"));
        Assert.assertArrayEquals(Util.toBytes("F2"), value);
        //db.stop();
    }

    @T
    public static void testT2() {
        byte[] value;
        KTestClock clock = new KTestClock();
        Db db = createT2DB(clock);
        
        value = DbUtil.get(db, 999, "apa");
        Assert.assertArrayEquals(Util.toBytes("P1"), value);

        value = DbUtil.get(db, 999, "ap");
        Assert.assertArrayEquals(Util.toBytes("P0"), value);

        value = DbUtil.get(db, 999, "md");
        Assert.assertArrayEquals(Util.toBytes("P7"), value);
    }
    
    private static Db createT2DB(Clock clock) {
        Db db = Db.builder().testSetup().clock(clock).start();
        String[] keys = new String[] { "ap", "apa", "d", "g", "kr", "kram",
                "mage", "md" };
        
        Trans.Builder b = Trans.builder();
        for (int i = 0; i < keys.length; i++) {
            b.put(keys[i], "P" + i);
        }
        db.execute(b.build());
        return db;
    }
    
    @T
    public static void testVersions() {
        //
        // Adds new value in a new key.
        //

        KTestClock clock = new KTestClock();
        Db db = createT2DB(clock);
        Trans t;
        
        clock.setTime(20);
        
        t = Trans.builder().put("e", "e-value").build();
        db.execute(t);

        Assert.assertEquals(true, t.transactionTime >= 20);
        Assert.assertArrayEquals(Util.toBytes("e-value"), DbUtil.get(db, 999, "e"));

        byte[] value = DbUtil.get(db, 10, "e");
        Assert.assertNull(value);
    }
    
    @T
    public static void testVersionsReplaceValue() {
        KTestClock clock = new KTestClock();
        Db db = createT2DB(clock);
        clock.setTime(20);
        db.execute(Trans.builder().put("apa", "A").build());

        Assert.assertArrayEquals(Util.toBytes("A"), DbUtil.get(db, 30, "apa"));
        Assert.assertArrayEquals(Util.toBytes("A"), DbUtil.get(db, 999, "apa"));
    }
    
    @T
    public static void testLongKey() {
        Db db = Db.builder().testSetup().start();
        db.execute(Trans.builder().put("myLongerKey", "v1").build());
        
        //System.out.println("---- DBTester.testLongKey ----");
        //System.out.println(db.findRoot(db.getTime()).printTree());
        
        Assert.assertNull(DbUtil.get(db, 99, Util.toBytes("rKey")));
        Assert.assertArrayEquals(Util.toBytes("v1"), DbUtil.get(db, 99, "myLongerKey"));
    }
    
    @T
    public static void testLongerKey() {
        String longerKey = "anotherKeyThatIsLongerThanThePreviousAndIndeedVeryLong";
        Db db = Db.builder().testSetup().start();
        db.execute(Trans.builder()
                .put(longerKey, "v2")
                .build());
        
        Assert.assertArrayEquals(Util.toBytes("v2"),
                DbUtil.get(db, 99, longerKey));
    }
    
    @T
    public static void testMultipleLongKeys() {
        String longerKey = "anotherKeyThatIsLongerThanThePreviousAndIndeedVeryLong";
        Db db = Db.builder().testSetup().start();
        db.execute(Trans.builder()
                .put(longerKey, "v2")
                .put("myLongerKey", "v1")
                .build());
        
        Assert.assertArrayEquals(Util.toBytes("v2"), DbUtil.get(db, 99, longerKey));
        Assert.assertArrayEquals(Util.toBytes("v1"), DbUtil.get(db, 99, "myLongerKey"));
        Assert.assertNull(DbUtil.get(db, 99, Util.toBytes("myLongerX")));
    }
    
    @T
    public static void testLongAndShortKeys() {
        //
        // Tests with two keys, k1, k2. k1 has two segments and k2 has one and
        // the order is: k1 < k2.
        //
        Db db = Db.builder().testSetup().start();
        db.execute(Trans.builder()
                .put("myLongerKey", "v1")
                .put("nash", "v2")
                .build());
        
        //System.out.println("---- DBTester.testLongAndShortKeys ----");
        //System.out.println(db.findRoot(db.getTime()).printTree());
        
        Assert.assertArrayEquals(Util.toBytes("v1"), DbUtil.get(db, 20, "myLongerKey"));
        Assert.assertArrayEquals(Util.toBytes("v2"), DbUtil.get(db, 20, "nash"));
        Assert.assertNull(DbUtil.get(db, 20, "myLongerX"));
        Assert.assertNull(DbUtil.get(db, 20, "anotherX"));
        Assert.assertNull(DbUtil.get(db, 20, "nas"));
        Assert.assertNull(DbUtil.get(db, 20, "nasher"));
    }
    
    @T
    public static void testMultipleKeysWithSamePrefix() {
        Db db = Db.builder().testSetup().start();
        db.execute(Trans.builder()
                .put("myLongerKey1", "v1")
                .put("myLongerKey2", "v2")
                .build());
        
        //System.out.println("---- DBTester.testMultipleKeysWithSamePrefix ----");
        //System.out.println(db.findRoot(db.getTime()).printTree());
        
        Assert.assertArrayEquals(Util.toBytes("v1"), DbUtil.get(db, 30, "myLongerKey1"));
        Assert.assertArrayEquals(Util.toBytes("v2"), DbUtil.get(db, 30, "myLongerKey2"));
        Assert.assertNull(DbUtil.get(db, 30, Util.toBytes("myLongerX")));
        Assert.assertNull(DbUtil.get(db, 30, Util.toBytes("myLongerKey1b")));
    }
    
    @T
    public static void testDeleteTwoValues() {
        //
        // Delete of two values in same transaction.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        TopNode superRoot = db.getSuperRoot();
        
        db.execute(Trans.builder().put("a", "a-value").put("b", "b-value").build());
        
        //System.out.println("== DbTester.testDeleteX ==");
        //db.printGraph(System.out);
        
        db.execute(Trans.builder().delete("a").delete("b").build());
        
        //System.out.println("== DbTester.testDeleteX ==");
        //db.printGraph(System.out);
        
        assert superRoot == db.getSuperRoot() : superRoot + " != " + db.getSuperRoot();
        
        // Get the KeyNode and examines the DELETE_BITMAP at the end.
        
        KeyNode k = (KeyNode) db.findNode(new int[]{0}, db.newGetData());
        long klong = k.getKlong(4);
        Assert.assertEquals(Klong.getType(klong), Klong.TYPE_DELETE_BITMAP);
        Assert.assertFalse(Klong.isDeleted(klong, 0));
        Assert.assertTrue(Klong.isDeleted(klong, 1));
        Assert.assertTrue(Klong.isDeleted(klong, 2));
        Assert.assertFalse(Klong.isDeleted(klong, 3));
        Assert.assertFalse(Klong.isDeleted(klong, 4));
        
        db.stop();
    }
    
    @T
    public static void testDelete0() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(Trans.builder().put("a", "a-value")
                .put("b", "b-value").build());
        
        clock.setTime(20);
        db.execute(Trans.builder().delete("a").build());
        
        byte[] value = DbUtil.get(db, 30, Keys.toBytes("a"));
        Assert.assertNull(value);
        
        value = DbUtil.get(db, 30, Keys.toBytes("b"));
        Assert.assertArrayEquals(Util.toBytes("b-value"), value);

        value = DbUtil.get(db, 15, Keys.toBytes("a"));
        Assert.assertArrayEquals(Util.toBytes("a-value"), value);
        
        db.stop();
    }
    
    @T
    public static void testDelete1() {
        // Tests rewriting a value and deleting it in-between.
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().put("a", "a-value").put("b", "b-value"));
        
        clock.setTime(20);
        db.execute(Trans.builder().delete("a"));
        
        clock.setTime(30);
        db.execute(Trans.builder().put("a", "a-value-2"));
        
        clock.setTime(40);
        db.execute(Trans.builder().delete("a"));
        
        clock.setTime(50);
        db.execute(Trans.builder().put("a", "a-value-3"));
        
        byte[] value;
        value = DbUtil.get(db, Long.MAX_VALUE, "a");
        Assert.assertArrayEquals(Util.toBytes("a-value-3"), value);
        
        value = DbUtil.get(db, 5, "a");
        Assert.assertNull(value);
        
        value = DbUtil.get(db, 15, "a");
        Assert.assertEquals("a-value", Util.toString(value));
        
        value = DbUtil.get(db, 25, "a");
        Assert.assertNull(value);
        
        value = DbUtil.get(db, 35, "a");
        Assert.assertEquals("a-value-2", Util.toString(value));
        
        value = DbUtil.get(db, 45, "a");
        Assert.assertNull(value);
        
        value = DbUtil.get(db, 55, "a");
        Assert.assertEquals("a-value-3", Util.toString(value));
    }
    
    @T
    public static void testDeleteOfNonExistingData0() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(Trans.builder().delete("a").build());   // This is a noop transaction.
        byte[] value = DbUtil.get(db, Long.MAX_VALUE, "a");
        Assert.assertNull(value);
    }
    
    @T
    public static void testDeleteOfNonExistingData1() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(Trans.builder().put("a", "a-value").put("b", "b-value").build());
        clock.setTime(20);
        db.execute(Trans.builder().delete("c").build());
        db.execute(Trans.builder().delete("anton").build());
        db.execute(Trans.builder().delete("anton-and-all-his-friends").build());
        
        byte[] value = DbUtil.get(db, Long.MAX_VALUE, "a");
        Assert.assertArrayEquals(Util.toBytes("a-value"), value);
        
        value = DbUtil.get(db, Long.MAX_VALUE, "b");
        Assert.assertArrayEquals(Util.toBytes("b-value"), value);

        db.execute(Trans.builder().delete("a").build());
        db.execute(Trans.builder().delete("a").build());
        db.execute(Trans.builder().delete("a").build());
        
        value = DbUtil.get(db, Long.MAX_VALUE, "a");
        Assert.assertNull(value);
    }
    
    @T
    public static void testRerun() throws NumberFormatException, UnsupportedEncodingException {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        
        Trans t = Trans.builder()
                .put("acc1", "200")
                .put("acc2", "100").build();
        db.execute(t);   // executes at t = 11.
        
        clock.setTime(20);
        db.execute(Trans.builder().put("acc1", "50").build());    // executes at t=21
        
        clock.setTime(30);
        
        // Try transfer
        
        long amount1 = Long.parseLong(new String(
                DbUtil.get(db, 11, Keys.toBytes("acc1")), "UTF-8"));
        long amount2 = Long.parseLong(new String(
                DbUtil.get(db, 11, Keys.toBytes("acc2")), "UTF-8"));
        long amountAfter1 = 0;
        long amountAfter2 = 0;
        
        amountAfter1 = amount1 - 100;
        amountAfter2 = amount2 + 100;
        
        t = Trans.builder()
                .lookupTime(11)
                .keyRead("acc1")
                .keyRead("acc2")
                .put("acc1", "" + amountAfter1)
                .put("acc2", "" + amountAfter2)
                .build();
        
        RerunException rerunException = null;
        try {
            db.execute(t);
        } catch (RerunException e) {
            rerunException = e;
        }
        
        Assert.assertTrue("rerunException should be non-null", rerunException != null);
        
        // A later read time should work
        
        amountAfter1 = amount1 - 1;
        amountAfter2 = amount2 + 1;
        
        t = Trans.builder()
                .lookupTime(21)
                .keyRead("acc1")
                .keyRead("acc2")
                .put("acc1", "" + amountAfter1)
                .put("acc2", "" + amountAfter2)
                .build();
        
        db.execute(t);
    }
    
    @T
    public static void testSame7BytesPrefix() {
        Db db = Db.builder().testSetup().start();
        Trans t = Trans.builder()
                .put("account1", "1")
                .put("account2", "2").build();
        db.execute(t);
    }
    
    @T
    public static void testGetSmallerKey() {
        //
        // Smaller key then previous added. More than one segment.
        //
        
        Db db = Db.builder().testSetup().start();
        
        //db.setTime(1);
        db.execute(Trans.builder()
                .put("account1", "1").build());
        
        byte[] value = DbUtil.get(db, 20, Util.toBytes("account0"));
        Assert.assertNull(value);
    }
    
    @T
    public static void testSplit0() {
        // Time split with an ordinary KeyNode as parent.
        
        Db db;
        AppendOnlyStream stream = new MemoryStream();
        KTestClock clock = new KTestClock();
        db = Db.builder().testSetup().maxNodeSize14().mainStream(stream).clock(clock).start();

        for (int i = 0; i < 10; i++) {
            String keyString = "account-id-" + i;
            clock.setTime(1 + i);
            db.execute(Trans.builder().put(keyString, "v" + i));
        }
        
        //System.out.println("---- DBTester.testSplit1 ----");
        //System.out.println("graph:");
        //db.printGraph(System.out);
        
        byte[] value;
        for (int i = 0; i < 10; i++) {
            String keyString = "account-id-" + i;
            value = DbUtil.get(db, 999, keyString);
            Assert.assertArrayEquals("i=" + i, Util.toBytes("v" + i), value);
        }
    }
    
    @T
    public static void testSplit1() {
        // Parent is a space root node.
        
        byte[] value;
        long time;
        Db db;
        int n = 10;
        KTestClock clock = new KTestClock();
        
        db = Db.builder().testSetup().maxNodeSize14().clock(clock).start();
        
        //System.out.println("---- DBTester.testSplit2 ----");
        
        time = 100;
        for (int i = 0; i < n; i++) {
            //db.setTime(time);   
            clock.setTime(time);
            db.execute(Trans.builder().put("k" + time, "v" + time).build());
            time += 10;
        }
        
        time = 100;
        for (int i = 0; i < n; i++) {
            value = DbUtil.get(db, 999, "k" + time);
            Assert.assertArrayEquals("i=" + i + ", time=" + time, 
                    Util.toBytes("v" + time), value);
            time += 10;
        }
    }
    
    private static String getKey(int i) {
        String key = "" + i;
        if (i < 10) {
            key = "0" + key;
        }
        return key;
    }
    
    @T
    public static void testSpaceSplit1() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().maxNodeSize8().clock(clock).start();
        
        Trans t;
        for (int i = 100; i < 105; i++) {
            clock.setTime(i);
            t = Trans.builder().put("admin-accounts-" + i, "v" + i).build();
            db.execute(t);
        }
        
        //System.out.println("---- DBTester.testSpaceSplit1 ----");
        //System.out.println(db.findRoot(Long.MAX_VALUE).printTree());
        
        Assert.assertArrayEquals("i=100", Util.toBytes("v100"), 
                DbUtil.get(db, 101, "admin-accounts-100"));
        
        Assert.assertArrayEquals("i=100", Util.toBytes("v100"), 
                DbUtil.get(db, 103, "admin-accounts-100"));
        
        Assert.assertArrayEquals("i=100", Util.toBytes("v100"), 
                DbUtil.get(db, 104, "admin-accounts-100"));
        
        Assert.assertArrayEquals("i=100", Util.toBytes("v100"), 
                DbUtil.get(db, 199, "admin-accounts-100"));
        
        for (int i = 100; i < 105; i++) {
            Assert.assertArrayEquals("i=" + i, Util.toBytes("v" + i), 
                    DbUtil.get(db, 199, "admin-accounts-" + i));
        }
    }
    
    @T
    public static void testSplitInSingleTransaction() {
        int n = 10;
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().maxNodeSize14().clock(clock).start();
        
        clock.setTime(10);
        Trans.Builder b = Trans.builder();
        for (int i = 0; i < n; i++) {
            b.put("admin-accounts-" + getKey(i), "v" + i);
        }
        db.execute(b);
        
        for (int i = 0; i < n; i++) {
            Assert.assertArrayEquals("i=" + i, Util.toBytes("v" + i), 
                    DbUtil.get(db, 20, "admin-accounts-" + getKey(i)));
        }
    }
    
    @T
    public static void testSplitTwoSplitsInOneTransaction() {
        int n = 15;
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().maxNodeSize14().clock(clock).start();
        
        clock.setTime(10);
        Trans.Builder b = Trans.builder();
        for (int i = 0; i < n; i++) {
            b.put("admin-accounts-" + getKey(i), "v" + i);
        }
        Trans t = b.build();
        db.execute(t);
       
        //System.out.println("---- DBTester.testSplitTwoSplitsInOneTransaction ----");
        //System.out.println(db.printGraph());
        
        for (int i = 0; i < n; i++) {
            Assert.assertArrayEquals("i=" + i, Util.toBytes("v" + i), 
                    DbUtil.get(db, Long.MAX_VALUE, "admin-accounts-" + getKey(i)));
        }
    }
    
    @T
    public static void testSpaceSplitAddBackwards() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().maxNodeSize8().clock(clock).start();
        int max = 10;
        
        clock.setTime(10);
        Trans.Builder b = Trans.builder();
        for (int i = max; i >= 0; i--) {
            b.put("admin-accounts-" + getKey(i), "v" + i);
        }
        Trans t = b.build();
        db.execute(t);
        
        //System.out.println("---- DBTester.testSpaceSplitAddBackwards ----");
        //System.out.println(db.findRoot(20).printTree());
       
        for (int i = 0; i <= max; i++) {
            Assert.assertArrayEquals("i=" + i, Util.toBytes("v" + i), 
                    DbUtil.get(db, 20, "admin-accounts-" + getKey(i)));
        }
    }
    
    @T
    public static void testSpaceSplitOfRoot() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().maxNodeSize8().clock(clock).start();
        
        int max = 10;
        
        clock.setTime(10);
        Trans.Builder b = Trans.builder();
        for (int i = max; i >= 0; i--) {
            b.put("k-" + getKey(i), "v" + i);
        }
        Trans t = b.build();
        db.execute(t);
        
        //System.out.println("---- DBTester.testSpaceSplitOfRoot ----");
        //System.out.println("transactionTime = " + t.transactionTime);
        //System.out.println(db.findRoot(Long.MAX_VALUE).printTree());
        
        for (int i = 0; i <= max; i++) {
            Assert.assertArrayEquals("i=" + i, Util.toBytes("v" + i), 
                    DbUtil.get(db, 999, "k-" + getKey(i)));
        }
    }
    
    @T
    public static void testTimeSplitOfRoot() {
        int n = 20;
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        for (int i = 1; i <= n; i++) {
            String key = getKey(i);
            clock.setTime(i * 10);
            db.execute(Trans.builder().put(key, "v" + key).build());
            
            byte[] v = DbUtil.get(db, 9999, key);
            Assert.assertArrayEquals(Util.toBytes("v" + key), v);
        }
        
        //System.out.println("---- DBTester.testTimeSplitOfRoot ----");
        //System.out.println(db.printSkipList());
        //System.out.println(db.printTree());
        
        Assert.assertEquals(true, db.getSuperRoot().rootTime != 0);
        
        for (int i = 1; i <= n; i++) {
            Assert.assertArrayEquals("i=" + i, Util.toBytes("v" + getKey(i)), 
                    DbUtil.get(db, n * 10 + 10, getKey(i)));
        }
    }
    
    @T
    public static void testManyKeysInOneTransaction() {
        //TestClock clock = new TestClock();
        Db db = Db.builder().testSetup().start();
        Trans.Builder b = Trans.builder();
        for (int i = 0; i < 15; i++) {
            b.put("admin-account-" + i, "v" + i);
        }
        db.execute(b.build());
        
        //System.out.println("---- DBTester.testManyKeysInOneTransaction ----");
        //System.out.println(db.printTree());
        Assert.assertArrayEquals(Util.toBytes("v5"), DbUtil.get(db, Long.MAX_VALUE, "admin-account-5"));
        Assert.assertArrayEquals(Util.toBytes("v14"), DbUtil.get(db, Long.MAX_VALUE, "admin-account-14"));
        Assert.assertArrayEquals(Util.toBytes("v0"), DbUtil.get(db, Long.MAX_VALUE, "admin-account-0"));
    }
    
    @T
    public static void testGet1() {
        Db db = Db.builder().testSetup().start();
        db.execute(Trans.builder().put("k", "v"));
        Assert.assertArrayEquals(Util.toBytes("v"), DbUtil.get(db, 999, "k"));
    }
    
    @T
    public static void testGet2() {
        Db db = Db.builder().testSetup().start();
        db.execute(Trans.builder().put("longerKey", "v"));
        Assert.assertArrayEquals(Util.toBytes("v"), DbUtil.get(db, 999, "longerKey"));
    }
    
    @T
    public static void testGetWithLongerKey() {
        String longerKey = "anotherKeyThatIsLongerThanThePreviousAndIndeedVeryLong";
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(2);
        db.execute(Trans.builder()
                .put(longerKey, "v2")
                .build());
        
        Assert.assertArrayEquals(Util.toBytes("v2"), DbUtil.get(db, 99, longerKey));
    }
    
    @T
    public static void testGetWithLongAndShortKeys() {
        //
        // Tests with two keys, k1, k2. k1 has two segments and k2 has one and
        // the order is: k1 < k2.
        //
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().start();
        //db.setTime(10);
        clock.setTime(10);
        db.execute(Trans.builder()
                .put("myLongerKey", "v1")
                .put("nash", "v2")
                .build());
        
        //System.out.println("---- DBTester.testLongAndShortKeys ----");
        //System.out.println(db.findRoot(db.getTime()).printTree());
        
        Assert.assertArrayEquals(Util.toBytes("v1"), DbUtil.get(db, 20, "myLongerKey"));
        Assert.assertArrayEquals(Util.toBytes("v2"), DbUtil.get(db, 20, "nash"));
        Assert.assertNull(DbUtil.get(db, 20, "myLongerX"));
        Assert.assertNull(DbUtil.get(db, 20, "anotherX"));
        Assert.assertNull(DbUtil.get(db, 20, "nas"));
        Assert.assertNull(DbUtil.get(db, 20, "nasher"));
    }
    
    @T
    public static void testGetBeforeFirstSet() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(Trans.builder().put("first", "f").build());
        
        Assert.assertArrayEquals(Util.toBytes("f"), DbUtil.get(db, 99, "first"));
        Assert.assertNull(DbUtil.get(db, 5, "first"));
    }
    
    private static Db createRandomDB(int n, AppendOnlyStream stream) {
        Random random = new Random(1);
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().mainStream(stream).clock(clock).start();
        GetData getData = db.newGetData();
        
        for (int i = 0; i < n; i++) {
            getData = db.newGetData();
            String key = "" + random.nextInt();
            Trans t = Trans.builder().put(key, "v" + key).build();
            clock.setTime(i * 10 + 10);
            db.execute(t);
            
            byte[] value = db.getOne(Long.MAX_VALUE, Keys.toSegments(key), getData);
            Assert.assertEquals("i=" + i, "v" + key, Util.toString(value));
        }
        return db;
    }
    
    @T
    public static void testWithRandomData() {
        createRandomDB(25, new MemoryStream());
    }
    
    @T("f")     // Too slow to be "unit"
    public static void testWithMoreRandomData() {
        createRandomDB(1000, new MemoryStream());
    }
    
    @T
    public static void testConfigTestClock() {
        Db db = Db.builder().testClock().stream("main", new MemoryStream()).start();
        db.execute(Trans.builder().put("k", "v").build());
    }
    
    @T
    public static void testSplit3() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().maxNodeSize14().clock(clock).start();
        
        clock.setTime(100);
        Trans.Builder b = Trans.builder();
        for (long i = 100; i < 113; i++) {
            b.put("four" + i + "end", "" + i);
        }
        db.execute(b.build());
        
        //System.out.println("---- DBTester.testSplit3 ----");
        //db.printGraph(System.out);
        db.checkNodes();
        
        clock.setTime(110);
        b = Trans.builder();
        for (long i = 100; i < 111; i++) {
            b.put("four110-" + i, "v-four110-" + i);
        }
        db.execute(b.build());
        
        //System.out.println("---- DBTester.testSplit3 ----");
        //db.printGraph(System.out);
        
        clock.setTime(120);
        db.execute(Trans.builder().put("four110-111", "v-four110-111"));
        
        //System.out.println("-- After adding four110-111 --");
        //db.printGraph(System.out);
        
        // Checking result
        
        byte[] value;
        
        for (long i = 100; i < 113; i++) {
            GetData gd = db.newGetData();
            value = db.getOne(Long.MAX_VALUE, Keys.toSegments("four" + i + "end"), gd);
            Assert.assertEquals("i=" + i, "" + i, Util.toString(value));
        }
        
        for (long i = 100; i < 111; i++) {
            value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("four110-" + i));
            Assert.assertEquals("i=" + i, "v-four110-" + i, Util.toString(value));
        }
        
        db.checkNodes();
        
        value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("four110-111"));
        Assert.assertEquals("v-four110-111", Util.toString(value));
        
        value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("four110-111"));
        Assert.assertEquals("v-four110-111", Util.toString(value));
    }
    
    @T
    public static void testSpecialCase() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(Trans.builder()
                .put("r/directory1", "v1")
                .put("r/direc", "v2")
                .put("2/directory2", "v3")
                .put("r/direct", "v4"));
        
        Assert.assertEquals("v1", Util.toString(DbUtil.get(db, 999, "r/directory1")));
        Assert.assertEquals("v2", Util.toString(DbUtil.get(db, 999, "r/direc")));
        Assert.assertNull(DbUtil.get(db, 999, "2/direc"));
        Assert.assertEquals("v4", Util.toString(DbUtil.get(db, 999, "r/direct")));
    }
    
    @T
    public static void testPrintGraph1() {
        // Test for manual inspection.
        
        Db db = Db.builder().testSetup().start();
        db.execute(Trans.builder()
                .put("r/directory1", "v1")
                .put("r/direc", "v2")
                .put("2/directory2", "v3")
                .put("r/direct", "v4"));
        
        //System.out.println("---- DBTester.testPrintGraph ----");
        //System.out.println(db.printGraph());
    }
    
    @T
    public static void testPrintGraph2() {
        // For manual inspection.
        
        Db db = Db.builder().testSetup().start();
        for (int i = 0; i < 9; i++) {
            db.execute(Trans.builder().put("k" + i, "v" + i));
        }
        
        //System.out.println("---- DBTester.testPrintGraph2 ----");
        //System.out.println(db.printGraph());
    }
    
    @T
    public static void testTwoBinaryKeysInOneTransaction() {
        //
        // Two kvs, one transaction, binary keys.
        //
        AppendOnlyStream s = new MemoryStream();
        Db db = Db.builder().testClock().mainStream(s).start();
        int n = 2;
        Trans.Builder b = Trans.builder();
         
        for (int j = 0; j < n; j++) {
            byte[] key = KeyFactory.binaryIntKeyLE(j);
            byte[] value = new byte[4];
            Bytes.intToBytesLE(j, value, 0);
            b.put(key, value);
        }
        
        db.execute(b);
        //System.out.println("db graph:\n" + db.printGraph());
        
        // Checks it
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.binaryIntKeyLE(i);
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
            Assert.assertTrue("i=" + i, value != null);
            Assert.assertEquals(4, value.length);
            int valueInt = Bytes.bytesToIntLE(value, 0);
            Assert.assertEquals(i, valueInt);
        }
    }
    
    @T
    public static void testManyOverwrites() {
        Db db = Db.builder().testSetup().start();
        
        //System.out.println("---- DBTester.testManyOverwrites ----");
        for (int i = 0; i < 40; i++) {
            //System.out.println("i = " + i);
            
            //if (i == 29 || i == 30) {
            //    System.out.println("======== db.printGraph(), i = " + i + " ========");
            //    db.printGraph(System.out);
            //    System.out.println();
            //}
            
            Trans trans = Trans.builder().put("key", "version " + i).build();
            db.execute(trans);
        }
        
        Assert.assertEquals("version 39", Util.toString(DbUtil.get(db, Long.MAX_VALUE, "key")));
    }
    
    /**
     * For the testCrazyKeys() test.
     */
    private static interface KeySource {
        byte[] getKey(int index);
    }
    
    @T
    public static void testCrazyKeys() {
        AppendOnlyStream s = new MemoryStream();
        KTestClock clock = new KTestClock();
        int n = 50;
        KeySource ks = new KeySource() {
            public byte[] getKey(int index) {
                return KeyFactory.crazyKey(index);
            }
        };
        
        Db db = Db.builder().clock(clock).mainStream(s).evictBoss(new NoEvictBoss()).start();
        
        // Creates some KVs, 0 - 999.
        
        for (int i = 0; i < n; i++) {
            clock.setTime(1*1000000 + i * 10);
            Trans t = Trans.builder().put(ks.getKey(i), Util.toBytes("v" + i)).build();
            db.execute(t);
        }
        
        // Checks keys 0 - 999.
        
        for (int i = 0; i < n; i++) {
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, ks.getKey(i));
            Assert.assertEquals("i=" + i, "v" + i, Util.toString(value));
        }
        
        // Removes some of the keys
        
        for (int i = 0; i < n; i += 10) {
            clock.setTime(2*1000000 + i * 10);
            Trans t = Trans.builder().delete(ks.getKey(i)).build();
            db.execute(t);
        }
        
        // Checks that they were removed and the rest of them are still present.
        
        //System.out.println("---- DBTester.testCrazyKeys ----");
        //System.out.println("Key 4: " + Util.toHexString(ks.getKey(4)));
        //db.printGraph(System.out);
        
        for (int i = 0; i < n; i++) {
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, ks.getKey(i));
            if (i % 10 == 0) {
                Assert.assertNull(value);
            } else {
                Assert.assertEquals("i=" + i, "v" + i, Util.toString(value));
            }
        }
        
        // Checks that they existed before they were removed.
        
        for (int i = 0; i < n; i++) {
            byte[] value = DbUtil.get(db, 2*1000000-1, ks.getKey(i));
            Assert.assertEquals("Get at 2*1000000-1, i=" + i, "v" + i, Util.toString(value));
        }
    }
    
    @T
    public static void testSettingValueManyTimes() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        int n = 20;
        String key = "directory/myFile";     // 3 klongs long (2x7 + 2)
        byte[] keyBytes = Keys.toBytes(key);
        
        for (int i = 0; i < n; i++) {
            clock.setTime(i * 10 + 1);
            db.execute(Trans.builder().put(key, "v-" + i));
        }
        
        //System.out.println("---- DBTester.testSettingValueManyTimes ----");
        //db.printGraph(System.out);
        
        for (int i = 0; i < n; i++) {
            long time = i * 10 + 5;
            byte[] value = DbUtil.get(db, time, keyBytes);
            Assert.assertEquals("i=" + i, "v-" + i, Util.toString(value));
        }
    }
    
    @T
    public static void tGetFirst1() {
        // Tests get first with simple db. Multiple times.
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().put("bert", "v1"));
        clock.setTime(20);
        db.execute(Trans.builder().put("anna", "v2"));
        
        GetData gd = db.newGetData();
        
        byte[] key = DbUtil.getFirstKey(db, 5, gd);
        Assert.assertEquals(null, key);
        
        key = DbUtil.getFirstKey(db, 15, gd);
        Assert.assertArrayEquals(Keys.toBytes("bert"), key);
        
        key = DbUtil.getFirstKey(db, 25, gd);
        Assert.assertArrayEquals(Keys.toBytes("anna"), key);
    }
    
    @T
    public static void tGetFirst2() {
        // Similar to tGetFirst1, but with longer, multi-segment keys.
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().put("employees/bertilsson", "v1"));
        clock.setTime(20);
        db.execute(Trans.builder().put("employees/annasson", "v2"));
        clock.setTime(30);
        db.execute(Trans.builder().put("a", "v3"));
        
        GetData gd = db.newGetData();
        
        byte[] key = DbUtil.getFirstKey(db, 5, gd);
        Assert.assertEquals(null, key);
        
        key = DbUtil.getFirstKey(db, 15, gd);
        Assert.assertEquals("employees/bertilsson", Keys.toString(key));
        
        key = DbUtil.getFirstKey(db, 25, gd);
        Assert.assertEquals("employees/annasson", Keys.toString(key));
        
        key = DbUtil.getFirstKey(db, 35, gd);
        Assert.assertEquals("a", Keys.toString(key));
    }
    
    /**
     * Creates and starts test DB based on the provided stream. Small bufferSize and bufferTime.
     */
    private static Db testDB(AppendOnlyStream stream) {
        Db.Builder b = Db.builder();
        b.testClock();
        b.evictBoss(new NoEvictBoss());
        b.retainForever();
        b.id(DatabaseId.getTestId());
        b.stream("main", stream, 10*1000, 10);
        return b.start();
    }
    
    @T
    public static void testCrash1() {
        //
        // Truncate from end, one transaction in addition to the primordial one.
        //
        MemoryStream mstream = new MemoryStream();
        Db db = testDB(mstream);
        
        long size1 = mstream.getLength();
        Trans trans = Trans.builder().put("key", "value").build();
        db.execute(trans);
        db.sync();
        db.stop();
        long size2 = mstream.getLength();
        long diff = size2 - size1;
        
        Assert.assertTrue(diff > 10);
        mstream.truncate(size2 - 10);
        
        Assert.assertEquals(size2 - 10, mstream.getLength());
        Db db2 = testDB(mstream);
        byte[] value = DbUtil.get(db2, Keys.toBytes("key"));
        Assert.assertTrue(value == null);
        db2.stop();
    }
    
    @T
    public static void testCrash2() {
        //
        // Truncate from end, two transactions, one should still work when database restarted.
        //
        MemoryStream mstream = new MemoryStream();
        Db db = testDB(mstream);
        
        Trans trans = Trans.builder().put("key", "the-first-value").build();
        db.execute(trans);
        db.syncStrong(trans.lastSpos);
        long size1 = mstream.getLength();
        
        trans = Trans.builder().put("key", "the-second-value").build();
        db.execute(trans);
        db.syncStrong(trans.lastSpos);
        long size2 = mstream.getLength();
        Assert.assertEquals("the-second-value", DbUtil.getString(db, "key"));
        db.stop();
        
        // Restart, no crash
        Db db2 = testDB(mstream);
        Assert.assertEquals("the-second-value", DbUtil.getString(db2, "key"));
        db2.stop();
        
        // Restart, truncate 10 bytes (last transaction)
        mstream.truncate(size2 - 10);
        Db db3 = testDB(mstream);
        Assert.assertEquals("the-first-value", DbUtil.getString(db3, "key"));
        db3.stop();
        
        // Restart, truncate first transaction.
        mstream.truncate(size1 - 10);
        Db db4 = testDB(mstream);
        Assert.assertNull(DbUtil.getString(db4, "key"));
        db4.stop();
    }
    
    @T
    public static void testCrash3() {
        //
        // Truncates complicated stream a few times.
        //
        MemoryStream mstream = new MemoryStream();
        Db db = testDB(mstream);
        
        long size1 = mstream.getLength();
        db.execute(Trans.builder().put("key", "value1").build());
        db.execute(Trans.builder().put("a-significantly-longer-key", "value2").build());
        Trans trans = Trans.builder().put("another-key-that-is-longer-than-most", "value3").build();
        db.execute(trans);
        db.syncStrong(trans.lastSpos);
        db.stop();
        db = null;
        
        long size2 = mstream.getLength();
        long diff = size2 - size1;
        
        int stepSize = (int) (diff / 10);
        
        for (int i = 1; i <= diff; i+= stepSize) {
            long newSize = size2 - i;

            MemoryStream mstream2 = mstream.copy();
            mstream2.truncate(newSize);
 
            Db db2 = testDB(mstream);
            byte[] value = DbUtil.get(db2, Util.toBytes("non-existing-key"));
            Assert.assertTrue(value == null);
            db2.stop();
        }
    }
    
    @T("f")   // Too slow to be "unit" test.
    public static void testCrash4MetaBlock() {
        //
        // Truncates stream in the middle of 2nd meta block.
        //
        MemoryStream mstream = new MemoryStream();
        Db db = testDB(mstream);
        final int blockDist = RecoverableStream.META_BLOCK_DISTANCE;
        
        db.execute(Trans.builder().put("key1", "value1"));
        
        byte[] v2 = new byte[blockDist];
        v2[0] = 2;
        
        Trans trans = Trans.builder().put("key2", v2).build();
        db.execute(trans);
        db.syncStrong(trans.lastSpos);
        db.stop();
        db = null;
        
        mstream.truncate(blockDist + RecoverableStream.META_BLOCK_SIZE / 2);
        
        Db db2 = testDB(mstream);
        String v1 = DbUtil.getString(db2, "key1");
        byte[] v2b = DbUtil.get(db2, "key2");
        
        Assert.assertEquals("value1", v1);
        Assert.assertTrue(v2b == null);
        
        db2.stop();
    }
    
    @T
    public static void testCrash5InTransSize() {
        //
        // Truncates stream in the middle of the size (4 first bytes) of a transaction.
        //
        MemoryStream mstream = new MemoryStream();
        Db db = testDB(mstream);
        Trans trans = Trans.builder().put("key1", "value1").build();
        db.execute(trans);
        db.syncStrong(trans.lastSpos);
        long size1 = mstream.getLength();
        
        trans = Trans.builder().put("key2", "value2").build();
        db.execute(trans);
        db.syncStrong(trans.lastSpos);
        
        Assert.assertTrue(mstream.getLength() >= trans.lastSpos);
        mstream.truncate(size1 + 3);
        Assert.assertEquals(size1 + 3, mstream.getLength());
        
        db.stop();
        db = null;
        
        Db db2 = testDB(mstream);
        
        String v1 = DbUtil.getString(db2, "key1");
        String v2 = DbUtil.getString(db2, "key2");
        Assert.assertEquals("value1", v1);
        Assert.assertTrue(v2 == null);
        
        db2.stop();
    }
    
    @T
    public static void testKeyTransformation1() {
        KeyTransformation kt = new KeyTransformation() {
            public void transform(Trans trans, int index) {
                long[] key = trans.kvs[index].keySegments;
                String keyString = Keys.toString(key);
                keyString = keyString.replace("<transactionTime>", "" + trans.transactionTime);
                long[] newKey = Keys.toSegments(keyString);
                trans.kvs[index].keySegments = newKey;
                trans.writeKeyHashes[index] = Keys.hash(newKey);
            }
        };
        
        Db db = Db.builder().testSetup().start();
        Trans t = Trans.builder()
                .put(Keys.toSegments("test/<transactionTime>"), kt, new byte[0], null)
                .build();
        db.execute(t);
        
        String s = Keys.toString(t.kvs[0].keySegments);
        Assert.assertFalse(s.contains("transactionTime"));
        long transactionTime1 = Long.parseLong(s.substring("test/".length()));
        Assert.assertTrue(transactionTime1 >= 0);
    }
    
    @T
    public static void testKeyTransformation2() {
        KeyTransformation kt = new KeyTransformation() {
            public void transform(Trans trans, int index) {
                long[] key = trans.kvs[index].keySegments;
                String keyString = Keys.toString(key);
                keyString = keyString.replace("<transactionTime>", "" + trans.transactionTime);
                long[] newKey = Keys.toSegments(keyString);
                trans.kvs[index].keySegments = newKey;
                trans.writeKeyHashes[index] = Keys.hash(newKey);
            }
        };
        
        Db db = Db.builder().testSetup().start();
        Trans t = Trans.builder()
                .put(Keys.toSegments("test/<transactionTime>"), kt, new byte[0], null)
                .build();
        db.execute(t);
        
        String s = Keys.toString(t.kvs[0].keySegments);
        Assert.assertFalse(s.contains("transactionTime"));
        long transactionTime1 = Long.parseLong(s.substring("test/".length()));
        
        t = Trans.builder()
                .put(Keys.toSegments("test/<transactionTime>"), kt, new byte[0], null)
                .build();
        db.execute(t);
        
        s = Keys.toString(t.kvs[0].keySegments);
        Assert.assertFalse(s.contains("transactionTime"));
        long transactionTime2 = Long.parseLong(s.substring("test/".length()));
        
        Assert.assertTrue(transactionTime2 > transactionTime1);
        
        // Getting KVs from database
        
        GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments("test/");
        g.stopCondition = new GetMany.Endpoint(Keys.toSegments("test0"));   
                // '0' == '/' + 1
        db.getMany(g);
        
        Assert.assertEquals(2, g.result.size());
        
        s = Keys.toString(g.result.get(0).key);
        Assert.assertFalse(s.contains("transactionTime"));
        transactionTime1 = Long.parseLong(s.substring("test/".length()));
        
        s = Keys.toString(g.result.get(1).key);
        Assert.assertFalse(s.contains("transactionTime"));
        transactionTime2 = Long.parseLong(s.substring("test/".length()));
        
        Assert.assertTrue(transactionTime2 > transactionTime1);
    }
    
    @T
    public static void testValueTransformation1() {
        // Uses transactionTime to compute value.
        
        ValueTransformation vt = new ValueTransformation() {
            public byte[] transform(long transactionTime, byte[] inputValue, byte[] previous) {
                String s = "tt" + transactionTime;
                return Util.toBytes(s);
            }
        };
        
        TestClock clock = new TestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(100);
        Trans t = Trans.builder()
                .put(Keys.toSegments("t/1.s"), null, new byte[0], vt)
                .build();
        db.execute(t);
        
        GetData g = db.newGetData();
        byte[] value = db.getOne(200, Keys.toSegments("t/1.s"), g);
        Assert.assertTrue(value != null);
        String s = Util.toString(value);
        Assert.assertTrue(s.startsWith("tt"));
        long time = Long.parseLong(s.substring("tt".length()));
        Assert.assertTrue(time == 100 || time == 101);
    }
    
    @T
    public static void testValueTransformation2() {
        // Uses previous value to do an atomic increment of a long (big-ending first).
        
        ValueTransformation vt = new ValueTransformation() {
            public byte[] transform(long transactionTime, byte[] inputValue, byte[] previous) {
                long previousValue = 0;
                if (previous != null && previous.length == 8) {
                    previousValue = Bytes.bytesToLongBE(previous, 0);
                }
                previousValue += 10;
                byte[] result = new byte[8];
                Bytes.longToBytesBE(previousValue, result, 0);
                return result;
            }
        };
        
        Db db = Db.builder().testSetup().start();
        
        Trans t = Trans.builder()
                .put(Keys.toSegments("a"), null, new byte[0], vt)
                .build();
        db.execute(t);
        
        GetData g = db.newGetData();
        byte[] value = db.getOne(200, Keys.toSegments("a"), g);
        Assert.assertTrue(value != null);
        Assert.assertEquals(8, value.length);
        Assert.assertEquals(10, Bytes.bytesToLongBE(value, 0));
        
        t = Trans.builder()
                .put(Keys.toSegments("a"), null, new byte[0], vt)
                .build();
        db.execute(t);
        
        g = db.newGetData();
        value = db.getOne(200, Keys.toSegments("a"), g);
        Assert.assertTrue(value != null);
        Assert.assertEquals(8, value.length);
        Assert.assertEquals(20, Bytes.bytesToLongBE(value, 0));
        db.stop();
    }
    
    @T
    public static void testStop1() {
        Db db = Db.builder().testSetup().start();
        db.stop();
    }
    
    @T
    public static void testStopGetException1() {
        Db db = Db.builder().testSetup().start();
        db.stop();
        IllegalDbStateException exception = null;
        GetData g = db.newGetData();
        
        try {
            db.getOne(200, Keys.toSegments("a"), g);
        } catch (IllegalDbStateException e) {
            exception = e;
        }
        
        Assert.assertTrue(exception != null);
    }
    
    @T
    public static void testStopGetException2() {
        Db db = Db.builder().testSetup().start();
        db.stop();
        IllegalDbStateException exception = null;
        GetMany d = db.newGetMany();
        
        try {
            db.getMany(d);
        } catch (IllegalDbStateException e) {
            exception = e;
        }
        
        Assert.assertTrue(exception != null);
    }
    
    @T
    public static void testStopExecute() {
        Db db = Db.builder().testSetup().start();
        db.stop();
        IllegalDbStateException exception = null;
        
        try {
            db.execute(Trans.builder().put("k", "v").build());
        } catch (IllegalDbStateException e) {
            exception = e;
        }
        
        Assert.assertTrue(exception != null);
    }
    
    @T
    public static void testStopMultipleStopCalls() {
        Db db = Db.builder().testSetup().start();
        db.stop();
        db.close();
        db.stop();
        db.stop();
    }
    
    @T
    public static void testFinalize1() {
        Db.builder().testSetup().start();
    }
    
    @T
    public static void testFinalize2() {
        Db.builder().testSetup().start();
    }
    
    @T
    public static void testFinalize3() {
        Db.builder().testSetup().start();
    }
    
    @T
    public static void testBadReplica1() throws IOException {
        MemoryStream m0 = new MemoryStream();
        MemoryStream m1 = new MemoryStream();
        
        Db db = Db.builder().stream("m0", m0).start();
        db.execute(Trans.builder().put("a.txt", "v1").build());
        db.sync();
        
        db = Db.builder().stream("m1", m1).start();
        db.execute(Trans.builder().put("b.txt", "v2-b").build());
        
        BadReplicaException ex = null;
        try {
            db.addReplica("m0", m0, 10*1000, 10);
        } catch (BadReplicaException e) {
            ex = e;
        }
        db.stop();
        
        Assert.assertTrue(ex != null);
    }
    
    @T
    public static void bug130403() {
        // Bug found 130403 when working with bergdb.test.StreamSize.
        // The following code reproduced the error (before bug was fixed).
        
        MemoryStream m = new MemoryStream();
        Db db = Db.builder().maxNodeSize62().mainStream(m).start();
        
        byte[] value = new byte[0];
        int n = 100;
        
        for (int i = 0; i < n; i++) {
            Trans trans = Trans.builder().put("" + i, value).build();
            db.execute(trans);
        }
        db.stop();
    }
    
    @T
    public static void testStartupDistance1() {
        // Checks that startupDistance from Db.Builder is used.
        
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().mainStream(stream).startupDistance(523456).build();
        
        Assert.assertEquals(523456, db.getStartupDistance());
        db.start();
        Assert.assertEquals(523456, db.getStartupDistance());
        db.stop();
    }
    
    @T
    public static void testStartupDistance2() {
        // A decreased of startup distance is seen immediately by DB.getStartupDistance().
        
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().mainStream(stream).startupDistance(2*1000000).build();
        
        Assert.assertEquals(2*1000000, db.getStartupDistance());
        db.start();
        
        db.execute(Trans.builder().put("key", "value").build());
        db.setStartupDistance(1*1000000);
        Assert.assertEquals(1*1000000, db.getStartupDistance());
        
        db.stop();
    }
}
