package bergdb.core;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Random;
import java.util.Set;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import static bergdb.nanotest.Assert.*;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * Class for general unit testing of Db.
 * 
 * @author Frans Lundberg
 */
public class DbTester {
    
    @Nano
    public static void test0() {
        Db db = Db.builder().testSetup().start();
        db.stop();
    }
    
    @Nano
    public static void test1() {
        Db db = Db.builder().testSetup().start();
        byte[] value = DbUtil.get(db, 99, StringUtil.toBytes("admin1"));
        Assert.assertNull(value);
        db.close();
    }
    
    @Nano
    public static void test2() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("admin1", "F").build());
        byte[] value = DbUtil.get(db, 99, Keys.toBytes("admin1"));
        Assert.assertArrayEquals(StringUtil.toBytes("F"), value);
        db.close();
    }
    
    @Nano
    public static void test3() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("admin1", "F1")
                .put("admin2", "F2").build());
        
        byte[] value = DbUtil.get(db, 99, Keys.toBytes("admin1"));
        Assert.assertArrayEquals(StringUtil.toBytes("F1"), value);
        value = DbUtil.get(db, 99, Keys.toBytes("admin2"));
        Assert.assertArrayEquals(StringUtil.toBytes("F2"), value);
        db.close();
    }
    
    @Nano
    public static void test4() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        //db.setTime(100);
        clock.setTime(100);
        db.execute(db.trans().put("admin1", "F1").build());
        //db.setTime(200);
        clock.setTime(200);
        db.execute(db.trans().put("admin2", "F2").build());
        
        byte[] value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("admin1"));
        Assert.assertArrayEquals(StringUtil.toBytes("F1"), value);
        value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("admin2"));
        Assert.assertArrayEquals(StringUtil.toBytes("F2"), value);
        db.close();
    }

    @Nano
    public static void testT2() {
        byte[] value;
        CoreTestClock clock = new CoreTestClock();
        Db db = createT2DB(clock);
        
        value = DbUtil.get(db, 999, "apa");
        Assert.assertArrayEquals(StringUtil.toBytes("P1"), value);

        value = DbUtil.get(db, 999, "ap");
        Assert.assertArrayEquals(StringUtil.toBytes("P0"), value);

        value = DbUtil.get(db, 999, "md");
        Assert.assertArrayEquals(StringUtil.toBytes("P7"), value);
        db.close();
    }
    
    private static Db createT2DB(Clock clock) {
        Db db = Db.builder().testSetup().clock(clock).start();
        String[] keys = new String[] { "ap", "apa", "d", "g", "kr", "kram",
                "mage", "md" };
        
        Trans.Builder b = db.trans();
        for (int i = 0; i < keys.length; i++) {
            b.put(keys[i], "P" + i);
        }
        db.execute(b.build());
        return db;
    }
    
    @Nano
    public static void testVersions() {
        //
        // Adds new value in a new key.
        //

        CoreTestClock clock = new CoreTestClock();
        Db db = createT2DB(clock);
        Trans t;
        
        clock.setTime(20);
        
        t = db.trans().put("e", "e-value").build();
        db.execute(t);

        Assert.assertEquals(true, t.tt >= 20);
        Assert.assertArrayEquals(StringUtil.toBytes("e-value"), DbUtil.get(db, 999, "e"));

        byte[] value = DbUtil.get(db, 10, "e");
        Assert.assertNull(value);
        db.close();
    }
    
    @Nano
    public static void testVersionsReplaceValue() {
        CoreTestClock clock = new CoreTestClock();
        Db db = createT2DB(clock);
        clock.setTime(20);
        db.execute(db.trans().put("apa", "A").build());

        Assert.assertArrayEquals(StringUtil.toBytes("A"), DbUtil.get(db, 30, "apa"));
        Assert.assertArrayEquals(StringUtil.toBytes("A"), DbUtil.get(db, 999, "apa"));
        db.close();
    }
    
    @Nano
    public static void testLongKey() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("myLongerKey", "v1").build());
        
        //System.out.println("---- DBTester.testLongKey ----");
        //System.out.println(db.findRoot(db.getTime()).printTree());
        
        Assert.assertNull(DbUtil.get(db, 99, StringUtil.toBytes("rKey")));
        Assert.assertArrayEquals(StringUtil.toBytes("v1"), DbUtil.get(db, 99, "myLongerKey"));
        db.close();
    }
    
    @Nano
    public static void testLongerKey() {
        String longerKey = "anotherKeyThatIsLongerThanThePreviousAndIndeedVeryLong";
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put(longerKey, "v2")
                .build());
        
        Assert.assertArrayEquals(StringUtil.toBytes("v2"),
                DbUtil.get(db, 99, longerKey));
        db.close();
    }
    
    @Nano
    public static void testMultipleLongKeys() {
        String longerKey = "anotherKeyThatIsLongerThanThePreviousAndIndeedVeryLong";
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put(longerKey, "v2")
                .put("myLongerKey", "v1")
                .build());
        
        Assert.assertArrayEquals(StringUtil.toBytes("v2"), DbUtil.get(db, 99, longerKey));
        Assert.assertArrayEquals(StringUtil.toBytes("v1"), DbUtil.get(db, 99, "myLongerKey"));
        Assert.assertNull(DbUtil.get(db, 99, StringUtil.toBytes("myLongerX")));
        db.close();
    }
    
    @Nano
    public static void testLongAndShortKeys() {
        //
        // Tests with two keys, k1, k2. k1 has two segments and k2 has one and
        // the order is: k1 < k2.
        //
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put("myLongerKey", "v1")
                .put("nash", "v2")
                .build());
        
        //System.out.println("---- DBTester.testLongAndShortKeys ----");
        //System.out.println(db.findRoot(db.getTime()).printTree());
        
        Assert.assertArrayEquals(StringUtil.toBytes("v1"), DbUtil.get(db, 20, "myLongerKey"));
        Assert.assertArrayEquals(StringUtil.toBytes("v2"), DbUtil.get(db, 20, "nash"));
        Assert.assertNull(DbUtil.get(db, 20, "myLongerX"));
        Assert.assertNull(DbUtil.get(db, 20, "anotherX"));
        Assert.assertNull(DbUtil.get(db, 20, "nas"));
        Assert.assertNull(DbUtil.get(db, 20, "nasher"));
        db.close();
    }
    
    @Nano
    public static void testMultipleKeysWithSamePrefix() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put("myLongerKey1", "v1")
                .put("myLongerKey2", "v2")
                .build());
        
        //System.out.println("---- DBTester.testMultipleKeysWithSamePrefix ----");
        //System.out.println(db.findRoot(db.getTime()).printTree());
        
        Assert.assertArrayEquals(StringUtil.toBytes("v1"), DbUtil.get(db, 30, "myLongerKey1"));
        Assert.assertArrayEquals(StringUtil.toBytes("v2"), DbUtil.get(db, 30, "myLongerKey2"));
        Assert.assertNull(DbUtil.get(db, 30, StringUtil.toBytes("myLongerX")));
        Assert.assertNull(DbUtil.get(db, 30, StringUtil.toBytes("myLongerKey1b")));
        db.close();
    }
    
    @Nano
    public static void testDeleteTwoValues() {
        //
        // Delete of two values in same transaction.
        //
        
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        TopNode superRoot = db.internal().superRoot();
        
        db.execute(db.trans().put("a", "a-value").put("b", "b-value").build());
        
        //System.out.println("== DbTester.testDeleteTwoValues ==");
        //db.printGraph(System.out);
        
        db.execute(db.trans().delete("a").delete("b").build());
        
        //System.out.println("== DbTester.testDeleteTwoValues ==");
        //db.printGraph(System.out);
        
        assert superRoot == db.internal().superRoot() : superRoot + " != " + db.internal().superRoot();
        
        // Gets the KeyNode and examines the DELETE_BITMAP at the end.
        
        KeyNode k = (KeyNode) db.internal().findNode(new int[]{0}, db.newGetData());
        
        // The root's klongs: time, time, the startup distance's key (bergdb 028-15), time,
        // "a", "b", time, and the delete bitmap; until 028-15 the bitmap was klong 5.
        long klong = k.getKlong(7);
        Assert.assertEquals("check TYPE_DELETE_BITMAP", Klong.getType(klong), Klong.TYPE_DELETE_BITMAP);
        
        boolean[] expected = new boolean[]{false, false, false, false, true, true, false, false};
        for (int i = 0; i < expected.length; i++) {
            Assert.assertEquals(expected[i], Klong.isDeleted(klong, i));
        }
        
        db.stop();
    }
    
    @Nano
    public static void testDelete0() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("a", "a-value")
                .put("b", "b-value").build());
        
        clock.setTime(20);
        db.execute(db.trans().delete("a").build());
        
        byte[] value = DbUtil.get(db, 30, Keys.toBytes("a"));
        Assert.assertNull(value);
        
        value = DbUtil.get(db, 30, Keys.toBytes("b"));
        Assert.assertArrayEquals(StringUtil.toBytes("b-value"), value);

        value = DbUtil.get(db, 15, Keys.toBytes("a"));
        Assert.assertArrayEquals(StringUtil.toBytes("a-value"), value);
        
        db.stop();
    }
    
    @Nano
    public static void testDelete1() {
        // Tests rewriting a value and deleting it in-between.
        
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(db.trans().put("a", "a-value").put("b", "b-value"));
        
        clock.setTime(20);
        db.execute(db.trans().delete("a"));
        
        clock.setTime(30);
        db.execute(db.trans().put("a", "a-value-2"));
        
        clock.setTime(40);
        db.execute(db.trans().delete("a"));
        
        clock.setTime(50);
        db.execute(db.trans().put("a", "a-value-3"));
        
        byte[] value;
        value = DbUtil.get(db, Long.MAX_VALUE, "a");
        Assert.assertArrayEquals(StringUtil.toBytes("a-value-3"), value);
        
        value = DbUtil.get(db, 5, "a");
        Assert.assertNull(value);
        
        value = DbUtil.get(db, 15, "a");
        Assert.assertEquals("a-value", StringUtil.toString(value));
        
        value = DbUtil.get(db, 25, "a");
        Assert.assertNull(value);
        
        value = DbUtil.get(db, 35, "a");
        Assert.assertEquals("a-value-2", StringUtil.toString(value));
        
        value = DbUtil.get(db, 45, "a");
        Assert.assertNull(value);
        
        value = DbUtil.get(db, 55, "a");
        Assert.assertEquals("a-value-3", StringUtil.toString(value));
        db.close();
    }
    
    @Nano
    public static void testDeleteOfNonExistingData0() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().delete("a").build());   // This is a noop transaction.
        byte[] value = DbUtil.get(db, Long.MAX_VALUE, "a");
        Assert.assertNull(value);
        db.close();
    }
    
    @Nano
    public static void testDeleteOfNonExistingData1() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("a", "a-value").put("b", "b-value").build());
        clock.setTime(20);
        db.execute(db.trans().delete("c").build());
        db.execute(db.trans().delete("anton").build());
        db.execute(db.trans().delete("anton-and-all-his-friends").build());
        
        byte[] value = DbUtil.get(db, Long.MAX_VALUE, "a");
        Assert.assertArrayEquals(StringUtil.toBytes("a-value"), value);
        
        value = DbUtil.get(db, Long.MAX_VALUE, "b");
        Assert.assertArrayEquals(StringUtil.toBytes("b-value"), value);

        db.execute(db.trans().delete("a").build());
        db.execute(db.trans().delete("a").build());
        db.execute(db.trans().delete("a").build());
        
        value = DbUtil.get(db, Long.MAX_VALUE, "a");
        Assert.assertNull(value);
        db.close();
    }
    
    @Nano
    public static void testRerun() throws NumberFormatException, UnsupportedEncodingException {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        
        Trans t = db.trans()
                .put("acc1", "200")
                .put("acc2", "100").build();
        db.execute(t);   // executes at t = 11.
        
        clock.setTime(20);
        db.execute(db.trans().put("acc1", "50").build());    // executes at t=21
        
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
        
        t = db.trans()
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
        
        t = db.trans()
                .lookupTime(21)
                .keyRead("acc1")
                .keyRead("acc2")
                .put("acc1", "" + amountAfter1)
                .put("acc2", "" + amountAfter2)
                .build();
        
        db.execute(t);
        db.close();
    }
    
    @Nano
    public static void testSame7BytesPrefix() {
        Db db = Db.builder().testSetup().start();
        Trans t = db.trans()
                .put("account1", "1")
                .put("account2", "2").build();
        db.execute(t);
        db.close();
    }
    
    @Nano
    public static void testGetSmallerKey() {
        //
        // Smaller key then previous added. More than one segment.
        //
        
        Db db = Db.builder().testSetup().start();
        
        //db.setTime(1);
        db.execute(db.trans()
                .put("account1", "1").build());
        
        byte[] value = DbUtil.get(db, 20, StringUtil.toBytes("account0"));
        Assert.assertNull(value);
        db.close();
    }
    
    @Nano
    public static void testSplit0() {
        // Time split with an ordinary KeyNode as parent.
        
        Db db;
        AppendOnlyStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        db = Db.builder().testSetup().maxNodeSize14().mainStream(stream).clock(clock).start();

        for (int i = 0; i < 10; i++) {
            String keyString = "account-id-" + i;
            clock.setTime(1 + i);
            db.execute(db.trans().put(keyString, "v" + i));
        }
        
        //System.out.println("---- DBTester.testSplit1 ----");
        //System.out.println("graph:");
        //db.printGraph(System.out);
        
        byte[] value;
        for (int i = 0; i < 10; i++) {
            String keyString = "account-id-" + i;
            value = DbUtil.get(db, 999, keyString);
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i), value);
        }
        db.close();
    }
    
    @Nano
    public static void testSplit1() {
        // Parent is a space root node, time-split
        
        byte[] value;
        long time;
        Db db;
        int n = 10;
        CoreTestClock clock = new CoreTestClock();
        
        db = Db.builder().testSetup().maxNodeSize14().clock(clock).start();
        
        time = 100;
        for (int i = 0; i < n; i++) {
            clock.setTime(time);
            db.execute(db.trans().put("k" + time, "v" + time).build());
            time += 10;
        }
        
        time = 100;
        for (int i = 0; i < n; i++) {
            value = DbUtil.get(db, 999, "k" + time);
            Assert.assertArrayEquals("i=" + i + ", time=" + time, 
                    StringUtil.toBytes("v" + time), value);
            time += 10;
        }
        db.close();
    }
    
    private static String getKey(int i) {
        String key = "" + i;
        if (i < 10) {
            key = "0" + key;
        }
        return key;
    }
    
    @Nano
    public static void testSpaceSplit1() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().maxNodeSize8().clock(clock).start();
        
        Trans t;
        for (int i = 100; i < 105; i++) {
            clock.setTime(i);
            t = db.trans().put("admin-accounts-" + i, "v" + i).build();
            db.execute(t);
        }
        
        //System.out.println("---- DBTester.testSpaceSplit1 ----");
        //System.out.println(db.findRoot(Long.MAX_VALUE).printTree());
        
        Assert.assertArrayEquals("i=100", StringUtil.toBytes("v100"), 
                DbUtil.get(db, 101, "admin-accounts-100"));
        
        Assert.assertArrayEquals("i=100", StringUtil.toBytes("v100"), 
                DbUtil.get(db, 103, "admin-accounts-100"));
        
        Assert.assertArrayEquals("i=100", StringUtil.toBytes("v100"), 
                DbUtil.get(db, 104, "admin-accounts-100"));
        
        Assert.assertArrayEquals("i=100", StringUtil.toBytes("v100"), 
                DbUtil.get(db, 199, "admin-accounts-100"));
        
        for (int i = 100; i < 105; i++) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i), 
                    DbUtil.get(db, 199, "admin-accounts-" + i));
        }
        db.close();
    }
    
    @Nano
    public static void testSplitInSingleTransaction() {
        int n = 10;
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().maxNodeSize14().clock(clock).start();
        
        clock.setTime(10);
        Trans.Builder b = db.trans();
        for (int i = 0; i < n; i++) {
            b.put("admin-accounts-" + getKey(i), "v" + i);
        }
        db.execute(b);
        
        for (int i = 0; i < n; i++) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i), 
                    DbUtil.get(db, 20, "admin-accounts-" + getKey(i)));
        }
        db.close();
    }
    
    @Nano
    public static void testSplitTwoSplitsInOneTransaction() {
        int n = 15;
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().maxNodeSize14().clock(clock).start();
        
        clock.setTime(10);
        Trans.Builder b = db.trans();
        for (int i = 0; i < n; i++) {
            b.put("admin-accounts-" + getKey(i), "v" + i);
        }
        Trans t = b.build();
        db.execute(t);
       
        //System.out.println("---- DBTester.testSplitTwoSplitsInOneTransaction ----");
        //System.out.println(db.printGraph());
        
        for (int i = 0; i < n; i++) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i), 
                    DbUtil.get(db, Long.MAX_VALUE, "admin-accounts-" + getKey(i)));
        }
        db.close();
    }
    
    @Nano
    public static void testSpaceSplitAddBackwards() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().maxNodeSize8().clock(clock).start();
        int max = 10;
        
        clock.setTime(10);
        Trans.Builder b = db.trans();
        for (int i = max; i >= 0; i--) {
            b.put("admin-accounts-" + getKey(i), "v" + i);
        }
        Trans t = b.build();
        db.execute(t);
        
        //System.out.println("---- DBTester.testSpaceSplitAddBackwards ----");
        //System.out.println(db.findRoot(20).printTree());
       
        for (int i = 0; i <= max; i++) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i), 
                    DbUtil.get(db, 20, "admin-accounts-" + getKey(i)));
        }
        db.close();
    }
    
    @Nano
    public static void testSpaceSplitOfRoot() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().maxNodeSize8().clock(clock).start();
        
        int max = 10;
        
        clock.setTime(10);
        Trans.Builder b = db.trans();
        for (int i = max; i >= 0; i--) {
            b.put("k-" + getKey(i), "v" + i);
        }
        Trans t = b.build();
        db.execute(t);
        
        //System.out.println("---- DBTester.testSpaceSplitOfRoot ----");
        //System.out.println("transTime = " + t.transTime);
        //System.out.println(db.findRoot(Long.MAX_VALUE).printTree());
        
        for (int i = 0; i <= max; i++) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i), 
                    DbUtil.get(db, 999, "k-" + getKey(i)));
        }
        db.close();
    }
    
    @Nano
    public static void testTimeSplitOfRoot() {
        int n = 20;
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        for (int i = 1; i <= n; i++) {
            String key = getKey(i);
            clock.setTime(i * 10);
            db.execute(db.trans().put(key, "v" + key).build());
            
            byte[] v = DbUtil.get(db, 9999, key);
            Assert.assertArrayEquals(StringUtil.toBytes("v" + key), v);
        }
        
        //System.out.println("---- DBTester.testTimeSplitOfRoot ----");
        //System.out.println(db.printSkipList());
        //System.out.println(db.printTree());
        
        Assert.assertEquals(true, db.internal().superRoot().rootTime != 0);
        
        for (int i = 1; i <= n; i++) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + getKey(i)), 
                    DbUtil.get(db, n * 10 + 10, getKey(i)));
        }
        db.close();
    }
    
    @Nano
    public static void testManyKeysInOneTransaction() {
        //TestClock clock = new TestClock();
        Db db = Db.builder().testSetup().start();
        Trans.Builder b = db.trans();
        for (int i = 0; i < 15; i++) {
            b.put("admin-account-" + i, "v" + i);
        }
        db.execute(b.build());
        
        //System.out.println("---- DBTester.testManyKeysInOneTransaction ----");
        //System.out.println(db.printTree());
        Assert.assertArrayEquals(StringUtil.toBytes("v5"), DbUtil.get(db, Long.MAX_VALUE, "admin-account-5"));
        Assert.assertArrayEquals(StringUtil.toBytes("v14"), DbUtil.get(db, Long.MAX_VALUE, "admin-account-14"));
        Assert.assertArrayEquals(StringUtil.toBytes("v0"), DbUtil.get(db, Long.MAX_VALUE, "admin-account-0"));
        db.close();
    }
    
    @Nano
    public static void testGet1() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("k", "v"));
        Assert.assertArrayEquals(StringUtil.toBytes("v"), DbUtil.get(db, 999, "k"));
        db.close();
    }
    
    @Nano
    public static void testGet2() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("longerKey", "v"));
        Assert.assertArrayEquals(StringUtil.toBytes("v"), DbUtil.get(db, 999, "longerKey"));
        db.close();
    }
    
    @Nano
    public static void testGetWithLongerKey() {
        String longerKey = "anotherKeyThatIsLongerThanThePreviousAndIndeedVeryLong";
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(2);
        db.execute(db.trans()
                .put(longerKey, "v2")
                .build());
        
        Assert.assertArrayEquals(StringUtil.toBytes("v2"), DbUtil.get(db, 99, longerKey));
        db.close();
    }
    
    @Nano
    public static void testGetWithLongAndShortKeys() {
        //
        // Tests with two keys, k1, k2. k1 has two segments and k2 has one and
        // the order is: k1 < k2.
        //
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().start();
        //db.setTime(10);
        clock.setTime(10);
        db.execute(db.trans()
                .put("myLongerKey", "v1")
                .put("nash", "v2")
                .build());
        
        //System.out.println("---- DBTester.testLongAndShortKeys ----");
        //System.out.println(db.findRoot(db.getTime()).printTree());
        
        Assert.assertArrayEquals(StringUtil.toBytes("v1"), DbUtil.get(db, 20, "myLongerKey"));
        Assert.assertArrayEquals(StringUtil.toBytes("v2"), DbUtil.get(db, 20, "nash"));
        Assert.assertNull(DbUtil.get(db, 20, "myLongerX"));
        Assert.assertNull(DbUtil.get(db, 20, "anotherX"));
        Assert.assertNull(DbUtil.get(db, 20, "nas"));
        Assert.assertNull(DbUtil.get(db, 20, "nasher"));
        db.close();
    }
    
    @Nano
    public static void testGetBeforeFirstSet() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("first", "f").build());
        
        Assert.assertArrayEquals(StringUtil.toBytes("f"), DbUtil.get(db, 99, "first"));
        Assert.assertNull(DbUtil.get(db, 5, "first"));
        db.close();
    }
    
    private static Db createRandomDB(int n, AppendOnlyStream stream) {
        Random random = new Random(1);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(stream).clock(clock).start();
        GetData getData = db.newGetData();
        
        for (int i = 0; i < n; i++) {
            getData = db.newGetData();
            String key = "" + random.nextInt();
            Trans t = db.trans().put(key, "v" + key).build();
            clock.setTime(i * 10 + 10);
            db.execute(t);
            
            byte[] value = db.getOne(Long.MAX_VALUE, Keys.toSegments(key), getData);
            Assert.assertEquals("i=" + i, "v" + key, StringUtil.toString(value));
        }
        return db;
    }
    
    @Nano
    public static void testWithRandomData() {
        createRandomDB(25, new MemoryStream()).close();
    }
    
    @Nano("f")     // Too slow to be "unit"
    public static void testWithMoreRandomData() {
        createRandomDB(1000, new MemoryStream()).close();
    }
    
    @Nano
    public static void testSplit3() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().maxNodeSize14().clock(clock).start();
        
        clock.setTime(100);
        Trans.Builder b = db.trans();
        for (long i = 100; i < 113; i++) {
            b.put("four" + i + "end", "" + i);
        }
        db.execute(b.build());
        
        //System.out.println("---- DBTester.testSplit3 ----");
        //db.printGraph(System.out);
        db.checkNodes();
        
        clock.setTime(110);
        b = db.trans();
        for (long i = 100; i < 111; i++) {
            b.put("four110-" + i, "v-four110-" + i);
        }
        db.execute(b.build());
        
        //System.out.println("---- DBTester.testSplit3 ----");
        //db.printGraph(System.out);
        
        clock.setTime(120);
        db.execute(db.trans().put("four110-111", "v-four110-111"));
        
        //System.out.println("-- After adding four110-111 --");
        //db.printGraph(System.out);
        
        // Checking result
        
        byte[] value;
        
        for (long i = 100; i < 113; i++) {
            GetData gd = db.newGetData();
            value = db.getOne(Long.MAX_VALUE, Keys.toSegments("four" + i + "end"), gd);
            Assert.assertEquals("i=" + i, "" + i, StringUtil.toString(value));
        }
        
        for (long i = 100; i < 111; i++) {
            value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("four110-" + i));
            Assert.assertEquals("i=" + i, "v-four110-" + i, StringUtil.toString(value));
        }
        
        db.checkNodes();
        
        value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("four110-111"));
        Assert.assertEquals("v-four110-111", StringUtil.toString(value));
        
        value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("four110-111"));
        Assert.assertEquals("v-four110-111", StringUtil.toString(value));
        db.close();
    }
    
    @Nano
    public static void testSpecialCase() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans()
                .put("r/directory1", "v1")
                .put("r/direc", "v2")
                .put("2/directory2", "v3")
                .put("r/direct", "v4"));
        
        Assert.assertEquals("v1", StringUtil.toString(DbUtil.get(db, 999, "r/directory1")));
        Assert.assertEquals("v2", StringUtil.toString(DbUtil.get(db, 999, "r/direc")));
        Assert.assertNull(DbUtil.get(db, 999, "2/direc"));
        Assert.assertEquals("v4", StringUtil.toString(DbUtil.get(db, 999, "r/direct")));
        db.close();
    }
    
    @Nano
    public static void testPrintGraph1() {
        // Test for manual inspection.
        
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put("r/directory1", "v1")
                .put("r/direc", "v2")
                .put("2/directory2", "v3")
                .put("r/direct", "v4"));
        
        //System.out.println("---- DBTester.testPrintGraph ----");
        //System.out.println(db.printGraph());
        db.close();
    }
    
    @Nano
    public static void testPrintGraph2() {
        // For manual inspection.
        
        Db db = Db.builder().testSetup().start();
        for (int i = 0; i < 9; i++) {
            db.execute(db.trans().put("k" + i, "v" + i));
        }
        
        //System.out.println("---- DBTester.testPrintGraph2 ----");
        //System.out.println(db.printGraph());
        db.close();
    }
    
    @Nano
    public static void testTwoBinaryKeysInOneTransaction() {
        //
        // Two kvs, one transaction, binary keys.
        //
        AppendOnlyStream s = new MemoryStream();
        TestClock clock = new TestClock();
        Db db = Db.builder().clock(clock).mainStream(s).start();
        int n = 2;
        Trans.Builder b = db.trans();
         
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
        db.close();
    }
    
    @Nano
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
            
            Trans trans = db.trans().put("key", "version " + i).build();
            db.execute(trans);
        }
        
        Assert.assertEquals("version 39", StringUtil.toString(DbUtil.get(db, Long.MAX_VALUE, "key")));
        db.close();
    }
    
    /**
     * For the testCrazyKeys() test.
     */
    private static interface KeySource {
        byte[] getKey(int index);
    }
    
    @Nano
    public static void testCrazyKeys() {
        AppendOnlyStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        int n = 50;
        KeySource ks = new KeySource() {
            public byte[] getKey(int index) {
                return KeyFactory.crazyKey(index);
            }
        };
        
        Db db = Db.builder().clock(clock).mainStream(s).noEvict().start();
        
        // Creates some KVs, 0 - 999.
        
        for (int i = 0; i < n; i++) {
            clock.setTime(1*1000000 + i * 10);
            Trans t = db.trans().put(ks.getKey(i), StringUtil.toBytes("v" + i)).build();
            db.execute(t);
        }
        
        // Checks keys 0 - 999.
        
        for (int i = 0; i < n; i++) {
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, ks.getKey(i));
            Assert.assertEquals("i=" + i, "v" + i, StringUtil.toString(value));
        }
        
        // Removes some of the keys
        
        for (int i = 0; i < n; i += 10) {
            clock.setTime(2*1000000 + i * 10);
            Trans t = db.trans().delete(ks.getKey(i)).build();
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
                Assert.assertEquals("i=" + i, "v" + i, StringUtil.toString(value));
            }
        }
        
        // Checks that they existed before they were removed.
        
        for (int i = 0; i < n; i++) {
            byte[] value = DbUtil.get(db, 2*1000000-1, ks.getKey(i));
            Assert.assertEquals("Get at 2*1000000-1, i=" + i, "v" + i, StringUtil.toString(value));
        }
        db.close();
    }
    
    @Nano
    public static void testSettingValueManyTimes() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        int n = 20;
        String key = "directory/myFile";     // 3 klongs long (2x7 + 2)
        byte[] keyBytes = Keys.toBytes(key);
        
        for (int i = 0; i < n; i++) {
            clock.setTime(i * 10 + 1);
            db.execute(db.trans().put(key, "v-" + i));
        }
        
        //System.out.println("---- DBTester.testSettingValueManyTimes ----");
        //db.printGraph(System.out);
        
        for (int i = 0; i < n; i++) {
            long time = i * 10 + 5;
            byte[] value = DbUtil.get(db, time, keyBytes);
            Assert.assertEquals("i=" + i, "v-" + i, StringUtil.toString(value));
        }
        db.close();
    }
    
    @Nano
    public static void tGetFirst1() {
        // Tests get first with simple db. Multiple times.
        
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(db.trans().put("bert", "v1"));
        clock.setTime(20);
        db.execute(db.trans().put("anna", "v2"));
        
        GetData gd = db.newGetData();
        
        byte[] key = DbUtil.getFirstKey(db, 5, gd);
        Assert.assertEquals(null, key);
        
        key = DbUtil.getFirstKey(db, 15, gd);
        Assert.assertArrayEquals(Keys.toBytes("bert"), key);
        
        key = DbUtil.getFirstKey(db, 25, gd);
        Assert.assertArrayEquals(Keys.toBytes("anna"), key);
        db.close();
    }
    
    @Nano
    public static void tGetFirst2() {
        // Similar to tGetFirst1, but with longer, multi-segment keys.
        
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(db.trans().put("employees/bertilsson", "v1"));
        clock.setTime(20);
        db.execute(db.trans().put("employees/annasson", "v2"));
        clock.setTime(30);
        db.execute(db.trans().put("a", "v3"));
        
        GetData gd = db.newGetData();
        
        byte[] key = DbUtil.getFirstKey(db, 5, gd);
        Assert.assertEquals(null, key);
        
        key = DbUtil.getFirstKey(db, 15, gd);
        Assert.assertEquals("employees/bertilsson", Keys.bkey2ikey(key));
        
        key = DbUtil.getFirstKey(db, 25, gd);
        Assert.assertEquals("employees/annasson", Keys.bkey2ikey(key));
        
        key = DbUtil.getFirstKey(db, 35, gd);
        Assert.assertEquals("a", Keys.bkey2ikey(key));
        db.close();
    }
    
    /**
     * Creates and starts a test Db based on the provided stream. Small bufferSize and bufferTime.
     */
    private static Db testDb(AppendOnlyStream stream) {
        DbBuilder b = Db.builder();
        b.clock(new TestClock());
        b.noEvict();
        b.id(DatabaseId.TEST_ID);
        b.stream("main", stream, 10*1000, 10);
        return b.start();
    }
    
    @Nano
    public static void testCrash1() {
        //
        // Truncate from end, one transaction in addition to the primordial one.
        //
        MemoryStream mstream = new MemoryStream();
        Db db = testDb(mstream);
        
        long size1 = mstream.getLength();
        Trans trans = db.trans().put("key", "value").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        db.stop();
        
        long size2 = mstream.getLength();
        long diff = size2 - size1;
        
        Assert.assertTrue(diff > 10);
        mstream.truncate(size2 - 10);
        
        MemoryStream mstream2 = mstream.copy();
        
        Assert.assertEquals(size2 - 10, mstream2.getLength());
     
        Db db2 = testDb(mstream2);
        byte[] value = DbUtil.get(db2, Keys.toBytes("key"));
        Assert.assertTrue(value == null);
        db2.stop();
    }
    
    @Nano
    public static void testCrash2() {
        //
        // Truncate from end, two transactions, one should still work when database restarted.
        //
        MemoryStream mstream = new MemoryStream();
        Db db = testDb(mstream);
        
        Trans trans = db.trans().put("key", "the-first-value").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        long size1 = mstream.getLength();
        
        trans = db.trans().put("key", "the-second-value").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        long size2 = mstream.getLength();
        Assert.assertEquals("the-second-value", DbUtil.getString(db, "key"));
        db.stop();
        
        // Restart, no crash
        Db db2 = testDb(mstream);
        Assert.assertEquals("the-second-value", DbUtil.getString(db2, "key"));
        db2.stop();
        
        // Restart, truncate 10 bytes (last transaction)
        mstream.truncate(size2 - 10);
        Db db3 = testDb(mstream);
        Assert.assertEquals("the-first-value", DbUtil.getString(db3, "key"));
        db3.stop();
        
        // Restart, truncate first transaction.
        mstream.truncate(size1 - 10);
        Db db4 = testDb(mstream);
        Assert.assertNull(DbUtil.getString(db4, "key"));
        db4.stop();
    }
    
    @Nano
    public static void testCrash3() {
        //
        // Truncates complicated stream a few times.
        //
        MemoryStream mstream = new MemoryStream();
        Db db = testDb(mstream);
        db.sync(SyncLevel.ORDINARY);      // The creation is written: the cuts come after it.
        
        long size1 = mstream.getLength();
        db.execute(db.trans().put("key", "value1").build());
        db.execute(db.trans().put("a-significantly-longer-key", "value2").build());
        Trans trans = db.trans().put("another-key-that-is-longer-than-most", "value3").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        long size2 = mstream.getLength();
        long diff = size2 - size1;
        
        int stepSize = (int) (diff / 10);
        
        for (int i = 1; i <= diff; i+= stepSize) {
            long newSize = size2 - i;

            MemoryStream mstream2 = mstream.copy();
            mstream2.truncate(newSize);
 
            Db db2 = testDb(mstream2);
            byte[] value = DbUtil.get(db2, StringUtil.toBytes("non-existing-key"));
            Assert.assertTrue(value == null);
            db2.stop();
        }
    }
    
    @Nano("f")   // Too slow to be "unit" test.
    public static void testCrash4MetaBlock() {
        //
        // Truncates stream in the middle of 2nd meta block.
        //
        MemoryStream mstream = new MemoryStream();
        Db db = testDb(mstream);
        final int blockDist = RecoverableStream.META_BLOCK_DISTANCE;
        
        db.execute(db.trans().put("key1", "value1"));
        
        byte[] v2 = new byte[blockDist];
        v2[0] = 2;
        
        Trans trans = db.trans().put("key2", v2).build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        mstream.truncate(blockDist + RecoverableStream.META_BLOCK_SIZE / 2);
        
        Db db2 = testDb(mstream);
        String v1 = DbUtil.getString(db2, "key1");
        byte[] v2b = DbUtil.get(db2, "key2");
        
        Assert.assertEquals("value1", v1);
        Assert.assertTrue(v2b == null);
        
        db2.stop();
    }
    
    @Nano
    public static void testCrash5InTransSize() {
        //
        // Truncates stream in the middle of the size (4 first bytes) of a transaction.
        //
        MemoryStream mstream = new MemoryStream();
        Db db = testDb(mstream);
        Trans trans = db.trans().put("key1", "value1").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        long size1 = mstream.getLength();
        
        trans = db.trans().put("key2", "value2").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        
        Assert.assertTrue(mstream.getLength() >= trans.lastPos);
        mstream.truncate(size1 + 3);
        Assert.assertEquals(size1 + 3, mstream.getLength());
        
        db.stop();
        db = null;
        
        Db db2 = testDb(mstream);
        
        String v1 = DbUtil.getString(db2, "key1");
        String v2 = DbUtil.getString(db2, "key2");
        Assert.assertEquals("value1", v1);
        Assert.assertTrue(v2 == null);
        
        db2.stop();
    }
    
    /**
     * Regression test for a bug found 2026-10-13 (java/stress/CrashTest.java): a crash
     * after the first byte of a transaction's size, when that byte is 6 to 16. Recovery
     * completed the size as that byte, a transaction shorter than NodeStream accepts, and
     * startup failed with "Bad transaction size".
     */
    @Nano
    public static void testCrash6TornSizeBelowMin() throws IOException {
        MemoryStream mstream = new MemoryStream();
        Db db = testDb(mstream);
        Trans trans = db.trans().put("key1", "value1").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        long size1 = mstream.getLength();
        
        trans = db.trans().put("key2", "value2").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        db.stop();
        
        // The first byte of the size of the second transaction is written, and it is 8.
        mstream = mstream.copy();       // db.stop() closed mstream.
        mstream.truncate(size1 + 1);
        MemoryStream.TestAccess.write(mstream, new byte[]{8}, size1);
        
        Db db2 = testDb(mstream);
        Assert.assertEquals("value1", DbUtil.getString(db2, "key1"));
        Assert.assertTrue(DbUtil.getString(db2, "key2") == null);
        trans = db2.trans().put("key3", "value3").build();
        db2.execute(trans);
        db2.sync(trans.lastPos, SyncLevel.ORDINARY);
        db2.stop();
        
        Db db3 = testDb(mstream.copy());
        Assert.assertEquals("value1", DbUtil.getString(db3, "key1"));
        Assert.assertEquals("value3", DbUtil.getString(db3, "key3"));
        db3.stop();
    }
    
    /**
     * Regression test for bergdb 005-27, found 2026-10-22: a crash that ends the stream
     * exactly at a meta block's position, after a transaction that ends there. The
     * transaction and the meta block are two appends, and a flush can come between them.
     * Recovery stepped past the meta block, beyond the end of the stream, and startup failed
     * ("spos >= streamSize"). Also a cut just after that meta block, and a transaction that
     * crosses the next position, cut there.
     */
    @Nano
    public static void testCrash7AtMetaBlockPosition() {
        final int dist = RecoverableStream.META_BLOCK_DISTANCE;
        MemoryStream mstream = new MemoryStream();
        Db db = Db.builder().testSetup(mstream).start();
        db.execute(db.trans().put("key1", "value1"));
        Trans trans = db.trans().put("key2", new byte[1000]).build();
        db.execute(trans);
        
        // The next put of key2 has the same overhead; its value is sized for the transaction
        // to end exactly at the position of the second meta block.
        long overhead = trans.nextPos - trans.tpos - 1000;
        byte[] v2 = new byte[(int) (dist - trans.nextPos - overhead)];
        v2[0] = 2;
        trans = db.trans().put("key2", v2).build();
        db.execute(trans);
        Assert.assertEquals(dist, trans.lastPos + 1);
        
        byte[] v3 = new byte[dist];
        trans = db.trans().put("key3", v3).build();
        db.execute(trans);
        Assert.assertTrue(trans.tpos < 2 * dist && trans.lastPos > 2 * dist);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        db.stop();
        
        long[] cuts = {dist, dist + RecoverableStream.META_BLOCK_SIZE, 2 * dist};
        for (long cut : cuts) {
            MemoryStream m = mstream.copy();     // db.stop() closed mstream.
            m.truncate(cut);
            Db db2 = Db.builder().testSetup(m).start();
            Assert.assertEquals("value1", DbUtil.getString(db2, "key1"));
            Assert.assertArrayEquals(v2, DbUtil.get(db2, "key2"));
            Assert.assertTrue(DbUtil.get(db2, "key3") == null);
            trans = db2.trans().put("key4", "value4").build();
            db2.execute(trans);
            db2.sync(trans.lastPos, SyncLevel.ORDINARY);
            db2.stop();
            
            Db db3 = Db.builder().testSetup(m.copy()).start();
            Assert.assertArrayEquals(v2, DbUtil.get(db3, "key2"));
            Assert.assertTrue(DbUtil.get(db3, "key3") == null);
            Assert.assertEquals("value4", DbUtil.getString(db3, "key4"));
            db3.stop();
        }
    }
    
    /**
     * Bergdb 005-33: a crash while the database is created, at every length of its stream
     * from 1 byte to the whole creation less one, and the whole creation with its transaction
     * failed, as recovery's zero fill left it before. The start throws a
     * DatabaseNotCreatedException and leaves the stream as it was. Before, it threw one of
     * three StreamFormatExceptions, and from 129 bytes on recovery zero-filled the
     * transaction first. The whole creation starts. An f-test, as its 264 starts take about
     * 110 ms; the unit tests start on some of the cuts (NodeStreamTester, PubTester). The
     * creating start's record of the startup distance (bergdb 028-15) is cut off first; the
     * primordial record whole and alone is refused too (bergdb 028-18), and a crash inside
     * the second record is DbTesterRestart.testCrashInCreationsSecondRecord. The whole
     * creation, both records, starts.
     */
    @Nano("f")
    public static void testCrash8InCreation() throws IOException {
        MemoryStream s = new MemoryStream();
        Db.builder().testSetup(s).start().close();
        MemoryStream created = s.copy();        // close() closed s.
        created.truncate(Db.CREATION_LENGTH);
        final int length = (int) created.getLength();
        Assert.assertEquals(Db.CREATION_LENGTH, length);
        byte[] bytes = new byte[length];
        created.read(0, bytes, 0, length);
        MemoryStream failed = created.copy();
        MemoryStream.TestAccess.write(failed, new byte[] {0}, length - 1);
        
        for (int cut = 1; cut <= length + 1; cut++) {
            // length + 1: the primordial record whole and alone (bergdb 028-18).
            MemoryStream m = cut < length ? created.copy() : cut == length ? failed.copy()
                    : created.copy();
            m.truncate(Math.min(cut, length));
            Db db = Db.builder().testSetup(m).build();
            try {
                db.start();
                throw new AssertionError("started, cut at " + cut);
            } catch (DatabaseNotCreatedException e) {
                // Expected.
            }
            MemoryStream after = m.copy();      // The failed start closed m.
            byte[] expected = java.util.Arrays.copyOf(bytes, Math.min(cut, length));
            if (cut == length) {
                expected[length - 1] = 0;
            }
            byte[] actual = new byte[(int) after.getLength()];
            after.read(0, actual, 0, actual.length);
            Assert.assertArrayEquals("cut at " + cut, expected, actual);
        }
        
        Db db = Db.builder().testSetup(s.copy()).start();
        db.execute(db.trans().put("key1", "value1"));
        Assert.assertEquals("value1", DbUtil.getString(db, "key1"));
        db.close();
    }
    
    /**
     * Regression test for a bug found 2026-10-13: when the stream failed (here,
     * closed under the running database), a sync returned as if the transaction were
     * durable. Now it throws, and so does the next transaction. An f-test: the sync after
     * the failure returns at StorageManager's next 500 ms poll, as nothing wakes it.
     * Since bergdb 005-30 the failed sync fails the database: a DbFailedException with
     * the StreamIoException as the cause, and the next transaction is refused with it.
     */
    @Nano("f")
    public static void testSyncAfterStreamFailure() {
        MemoryStream mstream = new MemoryStream();
        Db db = testDb(mstream);
        Trans trans = db.trans().put("key1", "value1").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.ORDINARY);
        
        mstream.stop();     // Appends to mstream now fail.
        trans = db.trans().put("key2", "value2").build();
        db.execute(trans);
        
        DbFailedException syncEx = null;
        try {
            db.sync(trans.lastPos, SyncLevel.ORDINARY);
        } catch (DbFailedException e) {
            syncEx = e;
        }
        Assert.assertTrue(syncEx != null && syncEx.getCause() instanceof StreamIoException);
        
        DbFailedException ex = null;
        try {
            db.execute(db.trans().put("key3", "value3").build());
        } catch (DbFailedException e) {
            ex = e;
        }
        Assert.assertTrue(ex != null && ex.getCause() == syncEx.getCause());
    }
    
    /**
     * A transaction's KVs reach the index in the order of their keys after the key
     * transformations (Db.putKvs; bergdb 023-08, section 7, Q4): two databases, each given
     * the same operations, puts through a key transformation in another order and plain
     * deletes, write the same stream, byte for byte, and give the same values, also after
     * a restart. The same transaction with a plain put at one of the transformed keys is
     * refused first, in both databases, with nothing written (bergdb 024-16; its KVs are the
     * transaction's, which get their keys as written back); until 024-16 one of the two was
     * kept, the later put in the builder's order (Db.sortByKey), and "k031" held "plain".
     * Before 023-09 the index got the transformed KVs in the order of their keys before the
     * transformation, and the streams differed.
     */
    @Nano
    public static void testTransformedKeysSorted() {
        final KeyTransformation toName = new KeyTransformation() {
            public void transform(Trans trans, int index) {
                String s = Keys.toString(trans.kvs[index].getKey());
                long[] key = Keys.toSegments("/t/" + s.substring(s.indexOf('=') + 1));
                trans.kvs[index].setKey(key);
                trans.writeKeyHashes[index] = Keys.hash(key);
            }
        };
        final int n = 60;
        byte[][] streams = new byte[2][];
        String[][] values = new String[2][];
        for (int d = 0; d < 2; d++) {
            List<Integer> names = new ArrayList<Integer>();
            for (int i = 0; i < n; i++) names.add(i);
            Collections.shuffle(names, new Random(10 + d));
            MemoryStream ms = new MemoryStream();
            Db db = Db.builder().testSetup(ms).maxNodeSize8().start();
            Trans.Builder tb = db.trans();
            for (int i = 0; i < 2 * n; i += 2) tb.put("/t/" + String.format("k%03d", i), "old" + i);
            db.execute(tb.build());
            tb = db.trans();
            for (int i = 0; i < n; i++) {
                // "/t/$NN=kXXX": the builder's order is NN's, the key after it kXXX.
                String name = String.format("k%03d", 2 * names.get(i) + 1);
                tb.put(Keys.toSegments("/t/$" + String.format("%02d", i) + "=" + name), toName,
                        StringUtil.toBytes("new" + name), null);
            }
            for (int i = 0; i < 2 * n; i += 6) tb.delete("/t/" + String.format("k%03d", i));
            Trans t = tb.build();
            tb.put("/t/k031", "plain");
            try {
                db.execute(tb.build());
                throw new AssertionError("not refused");
            } catch (DbException e) {
                // Refused (bergdb 024-16).
            }
            db.execute(t);
            db.close();
            
            db = Db.builder().testSetup(ms.copy()).maxNodeSize8().start();
            values[d] = new String[2 * n];
            for (int i = 0; i < 2 * n; i++) {
                values[d][i] = DbUtil.getString(db, "/t/" + String.format("k%03d", i));
            }
            db.close();
            streams[d] = new byte[(int) ms.getLength()];
            try {
                ms.read(0, streams[d], 0, streams[d].length);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
        for (int i = 0; i < 2 * n; i++) {
            String expected = i % 6 == 0 ? null : i % 2 == 0 ? "old" + i
                    : "new" + String.format("k%03d", i);
            String at = "key " + i + ": ";
            Assert.assertTrue(at + values[0][i], expected == null ? values[0][i] == null
                    : expected.equals(values[0][i]));
            Assert.assertTrue(at + values[1][i], expected == null ? values[1][i] == null
                    : expected.equals(values[1][i]));
        }
        Assert.assertTrue("the same stream, " + streams[0].length + " and "
                + streams[1].length + " bytes", java.util.Arrays.equals(streams[0], streams[1]));
    }
    
    @Nano
    public static void testKeyTransformation1() {
        KeyTransformation kt = new KeyTransformation() {
            public void transform(Trans trans, int index) {
                long[] key = trans.kvs[index].getKey();
                String keyString = Keys.toString(key);
                keyString = keyString.replace("<transactionTime>", "" + trans.tt);
                long[] newKey = Keys.toSegments(keyString);
                trans.kvs[index].setKey(newKey);
                trans.writeKeyHashes[index] = Keys.hash(newKey);
            }
        };
        
        Db db = Db.builder().testSetup().start();
        Trans t = db.trans()
                .put(Keys.toSegments("test/<transactionTime>"), kt, new byte[0], null)
                .build();
        db.execute(t);
        
        String s = Keys.toString(t.kvs[0].getKey());
        Assert.assertFalse(s.contains("transactionTime"));
        long transTime1 = Long.parseLong(s.substring("test/".length()));
        Assert.assertTrue(transTime1 >= 0);
        db.close();
    }
    
    @Nano
    public static void testKeyTransformation2() {
        KeyTransformation kt = new KeyTransformation() {
            public void transform(Trans trans, int index) {
                long[] key = trans.kvs[index].getKey();
                String keyString = Keys.toString(key);
                keyString = keyString.replace("<transactionTime>", "" + trans.tt);
                long[] newKey = Keys.toSegments(keyString);
                //trans.kvs[index].keySegments = newKey;
                trans.kvs[index].setKey(newKey);
                trans.writeKeyHashes[index] = Keys.hash(newKey);
            }
        };
        
        Db db = Db.builder().testSetup().start();
        Trans t = db.trans()
                .put(Keys.toSegments("test/<transactionTime>"), kt, new byte[0], null)
                .build();
        db.execute(t);
        
        String s = Keys.toString(t.kvs[0].getKey());
        Assert.assertFalse(s.contains("transactionTime"));
        long transactionTime1 = Long.parseLong(s.substring("test/".length()));
        
        t = db.trans()
                .put(Keys.toSegments("test/<transactionTime>"), kt, new byte[0], null)
                .build();
        db.execute(t);
        
        s = Keys.toString(t.kvs[0].getKey());
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
        db.close();
    }
    
    @Nano
    public static void testValueTransformation1() {
        // Uses transactionTime to compute value.
        
        ValueTransformation vt = new ValueTransformation() {
            public byte[] transform(long transactionTime, byte[] inputValue, byte[] previous) {
                String s = "tt" + transactionTime;
                return StringUtil.toBytes(s);
            }
        };
        
        TestClock clock = new TestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(100);
        Trans t = db.trans()
                .put(Keys.toSegments("t/1.s"), null, new byte[0], vt)
                .build();
        db.execute(t);
        
        GetData g = db.newGetData();
        byte[] value = db.getOne(200, Keys.toSegments("t/1.s"), g);
        Assert.assertTrue(value != null);
        String s = StringUtil.toString(value);
        Assert.assertTrue(s.startsWith("tt"));
        long time = Long.parseLong(s.substring("tt".length()));
        Assert.assertTrue(time == 100 || time == 101);
        db.close();
    }
    
    @Nano
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
        
        Trans t = db.trans()
                .put(Keys.toSegments("a"), null, new byte[0], vt)
                .build();
        db.execute(t);
        
        GetData g = db.newGetData();
        byte[] value = db.getOne(200, Keys.toSegments("a"), g);
        Assert.assertTrue(value != null);
        Assert.assertEquals(8, value.length);
        Assert.assertEquals(10, Bytes.bytesToLongBE(value, 0));
        
        t = db.trans()
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
    
    /** A value transformation that gives null, and records the previous value it got. */
    private static final class ToNull implements ValueTransformation {
        int calls = 0;
        byte[] previous;
        public byte[] transform(long transTime, byte[] inputValue, byte[] previous) {
            calls++;
            this.previous = previous;
            return null;
        }
    }
    
    /**
     * A value transformation whose result is null deletes the key, as a delete in the same
     * transaction would (ValueTransformation; bergdb 028-04; B2's probe in 026-13, U13-2):
     * the transaction commits, the key has no value at its time and its old value one unit
     * before, getTrans() lists the delete, and a restart keeps it. For a key without a
     * previous value the null result stores nothing: the transaction commits, and getTrans()
     * does not list the key.
     */
    @Nano
    public static void testValueTransformationNullDeletes() {
        final MemoryStream stream = new MemoryStream();
        final ToNull a = new ToNull(), n = new ToNull();
        Trans t;
        Db db = Db.builder().testSetup(stream).start();
        try {
            db.execute(db.trans().put("/a", "old").put("/b", "b").build());
            t = db.trans()
                    .put(Keys.toSegments("/a"), null, StringUtil.toBytes("new"), a)
                    .put(Keys.toSegments("/n"), null, StringUtil.toBytes("new"), n)
                    .build();
            db.execute(t);
            assertEquals("calls of /a", 1, a.calls);
            assertEquals("calls of /n", 1, n.calls);
            assertArrayEquals(StringUtil.toBytes("old"), a.previous);
            assertTrue("no previous value of /n", n.previous == null);
            
            assertTrue("/a deleted", DbUtil.get(db, t.tt, "/a") == null);
            assertArrayEquals(StringUtil.toBytes("old"), DbUtil.get(db, t.tt - 1, "/a"));
            assertTrue("/n has no value", DbUtil.get(db, t.tt, "/n") == null);
            assertArrayEquals(StringUtil.toBytes("b"), DbUtil.get(db, t.tt, "/b"));
            List<String> listed = new ArrayList<String>();
            for (StoredValueNode node : db.getTrans(t.tpos).getValueNodes()) {
                assertTrue("a delete", node.getNode().getType() == Node.TYPE_DELETE);
                listed.add(Keys.toString(node.getKey()));
            }
            assertEquals("listed", Collections.singletonList("/a"), listed);
        } finally {
            db.close();
        }
        
        db = Db.builder().testSetup(stream.copy()).start();
        try {
            assertTrue("/a deleted after a restart", DbUtil.get(db, Long.MAX_VALUE, "/a") == null);
            assertArrayEquals(StringUtil.toBytes("old"), DbUtil.get(db, t.tt - 1, "/a"));
            assertTrue("/n after a restart", DbUtil.get(db, Long.MAX_VALUE, "/n") == null);
            assertArrayEquals(StringUtil.toBytes("b"), DbUtil.get(db, Long.MAX_VALUE, "/b"));
        } finally {
            db.close();
        }
    }
    
    @Nano
    public static void testStop1() {
        Db db = Db.builder().testSetup().start();
        db.stop();
    }
    
    @Nano
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
    
    @Nano
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
    
    @Nano
    public static void testStopExecute() {
        Db db = Db.builder().testSetup().start();
        db.stop();
        IllegalDbStateException exception = null;
        
        try {
            db.execute(db.trans().put("k", "v").build());
        } catch (IllegalDbStateException e) {
            exception = e;
        }
        
        Assert.assertTrue(exception != null);
    }
    
    @Nano
    public static void testStopMultipleStopCalls() {
        Db db = Db.builder().testSetup().start();
        db.stop();
        db.close();
        db.stop();
        db.stop();
    }
    
    /**
     * bergdb 005-11: a database has one stream. A second stream of another name, until
     * 2026-11-04 a replica, is refused; one of the same name replaces the first.
     */
    @Nano
    public static void testSecondStreamRefused() {
        MemoryStream m0 = new MemoryStream();
        MemoryStream m1 = new MemoryStream();
        DbBuilder b = Db.builder().stream("m0", m0, 10*1000, 10);
        IllegalStateException ex = null;
        try {
            b.stream("m1", m1, 10*1000, 10);
        } catch (IllegalStateException e) {
            ex = e;
        }
        Assert.assertTrue("a second stream is refused", ex != null);
        Assert.assertTrue(b.getMainStream() == m0);
        b.stream("m0", m1, 10*1000, 10);
        Assert.assertTrue(b.getMainStream() == m1);
    }
    
    @Nano
    public static void bug130403() {
        // Bug found 130403 when working with bergdb.test.StreamSize.
        // The following code reproduced the error (before bug was fixed).
        
        MemoryStream m = new MemoryStream();
        Db db = Db.builder().testSetup(m).maxNodeSize62().start();
        
        byte[] value = new byte[0];
        int n = 100;
        
        for (int i = 0; i < n; i++) {
            Trans trans = db.trans().put("" + i, value).build();
            db.execute(trans);
        }
        db.stop();
    }
    
    /**
     * StartInfo.startupDistance is the setting in force at the start: the creation's, the
     * default, 50 MB, and after a restart the stream's, as setStartupDistance() set it
     * (bergdb 028-13: no builder sets it).
     */
    @Nano
    public static void testStartInfoReportsEffectiveDistance() {
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).build();
        try {
            Assert.assertEquals("creation", Db.DEFAULT_STARTUP_DISTANCE,
                    db.start().startupDistance);
            db.setStartupDistance(567890);
        } finally {
            db.close();
        }

        Db reopened = Db.builder().testSetup(stream.copy()).build();
        try {
            Assert.assertEquals("stored distance", 567890, reopened.start().startupDistance);
        } finally {
            reopened.close();
        }
    }

    @Nano
    public static void testStartupDistance1() {
        // A new database has the default, 50 MB, before and after its start (bergdb 028-13:
        // until then the builder's setting).
        
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().mainStream(stream).build();
        
        Assert.assertEquals(50 * 1000000, db.getStartupDistance());
        db.start();
        Assert.assertEquals(50 * 1000000, db.getStartupDistance());
        db.stop();
    }
    
    @Nano
    public static void testStartupDistance2() {
        // A decreased of startup distance is seen immediately by DB.getStartupDistance().
        
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().mainStream(stream).build();
        db.start();
        db.setStartupDistance(2*1000000);
        Assert.assertEquals(2*1000000, db.getStartupDistance());
        
        db.execute(db.trans().put("key", "value").build());
        db.setStartupDistance(1*1000000);
        Assert.assertEquals(1*1000000, db.getStartupDistance());
        
        db.stop();
    }
    
    /**
     * setStartupDistance with the setting in force writes nothing; a call on a stopping or
     * stopped database throws and leaves the setting as it was (bergdb 005-53). Until
     * 005-53 the first wrote its 200 kB transaction, and the second changed the setting
     * before execute() refused the transaction.
     */
    @Nano
    public static void testSetStartupDistanceInForceOrRefused() {
        Db db = Db.builder().testSetup().start();
        db.setStartupDistance(2*1000000);
        db.execute(db.trans().put("key", "value").build());
        long length = db.getStreamLength();
        db.setStartupDistance(2*1000000);
        Assert.assertEquals("nothing written", length, db.getStreamLength());
        db.setStartupDistance(1*1000000);
        Assert.assertTrue("written", db.getStreamLength() > length);
        
        db.stop();
        Exception ex = null;
        try {
            db.setStartupDistance(3*1000000);
        } catch (bergdb.pub.util.IllegalDbStateException e) {
            ex = e;
        }
        Assert.assertTrue("refused", ex != null);
        Assert.assertEquals(1*1000000, db.getStartupDistance());
        db.close();
    }
    
    /**
     * setStartupDistance clamps its argument to the database's whole range, 10 to 10^9
     * bytes, sets the clamped value and returns it; a call whose clamped value is the
     * setting in force writes nothing (bergdb 015-76, 016-06's R6-F5; 028-13: the range was
     * 400,000 to 10^9, and the builder took 10 and up). Every value of the range is taken as
     * it is, the smallest and the largest too, and kept over a restart. A value below 1 is
     * refused with IllegalArgumentException and changes nothing (0 was clamped until
     * 028-13).
     */
    @Nano
    public static void testSetStartupDistanceClamped() {
        int min = Db.MIN_STARTUP_DISTANCE;
        int max = Db.MAX_STARTUP_DISTANCE;
        Assert.assertEquals(10, min);
        Assert.assertEquals(1000 * 1000000, max);
        MemoryStream stream = new MemoryStream();
        try (Db db = Db.builder().testSetup(stream).start()) {
            db.execute(db.trans().put("key", "value").build());
            long length = db.getStreamLength();
            
            for (int v : new int[] {10, 11, 100, 2000, 399999, 400000, 50 * 1000000, max}) {
                Assert.assertEquals("returned, " + v, v, db.setStartupDistance(v));
                Assert.assertEquals("in force, " + v, v, db.getStartupDistance());
                Assert.assertTrue("written, " + v, db.getStreamLength() > length);
                length = db.getStreamLength();
            }
            
            Assert.assertEquals("above the range", max, db.setStartupDistance(max + 1));
            Assert.assertEquals("nothing written above", length, db.getStreamLength());
            Assert.assertEquals("above the range", max, db.setStartupDistance(Integer.MAX_VALUE));
            Assert.assertEquals("nothing written above", length, db.getStreamLength());
            
            Assert.assertEquals("below the range", min, db.setStartupDistance(1));
            Assert.assertEquals("below the range", min, db.getStartupDistance());
            Assert.assertTrue("written", db.getStreamLength() > length);
            length = db.getStreamLength();
            Assert.assertEquals("below the range", min, db.setStartupDistance(9));
            Assert.assertEquals("the clamped value in force", min, db.getStartupDistance());
            Assert.assertEquals("nothing written", length, db.getStreamLength());
            
            for (int bad : new int[] {0, -1, Integer.MIN_VALUE}) {
                Exception ex = null;
                try {
                    db.setStartupDistance(bad);
                } catch (IllegalArgumentException e) {
                    ex = e;
                }
                Assert.assertTrue("refused, " + bad, ex != null);
                Assert.assertEquals(min, db.getStartupDistance());
                Assert.assertEquals("nothing written, " + bad, length, db.getStreamLength());
            }
        }
        try (Db db = Db.builder().testSetup(stream.copy()).start()) {
            Assert.assertEquals("the smallest, kept", min, db.getStartupDistance());
            for (int i = 0; i < 20; i++) {
                db.execute(db.trans().put("key" + i, "value" + i).build());
            }
            Assert.assertEquals("value19", DbUtil.getString(db, "key19"));
        }
    }
    
    @Nano
    public static void testGetOp() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("key", new byte[1]));
        
        long count1 = db.getGetOpCount();
        DbUtil.get(db, "key");
        DbUtil.get(db, "non-existing");
        long count2 = db.getGetOpCount();
        db.stop();
        
        Assert.assertEquals("diff", 2, count2 - count1);
    }
    
    /**
     * The length of a new database's stream after its creating start: the creation
     * (Db.CREATION_LENGTH, the first meta block and the primordial record) and the record of
     * the startup distance's KV (bergdb 028-15).
     */
    static long createdLength() {
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).start();
        try {
            return db.getStreamLength();
        } finally {
            db.close();
        }
    }
    
    /**
     * Large transactions relative to startupDistance. 
     * Startup pos should be the tpos of the kv transaction
     * (the following index node transaction will write all dirty index nodes to stream).
     */
    @Nano private static void testStartupPos1() {
        Db db = Db.builder().testSetup().start();
        final long setterPos = db.getStreamLength();
        db.setStartupDistance(1*1000);
        int n = 6;
        long[] tpos = new long[n];
        long[] sp = new long[n];
        
        for (int i = 0; i < n; i++) {
            Trans t = db.trans().put("/k", new byte[10*1000]).build();
            db.execute(t);
            tpos[i] = t.tpos;
            sp[i] = db.internal().getStartupPosForEvict();
        }
        
        // The setter's record (bergdb 028-13); the record of the creating start's startup
        // distance from 028-15; 0, the primordial record, until then.
        assertEquals(setterPos, sp[0]);
        for (int i = 1; i < n; i++) {
            assertEquals("i=" + i, tpos[i-1], sp[i]);
        }
        db.close();
    }
    
    /**
     * Whether the trans seq holds a transaction that began 2 * sd or more before 'length',
     * the stream's length before the last record. The deadline of the take leaves none
     * (bergdb 007-03, step 3).
     */
    private static boolean dueLeft(Db db, long length, int sd) {
        return db.internal().transSeq().posOfTransBefore(length - 2L * sd + 1) != Spos.NULL;
    }
    
    /** The startup section: the stream's length minus the startup pos. */
    private static long section(Db db) {
        return db.getStreamLength() - db.internal().getStartupPosForEvict();
    }
    
    /** The span of the trans seq's transactions, TransSeq.span(). */
    private static long span(Db db) {
        return db.internal().transSeq().span();
    }
    
    /** A put of a random value of 'size' bytes to one of 'keys' keys; the record's bytes. */
    private static long putRandom(Db db, Random random, int keys, int size) {
        byte[] value = new byte[size];
        random.nextBytes(value);
        long length = db.getStreamLength();
        db.execute(db.trans().put("/k/" + random.nextInt(keys), value).build());
        return db.getStreamLength() - length;
    }
    
    /**
     * The paced take (bergdb 005-49; 007-03, step 3) holds the startup section near the
     * startup distance's setting, sd, and its deadline takes every transaction that begins
     * 2 * sd or more before the end of the stream. Random updates of 2000 keys at sd 10 kB:
     * the take before 2026-10-27 held the section at 1.30 sd on average, left transactions
     * past 2 sd after 57 of the records, and wrote records of up to 6.7 times the mean.
     */
    @Nano
    public static void testPaceHoldsTheStartupSection() {
        final int sd = 10 * 1000;
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        db.setStartupDistance(sd);
        Random random = new Random(1);
        double sections = 0;
        long records = 0;
        long bytes = 0;
        long largest = 0;
        for (int i = 0; i < 6000; i++) {
            clock.setTime(10 + i);
            long length = db.getStreamLength();
            long record = putRandom(db, random, 2000, 16);
            assertFalse("i=" + i, dueLeft(db, length, sd));
            if (db.getStreamLength() > 4 * sd) {
                sections += (double) section(db) / sd;
                records++;
                bytes += record;
                largest = Math.max(largest, record);
            }
        }
        db.close();
        double mean = sections / records;
        assertTrue("mean section " + mean, mean > 0.9 && mean < 1.1);
        assertTrue("largest record " + largest, largest < 5.0 * bytes / records);
    }
    
    /**
     * A decrease of the startup distance to less than half of the startup section (bergdb
     * 007-03, D4; 007-07). The pace uses the new setting at once. The deadline does not jump
     * to twice the new setting, which would make the transaction that setStartupDistance
     * runs write the index nodes of every transaction past it (007-06, section 3); it is at
     * the span of the section's transactions, which shrinks with every commit until it is
     * below twice the setting. 2 MB lowered to 450 kB, 1 kB values: transactions past twice
     * the new setting, counted from the stream's end before the call, are left after it (with
     * the deadline at twice the new setting at once, none are), the span is below twice the
     * setting after a few commits, and the deadline holds from then on. 500 kB until option 2
     * of dead klongs (bergdb 024-23; its review rev23, R1): with it, the paced take of the
     * call took the transaction just past the point at 500 kB, by a few kB, without a jump;
     * counted from the end after the call (the call's own record is about 250 kB) the check
     * held with a jump too.
     */
    @Nano
    public static void testDecreaseOfStartupDistance() {
        final int sd = 450 * 1000;
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        db.setStartupDistance(2000 * 1000);
        Random random = new Random(1);
        long time = 10;
        for (int i = 0; i < 4000; i++) {
            clock.setTime(time++);
            putRandom(db, random, 1000, 1000);
        }
        
        long length = db.getStreamLength();
        assertTrue(dueLeft(db, length, sd));
        db.setStartupDistance(sd);
        assertTrue("no jump", dueLeft(db, length, sd));
        
        long span = span(db);
        int below = -1;
        for (int i = 0; i < 400; i++) {
            clock.setTime(time++);
            length = db.getStreamLength();
            putRandom(db, random, 1000, 1000);
            if (below >= 0) {
                assertFalse("i=" + i, dueLeft(db, length, sd));
            } else {
                if (span >= 2L * sd) {
                    assertTrue("i=" + i, span(db) < span);
                }
                if (span(db) < 2L * sd) {
                    below = i;
                }
            }
            span = span(db);
        }
        db.close();
        // 116 commits with the cap of the share's factor at 2 (bergdb 024-31), which makes
        // the catch-up longer and its records smaller; below 60 before it. 154 since the
        // call's record is small (bergdb 028-15): its 200 kB dummy value, gone, was stream
        // that the take paced and the section's span counted. 246 with the writer of record
        // format 8 (bergdb 026-25; 192 with format 7's on 2026-11-19): the section's span at
        // the call is 1.93 MB, against 1.74 MB, both within the pace's band at 2 MB, and it
        // shrinks by about 4.4 kB a commit with either writer.
        assertTrue("below 2 sd after " + below, below >= 0 && below < 300);
    }
    
    /** The nodes of D: the nodes that got dirty in the transactions of TransSeq. */
    private static List<Node> nodesOfD(Db db) {
        final List<Node> result = new ArrayList<Node>();
        db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                result.add(node);
            }
        });
        return result;
    }
    
    /**
     * A delete of a key that does not exist changes nothing, and marks nothing: no node gets
     * dirty (step 3 of the Lean model; bergdb 011-11, M2). Before 2026-10-16,
     * every node on the path of the delete got dirty.
     */
    @Nano
    public static void testDeleteOfMissingKeyMarksNothing() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().maxNodeSize8().clock(clock).start();
        db.setStartupDistance(100);
        long time = 10;
        for (int i = 0; i < 30; i++) {
            clock.setTime(time++);
            db.execute(db.trans().put("/k/" + getKey(i), "v" + i).build());
        }
        // Transactions that change nothing move the startup pos past the puts: every node is
        // written, and D is empty.
        for (int i = 0; i < 40; i++) {
            clock.setTime(time++);
            db.execute(db.trans().build());
        }
        assertEquals("nodes of D before", 0, nodesOfD(db).size());
        
        clock.setTime(time++);
        db.execute(db.trans().delete("/k/missing").delete("/other/missing").build());
        assertEquals("nodes of D after", 0, nodesOfD(db).size());
        assertTrue("root key node clean", !db.internal().superRoot().getPointerNode(0).isDirty());
        
        for (int i = 0; i < 30; i++) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i),
                    DbUtil.get(db, Long.MAX_VALUE, "/k/" + getKey(i)));
        }
        db.close();
    }
    
    /**
     * A transaction that replaces a node by a split leaves that node clean and out of D,
     * also when the transaction followed and changed it: it is not current at the
     * transaction time, and its latest version is good for every earlier time (Db's
     * endOfTrans; bergdb 011-11, M2). The same for the super root that the
     * transaction replaces.
     */
    @Nano
    public static void testReplacedNodeLeavesD() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().maxNodeSize8().clock(clock).start();
        db.setStartupDistance(100);
        long time = 10;
        for (int i = 0; i < 3; i++) {
            clock.setTime(time++);
            db.execute(db.trans().put("/k/" + getKey(i), "v" + i).build());
        }
        // Transactions that change nothing move the startup pos past the puts: every node is
        // written and clean.
        for (int i = 0; i < 20; i++) {
            clock.setTime(time++);
            db.execute(db.trans().build());
        }
        TopNode oldTop = db.internal().superRoot();
        KeyNode oldRoot = (KeyNode) oldTop.getPointerNode(0);
        assertTrue("old root clean before", !oldRoot.isDirty());
        assertTrue("old top node clean before", !oldTop.isDirty());
        
        // Seven more keys in one transaction: the root key node, full, is replaced. (Two until
        // record format 8, whose writer appends them where they fit; bergdb 026-25.)
        clock.setTime(time++);
        Trans.Builder more = db.trans();
        for (int i = 10; i < 17; i++) {
            more.put("/k/" + getKey(i), "v" + i);
        }
        db.execute(more.build());
        
        assertTrue("a new super root", db.internal().superRoot() != oldTop);
        assertTrue("a new root key node", db.internal().superRoot().getPointerNode(0) != oldRoot);
        assertTrue("old root clean after", !oldRoot.isDirty());
        assertTrue("old top node clean after", !oldTop.isDirty());
        for (Node n : nodesOfD(db)) {
            assertTrue("old root in D", n != oldRoot);
            assertTrue("old top node in D", n != oldTop);
        }
        for (int i : new int[]{0, 1, 2, 10, 11, 12, 13, 14, 15, 16}) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i),
                    DbUtil.get(db, Long.MAX_VALUE, "/k/" + getKey(i)));
        }
        db.close();
    }

    /**
     * In a transaction with a touch (a reclaim step), a node that the puts mark and replace
     * leaves D, as in any other transaction; a node that the touch marked stays in D, also
     * when the puts replace it, as the Lean model's step 3 has it (`touchOf`; bergdb item
     * 001, WP R8: register M17 and the red list of bergdb 001-07, section 6).
     * Before 2026-10-17, a touch transaction kept every mark (Db's endOfTrans).
     * 
     * <p>Since bergdb 024-07 the test names no key range for the touch: it visits the paths
     * of the transaction's keys, and until then, with no range named, every index node. A
     * put replaces only nodes on its key's path that existed before the transaction (a node
     * that the transaction made is split in place), so the touch visited every node that
     * the puts replace, and each stays in D; the first case, a node replaced and not
     * touched, the test met only with a range that left the puts' paths out.</p>
     */
    @Nano
    public static void testTouchTransactionReplacedNodes() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().maxNodeSize8().clock(clock).start();
        db.setStartupDistance(100);
        long time = 10;
        for (int i = 0; i < 30; i++) {
            clock.setTime(time++);
            db.execute(db.trans().put("/k/" + getKey(i), "v" + i).build());
        }
        // Transactions that change nothing move the startup pos past the puts: every node is
        // written, and D is empty.
        for (int i = 0; i < 40; i++) {
            clock.setTime(time++);
            db.execute(db.trans().build());
        }
        assertEquals("nodes of D before", 0, nodesOfD(db).size());
        
        final Set<Node> touched = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        final Set<Node> replaced = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {}
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) { touched.add(node); }
            public void nodeReplaced(Node node) { replaced.add(node); }
        };
        try {
            // A touch, and puts of new keys after the last ones, enough to split the nodes
            // on their path, which the touch visits.
            Trans.Builder b = db.trans();
            for (int i = 30; i < 40; i++) {
                b.put("/k/" + getKey(i), "v" + i);
            }
            Trans t = b.build();
            t.testTouch = true;
            clock.setTime(time++);
            db.execute(t);
        } finally {
            Db.testHooks = null;
        }
        
        Set<Node> inD = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        inD.addAll(nodesOfD(db));
        int putsOnly = 0, touchedToo = 0;
        for (Node r : replaced) {
            if (touched.contains(r)) {
                touchedToo++;
                assertTrue("a node that the touch marked and the puts replaced stays in D",
                        inD.contains(r));
            } else {
                putsOnly++;
                assertTrue("a node that the puts marked and replaced is out of D",
                        !inD.contains(r));
                assertTrue("a node that the puts marked and replaced is clean", !r.isDirty());
            }
        }
        assertTrue("the puts replaced a node that the touch visited", touchedToo > 0);
        assertEquals("the puts replaced a node that the touch did not visit", 0, putsOnly);
        for (int i = 0; i < 40; i++) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i),
                    DbUtil.get(db, Long.MAX_VALUE, "/k/" + getKey(i)));
        }
        db.close();
    }
    
    /**
     * bergdb 005-17: a transaction whose value nodes pass 7/8 of the record limit is refused
     * before it changes anything, and the database goes on. Before, the record's size wrapped
     * in store(), after the puts, and every later transaction failed too. The limit is lowered
     * so that the test needs no 2 GB.
     */
    @Nano
    public static void testTransactionTooLarge() {
        final long saved = StoredTrans.recordLimit;
        StoredTrans.recordLimit = 1000 * 1000;
        try {
            MemoryStream stream = new MemoryStream();
            Db db = Db.builder().testSetup(stream).start();
            db.execute(db.trans().put("/a", "a").build());
            long length = db.getStreamLength();
            
            try {
                db.execute(db.trans().put("/big", new byte[900 * 1000]).put("/b", "b").build());
                throw new AssertionError("a transaction above the limit was executed");
            } catch (bergdb.pub.util.DbException e) {
                assertTrue(e.getMessage(), e.getMessage().contains("too large"));
            }
            assertTrue(DbUtil.get(db, Long.MAX_VALUE, "/big") == null);
            assertTrue(DbUtil.get(db, Long.MAX_VALUE, "/b") == null);
            assertEquals(length, db.getStreamLength());
            
            db.execute(db.trans().put("/c", new byte[800 * 1000]).build());
            assertEquals(800 * 1000, DbUtil.get(db, Long.MAX_VALUE, "/c").length);
            db.stop();
        } finally {
            StoredTrans.recordLimit = saved;
        }
    }
    
    /**
     * bergdb 015-51 (016-06's R7-F2), changed by bergdb 026-06: a result of a value
     * transformation that takes the transaction past StoredTrans.valueLimit() is refused
     * before the go point, as a value given directly is (Db.transformValues): a DbException,
     * nothing written, and the database goes on; a restart has the state before the
     * transaction and the one after it. Until 026-06 the transformation ran after the go
     * point, checkSize saw its input only, and a result whose record did not fit failed the
     * database when the record was made (the caller's fault, 015-51). The record limit is
     * lowered to 100 kB.
     */
    @Nano
    public static void testTransformedValueBeyondRecordLimit() {
        final long saved = StoredTrans.recordLimit;
        StoredTrans.recordLimit = 100 * 1000;
        MemoryStream stream = new MemoryStream();
        try {
            Db db = Db.builder().testSetup(stream).start();
            try {
                db.execute(db.trans().put("/a", "a").build());
                Trans.Builder b = db.trans();
                b.put(Keys.toSegments("/t"), null, new byte[0], new ValueTransformation() {
                    public byte[] transform(long transTime, byte[] in, byte[] previous) {
                        return new byte[120 * 1000];
                    }
                });
                db.sync(SyncLevel.ORDINARY);
                final long length = stream.getLength();
                try {
                    db.execute(b.build());
                    throw new AssertionError("a transformed value above the limit was taken");
                } catch (DbException e) {
                    assertTrue(e.getMessage(), e.getMessage().contains("after its value "
                            + "transformations") && e.getMessage().contains("(bergdb 005-17)"));
                }
                assertEquals("nothing appended", length, stream.getLength());
                assertTrue(DbUtil.get(db, Long.MAX_VALUE, "/t") == null);
                db.execute(db.trans().put("/x", "x").build());
                assertArrayEquals(StringUtil.toBytes("x"), DbUtil.get(db, Long.MAX_VALUE, "/x"));
            } finally {
                db.close();
            }
        } finally {
            StoredTrans.recordLimit = saved;
        }
        
        Db db = Db.builder().testSetup(stream.copy()).start();
        try {
            assertArrayEquals(StringUtil.toBytes("a"), DbUtil.get(db, Long.MAX_VALUE, "/a"));
            assertTrue(DbUtil.get(db, Long.MAX_VALUE, "/t") == null);
            assertArrayEquals(StringUtil.toBytes("x"), DbUtil.get(db, Long.MAX_VALUE, "/x"));
            db.execute(db.trans().put("/y", "y").build());
            assertArrayEquals(StringUtil.toBytes("y"), DbUtil.get(db, Long.MAX_VALUE, "/y"));
        } finally {
            db.stop();
        }
    }
    
    /**
     * Regression test for bergdb 005-31 (007-02's probe, in small): a transaction whose index
     * nodes, those it makes dirty, did not fit in one record was never taken, as
     * TransSeq.take takes transactions whole, and the startup pos stayed before it for good.
     * Now it is refused before it changes anything, and the database goes on with its
     * startup pos moving; a smaller update, and a load of new keys, are taken. The record
     * limit is lowered to 200 KB. Within L1 (bergdb 024-24): the update of every 20th key,
     * 500 operations (every 10th, 1,000, until then), and the load in two transactions of
     * 500 (one of 1,000).
     */
    @Nano("f")
    public static void testTooManyDirtyNodes() {
        final long saved = StoredTrans.recordLimit;
        StoredTrans.recordLimit = 200 * 1000;
        try {
            MemoryStream stream = new MemoryStream();
            CoreTestClock clock = new CoreTestClock();
            long time = 1000 * 1000;
            clock.setTime(time);
            final int sd = 10 * 1000;
            Db db = Db.builder().testSetup(stream).clock(clock).start();
            db.setStartupDistance(sd);
            List<Integer> order = new ArrayList<Integer>();
            for (int k = 0; k < 10000; k++) {
                order.add(k);
            }
            Collections.shuffle(order, new Random(7));
            for (int i = 0; i < 100; i++) {
                clock.setTime(time += 1000);
                Trans.Builder b = db.trans();
                for (int j = 0; j < 100; j++) {
                    b.put(dirtyKey(order.get(i * 100 + j)), "v");
                }
                db.execute(b.build());
            }
            for (int i = 0; i < 500; i++) {
                clock.setTime(time += 1000);
                db.execute(db.trans().put("/x", "a" + i).build());
            }
            
            // An update of every 20th key: a record of about 35 KB, and index nodes for more
            // than the record limit.
            clock.setTime(time += 1000);
            Trans.Builder b = db.trans();
            for (int k = 0; k < 10000; k += 20) {
                b.put(dirtyKey(k), "w");
            }
            long length = db.getStreamLength();
            try {
                db.execute(b.build());
                throw new AssertionError("a transaction above the bound was executed");
            } catch (bergdb.pub.util.DbException e) {
                assertTrue(e.getMessage(), e.getMessage().contains("005-31"));
            }
            assertEquals("nothing appended", length, db.getStreamLength());
            assertEquals("nothing changed", "v", DbUtil.getString(db, dirtyKey(0)));
            
            clock.setTime(time += 1000);
            b = db.trans();
            for (int k = 0; k < 10000; k += 1000) {
                b.put(dirtyKey(k), "w");
            }
            db.execute(b.build());
            for (int k0 = 0; k0 < 1000; k0 += 500) {
                clock.setTime(time += 1000);
                b = db.trans();
                for (int k = k0; k < k0 + 500; k++) {
                    b.put(String.format("/new/%06d", k), "n");
                }
                db.execute(b.build());
            }
            for (int i = 0; i < 500; i++) {
                clock.setTime(time += 1000);
                db.execute(db.trans().put("/y", "b" + i).build());
            }
            long section = db.getStreamLength() - db.internal().getStartupPosForEvict();
            assertTrue("the startup pos moves: a section of " + section, section < 3 * sd);
            assertEquals("w", DbUtil.getString(db, dirtyKey(0)));
            assertEquals("v", DbUtil.getString(db, dirtyKey(10)));
            assertEquals("n", DbUtil.getString(db, "/new/000999"));
            db.close();
        } finally {
            StoredTrans.recordLimit = saved;
        }
    }
    
    private static String dirtyKey(int k) {
        return String.format("/k/%06d", k);
    }
    
    /**
     * bergdb 005-17: records near the record limit stay within it; the writer takes fewer
     * dirty index nodes (TransSeq.take's budget), and a restart finds the state.
     */
    @Nano("f")
    public static void testRecordsWithinLimit() {
        final long saved = StoredTrans.recordLimit;
        final long limit = 200 * 1000;
        StoredTrans.recordLimit = limit;
        try {
            MemoryStream stream = new MemoryStream();
            CoreTestClock clock = new CoreTestClock();
            long time = 1000 * 1000;
            clock.setTime(time);
            Db db = Db.builder().testSetup(stream).clock(clock).maxNodeSize8()
                    .start();
            db.setStartupDistance(150 * 1000);
            Random r = new Random(17);
            for (int i = 0; i < 300; i++) {
                clock.setTime(time += 1000);
                Trans.Builder b = db.trans().put("/big/" + (i % 7), new byte[170 * 1000]);
                for (int j = 0; j < 50; j++) {
                    b.put("/k/" + r.nextInt(3000), "v" + i);
                }
                Trans t = b.build();
                db.execute(t);
                assertTrue("record of " + (t.nextPos - t.tpos) + " bytes",
                        t.nextPos - t.tpos <= limit + 2 * RecoverableStream.META_BLOCK_SIZE);
            }
            long checksum = DbUtil.checksum(db);
            db.sync(SyncLevel.ORDINARY);
            db.stop();
            
            CoreTestClock clock2 = new CoreTestClock();
            clock2.setTime(time += 1000);
            Db db2 = Db.builder().testSetup(stream.copy()).clock(clock2).maxNodeSize8()
                    .start();
            assertEquals(checksum, DbUtil.checksum(db2));
            db2.stop();
        } finally {
            StoredTrans.recordLimit = saved;
        }
    }
    
    /**
     * bergdb 005-18: a clock time above 2^56 - 1 is refused, before the transaction or the
     * database's first transaction changes anything. Before, the database took it, and
     * then could not start again ("Time too large").
     */
    @Nano
    public static void testClockOutOfRange() {
        final long[] now = {1000 * 1000};
        Clock clock = new Clock() {
            public long getTime() {
                return now[0];
            }
        };
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        db.execute(db.trans().put("/a", "v1").build());
        long length = db.getStreamLength();
        
        now[0] = Klong.MAX_TIME + 1000;
        try {
            db.execute(db.trans().put("/a", "v2").build());
            throw new AssertionError("a transaction with a time out of range was executed");
        } catch (bergdb.pub.util.DbException e) {
            assertTrue(e.getMessage(), e.getMessage().contains("outside the range"));
        }
        assertArrayEquals(StringUtil.toBytes("v1"), DbUtil.get(db, Long.MAX_VALUE, "/a"));
        assertEquals(length, db.getStreamLength());
        
        now[0] = 2 * 1000 * 1000;
        db.execute(db.trans().put("/a", "v3").build());
        assertArrayEquals(StringUtil.toBytes("v3"), DbUtil.get(db, Long.MAX_VALUE, "/a"));
        db.stop();
        
        now[0] = Klong.MAX_TIME + 1;
        try {
            Db.builder().testSetup().clock(clock).start();
            throw new AssertionError("a database with a time out of range was started");
        } catch (bergdb.pub.util.DbException e) {
            assertTrue(e.getMessage(), e.getMessage().contains("outside the range"));
        }
    }
    
    /** bergdb 005-20: Jmx's retain duration in days was computed in int. */
    @Nano
    public static void testJmxRetainDurationInDays() {
        Db db = Db.builder().testSetup().start();
        Jmx.DbMonitor monitor = new Jmx.DbMonitor(db);
        final long day = 24L * 3600 * Clock.UNITS_PER_SEC;
        int[] days = {1, 365, 24855, 30000, 50000, 99999, 10675199};
        for (int d : days) {
            monitor.setRetainDurationInDays(d);
            assertEquals(d * day, db.getRetainDuration());
        }
        try {
            monitor.setRetainDurationInDays(10675200);      // more than Long.MAX_VALUE units
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            // Expected.
        }
        monitor.setRetainDurationInSeconds(Integer.MAX_VALUE);
        assertEquals(Integer.MAX_VALUE * Clock.UNITS_PER_SEC, db.getRetainDuration());
        db.stop();
    }
    
    /**
     * Regression test for bergdb 005-34: a get gives the position of the transaction that
     * wrote the value (GetData.tpos), and getTrans of it gives that transaction, also for the
     * values after a meta block in their record, which were 128 bytes too far, and after a
     * restart. With the default startup distance the restart reruns every transaction, and a
     * rerun value had its own position as the transaction's; with a small one, most values are
     * then read from the stream.
     */
    @Nano
    public static void testGetTransOfEveryValue() {
        for (int startupDistance : new int[] {50 * 1000000, 20000}) {     // the default, small
            final int d = RecoverableStream.META_BLOCK_DISTANCE;
            Random random = new Random(34);
            MemoryStream s = new MemoryStream();
            Db db = Db.builder().testSetup(s).start();
            db.setStartupDistance(startupDistance);
            List<Trans> ts = new ArrayList<Trans>();
            int crossing = 0;
            while (crossing < 3) {
                Trans.Builder b = db.trans();
                for (int j = 0; j < 20; j++) {
                    byte[] v = new byte[500];
                    random.nextBytes(v);
                    b.put("/k" + ts.size() + "/" + j, v);
                }
                Trans t = b.build();
                db.execute(t);
                ts.add(t);
                if (t.tpos / d != t.lastPos / d) {
                    crossing++;
                }
            }
            checkGetTrans(db, ts);
            db.sync(SyncLevel.ORDINARY);
            db.stop();
            
            Db db2 = Db.builder().testSetup(s.copy()).start();
            checkGetTrans(db2, ts);
            db2.stop();
        }
    }
    
    /** Every value of the transactions: its tpos from a get; getTrans of it, once each. */
    private static void checkGetTrans(Db db, List<Trans> ts) {
        for (int i = 0; i < ts.size(); i++) {
            Trans t = ts.get(i);
            for (int j = 0; j < 20; j++) {
                GetData gd = db.newGetData();
                db.getOne(Long.MAX_VALUE, Keys.toSegments("/k" + i + "/" + j), gd);
                assertEquals("value " + i + "/" + j, t.tpos, gd.tpos);
            }
            assertEquals("transaction " + i, t.tt, db.getTrans(t.tpos).tt);
        }
    }
    
    /**
     * bergdb 005-34: getTrans refuses a position that cannot start a transaction before it
     * reads, and the database goes on. Since bergdb 005-43 also a position at or past the end
     * of the stream (end, end + 8 and d + 128 pass the other checks), which was a DbException.
     */
    @Nano
    public static void testGetTransRefusesBadPositions() {
        Db db = Db.builder().testSetup().start();
        Trans t = db.trans().put("/a", "a0").build();
        db.execute(t);
        final int d = RecoverableStream.META_BLOCK_DISTANCE;
        final long end = db.getStreamLength();
        assertEquals(t.lastPos + 1, end);
        long[] bad = {-1, Long.MIN_VALUE, t.tpos + 4, t.tpos + 1, 0, 64, d, d + 120,
                end, end + 8, d + 128};
        for (long tpos : bad) {
            try {
                db.getTrans(tpos);
                throw new AssertionError("taken, " + tpos);
            } catch (IllegalArgumentException e) {
                // Expected.
            }
        }
        assertEquals(t.tt, db.getTrans(t.tpos).tt);
        db.execute(db.trans().put("/b", "b0").build());
        assertEquals("b0", DbUtil.getString(db, "/b"));
        db.stop();
    }
    
    /**
     * bergdb 021-27 (found by a black-box user of the C port (022), U2-4): getTrans at a
     * multiple of 8 inside a committed transaction's record, not at its start, passes the
     * checks of testGetTransRefusesBadPositions and reads the bytes there as a record. It
     * failed the database (DbFailedException, and every later call threw it until a
     * restart). Since 2026-11-12 (Frans: a read-only call with a position from the caller
     * "should fail or succeed, but never block the database"; 010-04, R5) Db.getTrans()
     * takes the position as a caller's and refuses it: IllegalArgumentException, the read's
     * StreamFormatException its cause, and the database goes on. Until then this test kept
     * the old behaviour, as its Javadoc said it.
     */
    @Nano
    public static void testGetTransInsideARecord() {
        final String value = new String(new char[1000]).replace('\0', 'x');
        final long[] offsets = {8, 16, 24, 512};
        for (long offset : offsets) {
            Db db = Db.builder().testSetup().start();
            try {
                Trans t = db.trans().put("/a", value).build();
                db.execute(t);
                assertTrue("inside, " + offset, t.tpos + offset < t.lastPos);
                Throwable e = null;
                try {
                    db.getTrans(t.tpos + offset);
                } catch (Throwable x) {
                    e = x;
                }
                assertTrue("tpos + " + offset + ": " + e, e instanceof IllegalArgumentException);
                assertTrue("the position, " + e, e.getMessage().startsWith(
                        "Not a position of a transaction, " + (t.tpos + offset) + ":"));
                assertEquals("the database goes on, tpos + " + offset, value,
                        DbUtil.getString(db, "/a"));
                assertEquals(t.tt, db.getTrans(t.tpos).tt);
                db.execute(db.trans().put("/b", "b0").build());
                assertEquals("b0", DbUtil.getString(db, "/b"));
            } finally {
                db.stop();
            }
        }
    }
    
    /**
     * bergdb 021-27: every multiple of 8 inside a record that reaches over two meta blocks,
     * of random values and keys, is refused by getTrans with IllegalArgumentException, or
     * gives a StoredTrans where the bytes there happen to form a committed record (the
     * caller's position is the caller's responsibility; none is expected here); the database
     * goes on. The positions in the meta blocks inside the record are refused before the
     * read (bergdb 005-34). Last, a position inside the last record, at the stream's end.
     */
    @Nano
    public static void testGetTransInsideARecordOverMetaBlocks() {
        final int d = RecoverableStream.META_BLOCK_DISTANCE;
        final Random random = new Random(2127);
        final byte[] big = new byte[2 * d + 1000];
        random.nextBytes(big);
        Db db = Db.builder().testSetup().start();
        try {
            Trans.Builder b = db.trans();
            for (int i = 0; i < 20; i++) {
                byte[] v = new byte[random.nextInt(200)];
                random.nextBytes(v);
                b.put("/k" + i, v);
            }
            b.put("/big", big);
            Trans t = b.build();
            db.execute(t);
            assertTrue("over two meta blocks", t.lastPos / d - t.tpos / d == 2);
            Trans t2 = db.trans().put("/a", "a0").build();
            db.execute(t2);
            int refused = 0;
            for (long pos = t.tpos + 8; pos < t.lastPos; pos += 8) {
                try {
                    StoredTrans st = db.getTrans(pos);
                    assertTrue("a record of the bytes at " + pos, st.tpos == pos);
                } catch (IllegalArgumentException e) {
                    refused++;
                }
            }
            assertTrue("refused " + refused, refused > (t.lastPos - t.tpos) / 8 - 5);
            assertTrue("the end's record", t2.tpos + 16 < t2.lastPos);
            for (long pos = t2.tpos + 8; pos < t2.lastPos; pos += 8) {
                try {
                    db.getTrans(pos);
                    throw new AssertionError("taken, " + pos);
                } catch (IllegalArgumentException e) {
                    // Expected.
                }
            }
            assertEquals("the database goes on", t.tt, db.getTrans(t.tpos).tt);
            assertEquals(t2.tt, db.getTrans(t2.tpos).tt);
            assertArrayEquals(big, DbUtil.get(db, "/big"));
            db.execute(db.trans().put("/b", "b0").build());
            assertEquals("b0", DbUtil.getString(db, "/b"));
        } finally {
            db.stop();
        }
    }
    
    /**
     * bergdb 021-27, Q27-1: a value crafted so that a position inside it passes the header
     * check (a size of about the record's rest, its last byte LAST_BYTE, the format byte
     * right) is refused before the record's array is made: the size, over 1 MiB, is believed
     * only after the walk of the records' sizes reaches the position, and here it passes
     * over it (the cause says so; without the walk the read made an array of that size and
     * failed later, in the parse). The value is 3 MB, over 15 meta blocks; eight candidates
     * at offsets 65 k + 0..7 in it, one of them at a multiple of 8, whichever the value's
     * position. The real record of 3 MB at its start is still read, and the database goes on.
     */
    @Nano
    public static void testGetTransCraftedSizeInsideARecord() {
        final int n = 3 * 1000 * 1000;
        final byte[] v = new byte[n];
        final int[] offP = new int[8];
        final int[] size = new int[8];
        for (int k = 0; k < 8; k++) {
            offP[k] = 65 * k;
            final int offL = n - 100 + 8 * k;
            size[k] = offL - offP[k] + 1;
            Bytes.intToBytesLE(size[k], v, offP[k]);
            v[offP[k] + 4] = StoredTrans.RECORD_FORMAT;
            v[offL] = RecoverableStream.LAST_BYTE;
        }
        assertTrue("over the limit", size[7] > NodeStream.CALLERS_SIZE_LIMIT);
        Db db = Db.builder().testSetup().start();
        try {
            Trans t = db.trans().put("/v", v).build();
            db.execute(t);
            
            // The value's position: its first bytes in the record's bytes.
            final byte[] record = db.internal().nodeStream().readTransBytes(t.tpos);
            int d = -1;
            for (int i = 0; i + 8 <= record.length && d == -1; i++) {
                boolean match = true;
                for (int j = 0; j < 8; j++) {
                    match &= record[i + j] == v[j];
                }
                d = match ? i : -1;
            }
            assertTrue("the value in the record", d > 0);
            final long valueStart = RecoverableStream.getSpos(t.tpos, d);
            int aligned = 0;
            for (int k = 0; k < 8; k++) {
                final long p = RecoverableStream.getSpos(valueStart, offP[k]);
                if (p % 8 != 0) {
                    continue;
                }
                aligned++;
                IllegalArgumentException e = null;
                try {
                    db.getTrans(p);
                } catch (IllegalArgumentException x) {
                    e = x;
                }
                assertTrue("refused, " + p, e != null);
                assertEquals("refused before the array: " + e.getCause(), "A size of " + size[k]
                        + " bytes at stream pos " + p + ", which is inside the record at "
                        + t.tpos + ", not a record's start.", e.getCause().getMessage());
            }
            assertEquals("one candidate at a multiple of 8", 1, aligned);
            assertEquals("the record of 3 MB at its start", t.tt, db.getTrans(t.tpos).tt);
            assertArrayEquals(v, DbUtil.get(db, "/v"));
            db.execute(db.trans().put("/b", "b0").build());
            assertEquals("b0", DbUtil.getString(db, "/b"));
        } finally {
            db.stop();
        }
    }
    
    // ======== sync(), bergdb 005-44 ========
    
    /**
     * Regression test for bergdb 005-44: a sync returned when the durable length reached the
     * position of the transaction's last byte, its commit byte, so that byte could still be in
     * the write buffer, and a crash then lost the transaction. A buffer of 2 S - 2 bytes, for
     * a record of S bytes, writes S - 1 bytes of the record at once and its last byte a buffer
     * time later; the sync must wait for that byte.
     */
    @Nano("f")
    public static void testSyncWaitsForTheCommitByte() throws InterruptedException {
        final byte[] value = new byte[100];
        
        // The size of the third put's record, in a database of its own.
        Db db = Db.builder().stream("m", new MemoryStream(), 10 * 1000, 10).start();
        Trans t = null;
        for (int i = 0; i < 3; i++) {
            t = db.trans().put("/k", value).build();
            db.execute(t);
        }
        final long size = t.lastPos + 1 - t.tpos;
        db.close();
        
        db = Db.builder().stream("m", new MemoryStream(), (int) (2 * size - 2), 200).start();
        for (int i = 0; i < 2; i++) {
            db.execute(db.trans().put("/k", value).build());
        }
        // All written, so that the buffer holds the third record only.
        final long deadline = System.currentTimeMillis() + 10 * 1000;
        while (db.getDurableLength() < db.getStreamLength()) {
            assertTrue("written within 10 s", System.currentTimeMillis() < deadline);
            Thread.sleep(5);
        }
        t = db.trans().put("/k", value).build();
        db.execute(t);
        assertEquals("the record's size", size, t.lastPos + 1 - t.tpos);
        
        db.sync(t.lastPos, SyncLevel.ORDINARY);
        assertTrue("the commit byte is durable: " + db.getDurableLength() + " > " + t.lastPos,
                db.getDurableLength() > t.lastPos);
        db.close();
    }
    
    // ======== stop() and close(), bergdb 005-35 ========
    
    /**
     * Regression test for bergdb 005-35: stop() lost the transactions that were still in the
     * write buffer, all of them in a quick run. Now it writes them in a thread of its own:
     * once that thread has ended, the stream holds every transaction that returned, and it
     * is closed.
     */
    @Nano
    public static void testStopWritesAll() throws Exception {
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).start();
        for (int i = 0; i < 300; i++) {
            db.execute(db.trans().put("/k" + i, "v" + i).build());
        }
        long length = db.getStreamLength();
        Set<Thread> before = closeThreads();
        db.stop();
        joinNew(before);
        Assert.assertEquals("all written", length, s.getLength());
        DbTesterFailure.assertClosed(s);
        
        Db db2 = Db.builder().testSetup(s.copy()).start();
        for (int i = 0; i < 300; i++) {
            Assert.assertEquals("v" + i, DbUtil.getString(db2, "/k" + i));
        }
        db2.close();
    }
    
    /**
     * bergdb 005-35: a transaction that runs when stop() is called, here one that waits for
     * room in the buffer of a slow stream, completes and is written; stop() returns at once.
     * Before, stop() closed the storage under it, and it waited for ever.
     */
    @Nano("f")
    public static void testStopWithRunningTransaction() throws Exception {
        final SlowStream s = new SlowStream(20);
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.stream("main", s, 100 * 1000, 10);
        final Db db = b.start();
        db.sync(SyncLevel.ORDINARY);
        final byte[] big = new byte[400 * 1000];
        Thread w = new Thread() {
            public void run() {
                db.execute(db.trans().put("/big", big).build());
            }
        };
        w.start();
        while (s.appends.get() < 2) {           // It waits for room by now.
            Thread.sleep(1);
        }
        Set<Thread> before = closeThreads();
        long t0 = System.nanoTime();
        db.stop();
        // "At once": within 10 s, room for load (bergdb 028-23; 1 s until then); a stop that
        // waited for the writer would wait until the join below gives up.
        Assert.assertTrue("stop() returns at once", System.nanoTime() - t0 < 10L * 1000 * 1000 * 1000);
        w.join(30 * 1000);
        Assert.assertFalse("the transaction has ended", w.isAlive());
        joinNew(before);
        Assert.assertTrue("closed", s.closed);
        
        Db db2 = Db.builder().testSetup(s.inner.copy()).start();
        Assert.assertEquals("written", big.length, DbUtil.get(db2, "/big").length);
        db2.close();
    }
    
    /**
     * bergdb 005-35, Frans's note in close(): close() after stop(), and two close() at once,
     * returned at once, with the stream open and bytes not yet written. Now each returns only
     * when the stream is closed and holds everything.
     */
    @Nano("f")
    public static void testCloseWaits() throws Exception {
        for (int c = 0; c < 2; c++) {
            final SlowStream s = new SlowStream(100);
            DbBuilder b = Db.builder();
            b.testSetupExceptStream();
            b.stream("main", s, 100 * 1000, 10);
            final Db db = b.start();
            db.sync(SyncLevel.ORDINARY);
            for (int i = 0; i < 100; i++) {
                db.execute(db.trans().put("/k" + i, "v" + i).build());
            }
            final long length = db.getStreamLength();
            final String[] seen = new String[2];
            Thread[] closers = new Thread[2];
            for (int k = 0; k < 2; k++) {
                final int kk = k;
                closers[k] = new Thread() {
                    public void run() {
                        db.close();
                        seen[kk] = "closed " + s.closed + ", length " + s.getLength();
                    }
                };
            }
            if (c == 0) {
                db.stop();                      // close() after stop()
                closers[0].start();
                closers[0].join(30 * 1000);
                seen[1] = seen[0];
            } else {
                closers[0].start();             // two close() at once
                Thread.sleep(20);
                closers[1].start();
                closers[0].join(30 * 1000);
                closers[1].join(30 * 1000);
            }
            for (int k = 0; k < 2; k++) {
                Assert.assertEquals("close " + c + "/" + k, "closed true, length " + length, 
                        seen[k]);
            }
        }
    }
    
    /**
     * bergdb 005-35: a writer that waits for room in the buffer waited for ever when a flush
     * failed (a failing disk hung the database, holding the write lock). Now it throws, the
     * database fails, and the next transaction is refused.
     */
    @Nano
    public static void testWriterWaitingForRoomAfterFailedFlush() throws Exception {
        final DbTesterFailure.FaultStream s = new DbTesterFailure.FaultStream();
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.stream("main", s, 100 * 1000, 10);
        final Db db = b.start();
        db.sync(SyncLevel.ORDINARY);
        s.failAppends = true;
        Throwable thrown = DbTesterFailure.within(10 * 1000, new Runnable() {
            public void run() {
                db.execute(db.trans().put("/big", new byte[1000 * 1000]).build());
            }
        });
        Assert.assertTrue("the writer fails the database: " + thrown, 
                thrown instanceof DbFailedException);
        Throwable next = DbTesterFailure.within(10 * 1000, new Runnable() {
            public void run() {
                db.execute(db.trans().put("/small", "x").build());
            }
        });
        Assert.assertTrue("the next is refused: " + next, next instanceof DbFailedException);
        db.close();
    }
    
    /**
     * bergdb 005-73, F4: invalid fractions are refused without changing the setting. Since
     * 005-79 the fraction is kept in units of 2^-16, the nearest: 0.001, 0.90 and 0.25 give
     * 66, 58,982 and 16,384 units, and the getter gives the units over 65,536.
     */
    @Nano
    public static void testReclaimInternalFractionValidation() {
        try (Db db = Db.builder().testSetup().start()) {
            Reclaim reclaim = db.internal().reclaim();
            Assert.assertEquals("default", 16384, reclaim.getInternalFractionUnits());
            double[] valid = {0.001, 0.90, 0.1, 0.25};
            int[] units = {66, 58982, 6554, 16384};
            for (int i = 0; i < valid.length; i++) {
                db.setReclaimInternalFraction(valid[i]);
                Assert.assertEquals("units of " + valid[i], units[i],
                        reclaim.getInternalFractionUnits());
                Assert.assertTrue("accepted fraction " + valid[i],
                        db.getInternalFraction() == units[i] / 65536.0);
            }
            Assert.assertTrue("0.25 exactly", db.getInternalFraction() == 0.25);
            for (int invalid : new int[] {Reclaim.MIN_INTERNAL_FRACTION - 1,
                    Reclaim.MAX_INTERNAL_FRACTION + 1, 0, -1}) {
                boolean refused = false;
                try {
                    synchronized (db.internal().getWriteLock()) {
                        reclaim.setSettings(reclaim.getRetainDuration(), invalid);
                    }
                } catch (IllegalArgumentException expected) {
                    refused = true;
                }
                Assert.assertTrue("refused units " + invalid, refused);
                Assert.assertEquals("units unchanged", 16384, reclaim.getInternalFractionUnits());
            }
            for (double invalid : new double[] {Double.NaN, Double.NEGATIVE_INFINITY,
                    Double.POSITIVE_INFINITY, Math.nextDown(0.001), Math.nextUp(0.90)}) {
                boolean refused = false;
                try {
                    db.setReclaimInternalFraction(invalid);
                } catch (IllegalArgumentException expected) {
                    refused = true;
                }
                Assert.assertTrue("refused fraction " + invalid, refused);
                Assert.assertTrue("setting unchanged", db.getInternalFraction() == 0.25);
            }
        }
    }

    // ======== AutoCloseable, bergdb 005-59 ========

    /** bergdb 005-73, F5: the final flush fails, including a close begun by stop(). */
    @Nano
    public static void testCloseReportsFinalFlushFailure() {
        for (int mode = 0; mode < 2; mode++) {
            DbTesterFailure.FaultStream s = new DbTesterFailure.FaultStream();
            DbBuilder b = Db.builder();
            b.testSetupExceptStream();
            b.stream("main", s, 100 * 1000, 60 * 1000);
            Db db = b.start();
            db.sync(SyncLevel.ORDINARY);
            db.execute(db.trans().put("/buffered", "value").build());
            s.failAppends = true;
            if (mode == 1) db.stop();
            IOException first = null;
            for (int call = 0; call < 2; call++) {
                StreamIoException thrown = null;
                try {
                    db.close();
                } catch (StreamIoException e) {
                    thrown = e;
                }
                Assert.assertTrue("close reports the flush failure", thrown != null);
                Assert.assertTrue("I/O cause", thrown.getCause() instanceof IOException);
                if (first == null) first = (IOException) thrown.getCause();
                Assert.assertTrue("same stored failure", first == thrown.getCause());
            }
            DbTesterFailure.assertClosed(s.inner);
        }
    }

    /** A storage-close error is reported and suppressed by try-with-resources. */
    @Nano
    public static void testCloseFailureSuppressedByBlockFailure() {
        final IOException failure = new IOException("the storage close fails");
        DbTesterFailure.FaultStream s = new DbTesterFailure.FaultStream() {
            public void close() throws IOException {
                super.close();
                throw failure;
            }
        };
        IllegalStateException blockFailure = new IllegalStateException("the block fails");
        try (Db db = Db.builder().testSetup(s).start()) {
            throw blockFailure;
        } catch (IllegalStateException e) {
            Assert.assertTrue("the block failure", e == blockFailure);
            Throwable[] suppressed = e.getSuppressed();
            Assert.assertEquals("one close failure", 1, suppressed.length);
            Assert.assertTrue("storage exception", suppressed[0] instanceof StreamIoException);
            Assert.assertTrue("original I/O cause", suppressed[0].getCause() == failure);
        }
        DbTesterFailure.assertClosed(s.inner);
    }
    
    /**
     * bergdb 005-59: Db is AutoCloseable. A try-with-resources block closes the database when
     * it ends, also when it throws, and waits: with a buffer time of a minute nothing is
     * written before the close, and right after the block the stream is closed and holds
     * every transaction.
     */
    @Nano
    public static void testTryWithResourcesCloses() throws Exception {
        for (int c = 0; c < 2; c++) {
            MemoryStream s = new MemoryStream();
            DbBuilder b = Db.builder();
            b.testSetupExceptStream();
            b.stream("main", s, 100 * 1000, 60 * 1000);
            boolean caught = false;
            try (Db db = b.start()) {
                for (int i = 0; i < 20; i++) {
                    db.execute(db.trans().put("/k" + i, "v" + i).build());
                }
                if (c == 1) {
                    throw new IllegalStateException("the block throws");
                }
            } catch (IllegalStateException e) {
                caught = true;
            }
            Assert.assertEquals("block " + c + " threw", c == 1, caught);
            DbTesterFailure.assertClosed(s);
            
            Db db2 = Db.builder().testSetup(s.copy()).start();
            for (int i = 0; i < 20; i++) {
                Assert.assertEquals("block " + c, "v" + i, DbUtil.getString(db2, "/k" + i));
            }
            db2.close();
        }
    }
    
    /**
     * bergdb 005-59: close() after stop(), and close() twice, are safe, here through a
     * try-with-resources block: the second call waits for the close, or returns, and the
     * stream is closed.
     */
    @Nano
    public static void testCloseAfterStopAndTwice() throws Exception {
        for (int c = 0; c < 2; c++) {
            MemoryStream s = new MemoryStream();
            try (Db db = Db.builder().testSetup(s).start()) {
                db.execute(db.trans().put("/a", "a").build());
                if (c == 0) {
                    db.stop();
                } else {
                    db.close();
                }
            }
            DbTesterFailure.assertClosed(s);
            
            Db db2 = Db.builder().testSetup(s.copy()).start();
            Assert.assertEquals("call " + c, "a", DbUtil.getString(db2, "/a"));
            db2.close();
        }
    }
    
    /** The threads of stop()'s closes that are alive (bergdb 005-35). */
    public static Set<Thread> closeThreads() {
        Set<Thread> result = new java.util.HashSet<Thread>();
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            if (t.getName().startsWith("Db-close-") && t.isAlive()) {
                result.add(t);
            }
        }
        return result;
    }
    
    /** Joins, for up to 30 s each, the close threads that were not alive 'before'. */
    public static void joinNew(Set<Thread> before) throws InterruptedException {
        Set<Thread> now = closeThreads();
        now.removeAll(before);
        for (Thread t : now) {
            t.join(30 * 1000);
            Assert.assertFalse("the close has ended", t.isAlive());
        }
    }
    
    /** A MemoryStream whose appends take 'delayMs' each: a slow disk (bergdb 005-35). */
    static class SlowStream implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        final int delayMs;
        final java.util.concurrent.atomic.AtomicInteger appends = 
                new java.util.concurrent.atomic.AtomicInteger();
        volatile boolean closed = false;
        
        SlowStream(int delayMs) {
            this.delayMs = delayMs;
        }
        
        public long getLength() {
            return inner.getLength();
        }
        
        public long getFirstPos() {
            return inner.getFirstPos();
        }
        
        public void read(long position, byte[] dest, int destOffset, int length) 
                throws IOException {
            inner.read(position, dest, destOffset, length);
        }
        
        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            try {
                Thread.sleep(delayMs);
            } catch (InterruptedException e) {
                throw new IOException("interrupted");
            }
            inner.append(source, sourceOffset, length);
            appends.incrementAndGet();
        }
        
        public void pretruncate(long position) throws IOException {
            inner.pretruncate(position);
        }
        
        public void close() {
            closed = true;
            inner.close();
        }
    }
}
