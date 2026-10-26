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
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import static bergdb.nanotest.Assert.*;
import bergdb.nanotest.Nano;
import bergdb.pub.util.BadReplicaException;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
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
    }
    
    @Nano
    public static void test2() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("admin1", "F").build());
        byte[] value = DbUtil.get(db, 99, Keys.toBytes("admin1"));
        Assert.assertArrayEquals(StringUtil.toBytes("F"), value);
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
        //db.stop();
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
    }
    
    @Nano
    public static void testVersionsReplaceValue() {
        CoreTestClock clock = new CoreTestClock();
        Db db = createT2DB(clock);
        clock.setTime(20);
        db.execute(db.trans().put("apa", "A").build());

        Assert.assertArrayEquals(StringUtil.toBytes("A"), DbUtil.get(db, 30, "apa"));
        Assert.assertArrayEquals(StringUtil.toBytes("A"), DbUtil.get(db, 999, "apa"));
    }
    
    @Nano
    public static void testLongKey() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("myLongerKey", "v1").build());
        
        //System.out.println("---- DBTester.testLongKey ----");
        //System.out.println(db.findRoot(db.getTime()).printTree());
        
        Assert.assertNull(DbUtil.get(db, 99, StringUtil.toBytes("rKey")));
        Assert.assertArrayEquals(StringUtil.toBytes("v1"), DbUtil.get(db, 99, "myLongerKey"));
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
        
        long klong = k.getKlong(5);
        Assert.assertEquals("check TYPE_DELETE_BITMAP", Klong.getType(klong), Klong.TYPE_DELETE_BITMAP);
        
        boolean[] expected = new boolean[]{false, false, true, true, false, false};
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
    }
    
    @Nano
    public static void testDeleteOfNonExistingData0() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().delete("a").build());   // This is a noop transaction.
        byte[] value = DbUtil.get(db, Long.MAX_VALUE, "a");
        Assert.assertNull(value);
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
    }
    
    @Nano
    public static void testSame7BytesPrefix() {
        Db db = Db.builder().testSetup().start();
        Trans t = db.trans()
                .put("account1", "1")
                .put("account2", "2").build();
        db.execute(t);
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
    }
    
    @Nano
    public static void testGet1() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("k", "v"));
        Assert.assertArrayEquals(StringUtil.toBytes("v"), DbUtil.get(db, 999, "k"));
    }
    
    @Nano
    public static void testGet2() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("longerKey", "v"));
        Assert.assertArrayEquals(StringUtil.toBytes("v"), DbUtil.get(db, 999, "longerKey"));
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
    }
    
    @Nano
    public static void testGetBeforeFirstSet() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("first", "f").build());
        
        Assert.assertArrayEquals(StringUtil.toBytes("f"), DbUtil.get(db, 99, "first"));
        Assert.assertNull(DbUtil.get(db, 5, "first"));
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
        createRandomDB(25, new MemoryStream());
    }
    
    @Nano("f")     // Too slow to be "unit"
    public static void testWithMoreRandomData() {
        createRandomDB(1000, new MemoryStream());
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
    }
    
    /**
     * Creates and starts a test Db based on the provided stream. Small bufferSize and bufferTime.
     */
    private static Db testDb(AppendOnlyStream stream) {
        DbBuilder b = Db.builder();
        b.clock(new TestClock());
        b.noEvict();
        b.retainForever();
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
        db.sync(trans.lastPos, SyncLevel.STRONG);
        long size1 = mstream.getLength();
        
        trans = db.trans().put("key", "the-second-value").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.STRONG);
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
        db.sync(SyncLevel.STRONG);      // The creation is written: the cuts come after it.
        
        long size1 = mstream.getLength();
        db.execute(db.trans().put("key", "value1").build());
        db.execute(db.trans().put("a-significantly-longer-key", "value2").build());
        Trans trans = db.trans().put("another-key-that-is-longer-than-most", "value3").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.STRONG);
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
        db.sync(trans.lastPos, SyncLevel.STRONG);
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
        db.sync(trans.lastPos, SyncLevel.STRONG);
        long size1 = mstream.getLength();
        
        trans = db.trans().put("key2", "value2").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.STRONG);
        
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
        db.sync(trans.lastPos, SyncLevel.STRONG);
        long size1 = mstream.getLength();
        
        trans = db.trans().put("key2", "value2").build();
        db.execute(trans);
        db.sync(trans.lastPos, SyncLevel.STRONG);
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
        db2.sync(trans.lastPos, SyncLevel.STRONG);
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
        db.sync(trans.lastPos, SyncLevel.STRONG);
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
            db2.sync(trans.lastPos, SyncLevel.STRONG);
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
     * 110 ms; the unit tests start on some of the cuts (NodeStreamTester, PubTester).
     */
    @Nano("f")
    public static void testCrash8InCreation() throws IOException {
        MemoryStream s = new MemoryStream();
        Db.builder().testSetup(s).start().close();
        MemoryStream created = s.copy();        // close() closed s.
        final int length = (int) created.getLength();
        Assert.assertEquals(Db.CREATION_LENGTH, length);
        byte[] bytes = new byte[length];
        created.read(0, bytes, 0, length);
        MemoryStream failed = created.copy();
        MemoryStream.TestAccess.write(failed, new byte[] {0}, length - 1);
        
        for (int cut = 1; cut <= length; cut++) {
            MemoryStream m = cut < length ? created.copy() : failed.copy();
            m.truncate(cut);
            Db db = Db.builder().testSetup(m).build();
            try {
                db.start();
                throw new AssertionError("started, cut at " + cut);
            } catch (DatabaseNotCreatedException e) {
                // Expected.
            }
            MemoryStream after = m.copy();      // The failed start closed m.
            byte[] expected = java.util.Arrays.copyOf(bytes, cut);
            if (cut == length) {
                expected[length - 1] = 0;
            }
            byte[] actual = new byte[(int) after.getLength()];
            after.read(0, actual, 0, actual.length);
            Assert.assertArrayEquals("cut at " + cut, expected, actual);
        }
        
        Db db = Db.builder().testSetup(created.copy()).start();
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
        db.sync(trans.lastPos, SyncLevel.STRONG);
        
        mstream.stop();     // Appends to mstream now fail.
        trans = db.trans().put("key2", "value2").build();
        db.execute(trans);
        
        DbFailedException syncEx = null;
        try {
            db.sync(trans.lastPos, SyncLevel.STRONG);
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
    
    @Nano
    public static void testFinalize1() {
        Db.builder().testSetup().start();
    }
    
    @Nano
    public static void testFinalize2() {
        Db.builder().testSetup().start();
    }
    
    @Nano
    public static void testFinalize3() {
        Db.builder().testSetup().start();
    }
    
    @Nano
    public static void testBadReplica1() throws IOException {
        MemoryStream m0 = new MemoryStream();
        MemoryStream m1 = new MemoryStream();
        
        Db db = Db.builder().stream("m0", m0, 10*1000, 10).start();
        db.execute(db.trans().put("a.txt", "v1").build());
        db.sync(0, SyncLevel.ORDINARY);
        
        db = Db.builder().stream("m1", m1, 10*1000, 10).start();
        db.execute(db.trans().put("b.txt", "v2-b").build());
        
        BadReplicaException ex = null;
        try {
            db.addReplica("m0", m0, 10*1000, 10);
        } catch (BadReplicaException e) {
            ex = e;
        }
        Assert.assertTrue(ex != null);
        db.stop();
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
    
    @Nano
    public static void testStartupDistance1() {
        // Checks that startupDistance from Db.Builder is used.
        
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().mainStream(stream).startupDistance(523456).build();
        
        Assert.assertEquals(523456, db.getStartupDistance());
        db.start();
        Assert.assertEquals(523456, db.getStartupDistance());
        db.stop();
    }
    
    @Nano
    public static void testStartupDistance2() {
        // A decreased of startup distance is seen immediately by DB.getStartupDistance().
        
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().mainStream(stream).startupDistance(2*1000000).build();
        
        Assert.assertEquals(2*1000000, db.getStartupDistance());
        db.start();
        
        db.execute(db.trans().put("key", "value").build());
        db.setStartupDistance(1*1000000);
        Assert.assertEquals(1*1000000, db.getStartupDistance());
        
        db.stop();
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
     * Large transactions relative to startupDistance. 
     * Startup pos should be the tpos of the kv transaction
     * (the following index node transaction will write all dirty index nodes to stream).
     */
    @Nano private static void testStartupPos1() {
        Db db = Db.builder().testSetup().startupDistance(1*1000).start();
        int n = 6;
        long[] tpos = new long[n];
        long[] sp = new long[n];
        
        for (int i = 0; i < n; i++) {
            Trans t = db.trans().put("/k", new byte[10*1000]).build();
            db.execute(t);
            tpos[i] = t.tpos;
            sp[i] = db.internal().getStartupPosForEvict();
        }
        
        assertEquals(0, sp[0]);
        for (int i = 1; i < n; i++) {
            assertEquals("i=" + i, tpos[i-1], sp[i]);
        }
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
     * dirty (step 3 of the Lean model; docs/level2-alignment.md, M2). Before 2026-10-16,
     * every node on the path of the delete got dirty.
     */
    @Nano
    public static void testDeleteOfMissingKeyMarksNothing() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().startupDistance(100).maxNodeSize8().clock(clock).start();
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
    }
    
    /**
     * A transaction that replaces a node by a split leaves that node clean and out of D,
     * also when the transaction followed and changed it: it is not current at the
     * transaction time, and its latest version is good for every earlier time (Db's
     * endOfTrans; docs/level2-alignment.md, M2). The same for the super root that the
     * transaction replaces.
     */
    @Nano
    public static void testReplacedNodeLeavesD() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().startupDistance(100).maxNodeSize8().clock(clock).start();
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
        
        // Two more keys in one transaction: the root key node, full, is replaced.
        clock.setTime(time++);
        db.execute(db.trans().put("/k/" + getKey(10), "v10").put("/k/" + getKey(11), "v11").build());
        
        assertTrue("a new super root", db.internal().superRoot() != oldTop);
        assertTrue("a new root key node", db.internal().superRoot().getPointerNode(0) != oldRoot);
        assertTrue("old root clean after", !oldRoot.isDirty());
        assertTrue("old top node clean after", !oldTop.isDirty());
        for (Node n : nodesOfD(db)) {
            assertTrue("old root in D", n != oldRoot);
            assertTrue("old top node in D", n != oldTop);
        }
        for (int i : new int[]{0, 1, 2, 10, 11}) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i),
                    DbUtil.get(db, Long.MAX_VALUE, "/k/" + getKey(i)));
        }
    }

    /**
     * In a transaction with a touch (a reclaim step), a node that the puts mark and replace
     * leaves D, as in any other transaction; a node that the touch marked stays in D, also
     * when the puts replace it, as the Lean model's step 3 has it (`touchOf`; bergdb item
     * 001, WP R8: register M17 and the red list of docs/level3-alignment.md, section 6).
     * Before 2026-10-17, a touch transaction kept every mark (Db's endOfTrans).
     */
    @Nano
    public static void testTouchTransactionReplacedNodes() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().startupDistance(100).maxNodeSize8().clock(clock).start();
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
            // A touch of the first keys, and puts of new keys after the last ones, enough
            // to split the nodes on their path, which the touch does not visit.
            Trans.Builder b = db.trans();
            for (int i = 30; i < 40; i++) {
                b.put("/k/" + getKey(i), "v" + i);
            }
            Trans t = b.build();
            t.touch = true;
            t.touchFrom = null;
            t.touchTo = Keys.toSegments("/k/" + getKey(2));
            clock.setTime(time++);
            db.execute(t);
        } finally {
            Db.testHooks = null;
        }
        
        Set<Node> inD = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        inD.addAll(nodesOfD(db));
        int putsOnly = 0;
        for (Node r : replaced) {
            if (touched.contains(r)) {
                assertTrue("a node that the touch marked and the puts replaced stays in D",
                        inD.contains(r));
            } else {
                putsOnly++;
                assertTrue("a node that the puts marked and replaced is out of D",
                        !inD.contains(r));
                assertTrue("a node that the puts marked and replaced is clean", !r.isDirty());
            }
        }
        assertTrue("the puts replaced a node that the touch did not visit", putsOnly > 0);
        for (int i = 0; i < 40; i++) {
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + i),
                    DbUtil.get(db, Long.MAX_VALUE, "/k/" + getKey(i)));
        }
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
     * Regression test for bergdb 005-31 (007-02's probe, in small): a transaction whose index
     * nodes, those it makes dirty, did not fit in one record was never taken, as
     * TransSeq.take takes transactions whole, and the startup pos stayed before it for good.
     * Now it is refused before it changes anything, and the database goes on with its
     * startup pos moving; a smaller update, and a load of new keys, are taken. The record
     * limit is lowered to 200 KB.
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
            Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(sd).start();
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
            
            // An update of every 10th key: a record of about 70 KB, and index nodes for more
            // than the record limit.
            clock.setTime(time += 1000);
            Trans.Builder b = db.trans();
            for (int k = 0; k < 10000; k += 10) {
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
            clock.setTime(time += 1000);
            b = db.trans();
            for (int k = 0; k < 1000; k++) {
                b.put(String.format("/new/%06d", k), "n");
            }
            db.execute(b.build());
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
                    .startupDistance(150 * 1000).start();
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
            db.sync(SyncLevel.STRONG);
            db.stop();
            
            CoreTestClock clock2 = new CoreTestClock();
            clock2.setTime(time += 1000);
            Db db2 = Db.builder().testSetup(stream.copy()).clock(clock2).maxNodeSize8()
                    .startupDistance(150 * 1000).start();
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
            Db db = Db.builder().testSetup(s).startupDistance(startupDistance).start();
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
            db.sync(SyncLevel.STRONG);
            db.stop();
            
            Db db2 = Db.builder().testSetup(s.copy()).startupDistance(startupDistance).start();
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
        db.sync(SyncLevel.STRONG);
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
        Assert.assertTrue("stop() returns at once", System.nanoTime() - t0 < 1000L * 1000 * 1000);
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
            db.sync(SyncLevel.STRONG);
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
        db.sync(SyncLevel.STRONG);
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
        
        public void seekFirstPos(long position) throws IOException {
            inner.seekFirstPos(position);
        }
        
        public void close() {
            closed = true;
            inner.close();
        }
    }
}
