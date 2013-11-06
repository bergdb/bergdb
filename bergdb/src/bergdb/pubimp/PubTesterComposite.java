package bergdb.pubimp;

import java.util.Iterator;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pub.TestClock;
import bergdb.stream.MemoryStream;

/**
 * Tests composite indexes for Layer Pub.
 * 
 * @author Frans Lundberg
 */
public class PubTesterComposite {
    
    private static class Payment2 {
        String from;
        String to;
        long time;
        
        public Payment2() {
            from = "";
            to = "";
            time = 0;
        }
        
        public Payment2(String from, long time) {
            this();
            assert from != null;
            this.from = from;
            this.time = time;
        }
        
        public Payment2(String from, String to, long time) {
            this();
            assert from != null;
            assert to != null;
            this.from = from;
            this.to = to;
            this.time = time;
        }
        
        public String toString() {
            return "from:" + from + ", time:" + time;
        }
    }
    
    private static class DPayment2 {
        String from;
        double time;
        
        public DPayment2() {
            from = "";
            time = 0.0;
        }
        
        public DPayment2(String from, double time) {
            this();
            assert from != null;
            this.from = from;
            this.time = time;
        }
        
        public String toString() {
            return "from:" + from + ", time:" + time;
        }
    }
    
    @T
    public static void test0() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        
        IndexManager.Index index = ((DatabaseImp) database).getIndexManager().getIndex("i0");
        Assert.assertTrue(index != null);
        Assert.assertEquals(2, index.parts);
    }
    
    @T
    public static void test1() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", 100))
             .put("/p/2", new Payment2("2", 200))
             .put("/p/3", new Payment2("1", 300))
             .put("/p/4", new Payment2("1", 400))
             .put("/p/5", new Payment2("2", 0)).execute();
        
        long[] expected = new long[]{300, 400, 0, 100, 200};
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
    }
    
    @T
    public static void testTwoFields() {
        // Two parts, two fields at in first part.
        
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from").field("to")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", "3", 100))
             .put("/p/2", new Payment2("2", "1", 200))
             .put("/p/3", new Payment2("1", "3", 300))
             .put("/p/4", new Payment2("1", "2", 400))
             .put("/p/5", new Payment2("2", "1", 0)).execute();
        
        long[] expected = new long[]{0, 200, 300, 400, 0, 100, 200, 400, 100, 300};
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @T
    public static void testThreeParts() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("string/unicode").field("to")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", "3", 100))
             .put("/p/2", new Payment2("2", "1", 200))
             .put("/p/3", new Payment2("1", "3", 300))
             .put("/p/4", new Payment2("1", "2", 400))
             .put("/p/5", new Payment2("2", "1", 0)).execute();
        
        long[] expected = new long[]{400, 300, 0, 200, 100};
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @T
    public static void testWithRestart() {
        MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream);
        Database db = builder.start();
        Connection c = db.newConnection();
        
        db.indexBuilder("a").dir("/payments/")
            .type("string/unicode").field("from")
            .type("long").field("time").createFast();
        
        c.w().put("/payments/1", new Payment2("1001", 20))
             .put("/payments/2", new Payment2("1002", 30))
             .put("/payments/3", new Payment2("1001", 40)).execute();
        
        Iterator<Payment2> iter = c.useIndex("a", Payment2.class).objects().iterator();
        
        long[] expected = { 20, 40, 30 };
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        
        // Restarts the database and does the checks again.
        
        db.sync();
        db.stop();
        db = null;
        c = null;
        builder = null;
        
        DatabaseBuilder builder2 = Factory.database();
        ((DatabaseBuilderImp) builder2).getDbBuilder().mainStream(stream);
        Database db2 = builder2.start();
        Connection c2 = db2.newConnection();
        
        iter = c2.useIndex("a", Payment2.class).objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        
        db2.stop();
    }
    
    @T
    public static void testEq1() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", 100))
             .put("/p/2", new Payment2("2", 200))
             .put("/p/3", new Payment2("1", 300))
             .put("/p/4", new Payment2("1", 400))
             .put("/p/5", new Payment2("2", 0)).execute();
        
        long[] expected = new long[]{0, 100, 200};
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).eq("2").objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @T
    public static void testEq2() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", 100))
             .put("/p/2", new Payment2("2", 200))
             .put("/p/3", new Payment2("1", 300))
             .put("/p/4", new Payment2("1", 400))
             .put("/p/5", new Payment2("2", 0)).execute();
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).eq("3").objects().iterator();
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @T
    public static void testEq3() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", 100))
             .put("/p/2", new Payment2("2", 200))
             .put("/p/3", new Payment2("1", 300))
             .put("/p/3b", new Payment2("1", 300))
             .put("/p/4", new Payment2("1", 400))
             .put("/p/5", new Payment2("2", 0)).execute();
        
        long[] expected = new long[]{300, 300, 400};
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).eq("1").objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEq3long() {
        // Same as previous, but using eq(long) too.
        
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", 100))
             .put("/p/2", new Payment2("2", 200))
             .put("/p/3", new Payment2("1", 300))
             .put("/p/3b", new Payment2("1", 300))
             .put("/p/4", new Payment2("1", 400))
             .put("/p/5", new Payment2("2", 0)).execute();
        
        long[] expected = new long[]{300, 300};
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class)
                .eq("1").nextLevel()
                .eq(300)
                .objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEq3double() {
        // Same as previous, but using eq(double).
        
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("double").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new DPayment2("2", 100.0))
             .put("/p/2", new DPayment2("2", 200.0))
             .put("/p/3", new DPayment2("1", 300.0))
             .put("/p/3b", new DPayment2("1", 300.0))
             .put("/p/4", new DPayment2("1", 400.0))
             .put("/p/5", new DPayment2("2", 0.0)).execute();
        
        double[] expected = new double[]{300.0, 300.0};
        
        Iterator<DPayment2> iter = c.useIndex("i0", DPayment2.class)
                .eq("1").nextLevel()
                .eq(300.0)
                .objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            DPayment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEq4() {
        // Two eq levels.
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("string/unicode").field("to")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", "3", 100))
             .put("/p/2", new Payment2("2", "1", 200))
             .put("/p/3", new Payment2("1", "3", 300))
             .put("/p/4", new Payment2("1", "2", 400))
             .put("/p/6", new Payment2("3", "0", 333))
             .put("/p/5", new Payment2("2", "1", 0)).execute();
        
        long[] expected = new long[] { 200, 0 };
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).eq("2").nextLevel().eq("1").objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue("i="+ i, iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    
    @T
    public static void testStart1() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", 100))
             .put("/p/2", new Payment2("2", 200))
             .put("/p/3", new Payment2("1", 300))
             .put("/p/4", new Payment2("1", 400))
             .put("/p/6", new Payment2("3", 333))
             .put("/p/5", new Payment2("2", 0)).execute();
        
        long[] expected = new long[]{0, 100, 200, 333};
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).startAt("2").objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testStart2() {
        // Multiple startAt().
        
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("string/unicode").field("to")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", "3", 100))
             .put("/p/2", new Payment2("2", "1", 200))
             .put("/p/3", new Payment2("1", "3", 300))
             .put("/p/4", new Payment2("1", "2", 400))
             .put("/p/6", new Payment2("3", "0", 333))
             .put("/p/5", new Payment2("2", "1", 0)).execute();
        
        long[] expected = new long[] { 100, 333 };
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).startAt("2").nextLevel().startAt("2").objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue("i="+ i, iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @T
    public static void testStart3() {
        // Multiple startAt(), includes startAt(long).
        
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", "3", 100))
             .put("/p/2", new Payment2("2", "1", 200))
             .put("/p/3", new Payment2("1", "3", 300))
             .put("/p/4", new Payment2("1", "2", 400))
             .put("/p/6", new Payment2("3", "0", 33))
             .put("/p/5", new Payment2("2", "1", 0)).execute();
        
        long[] expected = new long[] { 100, 200, 33 };
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).startAt("2").nextLevel().startAt(77).objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue("i="+ i, iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @T
    public static void testEqAndStart1() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("string/unicode").field("to")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", "3", 100))
             .put("/p/2", new Payment2("2", "1", 200))
             .put("/p/3", new Payment2("1", "3", 300))
             .put("/p/4", new Payment2("1", "2", 400))
             .put("/p/6", new Payment2("3", "0", 333))
             .put("/p/6", new Payment2("2", "4", 444))
             .put("/p/5", new Payment2("2", "1", 0)).execute();
        
        long[] expected = new long[] { 100, 444 };
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).eq("2").nextLevel().startAt("3").objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue("i="+ i, iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEqAndStart2() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("string/unicode").field("to")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", "3", 100))
             .put("/p/2", new Payment2("2", "1", 200))
             .put("/p/3", new Payment2("1", "3", 300))
             .put("/p/4", new Payment2("1", "2", 400))
             .put("/p/6", new Payment2("3", "0", 333))
             .put("/p/6", new Payment2("2", "4", 444))
             .put("/p/5", new Payment2("2", "1", 0)).execute();
        
        long[] expected = new long[] { 444 };
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).eq("2").nextLevel().startAt("3")
                .inclusive(false).objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue("i="+ i, iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEqAndStart3() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("string/unicode").field("to")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", "3", 100))
             .put("/p/2", new Payment2("2", "1", 200))
             .put("/p/3", new Payment2("1", "3", 300))
             .put("/p/4", new Payment2("1", "2", 400))
             .put("/p/6", new Payment2("3", "0", 333))
             .put("/p/6", new Payment2("2", "4", 444))
             .put("/p/5", new Payment2("2", "1", 0)).execute();
        
        long[] expected = new long[] { 100, 0, 200 };
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).eq("2").nextLevel().startAt("3").backward()
                .objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue("i="+ i, iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEqAndStart4() {
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("string/unicode").field("to")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("2", "3", 100))
             .put("/p/2", new Payment2("2", "1", 200))
             .put("/p/3", new Payment2("1", "3", 300))
             .put("/p/4", new Payment2("1", "2", 400))
             .put("/p/6", new Payment2("3", "0", 333))
             .put("/p/6", new Payment2("2", "4", 444))
             .put("/p/5", new Payment2("2", "1", 0)).execute();
        
        long[] expected = new long[] { 0, 200 };
        
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).eq("2").nextLevel().startAt("3")
                .backward().inclusive(false).objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue("i="+ i, iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEqAndStart5() {
        // eq and startAt with string-long composite index.
        
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("1", 100))
             .put("/p/2", new Payment2("2", 200))
             .put("/p/3", new Payment2("1", 300))
             .put("/p/3b", new Payment2("1", 300))
             .put("/p/4", new Payment2("1", 400))
             .put("/p/5", new Payment2("1", 0)).execute();
        
        long[] expected = new long[]{100, 300, 300, 400};
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class)
                .eq("1").nextLevel()
                .startAt(1)
                .objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        expected = new long[]{400, 300, 300, 100, 0};
        iter = c.useIndex("i0", Payment2.class)
                .eq("1").nextLevel()
                .startAt(999)
                .backward().objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEqAndStart6() {
        // eq and startAt with string-long composite index. backward().exclude().
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new Payment2("1", 100))
             .put("/p/2", new Payment2("2", 200))
             .put("/p/3", new Payment2("1", 300))
             .put("/p/3b", new Payment2("1", 300))
             .put("/p/4", new Payment2("1", 400))
             .put("/p/5", new Payment2("1", 0)).execute();
        
        long[] expected = new long[]{300, 300, 100, 0};
        Iterator<Payment2> iter = c.useIndex("i0", Payment2.class).backward().inclusive(false)
                .eq("1").nextLevel()
                .startAt(400)
                .objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEqAndStart7() {
        // eq and startAt with string-double composite index. backward().exclude().
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("double").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new DPayment2("1", 100.0))
             .put("/p/2", new DPayment2("2", 200.0))
             .put("/p/3", new DPayment2("1", 300.0))
             .put("/p/3b", new DPayment2("1", 300.0))
             .put("/p/4", new DPayment2("1", 400.0))
             .put("/p/5", new DPayment2("1", 0.0)).execute();
        
        double[] expected = new double[]{300.0, 300.0, 100.0, 0.0};
        Iterator<DPayment2> iter = c.useIndex("i0", DPayment2.class).backward().inclusive(false)
                .eq("1").nextLevel()
                .startAt(400.0)
                .objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            DPayment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEqAndStart8() {
        // eq and startAt with string-double composite index. Uses Double.NEGATIVE_INFINITY
        // and POSITIVE_INFINITY.
        
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("i0").dir("/p/")
            .type("string/unicode").field("from")
            .type("double").field("time")
            .start().join();
        Connection c = database.newConnection();
        c.w().put("/p/1", new DPayment2("1", 100.0))
             .put("/p/2", new DPayment2("2", 200.0))
             .put("/p/3", new DPayment2("1", -99.9))
             .put("/p/3b", new DPayment2("1", 300.0))
             .put("/p/4", new DPayment2("1", Double.POSITIVE_INFINITY))
             .put("/p/5", new DPayment2("1", 0.0)).execute();
        
        double[] expected = new double[]{-99.9, 0.0, 100, 300.0, Double.POSITIVE_INFINITY};
        Iterator<DPayment2> iter = c.useIndex("i0", DPayment2.class)
                .eq("1").nextLevel()
                .startAt(Double.NEGATIVE_INFINITY)
                .objects().iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            DPayment2 p = iter.next();
            Assert.assertEquals(expected[i], p.time);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void tricky1() {
        // A tricky composite sort. Example with four keys.
        //
        //   string  long
        //   a       Long.MAX 
        //   ab      1         
        //   ab      2         
        //   ab\0    0       
        //
        // The strings "ab" and "ab\0" will not sort differently unless we use "Ln" level.
        //
        
        if (!IcuInfo.hasIcu()) {
            return;
        }
        
        Payment2 p4 = new Payment2("a", "4", Long.MAX_VALUE);
        Payment2 p3 = new Payment2("ab", "3", 1);
        Payment2 p2 = new Payment2("ab", "2", 2);
        Payment2 p1 = new Payment2("ab\0", "1", 0);
        
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("a").dir("/p/")
            .type("string/en/Ln").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        
        c.w().put("/p/1", p1)
            .put("/p/2", p2)
            .put("/p/3", p3)
            .put("/p/4", p4)
            .execute();
        
        String[] expected = new String[] { "4", "3", "2", "1" };
        
        Iterator<Payment2> iter = c.useIndex("a", Payment2.class).objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.to);
        }
        
        database.stop();
    }
    
    @T
    public static void tricky2() {
        // A tricky composite sort. Example with "string/unicode".
        //
        //   string  long
        //   a       Long.MAX 
        //   ab      1         
        //   ab      2         
        //   ab\0    0       
        //
        // This will work since UTF-8 bytes are each increased by 1.
        //
        
        Payment2 p4 = new Payment2("a", "4", Long.MAX_VALUE);
        Payment2 p3 = new Payment2("ab", "3", 1);
        Payment2 p2 = new Payment2("ab", "2", 2);
        Payment2 p1 = new Payment2("ab\0", "1", 0);
        
        TestClock clock = new TestClock();
        clock.setTime(10);
        Database database = Factory.database().memory().clock(clock).start();
        database.indexBuilder("a").dir("/p/")
            .type("string/unicode").field("from")
            .type("long").field("time")
            .start().join();
        Connection c = database.newConnection();
        
        c.w().put("/p/1", p1)
            .put("/p/2", p2)
            .put("/p/3", p3)
            .put("/p/4", p4)
            .execute();
        
        String[] expected = new String[] { "4", "3", "2", "1" };
        
        Iterator<Payment2> iter = c.useIndex("a", Payment2.class).objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment2 p = iter.next();
            Assert.assertEquals(expected[i], p.to);
        }
        
        database.stop();
    }
    
    public static void main(String[] args) {
        //
    }
}
