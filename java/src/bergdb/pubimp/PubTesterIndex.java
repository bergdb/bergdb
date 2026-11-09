package bergdb.pubimp;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import bergdb.common.EventToWaitFor;
import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbConstants;
import bergdb.core.Trans;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.*;
import bergdb.pub.DbObject;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.stream.MemoryStream;

/**
 * Tests secondary indexing for Layer Pub.
 * 
 * @author Frans Lundberg
 */
public class PubTesterIndex { 
    /**
     * Test class - payment with 'long' amount.
     */
    public static class Payment {
        public String from;
        public String to;
        public long amount;
        
        @SuppressWarnings("unused")
        public Payment() {}
        
        public Payment(String from, String to, long amount) {
            this.from = from;
            this.to = to;
            this.amount = amount;
        }
        
        public String toString() {
            return amount + " paid from " + from + " to " + to + ".";
        }
    }
    
    /**
     * Test class - payment with 'int' amount.
     */
    public static class IPayment {
        public String from;
        public String to;
        public int amount;
        
        @SuppressWarnings("unused")
        public IPayment() {}
        
        public IPayment(String from, String to, int amount) {
            this.from = from;
            this.to = to;
            this.amount = amount;
        }
        
        public String toString() {
            return amount + " paid from " + from + " to " + to + ".";
        }
    }
    
    /**
     * Test class - payment with 'double' amount.
     */
    public static class DPayment {
        public String from;
        public String to;
        public double amount;
        
        public DPayment() {}
        
        public DPayment(String from, String to, double amount) {
            this.from = from;
            this.to = to;
            this.amount = amount;
        }
        
        public String toString() {
            return amount + " paid from " + from + " to " + to + ".";
        }
    }
    
    /**
     * Test class - payment with 'float' amount.
     */
    public static class FPayment {
        public String from;
        public String to;
        public float amount;
        
        @SuppressWarnings("unused")
        public FPayment() {}
        
        public FPayment(String from, String to, float amount) {
            this.from = from;
            this.to = to;
            this.amount = amount;
        }
        
        public String toString() {
            return amount + " paid from " + from + " to " + to + ".";
        }
    }
    
    @Nano
    public static void test0() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from")
            .start().join();
        
        Payment p1 = new Payment("1001", "1002", 20);
        
        c.w().put("/payments/1", p1).execute();
        
        Iterator<Payment> iter;
        
        iter = c.useIndex("payments-from", Payment.class).objects().iterator();
        
        long[] expected = { 20 };
      
        for (int i = 0; i < expected.length; i++) {
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void test1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from")
            .start().join();
        
        c.w().put("/payments/2", new Payment("10", "pelle", 46))
             .put("/payments/1", new Payment("20", "jöns", 90))
             .execute();
        
        ArrayList<Payment> list = new ArrayList<Payment>();
        for (Payment p : c.useIndex("payments-from", Payment.class).objects()) {
            list.add(p);
        }
        
        db.stop();
        
        Assert.assertEquals("10", list.get(0).from);
        Assert.assertEquals("20", list.get(1).from);
    }
    
    @Nano
    public static void test2() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from")
            .start().join();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1002", "1009", 30);
        final Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1", p1)
            .put("/payments/2", p2)
            .put("/payments/3", p3).execute();
        
        Iterable<Payment> payments = c.useIndex("payments-from", Payment.class).eq("1001").objects();
        Iterator<Payment> iter = payments.iterator();
        
        Assert.assertTrue("has next 1", iter.hasNext());
        Payment p = iter.next();
        Assert.assertTrue("p != null check", p != null);
        Assert.assertEquals(20, p.amount);
        Assert.assertEquals("1001", p.from);
        Assert.assertEquals("1002", p.to);
        
        Assert.assertTrue("has next 2", iter.hasNext());
        p = iter.next();
        Assert.assertEquals(40, p.amount);
        Assert.assertEquals("1001", p.from);
        Assert.assertEquals("1009", p.to);
        
        Assert.assertFalse("has next 3", iter.hasNext());
        
        db.stop();
    }
    
    @Nano
    public static void testNonObjects1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        db.indexBuilder("payments-to").dir("/payments/").type("string").field("to").start().join();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1", p1)
            .put("/payments/2", p2)
            .put("/payments/3", p3)
            .put("/payments/1b.txt", "1b - my text.")
            .put("/payments/2.txt", "2.txt - another string")
            .execute();
        
        Iterable<Payment> payments2 = c.useIndex("payments-from", Payment.class).eq("1002").objects();
        
        Iterator<Payment> iter = payments2.iterator();
        Assert.assertTrue(iter.hasNext());
        Payment p = iter.next();
        Assert.assertEquals(30, p.amount);
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testNonObjects2() {
        //
        // Index creation after KVs have been addded.
        //
        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/10", p1)
            .put("/payments/20", p2)
            .put("/payments/22", new byte[]{8})
            .put("/payments/30", p3)
            .execute();
        
        // Hack to add value that is not a DbObject, but starts with DbObject.HEADER.
        
        Db db = ((DatabaseImp) database).getDb();
        byte[] value = new byte[] {DbObject.HEADER, 'a', 'b'};
        Trans trans = db.trans().put(Keys.toBytes(PubKeys.u2i("/payments/1b")), value).build();
        db.execute(trans);

        // Create index
        
        database.indexBuilder("payments-from").dir("/payments/").type("string").field("from")
            .start().join();
        
        Iterable<Payment> payments = c.useIndex("payments-from", Payment.class).objects();
        Iterator<Payment> iter = payments.iterator();
        
        Assert.assertEquals(20, iter.next().amount);
        Assert.assertEquals(40, iter.next().amount);
        Assert.assertEquals(30, iter.next().amount);
        
        database.stop();
    }
    
    @Nano
    public static void testTypeMix() {
        // Using DbObject.class as iteration type is a special case.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        
        Payment p10 = new Payment("1010", "1002", 20);
        Payment p20 = new Payment("1020", "1009", 30);
        Payment p30 = new Payment("1010", "1008", 40);
        DPayment p15 = new DPayment("1015", "1000", 12.3);
        
        c.w().put("/payments/p10", p10)
            .put("/payments/p20", p20)
            .put("/payments/p30", p30)
            .put("/payments/p15", p15)
            .execute();
        
        Iterator<DbObject> it = c.useIndex("payments-from", DbObject.class).objects().iterator();
        DbObject t = it.next();
        Assert.assertEquals("1002", t.getString("to"));
        t = it.next();
        Assert.assertEquals("1008", t.getString("to"));
        t = it.next();
        DPayment p15b = t.toJavaObject(DPayment.class);
        Assert.assertEquals("1000", t.getString("to"));
        Assert.assertEquals("1000", p15b.to);
        Assert.assertEquals(12.3, p15b.amount);
        t = it.next();
        Assert.assertEquals("1009", t.getString("to"));
        db.stop();
    }
    
    @Nano
    public static void testBackward1() {
        // Simple case with backward().
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from")
            .start().join();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        
        c.w().put("/payments/1", p1)
            .put("/payments/2", p2).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).backward()
                .objects().iterator();
        long[] expected = { 30, 20 };
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Assert.assertEquals(expected[i], iter.next().amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testBackward1b() {
        // Like testBackward1, but with double field instead.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("i1").dir("/payments/").type("double").field("value")
            .start().join();
        
        MyDouble p1 = new MyDouble(20);
        MyDouble p2 = new MyDouble(30);
        
        c.w().put("/payments/1", p1)
            .put("/payments/2", p2).execute();
        
        Iterator<MyDouble> iter = c.useIndex("i1", MyDouble.class).backward()
                .objects().iterator();
        double[] expected = { 30, 20 };
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Assert.assertEquals(expected[i], iter.next().value);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testBackward2() {
        // 3 elements, two has same indexed value, no eq()
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from")
            .start().join();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1", p1)
            .put("/payments/2", p2)
            .put("/payments/3", p3).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).backward()
                .objects().iterator();
        long[] expected = { 30, 40, 20 };
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Assert.assertEquals(expected[i], iter.next().amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testBackward3() {
        // backward(), empty iterator.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from")
            .start().join();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).backward()
                .objects().iterator();
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testBackward4() {
        // backward() and eq()
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from")
            .start().join();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1", p1)
            .put("/payments/2", p2)
            .put("/payments/3", p3).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).eq("1001").backward()
                .objects().iterator();
        long[] expected = { 40, 20 };
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Assert.assertEquals(expected[i], iter.next().amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testIterHistory() {
        TestClock clock = new TestClock();
        clock.setTime(Time.units(100));
        Database db = Factory.database().memory().clock(clock).start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        
        clock.setTime(Time.units(200));
        
        c.w().put("/payments/10", new Payment("1001", "1002", 10))
            .put("/payments/20", new Payment("1002", "1009", 20))
            .put("/payments/30", new Payment("1001", "1009", 30))
            .execute();
        
        clock.setTime(Time.units(300));
        
        c.w().put("/payments/12", new Payment("1001", "1012", 12))
            .put("/payments/30", new Payment("1001", "1030", 31))
            .put("/payments/40", new Payment("1001", "1040", 40))
            .execute();
        
        c.setLookupTime(Time.units(250));
        Iterable<Payment> it = c.useIndex("payments-from", Payment.class).eq("1001").objects();
        Iterator<Payment> iter = it.iterator();
        Assert.assertTrue(iter.hasNext());
        Assert.assertEquals(10, iter.next().amount);
        Assert.assertTrue(iter.hasNext());
        Assert.assertEquals(30, iter.next().amount);
        Assert.assertFalse(iter.hasNext());
        
        c.setLookupTime(Time.units(350));
        it = c.useIndex("payments-from", Payment.class).eq("1001").objects();
        iter = it.iterator();
        
        long[] expected = new long[]{10, 12, 31, 40};
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Assert.assertEquals(expected[i], iter.next().amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testNonExistantIndex() {
        TestClock clock = new TestClock();
        clock.setTime(Time.units(100));
        Database db = Factory.database().memory().clock(clock).start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        
        clock.setTime(Time.units(200));
        
        c.w().put("/payments/10", new Payment("1001", "1002", 10))
            .put("/payments/20", new Payment("1002", "1009", 20))
            .put("/payments/30", new Payment("1001", "1009", 30))
            .execute();
        
        Exception ex = null;
        
        try {
            c.setLookupTime(Time.units(50));
            c.useIndex("payments-from", Payment.class);
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex instanceof NoSuchIndexException);
        ex = null;
        
        try {
            c.setLookupTime(Time.units(500));
            c.useIndex("payments-from", Payment.class);
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        
        Assert.assertNull(ex);
        db.stop();
    }
    
    
    
    @Nano
    public static void testNegLongs1() {
        // Tests index including negative long integers.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-amount").dir("/payments/").type("long").field("amount").start().join();
        
        c.w().put("/payments/1", new Payment("1", "2", -100))
            .put("/payments/2", new Payment("1", "3", 0))
            .put("/payments/3", new Payment("1", "4", 90)).execute();
        
        Iterable<Payment> payments = c.useIndex("payments-amount", Payment.class).objects();
        
        long expected[] = new long[]{-100, 0, 90};
        Iterator<Payment> iter = payments.iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testNegLongs2() {
        // Tests index including negative long integers.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-amount").dir("/payments/").type("long").field("amount").start().join();
        
        c.w().put("/payments/1", new Payment("1", "1", -100))
            .put("/payments/2", new Payment("1", "2", 0))
            .put("/payments/3", new Payment("1", "3", 90))
            .put("/payments/4", new Payment("1", "4", Long.MIN_VALUE))
            .put("/payments/5", new Payment("1", "5", Long.MAX_VALUE))
            .put("/payments/6", new Payment("1", "6", -1))
            .put("/payments/7", new Payment("1", "7", -23))
            .execute();
        
        Iterable<Payment> payments = c.useIndex("payments-amount", Payment.class).objects();
        
        long expected[] = new long[]{Long.MIN_VALUE, -100, -23, -1, 0, 90, Long.MAX_VALUE};
        Iterator<Payment> iter = payments.iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    public static class MyDouble {
        public double value;
        
        public MyDouble() {}
        
        public MyDouble(double v) {
            value = v;
        }
    }
    
    @Nano
    public static void testDoubles1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("value").dir("/d/").type("double").field("value").start().join();
        
        c.w().put("/d/1", new MyDouble(1.23))
            .put("/d/2", new MyDouble(3e10))
            .put("/d/3", new MyDouble(1.2e-2))
            .execute();
        
        double[] expected = new double[]{1.2e-2, 1.23, 3e10};
        
        Iterable<MyDouble> doubles = c.useIndex("value", MyDouble.class).objects();
        Iterator<MyDouble> iter = doubles.iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            MyDouble p = iter.next();
            Assert.assertEquals(expected[i], p.value);
        }
        db.stop();
    }
    
    @Nano
    public static void testDoubles2() {
        // With negative values too.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("value").dir("/d/").type("double").field("value").start().join();
        
        double[] values = new double[] {
                Double.MAX_VALUE, 100.0, 1.2, 1.2, 0.0, -10, -300.0, -9e100 };
        
        WBuilder b = c.w();
        for (int i = 0; i < values.length; i++) {
            b.put("/d/" + i, new MyDouble(values[i]));
        }
        b.execute();
        
        double[] expected = new double[] {
                -9e100, -300.0, -10, 0.0, 1.2, 1.2, 100.0, Double.MAX_VALUE };
        
        Iterable<MyDouble> doubles = c.useIndex("value", MyDouble.class).objects();
        Iterator<MyDouble> iter = doubles.iterator();
        
        for (int i = 0; i < values.length; i++) {
            Assert.assertTrue(iter.hasNext());
            MyDouble p = iter.next();
            Assert.assertEquals(expected[i], p.value);
        }
        db.stop();
    }
    
    @Nano
    public static void testDoubles3() {
        // With INFINITY values.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("value").dir("/d/").type("double").field("value").start().join();
        
        double[] values = new double[] {
                Double.POSITIVE_INFINITY, 
                Double.MAX_VALUE, 100.0, 1.2, 1.2, 0.0, -10, -300.0, -9e100,
                Double.NEGATIVE_INFINITY};
        
        WBuilder b = c.w();
        for (int i = 0; i < values.length; i++) {
            b.put("/d/" + i, new MyDouble(values[i]));
        }
        b.execute();
        
        double[] expected = new double[] {
                Double.NEGATIVE_INFINITY,
                -9e100, -300.0, -10, 0.0, 1.2, 1.2, 100.0, Double.MAX_VALUE,
                Double.POSITIVE_INFINITY};
        
        Iterator<MyDouble> iter = c.useIndex("value", MyDouble.class).objects().iterator();
        
        for (int i = 0; i < values.length; i++) {
            Assert.assertTrue(iter.hasNext());
            MyDouble p = iter.next();
            Assert.assertEquals(expected[i], p.value);
        }
        db.stop();
    }
    
    @Nano
    public static void testFloat1() {
        // double and float fields mixed in same "double" index.
        
        Object[] objects = new Object[] {
                new DPayment("1", "", 12.3),
                new FPayment("2", "", 21.1f),
                new FPayment("3", "", 1e6f),
                new DPayment("4", "", 2e6),
                new FPayment("5", "", -111.11f)
        };
        
        String[] expected = new String[] {"5", "1", "2", "3", "4"};
        
        Database d = Factory.database().memory().start();
        d.indexBuilder("i1").dir("/d/").type("double").field("amount").start().join();
        
        Connection c = d.connection();
        WBuilder b = c.w();
        int index = 0;
        for (Object o : objects) {
            b.put("/d/" + index, o);
            index++;
        }
        b.execute();
        
        // Checks database sort order.
        index = 0;
        for (DbObject to : c.useIndex("i1", DbObject.class).objects()) {
            Assert.assertTrue(to.has("from", 's'));
            Assert.assertEquals(expected[index], to.getString("from"));
            index++;
        }
        
        // Checks double/float field values
        Iterator<DbObject> it = c.useIndex("i1", DbObject.class).objects().iterator();
        Assert.assertEquals(-111.11f, (float) it.next().getDouble("amount"));
        Assert.assertEquals(12.3, it.next().getDouble("amount"));
        Assert.assertEquals(21.1f, (float) it.next().getDouble("amount"));
        Assert.assertEquals(1e6f, (float) it.next().getDouble("amount"));
        Assert.assertEquals(2e6, it.next().getDouble("amount"));
        d.stop();
    }
    
    @Nano
    public static void testIntAndLongMixed() {
        // long and int fields mixed in same "long" index.
        
        Object[] objects = new Object[] {
                new IPayment("1", "", 12),
                new Payment("2", "", 21),
                new Payment("3", "", 1000),
                new IPayment("4", "", 2000),
                new IPayment("5", "", -111)
        };
        
        String[] expected = new String[] {"5", "1", "2", "3", "4"};
        
        Database d = Factory.database().memory().start();
        d.indexBuilder("i1").dir("/d/").type("long").field("amount").start().join();
        
        Connection c = d.connection();
        WBuilder b = c.w();
        int index = 0;
        for (Object o : objects) {
            b.put("/d/" + index, o);
            index++;
        }
        b.execute();
        
        // Checks database sort order.
        index = 0;
        for (DbObject to : c.useIndex("i1", DbObject.class).objects()) {
            Assert.assertTrue(to.has("from", 's'));
            Assert.assertEquals(expected[index], to.getString("from"));
            index++;
        }
        
        // Checks field values
        Iterator<DbObject> it = c.useIndex("i1", DbObject.class).objects().iterator();
        Assert.assertEquals(-111, it.next().getInt("amount"));
        Assert.assertEquals(12, it.next().getInt("amount"));
        Assert.assertEquals(21, it.next().getLong("amount"));
        Assert.assertEquals(1000, it.next().getLong("amount"));
        Assert.assertEquals(2000, it.next().getInt("amount"));
        d.stop();
    }
    
    public static class MyString {
        public String s;
        
        public MyString() {}
        
        public MyString(String s) {
            this.s = s;
        }
    }
    
    @Nano
    public static void testRestart1() {
        MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        Database db = builder.start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1002", "1009", 30);
        final Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1", p1).put("/payments/2", p2).put("/payments/3", p3).execute();
        
        Iterable<Payment> payments = c.useIndex("payments-from", Payment.class).eq("1001").objects();
        Iterator<Payment> iter = payments.iterator();
        
        Assert.assertTrue(iter.hasNext());
        Payment p = iter.next();
        Assert.assertTrue("p != null check", p != null);
        Assert.assertEquals(20, p.amount);
        Assert.assertEquals("1001", p.from);
        Assert.assertEquals("1002", p.to);
        
        Assert.assertTrue(iter.hasNext());
        p = iter.next();
        Assert.assertEquals(40, p.amount);
        Assert.assertEquals("1001", p.from);
        Assert.assertEquals("1009", p.to);
        
        Assert.assertFalse(iter.hasNext());
        
        // Restarts the database and does the checks again.

        db.sync();
        db.stop();
        db = null;
        c = null;
        builder = null;
        
        stream = stream.copy();
        
        DatabaseBuilder builder2 = Factory.database();
        ((DatabaseBuilderImp) builder2).getDbBuilder().testSetup(stream);
        Database db2 = builder2.start();
        Connection c2 = db2.newConnection();
        
        payments = c2.useIndex("payments-from", Payment.class).eq("1001").objects();
        iter = payments.iterator();
        
        Assert.assertTrue(iter.hasNext());
        p = iter.next();
        Assert.assertTrue("p != null check", p != null);
        Assert.assertEquals(20, p.amount);
        Assert.assertEquals("1001", p.from);
        Assert.assertEquals("1002", p.to);
        
        Assert.assertTrue(iter.hasNext());
        p = iter.next();
        Assert.assertEquals(40, p.amount);
        Assert.assertEquals("1001", p.from);
        Assert.assertEquals("1009", p.to);
        
        Assert.assertFalse(iter.hasNext());
        db2.stop();
    }
    
    @Nano
    public static void testRestart2() {
        MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream);
        Database db = builder.start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        
        Payment p1 = new Payment("1010", "2", 10);
        Payment p2 = new Payment("1000", "2", 20);
        c.w().put("/payments/1", p1).put("/payments/2", p2).execute();
        
        // Restarts the database, adds another indexed object.
        
        db.sync();
        db.stop();
        db = null;
        c = null;
        builder = null;
        
        DatabaseBuilder builder2 = Factory.database();
        ((DatabaseBuilderImp) builder2).getDbBuilder().mainStream(stream);
        Database db2 = builder2.start();
        Connection c2 = db2.newConnection();
        
        Payment p3 = new Payment("1005", "2", 5);
        c2.w().put("/payments/3", p3).execute();
        
        Iterator<Payment> iter = c2.useIndex("payments-from", Payment.class).objects().iterator();
        long[] expected = new long[] { 20, 5, 10 };
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Assert.assertEquals(expected[i], iter.next().amount);
        }
        Assert.assertFalse(iter.hasNext());
        db2.stop();
    }
    
    public static class Name {
        public String first;
        public String last;
    }
    
    public static class NestClass {
        public Name name;
    }
    
    private static NestClass nest(String first, String last) {
        NestClass n = new NestClass();
        n.name = new Name();
        n.name.first = first;
        n.name.last = last;
        return n;
    }
    
    @Nano
    public static void testRestartWithNestedFieldIndex() {
        MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream);
        Database db = builder.start();
        Connection c = db.newConnection();
        
        db.indexBuilder("name-last").dir("/d/").type("string").nestedField("name.last").start().join();
        
        c.w().put("/d/1", nest("Fredrik", "Andersson")).put("/d/2", nest("John", "Wickersson"))
            .put("/d/3", nest("Amy", "Dimeon")).execute();
        
        db.sync();
        db.stop();
        db = null;
        c = null;
        builder = null;
        
        // Restarts the database.
        
        DatabaseBuilder builder2 = Factory.database();
        ((DatabaseBuilderImp) builder2).getDbBuilder().mainStream(stream);
        Database db2 = builder2.start();
        Connection c2 = db2.newConnection();
        
        Iterator<NestClass> iter = c2.useIndex("name-last", NestClass.class).objects().iterator();
        String[] expected = new String[] { "Andersson", "Dimeon", "Wickersson" };
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            String lastName = iter.next().name.last;
            Assert.assertEquals(expected[i], lastName);
        }
        Assert.assertFalse(iter.hasNext());
        db2.stop();
    }
    
    @Nano
    public static void testKvDelete() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1002", "1009", 30);
        final Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1", p1).put("/payments/2", p2).put("/payments/3", p3).execute();
        
        // Assert we have index KVs.
        
        Assert.assertEquals(3, getIndexKvCount(db));
        
        // Now, delete all KVs and check that corresponding index entries were deleted too.
        
        c.w().delete("/payments/1").delete("/payments/2").execute();
        
        Assert.assertEquals(1, getIndexKvCount(db));
        
        c.w().delete("/payments/1").delete("/payments/3").execute();
        
        Assert.assertEquals(0, getIndexKvCount(db));
        db.stop();
    }

    private static int getIndexKvCount(Database db) {
        Db db2 = ((DatabaseImp) db).getDb();
        GetMany g = db2.newGetMany();
        final String prefix = DbConstants.INTERNAL_PREFIX + "dient/";   // bergdb 020-10, 4.1
        g.startKey = Keys.toSegments(prefix);
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                String s = Keys.toStringWithSubstitute(Keys.toBytes(kvt.key));
                if (!s.startsWith(prefix)) {
                    return GetMany.StopCondition.STOP;
                }
                return GetMany.StopCondition.ADD;
            }
            
            public void eod() {
            }
        };
        
        db2.getMany(g);
        int count = g.result.size();
        return count;
    }
    
    @Nano
    public static void testWithDeletesAndUpdates() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1002", "1009", 30);
        final Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1", p1).put("/payments/2", p2).put("/payments/3", p3).execute();
        
        final Payment p2b = new Payment("1002", "1019", 31);
        c.w().delete("/payments/1").put("/payments/2", p2b).execute();
        
        Assert.assertEquals(2, getIndexKvCount(db));
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).objects().iterator();
        
        long[] expected = new long[] {40, 31};
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testExistingData1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1002", "1009", 30);
        final Payment p3 = new Payment("1000", "1009", 40);
        c.w().put("/payments/1", p1).put("/payments/2", p2).put("/payments/3", p3).execute();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).objects().iterator();
        
        long[] expected = new long[] {40, 20, 30};
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testExistingData2() {
        // Like "1", but with two indexes.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        final Payment p1 = new Payment("1001", "2002", 20);
        final Payment p2 = new Payment("1002", "2003", 30);
        final Payment p3 = new Payment("1000", "2004", 40);
        c.w().put("/payments/1", p1).put("/payments/2", p2).put("/payments/3", p3).execute();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        db.indexBuilder("payments-to").dir("/payments/").type("string").field("to").start().join();
        
        Iterable<Payment> iterable = c.useIndex("payments-from", Payment.class).objects();
        Iterator<Payment> iter = iterable.iterator();
        long[] expected = new long[] {40, 20, 30};
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        
        iterable = c.useIndex("payments-to", Payment.class).objects();
        iter = iterable.iterator();
        expected = new long[] {20, 30, 40};
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testExistingData3() {
        // Like "2", but new KVs too.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        Payment p1 = new Payment("1010", "2020", 20);
        Payment p2 = new Payment("1020", "2030", 30);
        Payment p3 = new Payment("1000", "2040", 40);
        c.w().put("/payments/1", p1).put("/payments/2", p2).put("/payments/3", p3).execute();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        db.indexBuilder("payments-to").dir("/payments/").type("string").field("to").start().join();
        
        Payment p4 = new Payment("1005", "2019", 50);
        c.w().put("/payments/4", p4).execute();
        
        Iterable<Payment> iterable = c.useIndex("payments-from", Payment.class).objects();
        Iterator<Payment> iter = iterable.iterator();
        long[] expected = new long[] {40, 50, 20, 30};
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        
        iterable = c.useIndex("payments-to", Payment.class).objects();
        iter = iterable.iterator();
        expected = new long[] {50, 20, 30, 40};
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testCreateWhileWriteOps1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        for (int i = 0; i < 20; i++) {
            String id = "" + (1000 + (i * 10));
            Payment p = new Payment("1000", "2000", i * 10);
            c.w().put("/payments/" + id, p).execute();
        }
        
        // The build's steps of 10 values; held before its second step.
        Hold hold = new Hold(db, 10, 2);
        Job job = db.indexBuilder("payments-amount").dir("/payments/").type("long")
                .field("amount").start();
        hold.awaitReached();        // The first step made 10 index entries
        
        // Adds one payment in section handled by index creator.
        Payment p = new Payment("1000", "2000", 15);
        c.w().put("/payments/1015", p).execute();
        
        // Adds one payment in section not yet handled by index creator.
        p = new Payment("1000", "2000", 125);
        c.w().put("/payments/1125", p).execute();
        
        hold.release();
        Assert.assertEquals(JobStatus.State.ACTIVE, job.join().state());
        
        Iterable<Payment> iterable = c.useIndex("payments-amount", Payment.class).objects();
        Iterator<Payment> iter = iterable.iterator();
        
        long[] expected = new long[]{0, 10, 15, 20, 30, 40, 50, 60, 70, 80, 90, 
                100, 110, 120, 125, 130, 140, 150, 160, 170, 180, 190};
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testCreateDuringRestart() throws InterruptedException {
        // 
        // Advanced index test. Checks that index creation survives database restart.
        // Adds entries after restart to provocate the index creation thread that
        // will start when the database is started.
        //
        
        MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream);
        Database db = builder.start();
        Connection c = db.newConnection();
        
        for (int i = 0; i < 20; i++) {
            String id = "" + (1000 + (i * 10));
            Payment p = new Payment("1000", "2000", i * 10);
            c.w().put("/payments/" + id, p).execute();
        }
        
        // The build's steps of 10 values; held before its second step.
        Hold hold = new Hold(db, 10, 2);
        db.indexBuilder("payments-amount").dir("/payments/").type("long").field("amount")
                .start();
        hold.awaitReached();        // The first step made 10 index entries
        
        Exception ex = null;
        try {
            c.useIndex("payments-amount", Payment.class);
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        Assert.assertTrue(ex != null);
        
        // Restart database in the middle of index creation.
        
        db.sync();
        db.stop();
        hold.release();             // Its transaction then finds the database stopped
        db = null;
        c = null;
        stream = stream.copy();
        
        builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream);
        db = builder.start();
        c = db.newConnection();
        
        // Adds one payment in section already handled by index creator.
        Payment p = new Payment("1000", "2000", 15);
        c.w().put("/payments/1015", p).execute();
        
        // Adds one payment in section not yet handled by index creator.
        p = new Payment("1000", "2000", 125);
        c.w().put("/payments/1125", p).execute();
        
        // The start took the build again, from the first key of the directory.
        Assert.assertEquals(JobStatus.State.ACTIVE, db.indexJob("payments-amount").join()
                .state());
        
        Iterable<Payment> iterable = c.useIndex("payments-amount", Payment.class).objects();
        Iterator<Payment> iter = iterable.iterator();
        
        long[] expected = new long[]{0, 10, 15, 20, 30, 40, 50, 60, 70, 80, 90, 
                100, 110, 120, 125, 130, 140, 150, 160, 170, 180, 190};
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testCreateWhileWriteOps2() {
        // Arrange
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        for (int i = 0; i < 20; i++) {
            String id = "" + (1000 + (i * 10));
            Payment p = new Payment("1000", "2000", i * 10);
            c.w().put("/p/" + id, p).execute();
        }
        
        // Act
        // The build's steps of 10 values; held before its second step.
        Hold hold = new Hold(db, 10, 2);
        Job job = db.indexBuilder("p-amount").dir("/p/").type("long").field("amount").start();
        hold.awaitReached();        // The first step made 10 index entries
        
        // Adds one payment in section handled by index creator.
        Payment p = new Payment("1000", "2000", 15);
        c.w().put("/p/1015", p).execute();
        
        // Modifies one payment in section handled by index creator.
        p = new Payment("1000", "2000", 41);
        c.w().put("/p/1040", p).execute();
        
        // Deletes one payment in section handled by index creator.
        c.w().delete("/p/1060").execute();
        
        // Adds one payment in section not yet handled by index creator.
        p = new Payment("1000", "2000", 125);
        c.w().put("/p/1125", p).execute();
        
        // Modifies one payment in section not yet handled by index creator.
        p = new Payment("1000", "2000", 141);
        c.w().put("/p/1140", p).execute();
        
        // Deletes one payment in section not yet handled by index creator.
        c.w().delete("/p/1160").execute();
        
        hold.release();
        Assert.assertEquals(JobStatus.State.ACTIVE, job.join().state());
        
        // Assert
        long[] expected = new long[] {0, 10, 15, 20, 30, 41, 50, 70, 80, 90, 
                100, 110, 120, 125, 130, 141, 150, 170, 180, 190};
        
        Iterable<Payment> iterable = c.useIndex("p-amount", Payment.class).objects();
        Iterator<Payment> iter = iterable.iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testManyObjects() {
        // Tests index with more than 100 objects. DB.getMany() must be called more than once.
        
        // Arrange/Act
        int n = 150;
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        WBuilder b = c.w();
        
        db.indexBuilder("p-amount").dir("/p/").type("long").field("amount").start().join();
        
        for (int i = 0; i < n; i++) {
            String id = "" + (1000 + (i * 10));
            Payment p = new Payment("1", "2", i * 10);
            b.put("/p/" + id, p);
            
            if (i % 10 == 9 || i == (n - 1)) {
                b.execute();
                b = c.w();
            }
        }
        
        // Assert
        Iterator<Payment> iter = c.useIndex("p-amount", Payment.class).objects().iterator();
        
        for (int i = 0; i < n; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(i * 10, p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testDeleteIndex1() {
        // Arrange
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        database.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1000", "1009", 40);
        
        c.w().put("/payments/1", p1).put("/payments/2", p2).execute();
        
        c.useIndex("payments-from", Payment.class).objects();
        
        // Act
        
        database.deleteIndex("payments-from");
        PubTesterIndexRaces.awaitCleanups(((DatabaseImp) database).getIndexManager());
        
        // Assert
        
        Exception ex = null;
        try {
            c.useIndex("payments-from", Payment.class).objects();
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        Assert.assertTrue("Got NoSuchIndexException?", ex != null);
        
        byte[] indexDbDir = Keys.toBytes("/#i/dient/dpayments-from/");  // every generation
        Db db = ((DatabaseImp) database).getDb();
        
        final GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments(indexDbDir);
        g.inclusive = false;
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                return Keys.isPrefix(g.startKey, kvt.key) ? 
                        GetMany.StopCondition.ADD : GetMany.StopCondition.STOP;
            }
            
            public void eod() {
            }
        };
        
        
        db.getMany(g);
        Assert.assertEquals(0, g.result.size());
        
        database.stop();
    }
    
    @Nano
    public static void testDeleteIndex2() throws InterruptedException {
        // Arrange
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        database.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1000", "1009", 40);
        
        c.w().put("/payments/1", p1).put("/payments/2", p2).execute();
        
        c.useIndex("payments-from", Payment.class).objects();
        
        // Act
        
        database.deleteIndex("payments-from");
        PubTesterIndexRaces.awaitCleanups(((DatabaseImp) database).getIndexManager());
        
        // Assert
        
        Exception ex = null;
        try {
            c.useIndex("payments-from", Payment.class).objects();
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        Assert.assertTrue("Got NoSuchIndexException?", ex != null);
        
        byte[] indexDbDir = Keys.toBytes("/#i/dient/dpayments-from/");  // every generation
        Db db = ((DatabaseImp) database).getDb();
        final GetMany g = db.newGetMany();
        
        g.startKey = Keys.toSegments(indexDbDir);
        g.inclusive = false;
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                return Keys.isPrefix(g.startKey, kvt.key) ? 
                        GetMany.StopCondition.ADD : GetMany.StopCondition.STOP;
            }
            
            public void eod() {
            }
        };
        
        
        db.getMany(g);
        Assert.assertEquals(0, g.result.size());
        
        database.stop();
    }
    
    @Nano
    public static void testCreateInThread1() throws InterruptedException {
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1000", "1009", 40);
        Payment p3 = new Payment("1009", "2000", 50);
        
        c.w().put("/payments/1", p1).put("/payments/2", p2).execute();
        
        Job job = database.indexBuilder("payments-from").dir("/payments/").type("string")
                .field("from").start();
        c.w().put("/payments/3", p3).execute();
        job.join();
        
        // Assert
        long[] expected = new long[]{40, 20, 50};
        
        Iterable<Payment> iterable = c.useIndex("payments-from", Payment.class).objects();
        Iterator<Payment> iter = iterable.iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @Nano
    public static void testCreateInThread2() throws InterruptedException {
        // This test uses an EventToWaitFor to test concurrency.
        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1000", "1009", 40);
        Payment p3 = new Payment("1009", "2000", 50);
        
        c.w().put("/payments/1", p1).put("/payments/2", p2).execute();
        
        // The build is held before its first step.
        Hold hold = new Hold(database, 0, 1);
        Job job = database.indexBuilder("payments-from").dir("/payments/").type("string")
                .field("from").start();
        hold.awaitReached();
        c.w().put("/payments/3", p3).execute();
        hold.release();
        job.join();
        
        // Assert
        long[] expected = new long[]{40, 20, 50};
        
        Iterable<Payment> iterable = c.useIndex("payments-from", Payment.class).objects();
        Iterator<Payment> iter = iterable.iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @Nano
    public static void testKeyReplaceWithIndex() {
        TestClock clock = new TestClock();
        Database database = Factory.database().memory().clock(clock).start();
        Connection c = database.newConnection();
        String key = "/payments/${transactionTime}";
        
        database.indexBuilder("payments-from").dir("/payments/").type("string").field("from").start().join();
        c.setEnableKeyReplace(true);
        clock.setTime(Time.units(100));
        c.w().put(key, new Payment("101", "105", 5)).execute();
        clock.setTime(Time.units(200));
        c.w().put(key, new Payment("100", "106", 6)).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(6, p.amount);
        p = iter.next();
        Assert.assertEquals(5, p.amount);
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    /**
     * A put with key replace at /payments/${transactionTime} writes another key than the key
     * as written (bergdb 020-13, bug 3): a value at the key as written, put with key replace
     * off, keeps its entry. Before, the put read that value as its previous one and deleted
     * its entry, while the value stayed.
     */
    @Nano
    public static void testKeyReplaceKeepsTheEntryOfTheKeyAsWritten() {
        TestClock clock = new TestClock();
        Database database = Factory.database().memory().clock(clock).start();
        try {
            Connection c = database.newConnection();
            String key = "/payments/${transactionTime}";
            database.indexBuilder("payments-from").dir("/payments/").type("string")
                    .field("from").start().join();
            clock.setTime(Time.units(100));
            c.w().put(key, new Payment("101", "105", 5)).execute();     // key replace off
            c.setEnableKeyReplace(true);
            clock.setTime(Time.units(200));
            c.w().put(key, new Payment("100", "106", 6)).execute();
            
            StringBuilder b = new StringBuilder();
            for (Kv<Payment> kv : c.useIndex("payments-from", Payment.class).kvs()) {
                b.append(kv.key()).append('=').append(kv.value().amount).append(' ');
            }
            Assert.assertEquals("/payments/000000000000000200=6 /payments/${transactionTime}=5 ",
                    b.toString());
        } finally {
            database.stop();
        }
    }
    
    @Nano
    public static void testStartAt1() {
        // forward, include
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("payments-from").dir("/payments/").type("string")
            .field("from").start().join();
        
        c.w().put("/payments/1", new Payment("101", "105", 1)).execute();
        c.w().put("/payments/2", new Payment("100", "106", 2)).execute();
        c.w().put("/payments/3", new Payment("099", "106", 3)).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).from("100", true)
                .objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(2, p.amount);
        p = iter.next();
        Assert.assertEquals(1, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void testStartAt2() {
        // forward, exclude
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("pay-from").dir("/payments/").type("string")
            .field("from").start().join();
        
        c.w().put("/payments/1", new Payment("101", "105", 1)).execute();
        c.w().put("/payments/2", new Payment("100", "106", 2)).execute();
        c.w().put("/payments/3", new Payment("099", "106", 3)).execute();
        
        Iterator<Payment> iter = c.useIndex("pay-from", Payment.class).from("100", false).objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(1, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void testStartAt3() {
        // backward, include
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("payments-from").dir("/payments/").type("string")
            .field("from").start().join();
        
        c.w().put("/payments/1", new Payment("101", "105", 1)).execute();
        c.w().put("/payments/2", new Payment("100", "106", 2)).execute();
        c.w().put("/payments/3", new Payment("099", "106", 3)).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).to("100", true).backward().objects().iterator();
        
        Payment p = iter.next();
        Assert.assertEquals(2, p.amount);
        p = iter.next();
        Assert.assertEquals(3, p.amount);
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @Nano
    public static void testStartAt4() {
        // backward, exclude
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("payments-from").dir("/payments/").type("string")
            .field("from").start().join();
        
        c.w().put("/payments/1", new Payment("101", "105", 1)).execute();
        c.w().put("/payments/2", new Payment("100", "106", 2)).execute();
        c.w().put("/payments/3", new Payment("099", "106", 3)).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).to("100", false).backward().objects().iterator();
        
        Payment p = iter.next();
        Assert.assertEquals(3, p.amount);
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @Nano
    public static void testStartAtLong1() {
        // forward, include, long index
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").dir("/payments/").type("long")
            .field("amount").start().join();
        
        c.w().put("/payments/20", new Payment("101", "105", 20)).execute();
        c.w().put("/payments/30", new Payment("100", "106", 30)).execute();
        c.w().put("/payments/10", new Payment("099", "106", 10)).execute();
        
        Iterator<Payment> iter = c.useIndex("i0", Payment.class).from(20, true).objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(20, p.amount);
        p = iter.next();
        Assert.assertEquals(30, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void tStartAtLong2a() {
        // forward, include, long index
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("aaa").dir("/payments/").type("long")
            .field("amount").start().join();
        
        c.w().put("/payments/20", new Payment("101", "105", 20)).execute();
        c.w().put("/payments/30", new Payment("100", "106", 30)).execute();
        c.w().put("/payments/10", new Payment("099", "106", 10)).execute();
        
        Iterator<Payment> iter = c.useIndex("aaa", Payment.class).from(20, false)
                .objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(30, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void tStartAtLong2b() {
        // forward, include, long index
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("bb").dir("/payments/").type("long")
            .field("amount").start().join();
        
        c.w().put("/payments/20", new Payment("101", "105", 20)).execute();
        c.w().put("/payments/30", new Payment("100", "106", 30)).execute();
        c.w().put("/payments/10", new Payment("099", "106", 10)).execute();
        
        Iterator<Payment> iter = c.useIndex("bb", Payment.class).from(20, false)
                .objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(30, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void tStartAtLong2c() {        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("cc").dir("/p/").type("long")
            .field("amount").start().join();
        
        c.w().put("/p/a", new Payment("", "", 2)).execute();
        c.w().put("/p/b", new Payment("", "", 4)).execute();
        c.w().put("/p/c", new Payment("", "", 6)).execute();
        
        Iterator<Payment> iter = c.useIndex("cc", Payment.class).from(4, false)
                .objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(6, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void testStartAtLong3() {
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i11").dir("/payments/").type("long")
            .field("amount").start().join();
        
        c.w().put("/payments/20", new Payment("101", "105", -20)).execute();
        c.w().put("/payments/30", new Payment("100", "106", -30)).execute();
        c.w().put("/payments/10", new Payment("099", "106", 10)).execute();
        
        Iterator<Payment> iter = c.useIndex("i11", Payment.class).from(-25, false)
                .objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(-20, p.amount);
        p = iter.next();
        Assert.assertEquals(10, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        iter = c.useIndex("i11", Payment.class).to(10, false).backward()
                .objects().iterator();
        p = iter.next();
        Assert.assertEquals(-20, p.amount);
        p = iter.next();
        Assert.assertEquals(-30, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void testEqLong1() {
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").dir("/payments/").type("long")
            .field("amount").start().join();
        
        c.w().put("/payments/10", new Payment("101", "105", 10)).execute();
        c.w().put("/payments/20", new Payment("100", "106", 20)).execute();
        c.w().put("/payments/30", new Payment("099", "106", 20)).execute();
        
        Iterator<Payment> iter = c.useIndex("i0", Payment.class).eq(20).objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals("100", p.from);
        p = iter.next();
        Assert.assertEquals("099", p.from);
        Assert.assertFalse(iter.hasNext());
        
        iter = c.useIndex("i0", Payment.class).eq(10).objects().iterator();
        p = iter.next();
        Assert.assertEquals("101", p.from);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void testEqLong2() {
        // Same as previous, but uses backward().
        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").dir("/payments/").type("long")
            .field("amount").start().join();
        
        c.w().put("/payments/10", new Payment("101", "105", 10)).execute();
        c.w().put("/payments/20", new Payment("100", "106", 20)).execute();
        c.w().put("/payments/30", new Payment("099", "106", 20)).execute();
        
        Iterator<Payment> iter = c.useIndex("i0", Payment.class).eq(20).backward().objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals("099", p.from);
        p = iter.next();
        Assert.assertEquals("100", p.from);
        Assert.assertFalse(iter.hasNext());
        
        iter = c.useIndex("i0", Payment.class).eq(10).backward().objects().iterator();
        p = iter.next();
        Assert.assertEquals("101", p.from);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void testLongs256() {
        // Tests an index with all byte values 0..255 in a long.
        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").dir("/payments/").type("long")
            .field("amount").start().join();
        
        WBuilder b = c.w();
        for (int i = 0; i < 256; i++) {
            b.put("/payments/" + i, new Payment("" + i, "" + (i+1), i));
        }
        b.execute();
        
        Iterator<Payment> iter = c.useIndex("i0", Payment.class).objects().iterator();
        for (int i = 0; i < 256; i++) {
            Assert.assertTrue("i=" + i, iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals("i=" + i, i, p.amount);
        }
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void testEqDouble1() {
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").dir("/payments/").type("double")
            .field("amount").start().join();
        
        c.w().put("/payments/10", new DPayment("101", "105", 10.0)).execute();
        c.w().put("/payments/20", new DPayment("100", "106", 20.0)).execute();
        c.w().put("/payments/30", new DPayment("099", "106", 20.0)).execute();
        
        Iterator<DPayment> iter = c.useIndex("i0", DPayment.class).eq(20.0).objects().iterator();
        DPayment p = iter.next();
        Assert.assertEquals("100", p.from);
        p = iter.next();
        Assert.assertEquals("099", p.from);
        Assert.assertFalse(iter.hasNext());
        
        iter = c.useIndex("i0", DPayment.class).eq(10.0).objects().iterator();
        p = iter.next();
        Assert.assertEquals("101", p.from);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void testEqDouble2() {
        // Same as previous, but uses backward().
        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").dir("/payments/").type("double")
            .field("amount").start().join();
        
        c.w().put("/payments/10", new DPayment("101", "105", 10.0)).execute();
        c.w().put("/payments/20", new DPayment("100", "106", 20.0)).execute();
        c.w().put("/payments/30", new DPayment("099", "106", 20.0)).execute();
        
        Iterator<DPayment> iter = c.useIndex("i0", DPayment.class).eq(20.0).backward().objects().iterator();
        DPayment p = iter.next();
        Assert.assertEquals("099", p.from);
        p = iter.next();
        Assert.assertEquals("100", p.from);
        Assert.assertFalse(iter.hasNext());
        
        iter = c.useIndex("i0", DPayment.class).eq(10.0).backward().objects().iterator();
        p = iter.next();
        Assert.assertEquals("101", p.from);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @Nano
    public static void collationUnicode1() {
        String[] strings = new String[] {"a", "alfons", "AB", "AA", "", "B", "\n", "b", "0", "AAA", "~"};
        String[] expected = new String[]{"", "\n", "0", "AA", "AAA", "AB", "B", "a", "alfons", "b", "~"};
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("strings-s").dir("/strings/").type("string").field("s").start().join();
        
        WBuilder b = c.w();
        for (int i = 0; i < strings.length; i++) {
            b.put("/strings/" + i, new MyString(strings[i]));
        }
        b.execute();
        
        Iterable<MyString> iterable = c.useIndex("strings-s", MyString.class).objects();
        Iterator<MyString> iter = iterable.iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            MyString m = iter.next();
            Assert.assertEquals(expected[i], m.s);
        }
        db.stop();
    }
    
    @Nano
    public static void collationUnicode2() {
        // Tests sort order using strings that contain NUL characters (U+0000).
        // Sort is *stable* because of key naming: 0.obj, 1.obj, .., 5.obj.
        
        String[] strings = new String[] {"a", "\u0001", "\u0000", "", "\u0001a", "\u0000a"};
        String[] expected = new String[]{"", "\u0000", "\u0000a", "\u0001", "\u0001a"};
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("strings-s").dir("/strings/").type("string").field("s").start().join();
        
        WBuilder b = c.w();
        for (int i = 0; i < strings.length; i++) {
            b.put("/strings/" + i, new MyString(strings[i]));
        }
        b.execute();
        
        Iterable<MyString> iterable = c.useIndex("strings-s", MyString.class).objects();
        Iterator<MyString> iter = iterable.iterator();
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            MyString m = iter.next();
            Assert.assertEquals(expected[i], m.s);
        }
        
        db.stop();
    }
    
    
    
    
    /**
     * Regression test for bergdb 005-15: a long index value whose low byte is 0xff (255,
     * -1) ends its sort bytes with 0xff, and the start key of an exclusive forward scan, a
     * backward scan and an eq backward scan skipped or added entries.
     */
    @Nano
    public static void testStartKeyCarry() {
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        database.indexBuilder("amount").dir("/payments/").type("long")
            .field("amount").start().join();
        
        long[] values = {-300, -257, -256, -255, -2, -1, 0, 1, 254, 255, 256, 257, 300, 510, 511, 512};
        for (long v : values) {
            c.w().put("/payments/" + v, new Payment("a", "b", v)).execute();
        }
        
        assertAmounts(new long[]{256, 257, 300, 510, 511, 512}, 
                c.useIndex("amount", Payment.class).from(255, false).objects());
        assertAmounts(new long[]{0, 1, 254, 255, 256, 257, 300, 510, 511, 512}, 
                c.useIndex("amount", Payment.class).from(-1, false).objects());
        assertAmounts(new long[]{255, 254, 1, 0, -1, -2, -255, -256, -257, -300}, 
                c.useIndex("amount", Payment.class).to(255, true).backward().objects());
        assertAmounts(new long[]{254, 1, 0, -1, -2, -255, -256, -257, -300}, 
                c.useIndex("amount", Payment.class).to(255, false).backward()
                .objects());
        assertAmounts(new long[]{255}, 
                c.useIndex("amount", Payment.class).eq(255).backward().objects());
        assertAmounts(new long[]{-1}, 
                c.useIndex("amount", Payment.class).eq(-1).backward().objects());
        assertAmounts(new long[]{-257}, 
                c.useIndex("amount", Payment.class).eq(-257).backward().objects());
        
        database.stop();
    }
    
    private static void assertAmounts(long[] expected, Iterable<Payment> payments) {
        ArrayList<Long> got = new ArrayList<Long>();
        for (Payment p : payments) {
            got.add(p.amount);
        }
        ArrayList<Long> want = new ArrayList<Long>();
        for (long v : expected) {
            want.add(v);
        }
        Assert.assertEquals(want.toString(), got.toString());
    }
    
    public static void main(String[] args) {
        //composite1();
    }
    
    // ======== The scan of 2026.4 (bergdb 020-10, section 3.4) ========
    
    /** An object of every level type: a string, a long, a double, bytes. */
    public static class Row {
        public String s;
        public long n;
        public double d;
        public byte[] b;
        
        public Row() {}
        
        public Row(String s, long n, double d, byte[] b) {
            this.s = s;
            this.n = n;
            this.d = d;
            this.b = b;
        }
    }
    
    private static Database rows() {
        Database db = Factory.database().memory().start();
        db.indexBuilder("sn").dir("/r/").type("string").field("s").type("long").field("n")
                .start().join();
        db.indexBuilder("db").dir("/r/").type("double").field("d").type("bytes").field("b")
                .start().join();
        return db;
    }
    
    private static void assertState(String what, Runnable r) {
        try {
            r.run();
        } catch (IllegalStateException e) {
            return;
        }
        throw new AssertionError(what + ": no IllegalStateException");
    }
    
    private static void assertArgument(String what, Runnable r) {
        try {
            r.run();
        } catch (IllegalArgumentException e) {
            return;
        }
        throw new AssertionError(what + ": no IllegalArgumentException");
    }
    
    /**
     * The grammar, every call in every state (020-10, section 3.4; S2-F22): eq() on levels 1
     * to k, then one from() and one to(), or one prefix(), on level k + 1; backward() once,
     * anywhere; nothing after objects() or kvs() but objects() and kvs(). A call out of the
     * grammar is IllegalStateException, at once; a type that does not match the level, a
     * null, NaN, a lone surrogate, IllegalArgumentException.
     */
    @Nano
    public static void testGrammar() {
        Database db = rows();
        try {
            Connection c = db.newConnection();
            // Fresh: level 1 of "sn" is a string.
            assertArgument("eq(long) on a string level", () -> c.useIndex("sn", Row.class).eq(1));
            assertArgument("eq(double)", () -> c.useIndex("sn", Row.class).eq(1.0));
            assertArgument("eq(byte[])", () -> c.useIndex("sn", Row.class).eq(new byte[0]));
            assertArgument("from(long)", () -> c.useIndex("sn", Row.class).from(1, true));
            assertArgument("to(byte[])", () -> c.useIndex("sn", Row.class).to(new byte[0], true));
            assertArgument("prefix(byte[])", () -> c.useIndex("sn", Row.class)
                    .prefix(new byte[0]));
            assertArgument("eq(null)", () -> c.useIndex("sn", Row.class).eq((String) null));
            assertArgument("from(null)", () -> c.useIndex("sn", Row.class).from((String) null,
                    true));
            assertArgument("prefix(null)", () -> c.useIndex("sn", Row.class)
                    .prefix((String) null));
            assertArgument("a lone surrogate", () -> c.useIndex("sn", Row.class).eq("a\ud800"));
            assertArgument("NaN", () -> c.useIndex("db", Row.class).eq(Double.NaN));
            assertArgument("NaN to", () -> c.useIndex("db", Row.class).to(Double.NaN, true));
            assertArgument("eq(null bytes)", () -> c.useIndex("db", Row.class).eq(0.0)
                    .eq((byte[]) null));
            
            // After eq() on every level: no level left.
            assertState("eq past the levels", () -> c.useIndex("sn", Row.class).eq("a").eq(1)
                    .eq(2));
            assertState("from past the levels", () -> c.useIndex("sn", Row.class).eq("a").eq(1)
                    .from(2, true));
            assertState("to past the levels", () -> c.useIndex("sn", Row.class).eq("a").eq(1)
                    .to(2, true));
            assertState("prefix past the levels", () -> c.useIndex("sn", Row.class).eq("a")
                    .eq(1).prefix("x"));
            c.useIndex("sn", Row.class).eq("a").eq(1).backward().objects();
            
            // After a bound: no eq(), no second bound of its kind, no prefix.
            assertState("eq after from", () -> c.useIndex("sn", Row.class).from("a", true)
                    .eq("b"));
            assertState("eq after to", () -> c.useIndex("sn", Row.class).to("a", true).eq("b"));
            assertState("eq after prefix", () -> c.useIndex("sn", Row.class).prefix("a")
                    .eq("b"));
            assertState("a later level alone (S2-F22)", () -> c.useIndex("sn", Row.class)
                    .from("a", true).from(1, true));
            assertState("a second from", () -> c.useIndex("sn", Row.class).from("a", true)
                    .from("b", true));
            assertState("a second to", () -> c.useIndex("sn", Row.class).to("a", true)
                    .to("b", true));
            assertState("prefix after from", () -> c.useIndex("sn", Row.class).from("a", true)
                    .prefix("b"));
            assertState("from after prefix", () -> c.useIndex("sn", Row.class).prefix("a")
                    .from("b", true));
            assertState("a second prefix", () -> c.useIndex("sn", Row.class).prefix("a")
                    .prefix("b"));
            assertState("a second backward", () -> c.useIndex("sn", Row.class).backward()
                    .backward());
            c.useIndex("sn", Row.class).to("z", false).from("a", true).backward().kvs();
            c.useIndex("sn", Row.class).backward().eq("a").from(1, false).to(9, true).objects();
            c.useIndex("db", Row.class).eq(-0.0).prefix(new byte[] {0}).objects();
            
            // After objects() or kvs(): only objects() and kvs().
            UseIndexBuilder<Row> b = c.useIndex("sn", Row.class);
            b.objects();
            assertState("eq after objects", () -> b.eq("a"));
            assertState("from after objects", () -> b.from("a", true));
            assertState("to after objects", () -> b.to("a", true));
            assertState("prefix after objects", () -> b.prefix("a"));
            assertState("backward after objects", () -> b.backward());
            b.kvs();
            b.objects();
        } finally {
            db.close();
        }
    }
    
    /** The names (s) of a scan, in its order. */
    private static String names(Iterable<Row> scan) {
        StringBuilder r = new StringBuilder();
        for (Row row : scan) {
            r.append(r.length() == 0 ? "" : ",").append(row.s).append(row.n);
        }
        return r.toString();
    }
    
    /**
     * S2-F2: from() and to(), each inclusive or not, in both directions, on the level after
     * the eq() levels; from() above to() is an empty scan, not an exception.
     */
    @Nano
    public static void testExclusiveBounds() {
        Database db = rows();
        try {
            Connection c = db.newConnection();
            for (int i = 1; i <= 5; i++) {
                c.put("/r/a" + i, new Row("a", i, i, new byte[] {(byte) i}));
                c.put("/r/b" + i, new Row("b", i, i, new byte[] {(byte) i}));
            }
            Assert.assertEquals("a2,a3,a4", names(c.useIndex("sn", Row.class).eq("a")
                    .from(2, true).to(4, true).objects()));
            Assert.assertEquals("a3", names(c.useIndex("sn", Row.class).eq("a")
                    .from(2, false).to(4, false).objects()));
            Assert.assertEquals("a3,a4", names(c.useIndex("sn", Row.class).eq("a")
                    .from(2, false).to(4, true).objects()));
            Assert.assertEquals("a4,a3", names(c.useIndex("sn", Row.class).eq("a")
                    .from(2, false).to(4, true).backward().objects()));
            Assert.assertEquals("a5,a4", names(c.useIndex("sn", Row.class).eq("a")
                    .from(3, false).backward().objects()));
            Assert.assertEquals("a2,a1", names(c.useIndex("sn", Row.class).eq("a")
                    .to(3, false).backward().objects()));
            Assert.assertEquals("", names(c.useIndex("sn", Row.class).eq("a")
                    .from(4, true).to(2, true).objects()));
            Assert.assertEquals("", names(c.useIndex("sn", Row.class).eq("a")
                    .from(3, false).to(3, false).objects()));
            Assert.assertEquals("a3", names(c.useIndex("sn", Row.class).eq("a")
                    .from(3, true).to(3, true).objects()));
            Assert.assertEquals("b1,b2,b3,b4,b5", names(c.useIndex("sn", Row.class)
                    .from("a", false).objects()));
            Assert.assertEquals("a1,a2,a3,a4,a5", names(c.useIndex("sn", Row.class)
                    .to("b", false).objects()));
            Assert.assertEquals("a1,b1,a2,b2", names(c.useIndex("db", Row.class)
                    .from(-0.0, true).to(2.0, true).objects()));
        } finally {
            db.close();
        }
    }
    
    /**
     * S2-F13: prefix() on a level after eq(): the strings that start with it by code points,
     * a "string" level's E' (020-10, section 4.4); and bytes.
     */
    @Nano
    public static void testPrefix() {
        Database db = rows();
        try {
            Connection c = db.newConnection();
            String[] names = {"Ann", "Anna", "Annie", "An", "Bo", "Ann\u0000", "Ann\ud83d\ude00",
                    "Anm", "Ao"};
            for (int i = 0; i < names.length; i++) {
                c.put("/r/" + i, new Row(names[i], 1, 0.0, new byte[] {1, (byte) i}));
            }
            List<String> got = new ArrayList<>();
            for (Row r : c.useIndex("sn", Row.class).prefix("Ann").objects()) {
                got.add(r.s);
            }
            Assert.assertEquals("[Ann, Ann\u0000, Anna, Annie, Ann\ud83d\ude00]",
                    got.toString());
            got.clear();
            for (Row r : c.useIndex("sn", Row.class).prefix("Ann").backward().objects()) {
                got.add(r.s);
            }
            Assert.assertEquals("[Ann\ud83d\ude00, Annie, Anna, Ann\u0000, Ann]",
                    got.toString());
            Assert.assertEquals(9, count(c.useIndex("sn", Row.class).prefix("").objects()));
            Assert.assertEquals(0, count(c.useIndex("sn", Row.class).prefix("Z").objects()));
            assertArgument("prefix on a long level", () -> c.useIndex("sn", Row.class)
                    .eq("Ann").prefix("x"));
            Assert.assertEquals(9, count(c.useIndex("db", Row.class).eq(0.0)
                    .prefix(new byte[] {1}).objects()));
            Assert.assertEquals(1, count(c.useIndex("db", Row.class).eq(0.0)
                    .prefix(new byte[] {1, 4}).objects()));
        } finally {
            db.close();
        }
    }
    
    private static int count(Iterable<?> it) {
        int n = 0;
        for (Object o : it) {
            n++;
        }
        return n;
    }
    
    /**
     * S2-F23: stale entries, first, inside and last (their values deleted through the Core,
     * so no maintenance removed the entries): hasNext() looks ahead past them, and never
     * says true before a next() that throws NoSuchElementException.
     */
    @Nano
    public static void testStaleLastEntries() {
        Database db = rows();
        try {
            Connection c = db.newConnection();
            for (int i = 1; i <= 5; i++) {
                c.put("/r/a" + i, new Row("a", i, i, new byte[] {(byte) i}));
            }
            Db core = ((DatabaseImp) db).getDb();
            for (String k : new String[] {"/r/a1", "/r/a3", "/r/a5"}) {
                core.execute(core.trans().delete(Keys.toBytes(PubKeys.u2i(k))).build());
            }
            c.put("/r/a4", "now a String");     // A stale entry, by a maintained write too
            for (boolean back : new boolean[] {false, true}) {
                UseIndexBuilder<Row> b = c.useIndex("sn", Row.class);
                if (back) {
                    b.backward();
                }
                Iterator<Row> it = b.objects().iterator();
                Assert.assertTrue(it.hasNext());
                Assert.assertTrue(it.hasNext());
                Assert.assertEquals(2, it.next().n);
                Assert.assertFalse("the stale last entries skipped", it.hasNext());
                try {
                    it.next();
                    throw new AssertionError("next() after hasNext() false");
                } catch (NoSuchElementException e) {
                    // Expected.
                }
            }
        } finally {
            db.close();
        }
    }
    
    /**
     * N3: a scan reads the definition, the entries and the values with Db directly: it leaves
     * the connection's transactionInfo() as it was, which describes get() and exists() only.
     */
    @Nano
    public static void testScanKeepsTransactionInfo() {
        Database db = rows();
        try {
            Connection c = db.newConnection();
            c.put("/x.txt", "x");
            c.get("/x.txt", String.class);
            long t = c.transactionInfo().time().units();
            c.put("/r/a", new Row("a", 1, 1, new byte[0]));
            Assert.assertEquals(1, count(c.useIndex("sn", Row.class).objects()));
            Assert.assertEquals(1, count(c.useIndex("sn", Row.class).kvs()));
            Assert.assertEquals("transactionInfo() kept", t, c.transactionInfo().time().units());
        } finally {
            db.close();
        }
    }
    
    /**
     * 020-10, section 3.6: useIndex() is a read for freezeLookupTime(); every iterator of a
     * builder reads at its lookup time, from the beginning; a deleted index still scans at a
     * time it was active.
     */
    @Nano
    public static void testScanLookupTime() {
        Database db = rows();
        try {
            Connection c = db.newConnection();
            c.put("/r/a", new Row("a", 1, 1, new byte[0]));
            c.freezeLookupTime();
            UseIndexBuilder<Row> b = c.useIndex("sn", Row.class);
            Iterable<Row> scan = b.objects();
            Time frozen = c.getLookupTime();
            Assert.assertTrue("the scan froze the time", frozen.units() != Time.MAX.units());
            c.put("/r/b", new Row("b", 2, 2, new byte[0]));
            Assert.assertEquals(1, count(scan));
            Assert.assertEquals(1, count(scan));
            Assert.assertEquals(1, count(b.kvs()));
            Assert.assertEquals(1, count(c.useIndex("sn", Row.class).objects()));
            db.deleteIndex("sn");
            Assert.assertEquals("at the frozen time", 1, count(c.useIndex("sn", Row.class)
                    .objects()));
            c.setLookupTime(Time.MAX);
            try {
                c.useIndex("sn", Row.class);
                throw new AssertionError("a deleted index");
            } catch (NoSuchIndexException e) {
                // Expected.
            }
        } finally {
            db.close();
        }
    }
    
    /** 015-29: an index named "primary" is scanned as any other. */
    @Nano
    public static void testScanIndexNamedPrimary() {
        Database db = Factory.database().memory().start();
        try {
            db.indexBuilder("primary").dir("/r/").type("long").field("n").start().join();
            Connection c = db.newConnection();
            c.put("/r/a", new Row("a", 7, 0, new byte[0]));
            Assert.assertEquals(7, c.useIndex("primary", Row.class).eq(7).objects().iterator()
                    .next().n);
        } finally {
            db.close();
        }
    }
    
    /** Pages of 100 entries: 250 values in order, forward and backward, with a bound. */
    @Nano
    public static void testScanPages() {
        Database db = rows();
        try {
            Connection c = db.newConnection();
            WBuilder w = c.w();
            for (int i = 0; i < 250; i++) {
                w.put("/r/" + i, new Row("p", i, i, new byte[0]));
            }
            w.execute();
            long expected = 0;
            for (Row r : c.useIndex("sn", Row.class).objects()) {
                Assert.assertEquals(expected++, r.n);
            }
            Assert.assertEquals(250, expected);
            expected = 249;
            for (Row r : c.useIndex("sn", Row.class).backward().objects()) {
                Assert.assertEquals(expected--, r.n);
            }
            Assert.assertEquals(-1, expected);
            Assert.assertEquals(150, count(c.useIndex("sn", Row.class).eq("p")
                    .from(50, true).to(200, false).backward().objects()));
        } finally {
            db.close();
        }
    }
    
    /**
     * Holds the build of an index of the database before its step n (1 the first), in its
     * action after its reads, until release(); its steps of 'values' values (0: the
     * default). For the tests that took a build's steps one by one.
     */
    static final class Hold {
        private final CountDownLatch reached = new CountDownLatch(1);
        private final CountDownLatch gate = new CountDownLatch(1);
        
        Hold(Database database, int values, final int n) {
            IndexManager m = ((DatabaseImp) database).getIndexManager();
            m.testStepValues = values;
            final int[] steps = new int[1];
            m.testHook = p -> {
                if (p.equals(IndexManager.BUILD_STEP) && ++steps[0] == n) {
                    reached.countDown();
                    await(gate);
                }
            };
        }
        
        void awaitReached() {
            await(reached);
        }
        
        void release() {
            gate.countDown();
        }
        
        private static void await(CountDownLatch latch) {
            try {
                if (!latch.await(10, TimeUnit.SECONDS)) {
                    throw new AssertionError("not reached in 10 s");
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                throw new AssertionError(e);
            }
        }
    }
}
