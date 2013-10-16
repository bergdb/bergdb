package bergdb.pubimp;

import java.util.Iterator;

import bergdb.common.EventToWaitFor;
import bergdb.core.Db;
import bergdb.coreds.GetMany;
import bergdb.coreds.Keys;
import bergdb.coreds.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.*;
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
    private static class Payment {
        String from;
        String to;
        long amount;
        
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
    private static class IPayment {
        String from;
        String to;
        int amount;
        
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
    private static class DPayment {
        String from;
        String to;
        double amount;
        
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
    private static class FPayment {
        String from;
        String to;
        float amount;
        
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
    
    @T
    public static void test0() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").type("string").dir("/payments/").field("from")
            .createFast();
        
        Payment p1 = new Payment("1001", "1002", 20);
        
        c.w().put("/payments/1.obj", p1).execute();
        
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
    
    @T
    public static void test1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from")
            .createFast();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1002", "1009", 30);
        final Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1.obj", p1)
            .put("/payments/2.obj", p2)
            .put("/payments/3.obj", p3).execute();
        
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
        
        db.stop();
    }
    
    @T
    public static void testNonObjects() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").createFast();
        db.indexBuilder("payments-to").type("string/unicode").dir("/payments/").field("to").createFast();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1.obj", p1)
            .put("/payments/2.obj", p2)
            .put("/payments/3.obj", p3)
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
    
    @T
    public static void testTypeMix() {
        // Using DbObject.class as iteration type is a special case.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").createFast();
        
        Payment p10 = new Payment("1010", "1002", 20);
        Payment p20 = new Payment("1020", "1009", 30);
        Payment p30 = new Payment("1010", "1008", 40);
        DPayment p15 = new DPayment("1015", "1000", 12.3);
        
        c.w().put("/payments/p10.obj", p10)
            .put("/payments/p20.obj", p20)
            .put("/payments/p30.obj", p30)
            .put("/payments/p15.obj", p15)
            .execute();
        
        Iterator<DbObject> it = c.useIndex("payments-from", DbObject.class).objects().iterator();
        DbObject t = it.next();
        Assert.assertEquals("1002", t.getString("to"));
        t = it.next();
        Assert.assertEquals("1008", t.getString("to"));
        t = it.next();
        DPayment p15b = new DPayment();
        t.toJavaObject(p15b, new KvToObjectImp());
        Assert.assertEquals("1000", t.getString("to"));
        Assert.assertEquals("1000", p15b.to);
        Assert.assertEquals(12.3, p15b.amount);
        t = it.next();
        Assert.assertEquals("1009", t.getString("to"));
    }
    
    @T
    public static void testBackward1() {
        // Simple case with backward().
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from")
            .createFast();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        
        c.w().put("/payments/1.obj", p1)
            .put("/payments/2.obj", p2).execute();
        
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
    
    @T
    public static void testBackward1b() {
        // Like testBackward1, but with double field instead.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("i1").type("double").dir("/payments/").field("value")
            .createFast();
        
        MyDouble p1 = new MyDouble(20);
        MyDouble p2 = new MyDouble(30);
        
        c.w().put("/payments/1.obj", p1)
            .put("/payments/2.obj", p2).execute();
        
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
    
    @T
    public static void testBackward2() {
        // 3 elements, two has same indexed value, no eq()
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from")
            .createFast();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1.obj", p1)
            .put("/payments/2.obj", p2)
            .put("/payments/3.obj", p3).execute();
        
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
    
    @T
    public static void testBackward3() {
        // backward(), empty iterator.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from")
            .createFast();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).backward()
                .objects().iterator();
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @T
    public static void testBackward4() {
        // backward() and eq()
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from")
            .createFast();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1.obj", p1)
            .put("/payments/2.obj", p2)
            .put("/payments/3.obj", p3).execute();
        
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
    
    @T
    public static void testIterHistory() {
        TestClock clock = new TestClock();
        clock.setTime(100);
        Database db = Factory.database().memory().clock(clock).start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").dir("/payments/").type("string/unicode").field("from").createFast();
        
        clock.setTime(200);
        
        c.w().put("/payments/10.obj", new Payment("1001", "1002", 10))
            .put("/payments/20.obj", new Payment("1002", "1009", 20))
            .put("/payments/30.obj", new Payment("1001", "1009", 30))
            .execute();
        
        clock.setTime(300);
        
        c.w().put("/payments/12.obj", new Payment("1001", "1012", 12))
            .put("/payments/30.obj", new Payment("1001", "1030", 31))
            .put("/payments/40.obj", new Payment("1001", "1040", 40))
            .execute();
        
        c.setLookupTime(250);
        Iterable<Payment> it = c.useIndex("payments-from", Payment.class).eq("1001").objects();
        Iterator<Payment> iter = it.iterator();
        Assert.assertTrue(iter.hasNext());
        Assert.assertEquals(10, iter.next().amount);
        Assert.assertTrue(iter.hasNext());
        Assert.assertEquals(30, iter.next().amount);
        Assert.assertFalse(iter.hasNext());
        
        c.setLookupTime(350);
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
    
    @T
    public static void testNonExistantIndex() {
        TestClock clock = new TestClock();
        clock.setTime(100);
        Database db = Factory.database().memory().clock(clock).start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").createFast();
        
        clock.setTime(200);
        
        c.w().put("/payments/10.obj", new Payment("1001", "1002", 10))
            .put("/payments/20.obj", new Payment("1002", "1009", 20))
            .put("/payments/30.obj", new Payment("1001", "1009", 30))
            .execute();
        
        Exception ex = null;
        
        try {
            c.setLookupTime(50);
            c.useIndex("payments-from", Payment.class);
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex instanceof NoSuchIndexException);
        ex = null;
        
        try {
            c.setLookupTime(500);
            c.useIndex("payments-from", Payment.class);
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        
        Assert.assertNull(ex);
        db.stop();
    }
    
    @T
    public static void testIterMultiField1() {
        // A multi-field index.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-to-from").type("string/unicode").dir("/payments/")
            .field("to").field("from").start().join();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        Payment p3 = new Payment("1001", "1009", 40);
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).put("/payments/3.obj", p3).execute();
        
        Iterable<Payment> payments = c.useIndex("payments-to-from", Payment.class).objects();
        long expected[] = new long[] {20, 40, 20, 30, 30, 40};
        Iterator<Payment> iter = payments.iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @T
    public static void testIterMultiField2() {
        // A multi-field index.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-to-from").type("string/unicode").dir("/payments/")
                .field("to").field("from").start().join();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1002", "1009", 30);
        Payment p3 = new Payment("1001", "1009", 40);
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).put("/payments/3.obj", p3).execute();
        
        Iterable<Payment> payments = c.useIndex("payments-to-from", Payment.class).eq("1002").objects();
        long expected[] = new long[] {20, 30};
        Iterator<Payment> iter = payments.iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Payment p = iter.next();
            Assert.assertEquals(expected[i], p.amount);
        }
        
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @T
    public static void testNegLongs1() {
        // Tests index including negative long integers.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-amount").type("long").dir("/payments/").field("amount").start().join();
        
        c.w().put("/payments/1.obj", new Payment("1", "2", -100))
            .put("/payments/2.obj", new Payment("1", "3", 0))
            .put("/payments/3.obj", new Payment("1", "4", 90)).execute();
        
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
    
    @T
    public static void testNegLongs2() {
        // Tests index including negative long integers.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("payments-amount").type("long").dir("/payments/").field("amount").start().join();
        
        c.w().put("/payments/1.obj", new Payment("1", "1", -100))
            .put("/payments/2.obj", new Payment("1", "2", 0))
            .put("/payments/3.obj", new Payment("1", "3", 90))
            .put("/payments/4.obj", new Payment("1", "4", Long.MIN_VALUE))
            .put("/payments/5.obj", new Payment("1", "5", Long.MAX_VALUE))
            .put("/payments/6.obj", new Payment("1", "6", -1))
            .put("/payments/7.obj", new Payment("1", "7", -23))
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
    
    static class MyDouble {
        private double value;
        
        public MyDouble() {}
        
        public MyDouble(double v) {
            value = v;
        }
    }
    
    @T
    public static void testDoubles1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("value").type("double").dir("/d/").field("value").start().join();
        
        c.w().put("/d/1.obj", new MyDouble(1.23))
            .put("/d/2.obj", new MyDouble(3e10))
            .put("/d/3.obj", new MyDouble(1.2e-2))
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
    
    @T
    public static void testDoubles2() {
        // With negative values too.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("value").type("double").dir("/d/").field("value").start().join();
        
        double[] values = new double[] {
                Double.MAX_VALUE, 100.0, 1.2, 1.2, 0.0, -10, -300.0, -9e100 };
        
        WBuilder b = c.w();
        for (int i = 0; i < values.length; i++) {
            b.put("/d/" + i + ".obj", new MyDouble(values[i]));
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
    
    @T
    public static void testDoubles3() {
        // With INFINITY values.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("value").type("double").dir("/d/").field("value").start().join();
        
        double[] values = new double[] {
                Double.POSITIVE_INFINITY, 
                Double.MAX_VALUE, 100.0, 1.2, 1.2, 0.0, -10, -300.0, -9e100,
                Double.NEGATIVE_INFINITY};
        
        WBuilder b = c.w();
        for (int i = 0; i < values.length; i++) {
            b.put("/d/" + i + ".obj", new MyDouble(values[i]));
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
    
    @T
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
        d.indexBuilder("i1").dir("/d/").type("double").field("amount").createFast();
        
        Connection c = d.connection();
        WBuilder b = c.w();
        int index = 0;
        for (Object o : objects) {
            b.put("/d/" + index + ".obj", o);
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
    }
    
    @T
    public static void testInt1() {
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
        d.indexBuilder("i1").dir("/d/").type("long").field("amount").createFast();
        
        Connection c = d.connection();
        WBuilder b = c.w();
        int index = 0;
        for (Object o : objects) {
            b.put("/d/" + index + ".obj", o);
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
    }
    
    static class MyString {
        public String s;
        
        public MyString() {}
        
        public MyString(String s) {
            this.s = s;
        }
    }
    
    @T
    public static void testRestart1() {
        MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream);
        Database db = builder.start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").createFast();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1002", "1009", 30);
        final Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).put("/payments/3.obj", p3).execute();
        
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
        
        DatabaseBuilder builder2 = Factory.database();
        ((DatabaseBuilderImp) builder2).getDbBuilder().mainStream(stream);
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
    
    @T
    public static void testRestart2() {
        MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream);
        Database db = builder.start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").createFast();
        
        Payment p1 = new Payment("1010", "2", 10);
        Payment p2 = new Payment("1000", "2", 20);
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).execute();
        
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
        c2.w().put("/payments/3.obj", p3).execute();
        
        Iterator<Payment> iter = c2.useIndex("payments-from", Payment.class).objects().iterator();
        long[] expected = new long[] { 20, 5, 10 };
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(iter.hasNext());
            Assert.assertEquals(expected[i], iter.next().amount);
        }
        Assert.assertFalse(iter.hasNext());
        db2.stop();
    }
    
    @T
    public static void testKvDelete() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").createFast();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1002", "1009", 30);
        final Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).put("/payments/3.obj", p3).execute();
        
        // Assert we have index KVs.
        
        Assert.assertEquals(3, getIndexKvCount(db));
        
        // Now, delete all KVs and check that corresponding index entries were deleted too.
        
        c.w().delete("/payments/1.obj").delete("/payments/2.obj").execute();
        
        Assert.assertEquals(1, getIndexKvCount(db));
        
        c.w().delete("/payments/1.obj").delete("/payments/3.obj").execute();
        
        Assert.assertEquals(0, getIndexKvCount(db));
        db.stop();
    }

    private static int getIndexKvCount(Database db) {
        Db db2 = ((DatabaseImp) db).getDb();
        GetMany g = new GetMany();
        final String prefix = Db.INTERNAL_KEY_PREFIX + "di/";
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
    
    @T
    public static void testWithDeletesAndUpdates() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").start().join();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1002", "1009", 30);
        final Payment p3 = new Payment("1001", "1009", 40);
        
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).put("/payments/3.obj", p3).execute();
        
        final Payment p2b = new Payment("1002", "1019", 31);
        c.w().delete("/payments/1.obj").put("/payments/2.obj", p2b).execute();
        
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
    
    @T
    public static void testExistingData1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1002", "1009", 30);
        final Payment p3 = new Payment("1000", "1009", 40);
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).put("/payments/3.obj", p3).execute();
        
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").start().join();
        
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
    
    @T
    public static void testExistingData2() {
        // Like "1", but with two indexes.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        final Payment p1 = new Payment("1001", "2002", 20);
        final Payment p2 = new Payment("1002", "2003", 30);
        final Payment p3 = new Payment("1000", "2004", 40);
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).put("/payments/3.obj", p3).execute();
        
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").start().join();
        db.indexBuilder("payments-to").type("string/unicode").dir("/payments/").field("to").start().join();
        
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
    
    @T
    public static void testExistingData3() {
        // Like "2", but new KVs too.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        Payment p1 = new Payment("1010", "2020", 20);
        Payment p2 = new Payment("1020", "2030", 30);
        Payment p3 = new Payment("1000", "2040", 40);
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).put("/payments/3.obj", p3).execute();
        
        db.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").start().join();
        db.indexBuilder("payments-to").type("string/unicode").dir("/payments/").field("to").start().join();
        
        Payment p4 = new Payment("1005", "2019", 50);
        c.w().put("/payments/4.obj", p4).execute();
        
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
    
    @T
    public static void testCreateWhileWriteOps1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        for (int i = 0; i < 20; i++) {
            String id = "" + (1000 + (i * 10));
            Payment p = new Payment("1000", "2000", i * 10);
            c.w().put("/payments/" + id + ".obj", p).execute();
        }
        
        IndexBuilderImp iCreator = (IndexBuilderImp) db.indexBuilder("payments-amount").type("long")
                .dir("/payments/").field("amount");
        iCreator.bunchSize(10);
        
        IndexBuilderImp.IndexCreateState state = iCreator.createInit();
        iCreator.createStep(state);    // Creates 10 index entries
        Assert.assertFalse(state.isDone);
        
        // Adds one payment in section handled by index creator.
        Payment p = new Payment("1000", "2000", 15);
        c.w().put("/payments/1015.obj", p).execute();
        
        // Adds one payment in section not yet handled by index creator.
        p = new Payment("1000", "2000", 125);
        c.w().put("/payments/1125.obj", p).execute();
        
        while (!state.isDone) {
            iCreator.createStep(state);
        }
        
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
    
    @T
    public static void testCreateDuringRestart() throws InterruptedException {
        MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream);
        Database db = builder.start();
        Connection c = db.newConnection();
        
        for (int i = 0; i < 20; i++) {
            String id = "" + (1000 + (i * 10));
            Payment p = new Payment("1000", "2000", i * 10);
            c.w().put("/payments/" + id + ".obj", p).execute();
        }
        
        IndexBuilderImp iCreator = (IndexBuilderImp) db.indexBuilder("payments-amount").type("long")
                .dir("/payments/").field("amount");
        iCreator.bunchSize(10);
        
        IndexBuilderImp.IndexCreateState state = iCreator.createInit();
        iCreator.createStep(state);    // Creates 10 index entries
        Assert.assertFalse(state.isDone);
        
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
        db = null;
        c = null;
        
        builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().mainStream(stream);
        db = builder.start();
        c = db.newConnection();
        
        // Adds one payment in section handled by index creator.
        Payment p = new Payment("1000", "2000", 15);
        c.w().put("/payments/1015.obj", p).execute();
        
        // Adds one payment in section not yet handled by index creator.
        p = new Payment("1000", "2000", 125);
        c.w().put("/payments/1125.obj", p).execute();
        
        IndexManager m = ((DatabaseImp) db).getIndexManager();
        IndexManager.Index index = m.getIndex("payments-amount");
        Assert.assertTrue("m.getIndex(\"payments-amount\") != null", index != null);
        
        // Wait until creation thread has completed.
        
        Thread.yield();
        while (true) {
            int s = index.getState();
            if (s != IndexManager.Index.STATE_ACTIVE) {
                Thread.sleep(50);
            } else {
                break;
            }
        }
        
        // Assert
        
        Assert.assertEquals(IndexManager.Index.STATE_ACTIVE, index.getState());
        
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
    
    @T
    public static void testCreateWhileWriteOps2() {
        // Arrange
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        for (int i = 0; i < 20; i++) {
            String id = "" + (1000 + (i * 10));
            Payment p = new Payment("1000", "2000", i * 10);
            c.w().put("/p/" + id + ".obj", p).execute();
        }
        
        // Act
        IndexBuilderImp iCreator = (IndexBuilderImp) db.indexBuilder("p-amount").type("long")
                .dir("/p/").field("amount");
        iCreator.bunchSize(10);
        
        IndexBuilderImp.IndexCreateState state = iCreator.createInit();
        iCreator.createStep(state);    // Creates 10 index entries
        Assert.assertFalse(state.isDone);
        
        // Adds one payment in section handled by index creator.
        Payment p = new Payment("1000", "2000", 15);
        c.w().put("/p/1015.obj", p).execute();
        
        // Modifies one payment in section handled by index creator.
        p = new Payment("1000", "2000", 41);
        c.w().put("/p/1040.obj", p).execute();
        
        // Deletes one payment in section handled by index creator.
        c.w().delete("/p/1060.obj").execute();
        
        // Adds one payment in section not yet handled by index creator.
        p = new Payment("1000", "2000", 125);
        c.w().put("/p/1125.obj", p).execute();
        
        // Modifies one payment in section not yet handled by index creator.
        p = new Payment("1000", "2000", 141);
        c.w().put("/p/1140.obj", p).execute();
        
        // Deletes one payment in section not yet handled by index creator.
        c.w().delete("/p/1160.obj").execute();
        
        while (!state.isDone) {
            iCreator.createStep(state);
        }
        
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
    
    @T
    public static void testManyObjects() {
        // Tests index with more than 100 objects. DB.getMany() must be called more than once.
        
        // Arrange/Act
        int n = 150;
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        WBuilder b = c.w();
        
        db.indexBuilder("p-amount").type("long").dir("/p/").field("amount").createFast();
        
        for (int i = 0; i < n; i++) {
            String id = "" + (1000 + (i * 10));
            Payment p = new Payment("1", "2", i * 10);
            b.put("/p/" + id + ".obj", p);
            
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
    
    @T
    public static void testDeleteIndex1() {
        // Arrange
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        database.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").createFast();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1000", "1009", 40);
        
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).execute();
        
        c.useIndex("payments-from", Payment.class).objects();
        
        // Act
        
        database.deleteIndex("payments-from").join();
        
        // Assert
        
        Exception ex = null;
        try {
            c.useIndex("payments-from", Payment.class).objects();
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        Assert.assertTrue("Got NoSuchIndexException?", ex != null);
        
        byte[] indexDbDir = IndexManager.getIndexDbDirAsBytes("payments-from");
        final GetMany g = new GetMany();
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
        
        Db db = ((DatabaseImp) database).getDb();
        db.getMany(g);
        Assert.assertEquals(0, g.result.size());
        
        database.stop();
    }
    
    @T
    public static void testDeleteIndex2() throws InterruptedException {
        // Arrange
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        database.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").createFast();
        
        final Payment p1 = new Payment("1001", "1002", 20);
        final Payment p2 = new Payment("1000", "1009", 40);
        
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).execute();
        
        c.useIndex("payments-from", Payment.class).objects();
        
        // Act
        
        Job job = database.deleteIndex("payments-from");
        job.join();
        
        // Assert
        
        Exception ex = null;
        try {
            c.useIndex("payments-from", Payment.class).objects();
        } catch (NoSuchIndexException e) {
            ex = e;
        }
        Assert.assertTrue("Got NoSuchIndexException?", ex != null);
        
        byte[] indexDbDir = IndexManager.getIndexDbDirAsBytes("payments-from");
        final GetMany g = new GetMany();
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
        
        Db db = ((DatabaseImp) database).getDb();
        db.getMany(g);
        Assert.assertEquals(0, g.result.size());
        
        database.stop();
    }
    
    @T
    public static void testCreateInThread1() throws InterruptedException {
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1000", "1009", 40);
        Payment p3 = new Payment("1009", "2000", 50);
        
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).execute();
        
        Job job = database.indexBuilder("payments-from").type("string/unicode").dir("/payments/")
                .field("from").start();
        c.w().put("/payments/3.obj", p3).execute();
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
    
    @T
    public static void testCreateInThread2() throws InterruptedException {
        // This test uses an EventToWaitFor to test concurrency.
        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        Payment p1 = new Payment("1001", "1002", 20);
        Payment p2 = new Payment("1000", "1009", 40);
        Payment p3 = new Payment("1009", "2000", 50);
        
        c.w().put("/payments/1.obj", p1).put("/payments/2.obj", p2).execute();
        
        EventToWaitFor waitEvent = new EventToWaitFor();
        IndexBuilderImp creator = (IndexBuilderImp) database.indexBuilder("payments-from");
        creator.createInThreadWaitEvent(waitEvent);
        
        Job job = creator.type("string/unicode").dir("/payments/")
                .field("from").start();
        c.w().put("/payments/3.obj", p3).execute();
        waitEvent.happened();
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
    
    @T
    public static void testKeyReplaceWithIndex() {
        TestClock clock = new TestClock();
        Database database = Factory.database().memory().clock(clock).start();
        Connection c = database.newConnection();
        String key = "/payments/${transactionTime}.obj";
        
        database.indexBuilder("payments-from").type("string/unicode").dir("/payments/").field("from").start().join();
        c.setEnableKeyReplace(true);
        clock.setTime(100);
        c.w().put(key, new Payment("101", "105", 5)).execute();
        clock.setTime(200);
        c.w().put(key, new Payment("100", "106", 6)).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(6, p.amount);
        p = iter.next();
        Assert.assertEquals(5, p.amount);
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @T
    public static void testStartAt1() {
        // forward, include
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("payments-from").type("string/unicode").dir("/payments/")
            .field("from").start().join();
        
        c.w().put("/payments/1.obj", new Payment("101", "105", 1)).execute();
        c.w().put("/payments/2.obj", new Payment("100", "106", 2)).execute();
        c.w().put("/payments/3.obj", new Payment("099", "106", 3)).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).startAt("100")
                .objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(2, p.amount);
        p = iter.next();
        Assert.assertEquals(1, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testStartAt2() {
        // forward, exclude
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("pay-from").type("string/unicode").dir("/payments/")
            .field("from").start().join();
        
        c.w().put("/payments/1.obj", new Payment("101", "105", 1)).execute();
        c.w().put("/payments/2.obj", new Payment("100", "106", 2)).execute();
        c.w().put("/payments/3.obj", new Payment("099", "106", 3)).execute();
        
        Iterator<Payment> iter = c.useIndex("pay-from", Payment.class).startAt("100")
                .inclusive(false).objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(1, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testStartAt3() {
        // backward, include
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("payments-from").type("string/unicode").dir("/payments/")
            .field("from").start().join();
        
        c.w().put("/payments/1.obj", new Payment("101", "105", 1)).execute();
        c.w().put("/payments/2.obj", new Payment("100", "106", 2)).execute();
        c.w().put("/payments/3.obj", new Payment("099", "106", 3)).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).startAt("100")
                .backward().objects().iterator();
        
        Payment p = iter.next();
        Assert.assertEquals(2, p.amount);
        p = iter.next();
        Assert.assertEquals(3, p.amount);
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @T
    public static void testStartAt4() {
        // backward, exclude
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("payments-from").type("string/unicode").dir("/payments/")
            .field("from").start().join();
        
        c.w().put("/payments/1.obj", new Payment("101", "105", 1)).execute();
        c.w().put("/payments/2.obj", new Payment("100", "106", 2)).execute();
        c.w().put("/payments/3.obj", new Payment("099", "106", 3)).execute();
        
        Iterator<Payment> iter = c.useIndex("payments-from", Payment.class).startAt("100")
                .backward().inclusive(false).objects().iterator();
        
        Payment p = iter.next();
        Assert.assertEquals(3, p.amount);
        Assert.assertFalse(iter.hasNext());
        database.stop();
    }
    
    @T
    public static void testStartAtLong1() {
        // forward, include, long index
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").type("long").dir("/payments/")
            .field("amount").start().join();
        
        c.w().put("/payments/20.obj", new Payment("101", "105", 20)).execute();
        c.w().put("/payments/30.obj", new Payment("100", "106", 30)).execute();
        c.w().put("/payments/10.obj", new Payment("099", "106", 10)).execute();
        
        Iterator<Payment> iter = c.useIndex("i0", Payment.class).startAt(20).objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(20, p.amount);
        p = iter.next();
        Assert.assertEquals(30, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void tStartAtLong2a() {
        // forward, include, long index
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("aaa").type("long").dir("/payments/")
            .field("amount").start().join();
        
        c.w().put("/payments/20.obj", new Payment("101", "105", 20)).execute();
        c.w().put("/payments/30.obj", new Payment("100", "106", 30)).execute();
        c.w().put("/payments/10.obj", new Payment("099", "106", 10)).execute();
        
        Iterator<Payment> iter = c.useIndex("aaa", Payment.class).startAt(20).inclusive(false)
                .objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(30, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void tStartAtLong2b() {
        // forward, include, long index
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("bb").type("long").dir("/payments/")
            .field("amount").start().join();
        
        c.w().put("/payments/20.obj", new Payment("101", "105", 20)).execute();
        c.w().put("/payments/30.obj", new Payment("100", "106", 30)).execute();
        c.w().put("/payments/10.obj", new Payment("099", "106", 10)).execute();
        
        Iterator<Payment> iter = c.useIndex("bb", Payment.class).startAt(20).inclusive(false)
                .objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(30, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void tStartAtLong2c() {        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("cc").type("long").dir("/p/")
            .field("amount").start().join();
        
        c.w().put("/p/a.obj", new Payment("", "", 2)).execute();
        c.w().put("/p/b.obj", new Payment("", "", 4)).execute();
        c.w().put("/p/c.obj", new Payment("", "", 6)).execute();
        
        Iterator<Payment> iter = c.useIndex("cc", Payment.class).startAt(4).inclusive(false)
                .objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(6, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testStartAtLong3() {
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i11").type("long").dir("/payments/")
            .field("amount").start().join();
        
        c.w().put("/payments/20.obj", new Payment("101", "105", -20)).execute();
        c.w().put("/payments/30.obj", new Payment("100", "106", -30)).execute();
        c.w().put("/payments/10.obj", new Payment("099", "106", 10)).execute();
        
        Iterator<Payment> iter = c.useIndex("i11", Payment.class).startAt(-25).inclusive(false)
                .objects().iterator();
        Payment p = iter.next();
        Assert.assertEquals(-20, p.amount);
        p = iter.next();
        Assert.assertEquals(10, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        iter = c.useIndex("i11", Payment.class).startAt(10).inclusive(false).backward()
                .objects().iterator();
        p = iter.next();
        Assert.assertEquals(-20, p.amount);
        p = iter.next();
        Assert.assertEquals(-30, p.amount);
        Assert.assertFalse(iter.hasNext());
        
        database.stop();
    }
    
    @T
    public static void testEqLong1() {
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").type("long").dir("/payments/")
            .field("amount").start().join();
        
        c.w().put("/payments/10.obj", new Payment("101", "105", 10)).execute();
        c.w().put("/payments/20.obj", new Payment("100", "106", 20)).execute();
        c.w().put("/payments/30.obj", new Payment("099", "106", 20)).execute();
        
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
    
    @T
    public static void testEqLong2() {
        // Same as previous, but uses backward().
        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").type("long").dir("/payments/")
            .field("amount").start().join();
        
        c.w().put("/payments/10.obj", new Payment("101", "105", 10)).execute();
        c.w().put("/payments/20.obj", new Payment("100", "106", 20)).execute();
        c.w().put("/payments/30.obj", new Payment("099", "106", 20)).execute();
        
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
    
    @T
    public static void testLongs256() {
        // Tests an index with all byte values 0..255 in a long.
        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").type("long").dir("/payments/")
            .field("amount").start().join();
        
        WBuilder b = c.w();
        for (int i = 0; i < 256; i++) {
            b.put("/payments/" + i + ".obj", new Payment("" + i, "" + (i+1), i));
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
    
    @T
    public static void testEqDouble1() {
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").type("double").dir("/payments/")
            .field("amount").start().join();
        
        c.w().put("/payments/10.obj", new DPayment("101", "105", 10.0)).execute();
        c.w().put("/payments/20.obj", new DPayment("100", "106", 20.0)).execute();
        c.w().put("/payments/30.obj", new DPayment("099", "106", 20.0)).execute();
        
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
    
    @T
    public static void testEqDouble2() {
        // Same as previous, but uses backward().
        
        Database database = Factory.database().memory().start();
        Connection c = database.newConnection();
        
        database.indexBuilder("i0").type("double").dir("/payments/")
            .field("amount").start().join();
        
        c.w().put("/payments/10.obj", new DPayment("101", "105", 10.0)).execute();
        c.w().put("/payments/20.obj", new DPayment("100", "106", 20.0)).execute();
        c.w().put("/payments/30.obj", new DPayment("099", "106", 20.0)).execute();
        
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
    
    @T
    public static void collationUnicode1() {
        String[] strings = new String[] {"a", "alfons", "AB", "AA", "", "B", "\n", "b", "0", "AAA", "~"};
        String[] expected = new String[]{"", "\n", "0", "AA", "AAA", "AB", "B", "a", "alfons", "b", "~"};
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("strings-s").type("string/unicode").dir("/strings/").field("s").start().join();
        
        WBuilder b = c.w();
        for (int i = 0; i < strings.length; i++) {
            b.put("/strings/" + i + ".obj", new MyString(strings[i]));
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
    
    @T
    public static void collationUnicode2() {
        // Tests sort order using strings that contain NUL characters (U+0000).
        // Sort is *stable* because of key naming: 0.obj, 1.obj, .., 5.obj.
        
        String[] strings = new String[] {"a", "\u0001", "\u0000", "", "\u0001a", "\u0000a"};
        String[] expected = new String[]{"", "\u0000", "\u0000a", "\u0001", "\u0001a"};
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("strings-s").type("string/unicode").dir("/strings/").field("s").start().join();
        
        WBuilder b = c.w();
        for (int i = 0; i < strings.length; i++) {
            b.put("/strings/" + i + ".obj", new MyString(strings[i]));
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
    
    @T
    public static void collationSv() {
        if (!IcuInfo.hasIcu()) {
            return;
        }
        
        String[] strings = new String[] {"a", "å", "ö", "Örjan", "", "Gästar", "Gast", "GB"};
        String[] expected = new String[]{"", "a", "Gast", "GB", "Gästar", "å", "ö", "Örjan"};
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("strings-s").type("string/sv").dir("/strings/").field("s").start().join();
        
        WBuilder b = c.w();
        for (int i = 0; i < strings.length; i++) {
            b.put("/strings/" + i + ".obj", new MyString(strings[i]));
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
    
    @T
    public static void collationSvL3() {
        if (!IcuInfo.hasIcu()) {
            return;
        }
        
        // L3 differentiates between "abba" and "Abba". Lower-case sorted first.
        // This test compares sort of sv/L1 and sv/L3.
        // We have a stable sort for L1 since object names increase like: 1.obj, 2.obj, ...
        
        String[] strings = new String[] {"Bert", "bert", "Abba", "ABBA", "abba"};
        String[] expectedL1 = new String[]{"Abba", "ABBA", "abba", "Bert", "bert"};
        String[] expectedL3 = new String[] {"abba", "Abba", "ABBA", "bert", "Bert"};
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("strings-s-L1").type("string/sv/L1").dir("/strings/").field("s").start().join();
        db.indexBuilder("strings-s-L3").type("string/sv/L3").dir("/strings/").field("s").start().join();
        
        WBuilder b = c.w();
        for (int i = 0; i < strings.length; i++) {
            b.put("/strings/" + i + ".obj", new MyString(strings[i]));
        }
        b.execute();
        
        Iterator<MyString> iter = c.useIndex("strings-s-L3", MyString.class).objects().iterator();
        for (int i = 0; i < expectedL3.length; i++) {
            Assert.assertTrue(iter.hasNext());
            MyString m = iter.next();
            Assert.assertEquals(expectedL3[i], m.s);
        }
        
        iter = c.useIndex("strings-s-L1", MyString.class).objects().iterator();
        for (int i = 0; i < expectedL1.length; i++) {
            Assert.assertTrue(iter.hasNext());
            MyString m = iter.next();
            Assert.assertEquals(expectedL1[i], m.s);
        }
        db.stop();
    }
    
    @T
    public static void collationPl() {
        if (!IcuInfo.hasIcu()) {
            return;
        }
        
        String[] strings = new String[] {"a", "Ż", "ź", "zebra", "sz", "środa", "bycie", "być"};
        String[] expected = new String[]{"a", "bycie", "być", "sz", "środa", "zebra", "ź", "Ż"};
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        db.indexBuilder("strings-s").type("string/pl").dir("/strings/").field("s").start().join();
        
        WBuilder b = c.w();
        for (int i = 0; i < strings.length; i++) {
            b.put("/strings/" + i + ".obj", new MyString(strings[i]));
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
    
    public static void main(String[] args) {
        //composite1();
    }
}
