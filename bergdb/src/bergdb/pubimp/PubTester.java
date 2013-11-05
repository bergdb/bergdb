package bergdb.pubimp;

import java.util.Iterator;

import bergdb.common.EventToWaitFor;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.Action;
import bergdb.pub.BadReplicaException;
import bergdb.pub.Clock;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.RwEnvironment;
import bergdb.pub.TestClock;
import bergdb.pub.Transaction;
import bergdb.pub.WBuilder;
import bergdb.stream.MemoryStream;

/**
 * General test class for Layer Pub.
 * Secondary indexing is tested by PubTesterIndex.
 * 
 * @author Frans Lundberg
 */
public class PubTester {
    
    @T
    public static void test1() {
        Database db = Factory.database().memory().start();
        Connection c = db.connection();
        c.w().put("/key1", "value1").execute();
        
        String value = c.get("/key1", String.class);
        Assert.assertEquals("value1", value);
        db.stop();
    }
    
    private static String v1;
    private static String v2;
    
    @T
    public static void testRw1() {
        Connection c = Factory.database().memory().start().connection();
        c.w().put("/key1", "value1").put("/key2", "value2..").execute();
        
        Transaction t = c.rw(new Action() { 
            public void run(RwEnvironment env) {
                v1 = env.get("/key1", String.class);
                v2 = env.get("/key2", String.class);
                env.put("/length", "" + (v1.length() + v2.length()));
            }
        });
        t.execute();
        
        Assert.assertEquals("value1", v1);
        Assert.assertEquals("value2..", v2);
        Assert.assertEquals("14", c.get("/length", String.class));
    }
    
    @T
    public static void testRw2() throws InterruptedException {
        //
        // An RW transaction that should result in an STM rerun of the transaction since another
        // thread modified one of the KVs in the read set.
        //
        
        Database db = Factory.database().memory().start();
        Connection c1 = db.connection();
        c1.w().put("/key1", "value1").put("/key2", "value2..").execute();
        
        final EventToWaitFor modifiedKey1 = new EventToWaitFor();
        final EventToWaitFor getDone = new EventToWaitFor();
        
        final Transaction t = c1.rw(new Action() { 
            public void run(RwEnvironment env) {
                v1 = env.get("/key1", String.class);
                v2 = env.get("/key2", String.class);
                getDone.happened();
                modifiedKey1.waitForEvent();
                String lengthString = "" + (v1.length() + v2.length());
                env.put("/length", lengthString);
            }
        });
        
        Connection c2 = db.connection();
        
        Thread thread = new Thread(new Runnable() {
            public void run() {
                t.execute();
            }
        });
        thread.start();
        
        getDone.waitForEvent();
        c2.w().put("/key1", "value1B").execute();
        modifiedKey1.happened();
        
        thread.join();
        
        Assert.assertEquals(2, ((RwTransaction) t).getRunCount());
        Assert.assertEquals("value2..", v2);
        Assert.assertEquals("15", c1.get("/length", String.class));
        db.stop();
    }
    
    public static class Person {
        public String name;
        
        public Person() {}
        
        public Person(String name) {
            this.name = name;
        }
    }
    
    @T
    public static void testDirManyObjects1() {
        // Lookup of large number of objects. DB.getMany() must be called several times.   
        manyObjects(233);
    }
    
    @T
    public static void testDirManyObjects2() {
        // Lookup of large number of objects. Exactly 200 objects (same as precisely 2 DB.getMany
        // calls).
        manyObjects(200);
    }
    
    private static void manyObjects(int count) {        
        Database db = Factory.database().memory().start();
        Connection c = db.connection();
        
        WBuilder b = c.w();
        for (int i = 0; i < count; i++) {
            b.put("/persons/" + (1000 + i), new Person("P" + (1000 + i)));
        }
        b.execute();
        
        Iterator<Person> persons = c.usePrimary(Person.class).dir("/persons/").objects().iterator();
        
        for (int i = 0; i < count; i++) {
            Assert.assertTrue(persons.hasNext());
            Person p = persons.next();
            Assert.assertEquals("P" + (1000 + i), p.name);
        }
        
        Assert.assertFalse(persons.hasNext());
        db.stop();
    }
    
    
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
    
    static class MyDouble {
        public double value;
        public String key;
        
        public MyDouble() {}
        
        public MyDouble(double v) {
            value = v;
        }
    }
    
    
    static class MyString {
        public String s;
        
        public MyString() {}
        
        public MyString(String s) {
            this.s = s;
        }
        
        public String toString() {
            return s;
        }
    }
    
    static class House {
        public House() {}
        public String key;
        public String name;
        public long area;
    }
    
    
    
    @T
    public static void testKeyReplace1() {
        // Two write transactions. transactionTime used in key.
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        String key = "/payments/${transactionTime}";
        Payment p1 = new Payment("100", "105", 120);
        Payment p2 = new Payment("100", "105", 200);
        
        c.setEnableKeyReplace(true);
        c.w().put(key, p1).execute();
        c.w().put(key, p2).execute();
        
        Iterator<Kv<Payment>> iter = c.usePrimary(Payment.class).dir("/payments/").kvs().iterator();
        
        String key1;
        String key2;
        Assert.assertTrue(iter.hasNext());
        Kv<Payment> kv = iter.next();
        key1 = kv.key();
        Assert.assertTrue(key1.startsWith("/payments/"));
        long t1 = Long.parseLong(key1.substring("/payments/".length()));
        Assert.assertTrue(iter.hasNext());
        
        kv = iter.next();
        key2 = kv.key();
        Assert.assertTrue(key2.startsWith("/payments/"));
        long t2 = Long.parseLong(key2.substring("/payments/".length()));
        Assert.assertFalse(iter.hasNext());
        Assert.assertFalse(key1.equals(key2));
        
        Assert.assertTrue(t2 > t1);
        database.stop();
    }
    
    @T
    public static void testFreezeLookupTime1() {
        TestClock clock = new TestClock();
        Database database = Factory.database().memory().clock(clock).start();
        Connection c1 = database.connection();
        
        clock.setTime(100);
        c1.w().put("/a", "1").put("/b", "2").execute();
        c1.freezeLookupTime();
        c1.get("/a", String.class);
        
        Connection c2 = database.newConnection();
        clock.setTime(200);
        c2.w().put("/b", "2b").put("/c", "3b").execute();
        
        Assert.assertEquals("2", c1.get("/b", String.class));
        Assert.assertNull(c1.get("/c", String.class));
        
        c1.setLookupTime(Long.MAX_VALUE);
        Assert.assertEquals("2b", c1.get("/b", String.class));
        Assert.assertEquals("3b", c1.get("/c", String.class));
        database.stop();
    }
    
    @T
    public static void nullStringField() {
        // Tests storing an object with a null field.
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        MyString s1 = new MyString(null);
        c.w().put("/d/s.obj", s1).execute();
        MyString s2 = c.get("/d/s.obj", MyString.class);
        Assert.assertNull(s2.s);
        d.stop();
    }
    
    public static class StringArrayClass {
        public String[] strings;
    }
    
    @T
    public static void nullStringArrayField1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        StringArrayClass a = new StringArrayClass();
        a.strings = null;
        c.w().put("/d/a.obj", a).execute();
        StringArrayClass b = c.get("/d/a.obj", StringArrayClass.class);
        Assert.assertNull(b.strings);
        d.stop();
    }
    
    @T
    public static void nullStringArrayField2() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        StringArrayClass a = new StringArrayClass();
        a.strings = new String[]{"", null};
        c.w().put("/d/a.obj", a).execute();
        StringArrayClass b = c.get("/d/a.obj", StringArrayClass.class);
        Assert.assertEquals(2, b.strings.length);
        Assert.assertEquals("", b.strings[0]);
        Assert.assertNull(b.strings[1]);
        d.stop();
    }
    
    public static class IntClass {
        int field;
    }
    
    @T
    public static void intField() {
        IntClass o1 = new IntClass();
        o1.field = 1234567890;
        
        Database d = Factory.database().memory().start();
        d.connection().w().put("/d/o1.obj", o1).execute();
        IntClass o2 = d.connection().get("/d/o1.obj", IntClass.class);
        Assert.assertEquals(o2.field, o1.field);
        d.stop();
    }
    
    @T
    public static void testRetainDuration1() {
        Database d = Factory.database().memory().build();
        
        long retain = d.getRetainDuration();
        Assert.assertTrue("retain = " + retain, retain > 0);
        
        d.setRetainDuration(Clock.UNITS_PER_SEC * 123);
        Assert.assertEquals(Clock.UNITS_PER_SEC * 123, d.getRetainDuration());
        d.stop();
    }
    
    @T
    public static void testRetainDuration2() {
        Database d = Factory.database().memory().build();
        
        long retain = d.getRetainDuration();
        Assert.assertTrue("retain = " + retain, retain > 0);
        
        d.start();
        d.connection().w().put("/key", "value").execute();
        d.setRetainDuration(Clock.UNITS_PER_SEC * 21);
        
        d.connection().w().put("/key2", "value2").execute();
        Assert.assertEquals(Clock.UNITS_PER_SEC * 21, d.getRetainDuration());
        d.stop();
    }
    
    @T
    public static void testObjectInRootDir() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        c.w().put("/myDouble.obj", new MyDouble(12.3)).execute();
        MyDouble myDouble = c.get("/myDouble.obj", MyDouble.class);
        
        Assert.assertEquals(12.3, myDouble.value, 0.00001);
    }
    
    @T
    public static void minimalCodeToStoreObject() {
        MyDouble a = new MyDouble(1.2);
        a.key = "/a.obj";
        
        // One-liner with database creation.
        Factory.database().memory().start().connection().w().put(a).execute();
        
        Connection c = Factory.database().memory().start().connection();
        
        // Given connection, it is a short one-liner to store an object (assumes key field).
        c.w().put(a).execute();
        
        // To retrieve it.
        c.get("/a.obj", MyDouble.class);
        
        
        // To update in a atomic read-write transaction
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                MyDouble a = env.get("/a.obj", MyDouble.class);
                a.value = a.value + 2.0;
                env.put(a);
            }
        }).execute();
    }
    
    @T
    public static void testSync1() {
        // Tests Transaction.sync().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a.obj";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).build();
        t.execute();
        t.sync();
        Assert.assertEquals(((WTransaction)t).getTrans().lastSpos,
                ((DatabaseImp) d).getDb().getStreamLength() - 1);
    }
    
    @T
    public static void testSync2() {
        // Tests Transaction.syncStrong().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a.obj";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).build();
        t.execute();
        t.syncStrong();
        Assert.assertEquals(((WTransaction)t).getTrans().lastSpos,
                ((DatabaseImp) d).getDb().getStreamLength() - 1);
    }
    
    @T
    public static void testSync3() {
        // Tests Connection.sync().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a.obj";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).build();
        t.execute();
        c.sync();
        Assert.assertEquals(((WTransaction)t).getTrans().lastSpos,
                ((DatabaseImp) d).getDb().getStreamLength() - 1);
    }
    
    @T
    public static void testSync4() {
        // Tests Connection.syncStrong().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a.obj";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).build();
        t.execute();
        c.syncStrong();
        Assert.assertEquals(((WTransaction)t).getTrans().lastSpos,
                ((DatabaseImp) d).getDb().getStreamLength() - 1);
    }
    
    @T
    public static void testSync5() {
        // Tests Database.sync().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a.obj";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).build();
        t.execute();
        d.sync();
        Assert.assertEquals(((WTransaction)t).getTrans().lastSpos,
                ((DatabaseImp) d).getDb().getStreamLength() - 1);
    }
    
    @T
    public static void testSync6() {
        // Tests Database.syncStrong().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a.obj";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).build();
        t.execute();
        d.syncStrong();
        Assert.assertEquals(((WTransaction)t).getTrans().lastSpos,
                ((DatabaseImp) d).getDb().getStreamLength() - 1);
    }
    
    @T
    public static void testBadStartReplica() {
        MemoryStream m0 = new MemoryStream();
        DatabaseBuilderImp b = (DatabaseBuilderImp) Factory.database();
        Database d = b.mainStream(m0).start();
        Connection c = d.connection();
        c.w().put("/s1.txt", "S1-m0").execute();
        d.sync();
        d.stop();
        
        MemoryStream m1 = new MemoryStream();
        b = (DatabaseBuilderImp) Factory.database();
        d = b.mainStream(m1).start();
        c = d.connection();
        c.w().put("/s1.txt", "S1-m1-hej").execute();
        d.sync();
        d.stop();
        
        //System.out.println("m0: " + m0.getLength());
        //System.out.println("m1: " + m1.getLength());
        
        b = (DatabaseBuilderImp) Factory.database();
        b.stream("m0", m0);
        b.stream("m1", m1);
        d = b.build();
        
        BadReplicaException ex = null;
        try {
            d.start();
        } catch (BadReplicaException e) {
            ex = e;
        }
        
        Assert.assertTrue("We should get BadReplicaException", ex != null);
    }
    
    private static class A {
        public String key;
        public String name;
        public A() {}
        public A(String key, String name) {
            this.key = key;
            this.name = name;
        }
    }
    
    private static class A2 {
        private String key;
        private String name;
    }
    
    
    @T
    public static void testKeyField0() {
        // Uses key field, get.
        
        A a0 = new A();
        a0.name = "Saltis";
        
        Database d = Factory.database().memory().start();
        d.connection().w().put("/a.obj", a0).execute();
        
        A a1 = d.connection().get("/a.obj", A.class);
        Assert.assertEquals("Saltis", a1.name);
        Assert.assertEquals("/a.obj", a1.key);
    }
    
    @T
    public static void testKeyField0Private() {
        // Uses private key field, get.
        
        A2 a0 = new A2();
        a0.name = "Saltis";
        
        Database d = Factory.database().memory().start();
        d.connection().w().put("/a.obj", a0).execute();
        
        A2 a1 = d.connection().get("/a.obj", A2.class);
        Assert.assertEquals("Saltis", a1.name);
        Assert.assertEquals("/a.obj", a1.key);
    }
    
    @T
    public static void testKeyField1() {
        // Uses key field, set.
        
        A a0 = new A();
        a0.name = "Saltis";
        a0.key = "/a.obj";
        
        Database d = Factory.database().memory().start();
        d.connection().w().put(a0).execute();
        
        A a1 = d.connection().get("/a.obj", A.class);
        Assert.assertEquals("Saltis", a1.name);
        Assert.assertEquals("/a.obj", a1.key);
    }
    
    
    
    @T
    public static void testKeyField2() {
        // Uses key field, rw get.
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        final House h0 = new House();
        h0.key = null;
        h0.area = 120;
        h0.name = "MyHome";
        
        c.w().put("/h.obj", h0).execute();
        
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                House h = env.get("/h.obj", House.class);
                Assert.assertEquals("/h.obj", h.key);
                Assert.assertEquals("MyHome", h.name);
            }
        }).execute();
        
        database.stop();
    }
    
    
    @T
    public static void testKeyField3() {
        // Uses key field, rw set.
        
        // Arrange
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        final House house = new House();
        house.key = "/h.obj";
        house.area = 120;
        house.name = "MyHome";
        
        // Act
        
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                env.put(house);
            }
        }).execute();
        
        // Assert
        
        House house2 = c.get("/h.obj", House.class);
        Assert.assertEquals("MyHome", house2.name);
        Assert.assertEquals("/h.obj", house2.key);
        
        database.stop();
    }
    
    private static class S {
        String key;
    }
    
    private static class D extends S {
        String s;
    }
    
    @T
    public static void testKeyFieldInSuperClass0() {
        // key field in super class, set
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        D obj0 = new D();
        obj0.key = "/k.obj";
        obj0.s = "hello";
        
        c.w().put(obj0).execute();
        
        D obj1 = c.get("/k.obj", D.class);
        Assert.assertEquals("/k.obj", obj1.key);
        Assert.assertEquals("hello", obj1.s);
        
        database.stop();
    }
    
    @T
    public static void testKeyFieldInSuperClass1() {
        // key field in super class, get
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        D obj0 = new D();
        obj0.key = null;
        obj0.s = "hello";
        
        c.w().put("/k.obj", obj0).execute();
        
        D obj1 = c.get("/k.obj", D.class);
        Assert.assertEquals("/k.obj", obj1.key);
        Assert.assertEquals("hello", obj1.s);
        
        d.stop();
    }
    
    @T
    public static void testKeyFieldWithIterator() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/dir/a0", new A(null, "a0"))
             .put("/dir/a1", new A(null, "a1")).execute();
        
        int index = 0;
        for (A a : c.usePrimary(A.class).objects()) {
            Assert.assertEquals("/dir/a" + index, a.key);
            index++;
        }
        
        d.stop();
    }
    
    @T
    @SuppressWarnings("unused")
    public static void testKeyFieldWithDbObject0() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/a.obj", new Object() { String name = "Carl"; }).execute();
        DbObject dbo = c.get("/a.obj", DbObject.class);
        
        Assert.assertEquals("/a.obj", dbo.getString("key"));
        Assert.assertEquals("Carl", dbo.getString("name"));
        
        d.stop();
    }
    
    @T
    public static void testKeyFieldWithDbObject1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        DbObject dbo0 = new DbObject.Builder().addString("key", "/a.obj").addInt("b", 123).build();
        c.w().put(dbo0).execute();
        
        DbObject dbo1 = c.get("/a.obj", DbObject.class);
        
        Assert.assertEquals("/a.obj", dbo1.getString("key"));
        Assert.assertEquals(123, dbo1.getInt("b"));
        
        d.stop();
    }
    
    @T
    @SuppressWarnings("unused")
    public static void testAnonymous0() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/a.obj", new Object() { String name = "Gustav"; int b = 123; }).execute();
        DbObject dbo = c.get("/a.obj", DbObject.class);
        
        Assert.assertEquals("Gustav", dbo.getString("name"));
        Assert.assertEquals(123, dbo.getInt("b"));
        d.stop();
    }
    
    @T
    @SuppressWarnings("unused")
    public static void testAnonymous1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put(new Object() { String key = "/a.obj"; int b = 123; }).execute();
        DbObject dbo = c.get("/a.obj", DbObject.class);
        
        Assert.assertEquals("/a.obj", dbo.getString("key"));
        Assert.assertEquals(123, dbo.getInt("b"));
        d.stop();
    }
    
    @T
    public static void testDbObject0() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        DbObject dbo = new DbObject.Builder().addInt("i", 123).addString("s", "hello").build();
        c.w().put("/a.obj", dbo).execute();
        DbObject o = c.get("/a.obj", DbObject.class);
        
        Assert.assertEquals("hello", o.getString("s"));
        Assert.assertEquals(123, o.getInt("i"));
        
        d.stop();
    }
    
    @T
    public static void testDbObject1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        DbObject dbo = new DbObject.Builder().addInt("i", 123).addString(PubUtil.KEY_FIELD, "/a.obj").build();
        c.w().put(dbo).execute();
        DbObject o = c.get("/a.obj", DbObject.class);
        
        Assert.assertEquals("/a.obj", o.getString(PubUtil.KEY_FIELD));
        Assert.assertEquals(123, o.getInt("i"));
        
        d.stop();
    }
    
    @T
    public static void testBadKey() {
        IllegalArgumentException ex = null;
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        try {
            c.w().put("k", "v");
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        d.stop();
        Assert.assertTrue(ex != null);
    }
    
    @T
    public static void testStoreArray() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/strings.obj", new String[]{"adam", "eve"}).execute();
        String[] strings = c.get("/strings.obj", String[].class);
        d.stop();
        
        Assert.assertEquals(2, strings.length);
        Assert.assertEquals("adam", strings[0]);
        Assert.assertEquals("eve", strings[1]);
    }
    
    @T
    public static void testStorePrimitive() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/myInt.obj", 123).execute();
        int myInt = c.get("/myInt.obj", int.class);
        d.stop();
        
        Assert.assertEquals(123, myInt);
    }
    
    public static void main(String[] args) {
        //
    }
}
