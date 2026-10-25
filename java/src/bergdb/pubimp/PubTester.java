package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.io.UnsupportedEncodingException;
import java.util.Iterator;
import java.util.Set;
import java.util.function.Consumer;

import bergdb.common.EventToWaitFor;
import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbStoppingException;
import bergdb.core.DbTester;
import bergdb.core.DbTesterFailure;
import bergdb.core.SyncLevel;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.RwEnvironment;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.TransactionInfo;
import bergdb.pub.WBuilder;
import bergdb.pub.util.BadCryptoKey;
import bergdb.pub.util.BadReplicaException;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.storage.BufferedStream;
import bergdb.storage.RecoverableStream;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.SalsaStream;

/**
 * General test class for Layer Pub.
 * Secondary indexing is tested by PubTesterIndex.
 * 
 * @author Frans Lundberg
 */
public class PubTester {
    
    @Nano
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
    
    @Nano
    public static void testRw1() {
        Connection c = Factory.database().memory().start().connection();
        c.w().put("/key1", "value1").put("/key2", "value2..").execute();
        
        c.rw(new Action() { 
            public void run(RwEnvironment env) {
                v1 = env.get("/key1", String.class);
                v2 = env.get("/key2", String.class);
                env.put("/length", "" + (v1.length() + v2.length()));
            }
        });
        
        Assert.assertEquals("value1", v1);
        Assert.assertEquals("value2..", v2);
        Assert.assertEquals("14", c.get("/length", String.class));
    }
    
    @Nano
    public static void testRw2() throws InterruptedException {
        //
        // An RW transaction that should result in an STM rerun of the transaction since another
        // thread modified one of the KVs in the read set.
        //
        
        Database db = Factory.database().memory().start();
        final Connection c1 = db.connection();
        c1.w().put("/key1", "value1").put("/key2", "value2..").execute();
        
        final EventToWaitFor modifiedKey1 = new EventToWaitFor();
        final EventToWaitFor getDone = new EventToWaitFor();
        
        final Action action = new Action() { 
            public void run(RwEnvironment env) {
                v1 = env.get("/key1", String.class);
                v2 = env.get("/key2", String.class);
                getDone.happened();
                modifiedKey1.waitForEvent();
                String lengthString = "" + (v1.length() + v2.length());
                env.put("/length", lengthString);
            }
        };
        
        Connection c2 = db.connection();
        final Transaction[] transactionArray = new Transaction[1];
        
        Thread thread = new Thread(new Runnable() {
            public void run() {
                transactionArray[0] = c1.rw(action);
            }
        });
        thread.start();
        
        getDone.waitForEvent();
        c2.w().put("/key1", "value1B").execute();
        modifiedKey1.happened();
        
        thread.join();
        
        Assert.assertEquals(2, ((RwTransaction) transactionArray[0]).getRunCount());
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
    
    @Nano
    public static void testDirManyObjects1() {
        // Lookup of large number of objects. DB.getMany() must be called several times.   
        manyObjects(233);
    }
    
    @Nano
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
    
    
    
    @Nano
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
    
    @Nano
    public static void testFreezeLookupTime1() {
        TestClock clock = new TestClock();
        Database database = Factory.database().memory().clock(clock).start();
        Connection c1 = database.connection();
        
        clock.setTime(Time.units(100));
        c1.w().put("/a", "1").put("/b", "2").execute();
        c1.freezeLookupTime();
        c1.get("/a", String.class);
        
        Connection c2 = database.newConnection();
        clock.setTime(Time.units(200));
        c2.w().put("/b", "2b").put("/c", "3b").execute();
        
        Assert.assertEquals("2", c1.get("/b", String.class));
        Assert.assertNull(c1.get("/c", String.class));
        
        c1.setLookupTime(Time.MAX);
        Assert.assertEquals("2b", c1.get("/b", String.class));
        Assert.assertEquals("3b", c1.get("/c", String.class));
        database.stop();
    }
    
    @Nano
    public static void nullStringField() {
        // Tests storing an object with a null field.
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        MyString s1 = new MyString(null);
        c.w().put("/d/s", s1).execute();
        MyString s2 = c.get("/d/s", MyString.class);
        Assert.assertNull(s2.s);
        d.stop();
    }
    
    public static class StringArrayClass {
        public String[] strings;
    }
    
    @Nano
    public static void nullStringArrayField1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        StringArrayClass a = new StringArrayClass();
        a.strings = null;
        c.w().put("/d/a", a).execute();
        StringArrayClass b = c.get("/d/a", StringArrayClass.class);
        Assert.assertNull(b.strings);
        d.stop();
    }
    
    @Nano
    public static void nullStringArrayField2() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        StringArrayClass a = new StringArrayClass();
        a.strings = new String[]{"", null};
        c.w().put("/d/a", a).execute();
        StringArrayClass b = c.get("/d/a", StringArrayClass.class);
        Assert.assertEquals(2, b.strings.length);
        Assert.assertEquals("", b.strings[0]);
        Assert.assertNull(b.strings[1]);
        d.stop();
    }
    
    public static class IntClass {
        int field;
    }
    
    @Nano
    public static void intField() {
        IntClass o1 = new IntClass();
        o1.field = 1234567890;
        
        Database d = Factory.database().memory().start();
        d.connection().w().put("/d/o1", o1).execute();
        IntClass o2 = d.connection().get("/d/o1", IntClass.class);
        Assert.assertEquals(o2.field, o1.field);
        d.stop();
    }
    
    @Nano
    public static void testRetainDuration1() {
        Database d = Factory.database().memory().start();
        
        Duration duration = d.getRetainDuration();
        Assert.assertTrue(duration.units() > 0);
        
        d.setRetainDuration(Duration.seconds(123.0));
        Assert.assertEquals(Duration.seconds(123.0), d.getRetainDuration());
        d.stop();
    }
    
    @Nano
    public static void testRetainDuration2() {
        DatabaseBuilder builder = Factory.database().memory();
        Database d = builder.start();
        d.connection().w().put("/key", "value").execute();
        d.setRetainDuration(Duration.seconds(21));
        
        d.connection().w().put("/key2", "value2").execute();
        Assert.assertEquals(Duration.seconds(21.0), d.getRetainDuration());
        d.stop();
    }
    
    /**
     * Database.getFirstAvailableLookupTime() with infinite retention, the default: nothing is
     * reclaimed, so the time stays while the clock moves on (bergdb 005-10: the method
     * returned the current time).
     */
    @Nano
    public static void testFirstAvailableLookupTime1() {
        TestClock clock = new TestClock();
        Database d = Factory.database().memory().clock(clock).start();
        Connection c = d.connection();
        clock.setTime(Time.units(100));
        c.w().put("/a", "1").execute();
        Time first = d.getFirstAvailableLookupTime();
        
        clock.setTime(Time.units(1000 * 1000));
        c.w().put("/a", "2").execute();
        Assert.assertEquals(first, d.getFirstAvailableLookupTime());
        Assert.assertEquals(((DatabaseImp) d).getDb().getFirstAvailableLookupTime(), 
                d.getFirstAvailableLookupTime().units());
        Assert.assertTrue(d.getFirstAvailableLookupTime().units() < d.currentTime().units());
        
        c.setLookupTime(Time.units(100));
        Assert.assertEquals("1", c.get("/a", String.class));
        d.stop();
    }
    
    /**
     * Database.getFirstAvailableLookupTime() with a finite retain duration: reclaim moves the
     * time forward, never back, and keeps the retain duration; a lookup at the time works, one
     * before it throws LookupTimeNotAvailableException. The database is made with the core's
     * builder, as the Pub API's sets a startup distance of at least 5 MB, and reclaim only
     * cuts in front of the startup section: with 2000 bytes the first cut comes soon.
     */
    @Nano
    public static void testFirstAvailableLookupTime2() {
        TestClock clock = new TestClock();
        Db db = Db.builder().testSetup(new CutStream()).clock(clock).maxNodeSize8()
                .startupDistance(2000).build();
        Database d = DatabaseImp.createAndStart(db);
        Duration retain = Duration.seconds(1);
        d.setRetainDuration(retain);
        Connection c = d.connection();
        
        long sec = Duration.seconds(1).units();
        long time = sec;
        long last = 0;
        java.util.Random r = new java.util.Random(1);
        for (int i = 0; i < 20000 && last == 0; i++) {
            time += sec / 20;
            clock.setTime(Time.units(time));
            c.w().put("/k/" + r.nextInt(50), "v" + i).execute();
            long first = d.getFirstAvailableLookupTime().units();
            Assert.assertTrue("moved back: " + first + " < " + last, first >= last);
            last = first;
        }
        
        Assert.assertTrue("the first available lookup time never moved", last > 0);
        Assert.assertTrue("the retain duration is not kept: " + last + ", now " + time, 
                last <= time - retain.units());
        Assert.assertEquals(db.getFirstAvailableLookupTime(), last);
        
        c.setLookupTime(Time.units(last));
        c.get("/k/0", String.class);
        
        c.setLookupTime(Time.units(last - 1));
        LookupTimeNotAvailableException ex = null;
        try {
            c.get("/k/0", String.class);
        } catch (LookupTimeNotAvailableException e) {
            ex = e;
        }
        Assert.assertTrue("a lookup before the first available lookup time did not throw", 
                ex != null);
        d.stop();
    }
    
    @Nano
    public static void testObjectInRootDir() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        c.w().put("/myDouble", new MyDouble(12.3)).execute();
        MyDouble myDouble = c.get("/myDouble", MyDouble.class);
        
        Assert.assertEquals(12.3, myDouble.value, 0.00001);
    }
    
    @Nano
    public static void minimalCodeToStoreObject() {
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        // One-liner with database creation.
        Factory.database().memory().start().connection().w().put(a).execute();
        
        Connection c = Factory.database().memory().start().connection();
        
        // Given connection, it is a short one-liner to store an object (assumes key field).
        c.w().put(a).execute();
        
        // To retrieve it.
        c.get("/a", MyDouble.class);
        
        
        // To update in a atomic read-write transaction
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                MyDouble a = env.get("/a", MyDouble.class);
                a.value = a.value + 2.0;
                env.put(a);
            }
        });
    }
    
    @Nano
    public static void testSync1() {
        // Tests Transaction.sync().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).execute();
        t.sync();
        
        assertThatTransWrittenCompletely(d, t);
    }

    private static void assertThatTransWrittenCompletely(Database d, Transaction t) {
        long lastStreamPos = ((DatabaseImp) d).getDb().getStreamLength() - 1;
        long lastTransPos = ((WTransaction)t).getTrans().lastPos;
        Assert.assertTrue(lastStreamPos >= lastTransPos);
    }
    
    @Nano
    public static void testSync2() {
        // Tests Transaction.syncStrong().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).execute();
        t.sync(SyncLevel.STRONG);
     
        assertThatTransWrittenCompletely(d, t);
    }
    
    @Nano
    public static void testSync3() {
        // Tests Connection.sync().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).execute();
        c.sync();
        
        assertThatTransWrittenCompletely(d, t);
    }
    
    @Nano
    public static void testSync4() {
        // Tests Connection.syncStrong().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).execute();
        c.sync(SyncLevel.STRONG);
        
        assertThatTransWrittenCompletely(d, t);
    }
    
    @Nano
    public static void testSync5() {
        // Tests Database.sync().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).execute();
        d.sync();
        
        assertThatTransWrittenCompletely(d, t);
    }
    
    @Nano
    public static void testSync6() {
        // Tests Database.syncStrong().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put(a).execute();
        d.sync(SyncLevel.STRONG);
        
        assertThatTransWrittenCompletely(d, t);
    }
    
    @Nano
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
        
        b = (DatabaseBuilderImp) Factory.database();
        b.stream("m0", m0);
        b.stream("m1", m1);
        
        BadReplicaException ex = null;
        try {
            b.start();
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
    
    
    @Nano
    public static void testKeyField0() {
        // Uses key field, get.
        
        A a0 = new A();
        a0.name = "Saltis";
        
        Database d = Factory.database().memory().start();
        d.connection().w().put("/a", a0).execute();
        
        A a1 = d.connection().get("/a", A.class);
        Assert.assertEquals("Saltis", a1.name);
        Assert.assertEquals("/a", a1.key);
    }
    
    @Nano
    public static void testKeyField0Private() {
        // Uses private key field, get.
        
        A2 a0 = new A2();
        a0.name = "Saltis";
        
        Database d = Factory.database().memory().start();
        d.connection().w().put("/a", a0).execute();
        
        A2 a1 = d.connection().get("/a", A2.class);
        Assert.assertEquals("Saltis", a1.name);
        Assert.assertEquals("/a", a1.key);
    }
    
    @Nano
    public static void testKeyField1() {
        // Uses key field, set.
        
        A a0 = new A();
        a0.name = "Saltis";
        a0.key = "/a";
        
        Database d = Factory.database().memory().start();
        d.connection().w().put(a0).execute();
        
        A a1 = d.connection().get("/a", A.class);
        Assert.assertEquals("Saltis", a1.name);
        Assert.assertEquals("/a", a1.key);
    }
    
    
    
    @Nano
    public static void testKeyField2() {
        // Uses key field, rw get.
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        final House h0 = new House();
        h0.key = null;
        h0.area = 120;
        h0.name = "MyHome";
        
        c.w().put("/h", h0).execute();
        
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                House h = env.get("/h", House.class);
                Assert.assertEquals("/h", h.key);
                Assert.assertEquals("MyHome", h.name);
            }
        });
        
        database.stop();
    }
    
    
    @Nano
    public static void testKeyField3() {
        // Uses key field, rw set.
        
        // Arrange
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        final House house = new House();
        house.key = "/h";
        house.area = 120;
        house.name = "MyHome";
        
        // Act
        
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                env.put(house);
            }
        });
        
        // Assert
        
        House house2 = c.get("/h", House.class);
        Assert.assertEquals("MyHome", house2.name);
        Assert.assertEquals("/h", house2.key);
        
        database.stop();
    }
    
    private static class S {
        String key;
    }
    
    private static class D extends S {
        String s;
    }
    
    @Nano
    public static void testKeyFieldInSuperClass0() {
        // key field in super class, set
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        D obj0 = new D();
        obj0.key = "/k";
        obj0.s = "hello";
        
        c.w().put(obj0).execute();
        
        D obj1 = c.get("/k", D.class);
        Assert.assertEquals("/k", obj1.key);
        Assert.assertEquals("hello", obj1.s);
        
        database.stop();
    }
    
    @Nano
    public static void testKeyFieldInSuperClass1() {
        // key field in super class, get
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        D obj0 = new D();
        obj0.key = null;
        obj0.s = "hello";
        
        c.w().put("/k", obj0).execute();
        
        D obj1 = c.get("/k", D.class);
        Assert.assertEquals("/k", obj1.key);
        Assert.assertEquals("hello", obj1.s);
        
        d.stop();
    }
    
    @Nano
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
    
    @Nano
    @SuppressWarnings("unused")
    public static void testKeyFieldWithDbObject0() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/a", new Object() { String name = "Carl"; }).execute();
        DbObject dbo = c.get("/a", DbObject.class);
        
        Assert.assertEquals("/a", dbo.getString("key"));
        Assert.assertEquals("Carl", dbo.getString("name"));
        
        d.stop();
    }
    
    @Nano
    public static void testKeyFieldWithDbObject1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        DbObject dbo0 = new DbObject.Builder().addString("key", "/a").addInt("b", 123).build();
        c.w().put(dbo0).execute();
        
        DbObject dbo1 = c.get("/a", DbObject.class);
        
        Assert.assertEquals("/a", dbo1.getString("key"));
        Assert.assertEquals(123, dbo1.getInt("b"));
        
        d.stop();
    }
    
    @Nano
    @SuppressWarnings("unused")
    public static void testAnonymous0() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/a", new Object() { String name = "Gustav"; int b = 123; }).execute();
        DbObject dbo = c.get("/a", DbObject.class);
        
        Assert.assertEquals("Gustav", dbo.getString("name"));
        Assert.assertEquals(123, dbo.getInt("b"));
        d.stop();
    }
    
    @Nano
    @SuppressWarnings("unused")
    public static void testAnonymous1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put(new Object() { String key = "/a"; int b = 123; }).execute();
        DbObject dbo = c.get("/a", DbObject.class);
        
        Assert.assertEquals("/a", dbo.getString("key"));
        Assert.assertEquals(123, dbo.getInt("b"));
        d.stop();
    }
    
    @Nano
    public static void testDbObject0() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        DbObject dbo = new DbObject.Builder().addInt("i", 123).addString("s", "hello").build();
        c.w().put("/a", dbo).execute();
        DbObject o = c.get("/a", DbObject.class);
        
        Assert.assertEquals("hello", o.getString("s"));
        Assert.assertEquals(123, o.getInt("i"));
        
        d.stop();
    }
    
    @Nano
    public static void testDbObject1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        DbObject dbo = new DbObject.Builder()
            .addInt("i", 123)
            .addString(PubUtil.KEY_FIELD, "/a")
            .build();
        
        c.w().put(dbo).execute();
        DbObject o = c.get("/a", DbObject.class);
        
        Assert.assertEquals("/a", o.getString(PubUtil.KEY_FIELD));
        Assert.assertEquals(123, o.getInt("i"));
        
        d.stop();
    }
    
    @Nano
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
    
    @Nano
    public static void testStoreArray() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/strings", new String[]{"adam", "eve"}).execute();
        String[] strings = c.get("/strings", String[].class);
        d.stop();
        
        Assert.assertEquals(2, strings.length);
        Assert.assertEquals("adam", strings[0]);
        Assert.assertEquals("eve", strings[1]);
    }
    
    @Nano
    public static void testStorePrimitive() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/myInt", 123).execute();
        int myInt = c.get("/myInt", int.class);
        d.stop();
        
        Assert.assertEquals(123, myInt);
    }
    
    @Nano
    public static void testSetLookupWithTimeString1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        c.setLookupTime(Time.resolve(Time.UTC, "1970-01-01 00:00:01"));
        c.get("/key", String.class);
        Time time = c.getLookupTime();
        Assert.assertEquals(Time.millis(1000), time);
        d.stop();
    }
    
    @Nano
    public static void testSetLookupWithTimeString2() {
        TestClock clock = new TestClock();
        clock.setTime(Time.utc("1970-01-01 00:02:03.000"));       // UTC 1970-01-01 00:02:03.000
        Database d = Factory.database().memory().clock(clock).start();
        Time dbTime = d.currentTime();
        Time time1 = Time.resolve(Time.UTC, dbTime, "00:01");
        Time time2 = Time.millis(60 * 1000);
        Assert.assertEquals(time2, time1);
        d.stop();
    }
    
    @Nano
    public static void testCurrentTime() {
        TestClock clock = new TestClock();
        Time t0 = Time.utc("2010-01-01 00:02:03.0000000");
        clock.setTime(t0);
        Database d = Factory.database().memory().clock(clock).start();
        Transaction t = d.connection().put("/key", "value");
        Time t1 = t0.add(Duration.units(10));
        Time transTime = t.getTime();
        
        Assert.assertTrue(transTime.isBetween(t0, t1));
        d.stop();
    }
    
    @Nano
    public static void testHistoric1() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        c.put("/key", "v1");
        Time t1 = database.currentTime();
        c.put("/key", "v2");
        Time t2 = database.currentTime();
        c.put("/key", "v3");
        Time t3 = database.currentTime();
        
        c.setLookupTime(t1);
        Assert.assertEquals("v1", c.get("/key", String.class));
        c.setLookupTime(t2);
        Assert.assertEquals("v2", c.get("/key", String.class));
        c.setLookupTime(t3);
        Assert.assertEquals("v3", c.get("/key", String.class));
        
        database.stop();
    }
    
    // ---- Tests Connection.delete() ----
    
    @Nano
    public static void testThatSimpleDeleteWorks() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        String key = "/key";
        c.put(key, "v1");
        Assert.assertTrue(c.exists(key));
        c.delete(key);
        Assert.assertFalse(c.exists(key));
        
        database.stop();
    }
    
    @Nano
    public static void testDeleteWithNullNotPossible() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        String key = "/key";
        c.put(key, "v1");
        Assert.assertTrue(c.exists(key));
        
        IllegalArgumentException ex = null;
        try {
            c.put(key, null);
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
        database.stop();
    }
    
    @Nano
    public static void testDeleteInW() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        c.w().put("/k1", "v1").put("/k2", "v2").execute();
        c.w().put("/k3", "v3").delete("/k1").execute();
        
        Assert.assertFalse(c.exists("/k1"));
        Assert.assertTrue(c.exists("/k2"));
        Assert.assertTrue(c.exists("/k3"));
        
        database.stop();
    }
    
    @Nano
    public static void testDeleteInRW() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        c.w().put("/k1", "v1").put("/k2", "v2").execute();
        
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                env.delete("/k2");
                env.delete("/k9");
            }
        });
        
        Assert.assertTrue(c.exists("/k1"));
        Assert.assertFalse(c.exists("/k2"));
        Assert.assertEquals(1, countEntries(c));
        
        database.stop();
    }
    
    @SuppressWarnings("unused")
    private static int countEntries(Connection c) {
        int count = 0;
        
        for (byte[] value : c.usePrimary(byte[].class).dir("/").objects()) {
            count++;
        }
        
        return count;
    }
    
    @Nano
    public static void testDeleteOfNonExistantEntry() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        c.w().put("/k1", "v1").put("/k2", "v2").execute();
        c.delete("/k1");
        c.delete("/k5");
        
        Assert.assertEquals(1, countEntries(c));
        database.stop();
    }
    
    @Nano
    public static void testStartupInfoTime() {
        Database database = Factory.database().memory().start();        
        double time = database.getStartupInfo().getStartupDuration();
        Assert.assertTrue("time:" + time, time > 0.0);
        
        database.stop();
    }
    
    @Nano
    public static void testEncrypted1() throws IOException {
        // Creates an encrypted database, makes sure beginning of encrypted bytes not
        // same as unencrypted bytes.
        
        CryptoKey cryptoKey = CryptoKey.parse("8184a9f2-salsa-75ac20b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c");
        
        Database database = Factory.database().memory().cryptoKey(cryptoKey).start();
        
        DatabaseImp imp = (DatabaseImp) database;
        BufferedStream buffered = (BufferedStream) imp.getDb().internal().getMainStream();
        SalsaStream salsa = (SalsaStream) buffered.getUnderlyingStream();
        MemoryStream memory = (MemoryStream) salsa.getUnderlyingStream();
        
        Connection c = database.connection();
        c.put("/s1", "Hej!");
        c.sync();
        
        byte[] firstEncryptedBytes = new byte[8];
        memory.read(0, firstEncryptedBytes, 0, firstEncryptedBytes.length);
        
        byte[] firstUnencryptedBytes = new byte[8];
        salsa.read(0, firstUnencryptedBytes, 0, firstUnencryptedBytes.length);
        
        String magic = new String(firstUnencryptedBytes, 0, 4, "UTF-8");
        
        Assert.assertEquals("berg", magic);
        Assert.assertFalse(Util.areEqual(firstUnencryptedBytes, firstEncryptedBytes));
    }
    
    @Nano
    public static void testEncrypted2() throws IOException {
        // Creates an encrypted database, writes to it, closes it, and reopens it.
        
        CryptoKey cryptoKey = CryptoKey.parse("8184a9f2-salsa-75ac20b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c");
        
        Database database = Factory.database().memory().cryptoKey(cryptoKey).start();
        
        DatabaseImp imp = (DatabaseImp) database;
        BufferedStream buffered = (BufferedStream) imp.getDb().internal().getMainStream();
        SalsaStream salsa = (SalsaStream) buffered.getUnderlyingStream();
        MemoryStream memory = (MemoryStream) salsa.getUnderlyingStream();
        
        Connection c = database.connection();
        c.put("/s1", "Hej!");
        c.sync();
        
        database.stop();
        
        // --- Re-opens database
        
        MemoryStream m = memory.copy();
        DatabaseBuilderImp builder = (DatabaseBuilderImp) Factory.database();
        builder.stream("main", m);
        builder.cryptoKey(CryptoKey.parse("8184a9f2-salsa-75ac20b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c"));
        Database database2 = builder.start();
        
        String s = database2.connection().get("/s1", String.class);
        
        Assert.assertEquals("Hej!", s);
    }
    
    @Nano
    public static void testEncrypted3() throws IOException {
        // Creates an encrypted database, writes to it, closes it, and reopens it
        // with the wrong crypto key. BadCryptoKey should be thrown.
        
        CryptoKey cryptoKey = CryptoKey.parse("8184a9f2-salsa-75ac20b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c");
        
        Database database = Factory.database().memory().cryptoKey(cryptoKey).start();
        
        DatabaseImp imp = (DatabaseImp) database;
        BufferedStream buffered = (BufferedStream) imp.getDb().internal().getMainStream();
        SalsaStream salsa = (SalsaStream) buffered.getUnderlyingStream();
        MemoryStream memory = (MemoryStream) salsa.getUnderlyingStream();
        
        Connection c = database.connection();
        c.put("/s1", "Hej!");
        c.sync();
        
        database.stop();
        
        // --- Re-opens database
        
        MemoryStream m = memory.copy();
        DatabaseBuilderImp builder = (DatabaseBuilderImp) Factory.database();
        builder.stream("main", m);
        builder.cryptoKey(CryptoKey.parse("8184a9f2-salsa-222222b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c"));
        
        BadCryptoKey ex = null;
        
        try { 
            builder.start();
        } catch (BadCryptoKey e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    /**
     * Regression test for bergdb 005-40: a start with a wrong crypto key, or with none, on a
     * database whose stream a crash had cut where a meta block starts, filled out that meta
     * block through the key before it found the key wrong; the right key then read garbage
     * there, and the database never started again. Now such a start writes nothing.
     */
    @Nano
    private static void testWrongKeyAfterCrashAtMetaBlock() {
        CryptoKey right = CryptoKey.generate();
        MemoryStream m = new MemoryStream();
        Database d = builderOn(m, right).start();
        Connection c = d.connection();
        String big = new String(new char[100 * 1000]).replace('\0', 'b');
        for (int i = 0; i < 3; i++) {
            c.put("/k" + i, big);           // Past the meta block at 200,000.
        }
        d.sync();
        ((DatabaseImp) d).getDb().close();
        final long cut = RecoverableStream.META_BLOCK_DISTANCE;
        Assert.assertTrue("length " + m.getLength(),
                m.getLength() > cut + RecoverableStream.META_BLOCK_SIZE);
        MemoryStream crashed = m.copy();
        crashed.truncate(cut);              // A crash just before the meta block (005-27).
        
        for (CryptoKey wrong : new CryptoKey[] {CryptoKey.generate(), null}) {
            MemoryStream m2 = crashed.copy();
            try {
                builderOn(m2, wrong).start();
                throw new AssertionError("started with a wrong key");
            } catch (BadCryptoKey e) {
                // Expected.
            }
            Assert.assertEquals("the stream as it was", cut, m2.getLength());
            
            Database d2 = builderOn(m2.copy(), right).start();
            Assert.assertEquals(big, d2.connection().get("/k0", String.class));
            ((DatabaseImp) d2).getDb().close();
        }
    }
    
    /**
     * Bergdb 005-33: a crash while the database is created, through the Pub API, with and
     * without a crypto key. At each cut of the creation the start throws a
     * DatabaseNotCreatedException and writes nothing; the whole creation starts. A stream of
     * zero bytes, as a power loss can leave, gives a BadCryptoKey whose message names a wrong
     * key only when a key is used; until 2026-10-25, also without one.
     */
    @Nano
    private static void testCrashInCreation() throws IOException {
        for (CryptoKey key : new CryptoKey[] {null, CryptoKey.generate()}) {
            MemoryStream m = new MemoryStream();
            ((DatabaseImp) builderOn(m, key).start()).getDb().close();
            final long length = m.getLength();
            
            for (long cut : new long[] {1, 64, 127, 128, 129, 132, 200, length - 1}) {
                MemoryStream m2 = m.copy();
                m2.truncate(cut);
                try {
                    builderOn(m2, key).start();
                    throw new AssertionError("started, cut at " + cut);
                } catch (DatabaseNotCreatedException e) {
                    // Expected.
                }
                Assert.assertEquals("cut at " + cut, cut, m2.getLength());
            }
            
            MemoryStream zeros = new MemoryStream();
            zeros.append(new byte[128], 0, 128);
            try {
                builderOn(zeros, key).start();
                throw new AssertionError("started on zero bytes");
            } catch (BadCryptoKey e) {
                Assert.assertTrue(e.getMessage(),
                        e.getMessage().contains("wrong crypto key") == (key != null));
            }
            
            Database d = builderOn(m.copy(), key).start();
            d.connection().put("/k", "v");
            Assert.assertEquals("v", d.connection().get("/k", String.class));
            ((DatabaseImp) d).getDb().close();
        }
    }
    
    /** A builder of a database on the stream m, with the crypto key unless it is null. */
    private static DatabaseBuilder builderOn(MemoryStream m, CryptoKey key) {
        DatabaseBuilderImp b = (DatabaseBuilderImp) Factory.database();
        b.mainStream(m);
        if (key != null) {
            b.cryptoKey(key);
        }
        return b;
    }
    
    @Nano
    private static void testCreatedTxt1(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        
        File dir = env.createTempDir();
        CryptoKey cryptoKey = CryptoKey.parse("8184a9f2-salsa-75ac20b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c");
        
        Database database = Factory.database().dir(dir.getPath()).cryptoKey(cryptoKey).start();
        database.stop();
        
        File file = new File(dir, "created.txt");
        Assert.assertTrue(file.exists());
        
        String s = new String(Util.fileToBytes(file.getPath()), "UTF-8");
        Assert.assertTrue(s.contains("8184a9f2"));
    }
    
    @Nano
    private static void testCreatedTxt2(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        
        File dir = env.createTempDir();
        Database database = Factory.database().dir(dir.getPath()).start();
        database.stop();
        
        File file = new File(dir, "created.txt");
        Assert.assertTrue(file.exists());
        
        String s = new String(Util.fileToBytes(file.getPath()), "UTF-8");
        Assert.assertTrue(s.contains("creation date"));
    }
    
    @Nano
    private static void testTransactionInfo1() throws UnsupportedEncodingException {
        TestClock clock = new TestClock();
        Database db = Factory.database().clock(clock).memory().start();
        Connection c = db.connection();
        
        clock.setTime(Time.units(1000));
        Transaction trans1 = c.w()
                .put("/key1", "v1")
                .put("/key2", "v2")
                .execute();
        
        c.get("/key1", byte[].class);
        TransactionInfo tinfo = c.transactionInfo();
        db.stop();
        
        Assert.assertEquals(trans1.getTime(), tinfo.time());
        Assert.assertEquals(2, tinfo.kvs().size());
        Assert.assertArrayEquals("v1".getBytes("UTF-8"), tinfo.kvs().get(0).value());
        Assert.assertArrayEquals("v2".getBytes("UTF-8"), tinfo.kvs().get(1).value());
        Assert.assertEquals("/key1", tinfo.kvs().get(0).key());
        Assert.assertEquals("/key2", tinfo.kvs().get(1).key());
    }
    
    /**
     * Regression test for bergdb 005-34: after a restart, transactionInfo() read at the
     * value's own position and threw StreamFormatException, as startup's rerun of the
     * transaction did not give the value its transaction's position.
     */
    @Nano
    private static void testTransactionInfoAfterRestart() {
        MemoryStream m = new MemoryStream();
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m).start();
        Connection c = d.connection();
        Transaction t = c.w().put("/key1", "v1").put("/key2", "v2").execute();
        d.sync();
        d.stop();
        
        d = ((DatabaseBuilderImp) Factory.database()).mainStream(m.copy()).start();
        c = d.connection();
        Assert.assertEquals("v2", c.get("/key2", String.class));
        TransactionInfo tinfo = c.transactionInfo();
        Assert.assertEquals(t.getTime(), tinfo.time());
        Assert.assertEquals(2, tinfo.kvs().size());
        Assert.assertEquals("/key2", tinfo.kvs().get(1).key());
        d.stop();
    }
    
    /**
     * Regression test for bergdb 005-42: a transaction that wrote an index entry gave it
     * among its KVs, and its key() threw IllegalArgumentException. Now the KVs are the
     * user's, also when a put replaces an index entry.
     */
    @Nano
    private static void testTransactionInfoWithIndex() {
        Database db = Factory.database().memory().start();
        db.indexBuilder("area").type("long").dir("/houses/").field("area").createFast();
        Connection c = db.connection();
        House h = new House();
        h.area = 120;
        c.put("/houses/h1", h);
        h.area = 130;
        Transaction t = c.w().put("/houses/h1", h).put("/other", "x").execute();
        
        Assert.assertEquals(130, c.get("/houses/h1", House.class).area);
        TransactionInfo tinfo = c.transactionInfo();
        Assert.assertEquals(t.getTime(), tinfo.time());
        Set<String> keys = new java.util.HashSet<String>();
        for (Kv<byte[]> kv : tinfo.kvs()) {
            keys.add(kv.key());
        }
        Assert.assertEquals(2, tinfo.kvs().size());
        Assert.assertTrue("keys: " + keys, keys.contains("/houses/h1") && keys.contains("/other"));
        db.stop();
    }
    
    /**
     * Regression test for bergdb 005-42: for a value that reclaim had rewritten,
     * transactionInfo() described reclaim's step, with its time and its row, whose key()
     * threw. Now it throws LookupTimeNotAvailableException, as for a transaction that reclaim
     * has removed; a value written after the cut still gives its transaction. Made with the
     * core's builder, as testFirstAvailableLookupTime2, so that reclaim cuts soon.
     */
    @Nano
    private static void testTransactionInfoAfterReclaim() {
        TestClock clock = new TestClock();
        Db db = Db.builder().testSetup(new CutStream()).clock(clock).maxNodeSize8()
                .startupDistance(2000).build();
        Database d = DatabaseImp.createAndStart(db);
        d.setRetainDuration(Duration.seconds(1));
        Connection c = d.connection();
        
        long sec = Duration.seconds(1).units();
        long time = sec;
        clock.setTime(Time.units(time));
        long t0 = c.w().put("/a", "a0").execute().getTime().units();
        java.util.Random r = new java.util.Random(1);
        for (int i = 0; i < 20000 && d.getFirstAvailableLookupTime().units() <= t0; i++) {
            time += sec / 20;
            clock.setTime(Time.units(time));
            c.w().put("/k/" + r.nextInt(50), "v" + i).execute();
        }
        Assert.assertTrue("no cut after /a", d.getFirstAvailableLookupTime().units() > t0);
        
        Assert.assertEquals("a0", c.get("/a", String.class));
        String gave = null;
        try {
            gave = "a transaction at " + c.transactionInfo().time().units();
        } catch (LookupTimeNotAvailableException e) {
            // Expected.
        }
        Assert.assertTrue("a value that reclaim rewrote gave " + gave + "; /a was put at " + t0,
                gave == null);
        
        clock.setTime(Time.units(time + sec));
        Transaction t1 = c.w().put("/b", "b1").execute();
        Assert.assertEquals("b1", c.get("/b", String.class));
        TransactionInfo tinfo = c.transactionInfo();
        Assert.assertEquals(t1.getTime(), tinfo.time());
        Assert.assertEquals(1, tinfo.kvs().size());
        Assert.assertEquals("/b", tinfo.kvs().get(0).key());
        d.stop();
    }
    
    /**
     * Regression test for bergdb 005-45: a w-transaction's sync(level) waited for the
     * database's last transaction, not for its own, as its sync() and an rw-transaction's
     * sync(level) do. Here the stream holds back the appends of a later transaction, and the
     * first one's sync(level) returns at once, as that one is durable.
     */
    @Nano
    private static void testWSyncLevelWaitsForItsOwn() throws InterruptedException {
        final HeldStream s = new HeldStream();
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(s).start();
        Connection c = d.connection();
        final Transaction t1 = c.w().put("/a", "1").execute();
        t1.sync();
        s.hold();
        c.w().put("/b", "2").execute();
        
        Thread syncer = new Thread() {
            public void run() {
                t1.sync(SyncLevel.ORDINARY);
            }
        };
        syncer.start();
        syncer.join(5000);
        final boolean returned = !syncer.isAlive();
        s.release();
        syncer.join();
        Assert.assertTrue("sync(ORDINARY) waited for a later transaction", returned);
        d.stop();
    }
    
    /** A MemoryStream whose appends wait while it is held (bergdb 005-45). */
    private static class HeldStream implements AppendOnlyStream {
        private final MemoryStream inner = new MemoryStream();
        private boolean held = false;
        
        synchronized void hold() {
            held = true;
        }
        
        synchronized void release() {
            held = false;
            notifyAll();
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
        
        public synchronized void append(byte[] source, int sourceOffset, int length) 
                throws IOException {
            while (held) {
                try {
                    wait();
                } catch (InterruptedException e) {
                    throw new IOException("interrupted");
                }
            }
            inner.append(source, sourceOffset, length);
        }
        
        public void pretruncate(long position) throws IOException {
            inner.pretruncate(position);
        }
        
        public void seekFirstPos(long position) throws IOException {
            inner.seekFirstPos(position);
        }
        
        public void close() {
            inner.close();
        }
    }
    
    /**
     * Regression test for bergdb 005-32: a start through the Pub API that throws, here with a
     * wrong crypto key, left its storage's thread and open file until the garbage collector
     * finalized the Db. Now ten such starts leave none, counted at once; then the right key
     * starts.
     */
    @Nano
    private static void testFailedStartsLeaveNothing(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = env.createTempDir();
        CryptoKey right = CryptoKey.generate();
        Database d = Factory.database().dir(dir.getPath()).cryptoKey(right).start();
        d.connection().put("/k", "v");
        d.sync();
        ((DatabaseImp) d).getDb().close();
        
        Set<Thread> before = DbTesterFailure.storageThreads();
        long files = openFiles();
        for (int i = 0; i < 10; i++) {
            try {
                Factory.database().dir(dir.getPath()).cryptoKey(CryptoKey.generate()).start();
                throw new AssertionError("started with a wrong key");
            } catch (BadCryptoKey e) {
                // Expected.
            }
        }
        DbTesterFailure.assertNoNewStorageThreads(before);
        if (files >= 0) {
            Assert.assertTrue("open files " + openFiles() + ", before " + files, 
                    openFiles() <= files);
        }
        
        Database d2 = Factory.database().dir(dir.getPath()).cryptoKey(right).start();
        Assert.assertEquals("v", d2.connection().get("/k", String.class));
        ((DatabaseImp) d2).getDb().close();
    }
    
    /**
     * bergdb 005-32: a directory whose start failed, here as its creation crashed (005-33),
     * can be removed and created again at once: the failed start has closed its files.
     */
    @Nano
    private static void testFailedStartsDirectoryRemoved(TestEnvironment env) 
            throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File d = new File(env.createTempDir(), "db");
        Database first = Factory.database().dir(d.getPath()).start();
        first.sync();
        ((DatabaseImp) first).getDb().close();
        File[] streams = d.listFiles();
        File stream = null;
        for (File f : streams) {
            if (f.getName().endsWith(".bergdb")) {
                stream = f;
            }
        }
        RandomAccessFile raf = new RandomAccessFile(stream, "rw");
        raf.setLength(200);                 // In the creation's first transaction.
        raf.close();
        
        Set<Thread> before = DbTesterFailure.storageThreads();
        long files = openFiles();
        try {
            Factory.database().dir(d.getPath()).start();
            throw new AssertionError("started");
        } catch (DatabaseNotCreatedException e) {
            // Expected (005-33; until 2026-10-25 a StreamFormatException, 005-28).
        }
        Assert.assertEquals("the stream as it was", 200, stream.length());
        DbTesterFailure.assertNoNewStorageThreads(before);
        if (files >= 0) {
            Assert.assertTrue("open files " + openFiles() + ", before " + files, 
                    openFiles() <= files);
        }
        for (File f : d.listFiles()) {
            Assert.assertTrue("removed " + f, f.delete());
        }
        Assert.assertTrue("removed " + d, d.delete());
        
        Database again = Factory.database().dir(d.getPath()).start();
        again.connection().put("/a", "a0");
        Assert.assertEquals("a0", again.connection().get("/a", String.class));
        ((DatabaseImp) again).getDb().close();
    }
    
    /**
     * bergdb 005-32: when anything throws after db.start() in DatabaseImp.createAndStart()
     * (here a test hook), the Db is closed; it ran on until the garbage collector stopped it.
     */
    @Nano
    private static void testExceptionAfterStartClosesDb() {
        final Db[] started = new Db[1];
        DatabaseImp.testHookAfterStart = new Consumer<Db>() {
            public void accept(Db db) {
                started[0] = db;
                throw new IllegalStateException("the test hook");
            }
        };
        Set<Thread> before = DbTesterFailure.storageThreads();
        MemoryStream m = new MemoryStream();
        try {
            ((DatabaseBuilderImp) Factory.database()).mainStream(m).start();
            throw new AssertionError("started");
        } catch (IllegalStateException e) {
            Assert.assertEquals("the test hook", e.getMessage());
        } finally {
            DatabaseImp.testHookAfterStart = null;
        }
        DbTesterFailure.assertNoNewStorageThreads(before);
        DbTesterFailure.assertClosed(m);
        try {
            started[0].execute(started[0].trans().put("/a", "a0").build());
            throw new AssertionError("a transaction was taken");
        } catch (DbStoppingException e) {
            // Expected.
        }
    }
    
    /**
     * bergdb 005-32: a start that throws before the Db is built, here for a crypto key of an
     * unknown algorithm, closes the file that dir() opened.
     */
    @Nano
    private static void testUnknownCryptoAlgorithmClosesFile(TestEnvironment env) 
            throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = env.createTempDir();
        CryptoKey key = CryptoKey.parse("8184a9f2-other-75ac20b68ccdbf95b9999287bc4da0caf67b4c8e"
                + "dc40d7615bebf1beae3578b800cfc3dfbaad319c");
        long files = openFiles();
        for (int i = 0; i < 3; i++) {
            try {
                Factory.database().dir(dir.getPath()).cryptoKey(key).start();
                throw new AssertionError("started");
            } catch (IllegalStateException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("other"));
            }
        }
        if (files >= 0) {
            Assert.assertTrue("open files " + openFiles() + ", before " + files, 
                    openFiles() <= files);
        }
    }
    
    /**
     * Regression test for bergdb 005-35: Database.stop() lost the transactions still in the
     * write buffer, all of them in a quick run. Now, once its close has ended, the stream
     * holds every one, and it is closed.
     */
    @Nano
    private static void testStopWritesAll() throws Exception {
        MemoryStream m = new MemoryStream();
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m).start();
        Connection c = d.connection();
        for (int i = 0; i < 300; i++) {
            c.put("/k" + i, "v" + i);
        }
        Set<Thread> before = DbTester.closeThreads();
        d.stop();
        DbTester.joinNew(before);
        DbTesterFailure.assertClosed(m);
        
        Database d2 = ((DatabaseBuilderImp) Factory.database()).mainStream(m.copy()).start();
        for (int i = 0; i < 300; i++) {
            Assert.assertEquals("v" + i, d2.connection().get("/k" + i, String.class));
        }
        ((DatabaseImp) d2).getDb().close();
    }
    
    /**
     * bergdb 005-35: a program that called Database.stop() and returned from main kept only
     * what had been flushed, as the storage threads are daemons. Now stop()'s close runs in
     * a thread that is not, and the JVM ends after it: the files hold all transactions.
     */
    @Nano("f")
    private static void testStopThenReturnFromMain(TestEnvironment env) throws Exception {
        if (Util.runsAndroid()) {
            return;
        }
        File tmp = env.createTempDir();
        File dir = new File(tmp, "db");
        File out = new File(tmp, "child.txt");
        String javaBin = System.getProperty("java.home") + "/bin/java";
        String cp = System.getProperty("java.class.path");
        Process p = new ProcessBuilder(javaBin, "-cp", cp, StopAndReturn.class.getName(), 
                dir.getPath()).redirectErrorStream(true).redirectOutput(out).start();
        Assert.assertTrue("the child ends", p.waitFor(60, java.util.concurrent.TimeUnit.SECONDS));
        String output = new String(Util.fileToBytes(out.getPath()), "UTF-8");
        Assert.assertEquals("the child's exit, " + output, 0, p.exitValue());
        
        Database d = Factory.database().dir(dir.getPath()).start();
        Connection c = d.connection();
        int found = 0;
        for (int i = 0; i < StopAndReturn.N; i++) {
            if (c.get("/k" + i, String.class) != null) {
                found++;
            }
        }
        ((DatabaseImp) d).getDb().close();
        Assert.assertEquals("the keys in the files", StopAndReturn.N, found);
    }
    
    /** testStopThenReturnFromMain's child: puts, Database.stop(), and returns from main. */
    public static class StopAndReturn {
        static final int N = 2000;
        
        public static void main(String[] args) {
            Database d = Factory.database().dir(args[0]).start();
            Connection c = d.connection();
            for (int i = 0; i < N; i++) {
                c.put("/k" + i, "v" + i);
            }
            d.stop();
        }
    }
    
    /** Open file descriptors of this JVM, or -1 where it cannot be told (bergdb 005-32). */
    private static long openFiles() {
        java.lang.management.OperatingSystemMXBean os = 
                java.lang.management.ManagementFactory.getOperatingSystemMXBean();
        if (os instanceof com.sun.management.UnixOperatingSystemMXBean) {
            return ((com.sun.management.UnixOperatingSystemMXBean) os)
                    .getOpenFileDescriptorCount();
        }
        return -1;
    }
}
