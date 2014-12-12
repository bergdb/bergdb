package bergdb.pubimp;

import java.util.Iterator;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.Time;
import bergdb.pub.WBuilder;

/**
 * Tests use of primary index.
 * 
 * @author Frans Lundberg
 */
public class PubTesterPrimary {
    
    public static class Person {
        public String name;
        
        public Person() {}
        
        public Person(String name) {
            this.name = name;
        }
    }
    
    @Nano
    public static void test0() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        c.w().put("/d/person1", new Person("Fredrik"))
             .put("/d/person2", new Person("Amelia")).execute();
        
        Iterator<Person> iter = c.usePrimary(Person.class).dir("/d/").objects().iterator();
        Assert.assertTrue(iter.hasNext());
        Person a = iter.next();
         Assert.assertEquals("Fredrik", a.name);
        Assert.assertTrue(iter.hasNext());
        a = iter.next();
        Assert.assertEquals("Amelia", a.name);
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void test1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        Person t1 = new Person("Fredrik");
        Person t2 = new Person("Amelia");
        Person t3 = new Person("Emma");
        
        c.w().put("/d/person1", t1).put("/d/person2", t2).put("/e/emma", t3).execute();
        
        Iterable<Person> it = c.usePrimary(Person.class).dir("/d/").objects();
        Iterator<Person> iter1 = it.iterator();
        while (iter1.hasNext()) {
            iter1.next();
        }
        
        Iterator<Person> iter2 = it.iterator();
        Assert.assertTrue(iter2.hasNext());
        Person a = iter2.next();
        Assert.assertEquals("Fredrik", a.name);
        Assert.assertTrue(iter2.hasNext());
        a = iter2.next();
        Assert.assertEquals("Amelia", a.name);
        Assert.assertFalse(iter2.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testStart() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        c.w().put("/p/1", new Person("1"))
             .put("/p/2", new Person("2"))
             .put("/p/3", new Person("3"))
             .put("/p/4", new Person("4")).execute();
        
        Iterator<Person> iter = c.usePrimary(Person.class).dir("/p/").startAt("2")
                .objects().iterator();
        
        String[] expected = {"2", "3", "4"};
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertEquals(expected[i], iter.next().name);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testExclusive1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        c.w().put("/p/1", new Person("1"))
             .put("/p/2", new Person("2"))
             .put("/p/3", new Person("3"))
             .put("/p/4", new Person("4")).execute();
        
        Iterator<Person> iter = c.usePrimary(Person.class).dir("/p/").startAt("2")
                .inclusive(false).objects().iterator();
        String[] expected = {"3", "4"};
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertEquals(expected[i], iter.next().name);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testExclude2() {
        // An empty iterator.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        c.w().put("/p/1", new Person("1"))
             .put("/p/2", new Person("2"))
             .put("/p/3", new Person("3"))
             .put("/p/4", new Person("4")).execute();
        
        Iterator<Person> iter = c.usePrimary(Person.class).dir("/p/").startAt("4")
                .inclusive(false).objects().iterator();
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testBackward1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        c.w().put("/p/1", new Person("1"))
             .put("/p/2", new Person("2"))
             .put("/p/3", new Person("3"))
             .put("/p/4", new Person("4")).execute();
        
        Iterator<Person> iter = c.usePrimary(Person.class).dir("/p/").backward().objects().iterator();
        String[] expected = {"4", "3", "2", "1"};
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertEquals(expected[i], iter.next().name);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testBackward2() {
        // With startAt("3").
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        c.w().put("/p/1", new Person("1"))
             .put("/p/2", new Person("2"))
             .put("/p/3", new Person("3"))
             .put("/p/4", new Person("4")).execute();
        
        Iterator<Person> iter = c.usePrimary(Person.class).dir("/p/").backward().startAt("3")
                .objects().iterator();
        
        String[] expected = {"3", "2", "1"};
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertEquals(expected[i], iter.next().name);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testBackward3() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        c.w().put("/p/1", new Person("1"))
             .put("/p/2", new Person("2"))
             .put("/p/3", new Person("3"))
             .put("/p/4", new Person("4")).execute();
        
        Iterator<Person> iter = c.usePrimary(Person.class).dir("/p/")
                .backward().startAt("3").inclusive(false).objects().iterator();
        String[] expected = {"2", "1"};
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertEquals(expected[i], iter.next().name);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testKv() {        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        Person t1 = new Person("Fredrik");
        Person t2 = new Person("Amelia");
        Person t3 = new Person("Emma");
        
        c.w().put("/d/person1", t1)
             .put("/d/person2", t2)
             .put("/e/person1", t3).execute();
        
        Iterable<Kv<Person>> it = c.usePrimary(Person.class).dir("/d/").kvs();
        
        Iterator<Kv<Person>> iter2 = it.iterator();
        Assert.assertTrue(iter2.hasNext());
        Kv<Person> kv = iter2.next();
        Assert.assertEquals("Fredrik", kv.value().name);
        Assert.assertTrue(iter2.hasNext());
        kv = iter2.next();
        Assert.assertEquals("Amelia", kv.value().name);
        Assert.assertFalse(iter2.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testManyObjects1() {
        // Lookup of large number of objects. DB.getMany() must be called several times.   
        manyObjects(233);
    }
    
    @Nano
    public static void testManyObjects2() {
        // Lookup of large number of objects. Exactly 200 objects (same as precisely 2 DB.getMany
        // calls).
        manyObjects(200);
    }
    
    private static void manyObjects(int count) {        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
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
    
    @Nano
    public static void testHistoric() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        Time t0 = db.currentTime();
        
        c.w().put("/p/p10", new Person("p10"))
            .put("/p/p20", new Person("p20"))
            .put("/p/p30", new Person("p30")).execute();
        
        Time t1 = db.currentTime();
        
        c.w().put("/p/p01", new Person("p01"))
            .put("/p/p22", new Person("p22"))
            .put("/p/p23", new Person("p23")).execute();
        
        String[] expected = new String[]{"p01", "p10", "p20", "p22", "p23", "p30"};
        
        Iterable<Person> persons = c.usePrimary(Person.class).dir("/p/").objects();
        
        int index = 0;
        for (Person p : persons) {
            Assert.assertEquals(expected[index], p.name);
            index++;
        }
        
        expected = new String[]{"p10", "p20", "p30"};
        c.setLookupTime(t1);
        persons = c.usePrimary(Person.class).objects();
        index = 0;
        for (Person p : persons) {
            Assert.assertEquals(expected[index], p.name);
            index++;
        }
        
        c.setLookupTime(t0);
        persons = c.usePrimary(Person.class).objects();
        index = 0;
        for (@SuppressWarnings("unused") Person p : persons) {
            index++;
        }
        Assert.assertEquals(0, index);
        db.stop();
    }
    
    @Nano
    public static void testNonObjects1() {
        // Non .obj KVs in the middle of Person.class objects. Iterate with Person.class.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        c.w().put("/p10", new Person("p10"))
            .put("/p20", new Person("p20"))
            .put("/p30", new Person("p30"))
            .put("/p12.txt", "p12 - my string!")
            .put("/p13.txt", "p13 - second string")
            .execute();
        
        String[] expected = new String[] {"p10", "p20", "p30"};
        
        Iterator<Person> it = c.usePrimary(Person.class).objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(it.hasNext());
            Assert.assertEquals(expected[i], it.next().name);
        }
        
    }
    
    @Nano
    public static void testNonObjects2() {
        // Testing a mix of objects and strings. Iterate with Object.class.
        // Results in Objects of type: DbObject (.obj), String (.txt) and byte[] (the rest).
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        c.w().put("/p10", new Person("p10"))
            .put("/p20", new Person("p20"))
            .put("/p30", new Person("p30"))
            .put("/p12.txt", "p12 - my string!")
            .put("/p13.txt", "p13 - second string")
            .put("/p22.bytes", new byte[] {12})
            .execute();
        
        Iterator<Object> it = c.usePrimary(Object.class).objects().iterator();
        Object obj = it.next();
        Assert.assertEquals("p10", ((DbObject) obj).getString("name"));
        obj = it.next();
        Assert.assertEquals("p12 - my string!", (String) obj);
        obj = it.next();
        Assert.assertEquals("p13 - second string", (String) obj);
        obj = it.next();
        Assert.assertEquals("p20", ((DbObject) obj).getString("name"));
        obj = it.next();
        Assert.assertEquals(12, ((byte[]) obj)[0]);
        obj = it.next();
        Assert.assertEquals("p30", ((DbObject) obj).getString("name"));
    }
    
    @Nano
    public static void testTypeMix() {
        // Retrieving stored objects with DbObject iterator.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        c.w().put("/10", new Person("10"))
            .put("/20", new MyDouble(1.2))
            .put("/30", new Person("30"))
            .execute();
        
        Iterator<DbObject> it = c.usePrimary(DbObject.class).objects().iterator();
        DbObject obj = it.next();
        Assert.assertEquals("10", obj.getString("name"));
        obj = it.next();
        Assert.assertEquals(1.2, obj.getDouble("value"));
        obj = it.next();
        Assert.assertEquals("30", obj.getString("name"));
    }
    
    @Nano
    public static void testByteArrayIterator() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        c.w().put("/10", new Person("10"))
            .put("/20", new MyDouble(1.2))
            .put("/30.txt", "30.txt - a string")
            .put("/40", new byte[] {1, 2})
            .execute();
        
        Iterator<byte[]> it = c.usePrimary(byte[].class).objects().iterator();
        byte[] bytes;
        
        bytes = it.next();
        Person p = new Person();
        new DbObject(bytes).toJavaObject(p, new KvToObjectImp());
        Assert.assertEquals("10", p.name);
        
        bytes = it.next();
        MyDouble myDouble = new MyDouble();
        new DbObject(bytes).toJavaObject(myDouble, new KvToObjectImp());
        Assert.assertEquals(1.2, myDouble.value);
        
        bytes = it.next();
        String s = Util.toString(bytes);
        Assert.assertEquals("30.txt - a string", s);
        
        bytes = it.next();
        Assert.assertEquals(2, bytes.length);
        Assert.assertEquals(1, bytes[0]);
    }
    
    static class MyDouble {
        private double value;
        
        public MyDouble() {}
        
        public MyDouble(double v) {
            value = v;
        }
    }
    
    private static void sortOrderCheck(String[] keys, String[] expected, boolean oneTrans) {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        if (oneTrans) {
            WBuilder b = c.w();
            for (int i = 0; i < keys.length; i++) {
                b.put(keys[i], new byte[0]);
            }
            b.execute();
        } else {
            for (int i = 0; i < keys.length; i++) {
                c.w().put(keys[i], new byte[0]).execute();
            }
        }
        
        int i = 0;
        for (Kv<byte[]> kv : c.usePrimary(byte[].class).kvs()) {
            Assert.assertEquals(expected[i], kv.key());
            i++;
        }
    }
    
    @Nano
    public static void sortOrder0() {
        String[] keys = {"/c", "/a", "/b"};
        String[] expected = {"/a", "/b", "/c"};
        sortOrderCheck(keys, expected, true);
    }
    
    @Nano
    public static void sortOrder1() {
        // Files always sorted before directories. 
        // File "/c" sorts before subdir files "/b/1" and "/b/2".
        String[] keys = {"/c", "/a", "/b/1", "/b/2"};
        String[] expected = {"/a", "/c", "/b/1", "/b/2"};
        sortOrderCheck(keys, expected, true);
    }
    
    @Nano
    public static void testSubdir0() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        c.w().put("/d/10", new Person("1"))
             .put("/d/20", new Person("2"))
             .put("/d/25/p5", new Person("p5"))
             .put("/d/25/p6", new Person("p6"))
             .put("/d/30", new Person("3"))
             .put("/d/40", new Person("4"))
             .put("/d/45/p7", new Person("p7")).execute();
        
        Iterator<Person> iter = c.usePrimary(Person.class).dir("/d/").startAt("20")
                .inclusive(false).objects().iterator();
        String[] expected = {"3", "4"};
        
        for (int i = 0; i < expected.length; i++) {
            Assert.assertEquals(expected[i], iter.next().name);
        }
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testRootDir0() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        c.w().put("/person1", new Person("Fredrik"))
             .put("/person2", new Person("Amelia")).execute();
        
        Iterator<Person> iter = c.usePrimary(Person.class).objects().iterator();
        Assert.assertTrue(iter.hasNext());
        Person a = iter.next();
         Assert.assertEquals("Fredrik", a.name);
        Assert.assertTrue(iter.hasNext());
        a = iter.next();
        Assert.assertEquals("Amelia", a.name);
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @Nano
    public static void testRootDir1() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        c.w().put("/person1", new Person("Fredrik"))
             .put("/person2", new Person("Amelia")).execute();
        
        Iterator<Person> iter = c.usePrimary(Person.class).dir("/").objects().iterator();
        Assert.assertTrue(iter.hasNext());
        Person a = iter.next();
         Assert.assertEquals("Fredrik", a.name);
        Assert.assertTrue(iter.hasNext());
        a = iter.next();
        Assert.assertEquals("Amelia", a.name);
        Assert.assertFalse(iter.hasNext());
        db.stop();
    }
    
    @SuppressWarnings("unused")
    @Nano
    public static void testAll() {
        // Iterates through all entries in /, expect not to get any internal entries.
        
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        c.w().put("/a", new byte[0])
             .put("/b", new byte[1]).execute();
        
        int count = 0;
        for (byte[] value : c.usePrimary(byte[].class).dir("/").objects()) {
            count++;
        }
        
        Assert.assertEquals(2, count);
        
        db.stop();
    }
}
