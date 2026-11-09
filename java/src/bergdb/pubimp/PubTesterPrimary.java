package bergdb.pubimp;

import java.util.Arrays;
import java.util.Iterator;
import java.util.NoSuchElementException;

import bergdb.common.StringUtil;
import bergdb.core.Db;
import bergdb.core.DbConstants;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.DataFormatException;
import bergdb.pub.Database;
import bergdb.pub.DbObject;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.UsePrimaryBuilder;
import bergdb.pub.WBuilder;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.CutStream;

/**
 * Tests the primary scan, the listing of a directory: Connection.usePrimary() (bergdb 020-10,
 * section 3.5). Harness H4 is PrimaryHarness.
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
        persons = c.usePrimary(Person.class).dir("/p/").objects();
        index = 0;
        for (Person p : persons) {
            Assert.assertEquals(expected[index], p.name);
            index++;
        }
        
        c.setLookupTime(t0);
        persons = c.usePrimary(Person.class).dir("/p/").objects();
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
        
        Iterator<Person> it = c.usePrimary(Person.class).dir("/").objects().iterator();
        for (int i = 0; i < expected.length; i++) {
            Assert.assertTrue(it.hasNext());
            Assert.assertEquals(expected[i], it.next().name);
        }
        
        db.stop();
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
        
        Iterator<Object> it = c.usePrimary(Object.class).dir("/").objects().iterator();
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
        db.stop();
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
        
        Iterator<DbObject> it = c.usePrimary(DbObject.class).dir("/").objects().iterator();
        DbObject obj = it.next();
        Assert.assertEquals("10", obj.getString("name"));
        obj = it.next();
        Assert.assertEquals(1.2, obj.getDouble("value"));
        obj = it.next();
        Assert.assertEquals("30", obj.getString("name"));
        db.stop();
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
        
        Iterator<byte[]> it = c.usePrimary(byte[].class).dir("/").objects().iterator();
        byte[] bytes;
        
        bytes = it.next();
        Person p = new DbObject(bytes).toJavaObject(Person.class);
        Assert.assertEquals("10", p.name);
        
        bytes = it.next();
        MyDouble myDouble = new DbObject(bytes).toJavaObject(MyDouble.class);
        Assert.assertEquals(1.2, myDouble.value);
        
        bytes = it.next();
        String s = StringUtil.toString(bytes);
        Assert.assertEquals("30.txt - a string", s);
        
        bytes = it.next();
        Assert.assertEquals(2, bytes.length);
        Assert.assertEquals(1, bytes[0]);
        db.stop();
    }
    
    public static class MyDouble {
        public double value;
        
        public MyDouble() {}
        
        public MyDouble(double v) {
            value = v;
        }
    }
    
    private static void sortOrderCheck(String[] keys, String dir, String[] expected, 
            boolean oneTrans) {
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
        for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir(dir).kvs()) {
            Assert.assertEquals(expected[i], kv.key());
            i++;
        }
        Assert.assertEquals(expected.length, i);
        db.stop();
    }
    
    @Nano
    public static void sortOrder0() {
        String[] keys = {"/c", "/a", "/b"};
        String[] expected = {"/a", "/b", "/c"};
        sortOrderCheck(keys, "/", expected, true);
    }
    
    @Nano
    public static void sortOrder1() {
        // A listing has its directory's own keys only, not its subdirectories' (bergdb
        // 020-10, section 3.5). A listing of the root gave the files of /b/ after "/c".
        String[] keys = {"/c", "/a", "/b/1", "/b/2"};
        sortOrderCheck(keys, "/", new String[] {"/a", "/c"}, true);
        sortOrderCheck(keys, "/b/", new String[] {"/b/1", "/b/2"}, false);
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
    
    /**
     * Regression test for bergdb 015-20 (review R3-F12): a page of the scan (100 entries)
     * that holds no object is not the end of the range. 100 Strings and then an object;
     * an object, 250 Strings (more than two pages) and an object, forward and backward,
     * with objects() and kvs().
     */
    @Nano
    public static void testFilteredPages() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            WBuilder w = c.w();
            for (int i = 0; i < 100; i++) {
                w.put(String.format("/a/s%03d", i), "not an object");
            }
            w.put("/a/z", new Person("z")).execute();
            Assert.assertEquals("z", c.get("/a/z", Person.class).name);
            Assert.assertEquals("[z]", names(c.usePrimary(Person.class).dir("/a/").objects()));
            
            w = c.w();
            w.put("/b/a", new Person("a"));
            for (int i = 0; i < 250; i++) {
                w.put(String.format("/b/s%03d", i), "not an object");
            }
            w.put("/b/z", new Person("z")).execute();
            Assert.assertEquals("[a, z]", names(c.usePrimary(Person.class).dir("/b/").objects()));
            Assert.assertEquals("[z, a]", 
                    names(c.usePrimary(Person.class).dir("/b/").backward().objects()));
            StringBuilder keys = new StringBuilder();
            for (Kv<Person> kv : c.usePrimary(Person.class).dir("/b/").kvs()) {
                keys.append(kv.key()).append(' ');
            }
            Assert.assertEquals("/b/a /b/z ", keys.toString());
        } finally {
            db.stop();
        }
    }
    
    private static String names(Iterable<Person> persons) {
        java.util.List<String> result = new java.util.ArrayList<String>();
        for (Person p : persons) {
            result.add(p.name);
        }
        return result.toString();
    }
    
    // ======== The primary scan of 2026.4 (bergdb 020-10, section 3.5) ========
    
    /**
     * Regression test for S2-F17 (bergdb 020-10, section 8): dir() is required, and first.
     * Without it, objects() and kvs() listed the database's internal keys too (reclaim's
     * settings, an index's definitions and entries), and startAt() before dir() found
     * nothing. Now each call out of order is IllegalStateException and a bad argument
     * IllegalArgumentException, at the call, and a listing of the root has the user's own
     * keys only.
     */
    @Nano
    public static void testPrimaryNeedsDir() {
        Database db = Factory.database().memory().start();
        try {
            final Connection c = db.newConnection();
            db.setRetainDuration(Duration.seconds(1000));      // reclaim's internal keys
            c.w().put("/a", "a").put("/b", new byte[] {'b'}).put("/d/c", "c").execute();
            Assert.assertTrue("no internal key to leave out", internalKeys(db) > 0);
            
            assertThrows(IllegalStateException.class, () -> c.usePrimary(byte[].class).objects());
            assertThrows(IllegalStateException.class, () -> c.usePrimary(byte[].class).kvs());
            assertThrows(IllegalStateException.class, 
                    () -> c.usePrimary(String.class).startAt("a"));
            assertThrows(IllegalStateException.class, 
                    () -> c.usePrimary(String.class).inclusive(false));
            assertThrows(IllegalStateException.class, () -> c.usePrimary(String.class).backward());
            assertThrows(IllegalStateException.class, 
                    () -> c.usePrimary(String.class).dir("/").dir("/d/"));
            assertThrows(IllegalStateException.class, 
                    () -> c.usePrimary(String.class).dir("/").startAt("a").startAt("b"));
            assertThrows(IllegalStateException.class, 
                    () -> c.usePrimary(String.class).dir("/").inclusive(false).inclusive(true));
            assertThrows(IllegalStateException.class, 
                    () -> c.usePrimary(String.class).dir("/").backward().backward());
            
            for (String dir : new String[] {null, "", "a", "a/", "d/", "/a", "//", "/a//", 
                    "/a\ud800/"}) {
                assertThrows(IllegalArgumentException.class, 
                        () -> c.usePrimary(String.class).dir(dir));
            }
            for (String name : new String[] {null, "", "a/b", "/", "a\ud800"}) {
                assertThrows(IllegalArgumentException.class, 
                        () -> c.usePrimary(String.class).dir("/").startAt(name));
            }
            assertThrows(IllegalArgumentException.class, () -> c.usePrimary(null));
            
            Assert.assertEquals("/a=a /b=b ", kvs(c.usePrimary(String.class).dir("/").kvs()));
            Assert.assertEquals("/b=b /a=a ", 
                    kvs(c.usePrimary(String.class).dir("/").backward().kvs()));
            Assert.assertEquals("/a=a ", 
                    kvs(c.usePrimary(String.class).dir("/").startAt("a").backward().kvs()));
            Assert.assertEquals("/d/c=c ", kvs(c.usePrimary(String.class).dir("/d/").kvs()));
            
            // "/#i/" is a user's directory, "#i", not the internal one.
            c.w().put("/#i/x", "x").execute();
            Assert.assertEquals("/#i/x=x ", kvs(c.usePrimary(String.class).dir("/#i/").kvs()));
            Assert.assertEquals("/a=a /b=b ", kvs(c.usePrimary(String.class).dir("/").kvs()));
        } finally {
            db.stop();
        }
    }
    
    /**
     * Regression test for S2-F25 (bergdb 020-10, section 3.5): each type lists the values of
     * its kind, each as get() gives it. String.class lists the values that are not objects,
     * decoded; it left out the Strings and gave the objects' bytes as text. byte[].class and
     * Object.class list every value; DbObject.class and a class, the objects.
     */
    @Nano
    public static void testTypesListByKind() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            c.w().put("/m/a", new Person("a"))
                 .put("/m/b", "text b")
                 .put("/m/c", new byte[] {'c', 1})
                 .put("/m/d.txt", "text d")
                 .put("/m/e.obj", new Person("e"))
                 .put("/m/f.bin", new byte[] {'f'})
                 .put("/m/sub/g", new Person("g"))
                 .put("/m/sub/h", "text h")
                 .execute();
            byte[] a = c.get("/m/a", byte[].class);
            Assert.assertEquals("/m/b=text b /m/c=c\u0001 /m/d.txt=text d /m/f.bin=f ", 
                    kvs(c.usePrimary(String.class).dir("/m/").kvs()));
            Assert.assertEquals("[f, text d, c\u0001, text b]", 
                    list(c.usePrimary(String.class).dir("/m/").backward().objects()));
            byte[] fake = Arrays.copyOf(a, 3);      // an object's first bytes, not an object
            c.w().put("/m/g", fake).execute();
            // Format 2's header, 0x82, starts no UTF-8 (bergdb 020-07, section 5.1), so the
            // fake is no String either: a String listing throws DataFormatException for it,
            // as get() does, and goes on (bergdb 021-06).
            Iterator<String> strings = c.usePrimary(String.class).dir("/m/").backward()
                    .objects().iterator();
            try {
                strings.next();
                throw new AssertionError("the fake read as a String");
            } catch (DataFormatException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("/m/g"));
            }
            Assert.assertEquals("f", strings.next());
            
            String[] keys = {"/m/a", "/m/b", "/m/c", "/m/d.txt", "/m/e.obj", "/m/f.bin", "/m/g"};
            int i = 0;
            for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/m/").kvs()) {
                Assert.assertEquals(keys[i], kv.key());
                Assert.assertArrayEquals(c.get(keys[i], byte[].class), kv.value());
                i++;
            }
            Assert.assertEquals(keys.length, i);
            
            StringBuilder kinds = new StringBuilder();
            for (Kv<Object> kv : c.usePrimary(Object.class).dir("/m/").kvs()) {
                Object got = c.get(kv.key(), Object.class);
                Assert.assertEquals(got.getClass(), kv.value().getClass());
                kinds.append(kv.key()).append('=').append(kv.value().getClass().getSimpleName())
                        .append(' ');
            }
            Assert.assertEquals("/m/a=DbObject /m/b=byte[] /m/c=byte[] /m/d.txt=String " 
                    + "/m/e.obj=DbObject /m/f.bin=byte[] /m/g=byte[] ", kinds.toString());
            
            StringBuilder objects = new StringBuilder();
            for (Kv<DbObject> kv : c.usePrimary(DbObject.class).dir("/m/").kvs()) {
                objects.append(kv.key()).append('=').append(kv.value().getString("name"))
                        .append(' ');
            }
            Assert.assertEquals("/m/a=a /m/e.obj=e ", objects.toString());
            Assert.assertEquals("[a, e]", names(c.usePrimary(Person.class).dir("/m/").objects()));
            Assert.assertEquals("[e, a]", 
                    names(c.usePrimary(Person.class).dir("/m/").backward().objects()));
            Assert.assertEquals("[g]", names(c.usePrimary(Person.class).dir("/m/sub/").objects()));
            Assert.assertEquals("[text h]", 
                    list(c.usePrimary(String.class).dir("/m/sub/").objects()));
        } finally {
            db.stop();
        }
    }
    
    /**
     * An object is a value that passes the full check (bergdb 020-10, section 3.5; 020-08,
     * section 3): an object's bytes less the last one, at an object key, are a byte[] value.
     * DbObject.class and a class leave it out, String.class and byte[].class list it, and
     * Object.class gives what get() gives. A class threw ObjectCreationException at it.
     */
    @Nano
    public static void testTruncatedObjectIsNotAnObject() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            c.w().put("/t/a", new Person("a")).put("/t/c", new Person("c")).execute();
            byte[] bytes = c.get("/t/a", byte[].class);
            c.w().put("/t/b", Arrays.copyOf(bytes, bytes.length - 1)).execute();
            
            Assert.assertEquals("[a, c]", names(c.usePrimary(Person.class).dir("/t/").objects()));
            Assert.assertEquals("[c, a]", 
                    names(c.usePrimary(Person.class).dir("/t/").backward().objects()));
            int n = 0;
            for (DbObject o : c.usePrimary(DbObject.class).dir("/t/").objects()) {
                Assert.assertTrue(o.getString("name") != null);
                n++;
            }
            Assert.assertEquals(2, n);
            // As String, the bytes are not well-formed UTF-8 (format 2's header, 0x82, never
            // starts a character): DataFormatException from next(), as from get() (bergdb
            // 021-06).
            Iterator<Kv<String>> strings = c.usePrimary(String.class).dir("/t/").kvs()
                    .iterator();
            Assert.assertTrue(strings.hasNext());
            Object gotString;
            try {
                gotString = c.get("/t/b", String.class);
            } catch (DataFormatException e) {
                gotString = e;
            }
            Object listedString;
            try {
                listedString = strings.next().value();
            } catch (DataFormatException e) {
                listedString = e;
            }
            Assert.assertEquals(gotString.getClass(), listedString.getClass());
            Assert.assertFalse(strings.hasNext());
            Assert.assertEquals("/t/a /t/b /t/c ", 
                    keys(c.usePrimary(byte[].class).dir("/t/").kvs()));
            
            Object got;
            try {
                got = c.get("/t/b", Object.class);
            } catch (ObjectCreationException e) {
                got = e;
            }
            Iterator<Object> it = c.usePrimary(Object.class).dir("/t/").startAt("b").objects()
                    .iterator();
            Assert.assertTrue(it.hasNext());
            Object listed;
            try {
                listed = it.next();
            } catch (ObjectCreationException e) {
                listed = e;
            }
            Assert.assertEquals(got.getClass(), listed.getClass());
        } finally {
            db.stop();
        }
    }
    
    /**
     * After objects() or kvs() the builder is spent: each builder call is
     * IllegalStateException; objects() and kvs() may be called again, and each iterator
     * starts from the beginning at the lookup time that usePrimary() took (bergdb 020-10,
     * sections 3.4 to 3.6). A second objects() or kvs() was IllegalStateException, and a
     * builder call after it was taken.
     */
    @Nano
    public static void testBuilderSpentAfterListing() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            c.w().put("/i/a", "1").execute();
            final UsePrimaryBuilder<String> b = c.usePrimary(String.class).dir("/i/");
            Iterable<String> objects = b.objects();
            c.w().put("/i/b", "2").put("/i/a", "3").execute();
            
            Assert.assertEquals("[1]", list(objects));
            Assert.assertEquals("[1]", list(objects));
            Assert.assertEquals("/i/a=1 ", kvs(b.kvs()));
            Assert.assertEquals("[1]", list(b.objects()));
            assertThrows(IllegalStateException.class, () -> b.dir("/i/"));
            assertThrows(IllegalStateException.class, () -> b.startAt("a"));
            assertThrows(IllegalStateException.class, () -> b.inclusive(true));
            assertThrows(IllegalStateException.class, () -> b.backward());
            Assert.assertEquals("[1]", list(b.objects()));
            
            Assert.assertEquals("[2, 3]", 
                    list(c.usePrimary(String.class).dir("/i/").backward().objects()));
        } finally {
            db.stop();
        }
    }
    
    /**
     * A scan is a read for freezeLookupTime(), as a get is (bergdb 020-10, section 3.6):
     * the first read after freezeLookupTime() fixes the frozen time, also when it is a
     * usePrimary(), and later gets and scans read at it. A scan did not fix it.
     */
    @Nano
    public static void testScanFixesFrozenLookupTime() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            Transaction t1 = c.w().put("/f/a", "1").execute();
            c.freezeLookupTime();
            Iterable<String> it = c.usePrimary(String.class).dir("/f/").objects();
            Assert.assertEquals(t1.getTime(), c.getLookupTime());
            
            c.w().put("/f/a", "2").put("/f/b", "3").execute();
            Assert.assertEquals("[1]", list(it));
            Assert.assertEquals("1", c.get("/f/a", String.class));
            Assert.assertEquals("[1]", list(c.usePrimary(String.class).dir("/f/").objects()));
            Assert.assertEquals(t1.getTime(), c.getLookupTime());
            
            c.setLookupTime(Time.MAX);
            Assert.assertEquals("[2, 3]", list(c.usePrimary(String.class).dir("/f/").objects()));
            Assert.assertEquals(Time.MAX, c.getLookupTime());
        } finally {
            db.stop();
        }
    }
    
    /**
     * bergdb 020-22: a value written through the Core at the directory's own file prefix,
     * /dm/-, the ikey of an empty name, which no ukey gives, is not listed, forward or
     * backward: a page holds the keys that the prefix is a proper prefix of
     * (Keys.isPrefix), and a key that no ukey gives is left out (PubKeys.i2uOrNull), as by
     * an index's scan and transactionInfo(). The index's scan gave such a key as "/r/"
     * (PubTesterIndex.testScanLeavesOutAKeyWithNoUkey).
     */
    @Nano
    public static void testScanLeavesOutTheEmptyName() {
        Database d = Factory.database().memory().start();
        try {
            Db db = ((DatabaseImp) d).getDb();
            db.execute(db.trans().put(Keys.toBytes("/dm/-"), new byte[] {'x'}).build());
            Connection c = d.connection();
            c.put("/m/a", "a");
            Assert.assertEquals("/m/a ", keys(c.usePrimary(byte[].class).dir("/m/").kvs()));
            Assert.assertEquals("/m/a ", 
                    keys(c.usePrimary(byte[].class).dir("/m/").backward().kvs()));
            Assert.assertEquals("/m/a ", 
                    keys(c.usePrimary(Object.class).dir("/m/").backward().kvs()));
        } finally {
            d.stop();
        }
    }
    
    /**
     * A scan reads with the Core's Db, not through the connection's get: transactionInfo()
     * still describes the last get() (bergdb 020-10, section 3.6, N3).
     */
    @Nano
    public static void testScanKeepsTransactionInfo() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            Transaction t1 = c.w().put("/n/a", "1").execute();
            c.w().put("/n/b", "2").execute();
            Assert.assertEquals("1", c.get("/n/a", String.class));
            Assert.assertEquals("[1, 2]", list(c.usePrimary(String.class).dir("/n/").objects()));
            Assert.assertEquals(t1.getTime(), c.transactionInfo().time());
        } finally {
            db.stop();
        }
    }
    
    /**
     * A scan whose lookup time falls behind reclaim's cut while it runs throws
     * LookupTimeNotAvailableException from hasNext() (bergdb 020-10, section 3.6): here at
     * its second page. Made with the Core's builder, as
     * PubTester.testFirstAvailableLookupTime2, so that reclaim cuts soon.
     */
    @Nano
    public static void testScanBehindCut() {
        TestClock clock = new TestClock();
        Db core = Db.builder().testSetup(new CutStream()).clock(clock).maxNodeSize8()
                .startupDistance(2000).build();
        Database d = DatabaseImp.createAndStart(core);
        try {
            d.setRetainDuration(Duration.seconds(1));
            Connection c = d.connection();
            long sec = Duration.seconds(1).units();
            long time = sec;
            clock.setTime(Time.units(time));
            WBuilder w = c.w();
            for (int i = 0; i < 150; i++) {
                w.put(String.format("/s/%03d", i), "v" + i);
            }
            long t0 = w.execute().getTime().units();
            Iterator<String> it = c.usePrimary(String.class).dir("/s/").objects().iterator();
            Assert.assertEquals("v0", it.next());
            
            java.util.Random r = new java.util.Random(1);
            for (int i = 0; i < 20000 && d.getFirstAvailableLookupTime().units() <= t0; i++) {
                time += sec / 20;
                clock.setTime(Time.units(time));
                c.w().put("/k/" + r.nextInt(50), "v" + i).execute();
            }
            Assert.assertTrue("no cut after the scan's time", 
                    d.getFirstAvailableLookupTime().units() > t0);
            
            int n = 1;
            LookupTimeNotAvailableException ex = null;
            try {
                while (it.hasNext()) {
                    it.next();
                    n++;
                }
            } catch (LookupTimeNotAvailableException e) {
                ex = e;
            }
            Assert.assertTrue("a scan behind the cut listed " + n + " values", ex != null);
        } finally {
            d.stop();
        }
    }
    
    /**
     * A listing stays in its directory, forward and backward, from a startAt() before, among
     * or after its names, which are in code-point order: its neighbours (a file of its name
     * in the parent, directories whose names start with its own, its subdirectory) are not
     * listed.
     */
    @Nano
    public static void testListingStaysInItsDirectory() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            String smile = "😀";
            c.w().put("/q", "q").put("/q0/x", "q0x").put("/p/z", "pz").put("/q-/x", "q-x")
                 .put("/q/b", "b").put("/q/d", "d").put("/q/sub/x", "subx").put("/r/a", "ra")
                 .put("/q/～", "ff5e").put("/q/" + smile, "smile").execute();
            
            Assert.assertEquals("[b, d, ff5e, smile]", listQ(c, null, true, false));
            Assert.assertEquals("[smile, ff5e, d, b]", listQ(c, null, true, true));
            Assert.assertEquals("[b, d, ff5e, smile]", listQ(c, "a", true, false));
            Assert.assertEquals("[]", listQ(c, "a", true, true));
            Assert.assertEquals("[d, ff5e, smile]", listQ(c, "c", true, false));
            Assert.assertEquals("[b]", listQ(c, "c", false, true));
            Assert.assertEquals("[d, ff5e, smile]", listQ(c, "d", true, false));
            Assert.assertEquals("[ff5e, smile]", listQ(c, "d", false, false));
            Assert.assertEquals("[d, b]", listQ(c, "d", true, true));
            Assert.assertEquals("[b]", listQ(c, "d", false, true));
            Assert.assertEquals("[ff5e, smile]", listQ(c, "zzz", true, false));
            Assert.assertEquals("[d, b]", listQ(c, "zzz", true, true));
            Assert.assertEquals("[smile]", listQ(c, "￿", true, false));
            Assert.assertEquals("[ff5e, d, b]", listQ(c, "￿", true, true));
            Assert.assertEquals("[]", listQ(c, "😁", true, false));
            Assert.assertEquals("[smile, ff5e, d, b]", listQ(c, "😁", true, true));
            
            Assert.assertEquals("[q]", list(c.usePrimary(String.class).dir("/").objects()));
            Assert.assertEquals("[q0x]", list(c.usePrimary(String.class).dir("/q0/").objects()));
            Assert.assertEquals("[q-x]", list(c.usePrimary(String.class).dir("/q-/").objects()));
            Assert.assertEquals("[subx]", 
                    list(c.usePrimary(String.class).dir("/q/sub/").objects()));
            Assert.assertEquals("[]", list(c.usePrimary(String.class).dir("/none/").objects()));
        } finally {
            db.stop();
        }
    }
    
    private static String listQ(Connection c, String startAt, boolean inclusive, 
            boolean backward) {
        UsePrimaryBuilder<String> b = c.usePrimary(String.class).dir("/q/");
        if (startAt != null) {
            b.startAt(startAt).inclusive(inclusive);
        }
        if (backward) {
            b.backward();
        }
        return list(b.objects());
    }
    
    /** The iterator's contract: hasNext() as often as wished, then next() throws. */
    @Nano
    public static void testIteratorContract() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            Assert.assertFalse(c.usePrimary(String.class).dir("/").objects().iterator().hasNext());
            c.w().put("/u/a", "1").execute();
            
            final Iterator<String> it = c.usePrimary(String.class).dir("/u/").objects()
                    .iterator();
            Assert.assertTrue(it.hasNext());
            Assert.assertTrue(it.hasNext());
            Assert.assertEquals("1", it.next());
            Assert.assertFalse(it.hasNext());
            Assert.assertFalse(it.hasNext());
            assertThrows(NoSuchElementException.class, () -> it.next());
            assertThrows(UnsupportedOperationException.class, () -> it.remove());
            
            final Iterator<Kv<String>> kvs = c.usePrimary(String.class).dir("/u/").kvs()
                    .iterator();
            Assert.assertEquals("/u/a", kvs.next().key());
            assertThrows(NoSuchElementException.class, () -> kvs.next());
        } finally {
            db.stop();
        }
    }
    
    /** The number of the database's internal keys (under /#i/), read with the Core's Db. */
    static int internalKeys(Database database) {
        Db db = ((DatabaseImp) database).getDb();
        final long[] prefix = DbConstants.INTERNAL_PREFIX_SKEY;
        final int[] count = {0};
        GetMany g = db.newGetMany();
        g.startKey = prefix;
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                if (!Keys.isPrefix(prefix, kvt.key)) {
                    return STOP;
                }
                count[0]++;
                return CONTINUE;
            }
            
            public void eod() {
            }
        };
        db.getMany(g);
        return count[0];
    }
    
    static void assertThrows(Class<? extends Throwable> expected, Runnable call) {
        try {
            call.run();
        } catch (Throwable e) {
            if (expected.isInstance(e)) {
                return;
            }
            AssertionError a = new AssertionError("expected " + expected.getSimpleName() 
                    + ", got " + e);
            a.initCause(e);
            throw a;
        }
        throw new AssertionError("expected " + expected.getSimpleName() + ", nothing thrown");
    }
    
    private static <T> String kvs(Iterable<Kv<T>> kvs) {
        StringBuilder b = new StringBuilder();
        for (Kv<T> kv : kvs) {
            b.append(kv.key()).append('=').append(kv.value()).append(' ');
        }
        return b.toString();
    }
    
    private static <T> String keys(Iterable<Kv<T>> kvs) {
        StringBuilder b = new StringBuilder();
        for (Kv<T> kv : kvs) {
            b.append(kv.key()).append(' ');
        }
        return b.toString();
    }
    
    private static String list(Iterable<String> values) {
        java.util.List<String> result = new java.util.ArrayList<String>();
        for (String s : values) {
            result.add(s);
        }
        return result.toString();
    }
}
