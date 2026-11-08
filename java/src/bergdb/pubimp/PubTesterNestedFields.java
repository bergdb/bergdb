package bergdb.pubimp;

import java.util.Iterator;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;

/**
 * Tests indexing of nested fields for Pub API.
 * 
 * @author Frans Lundberg
 */
public class PubTesterNestedFields {
    public static class Person {
        public long id;
    }
    
    public static class Dialog {
        public Person personA;
        public Person personB;
    }
    
    public static class Top {
        public Nested1 nested1;
        
        @SuppressWarnings("unused")
        public Top() {}
        
        public Top(long value) {
            nested1 = new Nested1();
            nested1.nested2 = new Nested2();
            nested1.nested2.value = value;
        }
    }
    
    public static class Nested1 {
        public Nested2 nested2;
    }
    
    public static class Nested2 {
        public long value;
    }
    
    @Nano
    public static void test0() {
        Database db = Factory.database().memory().start();
        Connection c = db.newConnection();
        
        Dialog d1 = new Dialog();
        Dialog d2 = new Dialog();
        Dialog d3 = new Dialog();
        
        Person p1 = new Person();
        Person p2 = new Person();
        Person p3 = new Person();
        
        p1.id = 10;
        p2.id = 20;
        p3.id = 30;
        
        d1.personA = p1;
        d1.personB = p2;
        
        d2.personA = p2;
        d2.personB = p3;
        
        d3.personA = p3;
        d3.personB = p1;
        
        db.indexBuilder("i1").type("long").dir("/dialogs/")
            .nestedField(new String[]{"personB", "id"}).createFast();
        
        c.put("/dialogs/d1", d1);
        c.put("/dialogs/d2", d2);
        c.put("/dialogs/d3", d3);
        
        Iterator<Dialog> iter = c.useIndex("i1", Dialog.class).objects().iterator();
        
        long[] expectedIdA = {30, 10, 20};
        long[] expectedIdB = {10, 20, 30};
        
        for (int i = 0; i < expectedIdA.length; i++) {
            Dialog d = iter.next();
            Assert.assertEquals(expectedIdA[i], d.personA.id);
            Assert.assertEquals(expectedIdB[i], d.personB.id);
        }
        Assert.assertFalse(iter.hasNext());
        
        db.stop();
    }
    
    @Nano
    public static void test1() {
        // Tests with some Top instances, index on "nested1.nested2.value".
        
        Database db = Factory.database().memory().start();
        Connection c = db.connection();
        
        db.indexBuilder("i1").type("long").dir("/tops/").nestedField("nested1.nested2.value").createFast();    
        c.put("/tops/t1", new Top(20));
        c.put("/tops/t2", new Top(10));
        c.put("/tops/t3", new Top(30));
        c.put("/tops/t4", new Top(3));
        
        long[] expected = new long[]{3, 10, 20, 30};
        int index = 0;
        
        for (Top t : c.useIndex("i1", Top.class).objects()) {
            Assert.assertEquals(expected[index], t.nested1.nested2.value);
            index++;
        }
        
        Assert.assertEquals(4, index);
        
        db.stop();
    }
    
    /** {f: {value: v}}: a nested object, as the put of an object with a nested one gives. */
    private static DbObject nested(DbValue v) {
        return new DbObject.Builder().addObject("f", 
                new DbObject.Builder().addDbValue("value", v).build()).build();
    }
    
    @Nano
    public static void testWithDoubles() {        
        Database db = Factory.database().memory().start();
        Connection c = db.connection();
        
        db.indexBuilder("i1").type("double").dir("/d/").nestedField("f.value").createFast();    
        c.put("/d/1", nested(new DbDouble(12.3)));
        
        c.put("/d/2", nested(new DbDouble(-1.2)));
        
        c.put("/d/3", nested(new DbDouble(0.0)));
        
        double[] expected = new double[]{-1.2, 0.0, 12.3};
        int index = 0;
        
        for (DbObject dbo : c.useIndex("i1", DbObject.class).objects()) {
            Assert.assertEquals(expected[index], dbo.getObject("f").getDouble("value"));
            Assert.assertEquals(expected[index], dbo.getDouble(new String[]{"f", "value"}));
            index++;
        }
        
        Assert.assertEquals(3, index);
        
        db.stop();
    }
    
    @Nano
    public static void testWithStrings() {        
        Database db = Factory.database().memory().start();
        Connection c = db.connection();
        
        db.indexBuilder("i1").type("string").dir("/d/").nestedField("f.value").createFast();    
        c.put("/d/1", nested(new DbString("anna")));
        
        c.put("/d/2", nested(new DbString("zebra")));
        
        c.put("/d/3", nested(new DbString("cecilia")));
        
        String[] expected = new String[]{"anna", "cecilia", "zebra"};
        int index = 0;
        
        for (DbObject dbo : c.useIndex("i1", DbObject.class).objects()) {
            Assert.assertEquals(expected[index], dbo.getObject("f").getString("value"));
            Assert.assertEquals(expected[index], dbo.getString(new String[]{"f", "value"}));
            index++;
        }
        
        Assert.assertEquals(3, index);
        
        db.stop();
    }
}
