package kissdb.pubimp;

import java.io.UnsupportedEncodingException;
import java.util.HashMap;

import kissdb.common.BadFormatException;
import kissdb.common.Util;
import kissdb.nanotest.Assert;
import kissdb.nanotest.T;
import kissdb.pub.ObjectCreationException;

/**
 * Default implementation of KvToObject.
 * Special handling is used when c is byte[].class, java.lang.String, or java.lang.Object.
 * Otherwise, this implementation assumes the class has a public no-arg constructor and 
 * creates objects using that constructor.
 * 
 * @author Frans Lundberg
 */
public class KvToObjectImp implements KvToObject, ClassToObject {
    private HashMap<Class<?>, BlankConstructorFactory> factories;
        // Protected by sync on itself.
    
    public KvToObjectImp() {
        factories = new HashMap<Class<?>, BlankConstructorFactory>();
    }

    @SuppressWarnings("unchecked")
    public <TYPE> TYPE createObject(Class<TYPE> c, String ikey, byte[] value) 
            throws ObjectCreationException {
        if (c == null) {
            throw new IllegalArgumentException("c == null is not allowed");
        }
        
        if (ikey == null) {
            throw new IllegalArgumentException("ikey == null not allowed");
        }
        
        if (value == null) {
            return null;
        }
        
        String ukey;
        try {
            ukey = PubKeys.i2u(ikey);
        } catch (IllegalArgumentException e) {
            ukey = null;
        }
        
        TYPE result;
        
        if (c.equals(String.class)) {
            result = (TYPE) Util.toString(value);
        } else if (c.equals(byte[].class)) {
            result = (TYPE) value;
        } else if (c.equals(DbObject.class)) {
            if (ukey == null) {
                result = (TYPE) new DbObject(value);
            } else {
                result = (TYPE) new DbObject(value, ukey);
            }            
        } else if (c.equals(Object.class)) {
            // Handling a mix of KVs: .obj -> DbObject, .txt -> String, others -> byte[]
            
            if (ikey.endsWith(".obj")) {
                DbObject dbObject;
                try {
                    if (ukey == null) {
                        dbObject = new DbObject(value);
                    } else {
                        dbObject = new DbObject(value, ukey);
                    }
                } catch (BadFormatException e) {
                    throw new ObjectCreationException(e.getMessage() + " ikey=" + ikey);
                }
                result = (TYPE) dbObject;
                
            } else if (ikey.endsWith(".txt")) {
                result = (TYPE) Util.toString(value);
            } else {
                result = (TYPE) value;
            }
        } else {   
            // The ordinary case of creating an object based on an DbObject value stored in 
            // the database.
            
            DbObject dbObject;
            try {
                if (ukey == null) {
                    dbObject = new DbObject(value);
                } else {
                    dbObject = new DbObject(value, ukey);
                }
            } catch (BadFormatException e) {
                throw new ObjectCreationException(e.getMessage() + " ikey=" + ikey);
            }
            result = (TYPE) dbObject.toJavaObject(c, this);
        }
        
        return result;
    }
    
    @SuppressWarnings("unchecked")
    public <TYPE> TYPE newObject(Class<TYPE> c) {
        BlankConstructorFactory f;
        synchronized  (factories) {
            f = factories.get(c);
        }
        if (f == null) {
            try {
                f = new BlankConstructorFactory(c);
                factories.put(c, f);
            } catch (IllegalArgumentException e) {
                throw new ObjectCreationException(e.getMessage());
            }
        }
        
        Object object = f.createObject();
        return (TYPE) object;
    }
    
    // -------- Testing ---------------
    
    private static class ClassA {
        public ClassA() {}
        public String greeting = "hello";
        public long count = 123L;
    }
    
    @SuppressWarnings("unused")
    private static class ClassB {
        public ClassB(int myInt) {}
        public long count = 123L;
    }
    
    @T
    public static void test0() {
        KvToObjectImp k = new KvToObjectImp();
        
        ClassA a0 = new ClassA();
        a0.count = 200;
        byte[] value = DbObject.toDbObject(a0).getBytes();
        String ukey = "/classA/1.obj";
        
        ClassA a1 = k.createObject(KvToObjectImp.ClassA.class, PubKeys.u2i(ukey), value);
        
        Assert.assertEquals(200, a1.count);
        Assert.assertEquals("hello", a1.greeting);
    }
    
    @T
    public static void testByteArray() {
        KvToObjectImp k = new KvToObjectImp();
        
        ClassA a0 = new ClassA();
        a0.count = 200;
        byte[] value = DbObject.toDbObject(a0).getBytes();
        String key = "/classA/1.obj";
        
        byte[] value2 = k.createObject(byte[].class, PubKeys.u2i(key), value);
        
        Assert.assertEquals(value, value2);
    }
    
    @T
    public static void testString() throws UnsupportedEncodingException {
        KvToObjectImp k = new KvToObjectImp();
        String s0 = "hello";
        byte[] value = s0.getBytes("UTF-8");
        String key = "classA/1.obj";
        
        String s1 = k.createObject(String.class, key, value);
        
        Assert.assertEquals(s1, s0);
    }
    
    @T
    public static void testNull() throws UnsupportedEncodingException {
        KvToObjectImp k = new KvToObjectImp();
        String s1 = k.createObject(String.class, "key", null);
        Assert.assertNull(s1);
    }
    
    @T
    public static void testCouldNotCreateObject() {
        KvToObjectImp k = new KvToObjectImp();
        byte[] dummyBytes = new byte[100];
        Exception ex = null;
        try {
            k.createObject(ClassB.class, "k", dummyBytes);
        } catch (ObjectCreationException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
}
