package bergdb.pubimp;

import java.io.UnsupportedEncodingException;
import java.util.HashMap;

import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.util.BadFormatException;

/**
 * Default implementation of KvToObject.
 * Special handling is used when c is byte[].class, java.lang.String, or java.lang.Object.
 * Otherwise, this implementation assumes the class has a public no-arg constructor and 
 * creates objects using that constructor.
 * 
 * @author Frans Lundberg
 */
public class KvToObjectImp implements KvToObjectConverter, ClassToObject {
    private HashMap<Class<?>, BlankConstructorFactory> factories;
        // Protected by sync on itself.
    
    public KvToObjectImp() {
        factories = new HashMap<Class<?>, BlankConstructorFactory>();
    }

    @SuppressWarnings("unchecked")
    public <TYPE> TYPE createObject(Class<TYPE> c, String ikey, byte[] value) 
            throws ObjectCreationException {
        //
        // If c is String.class, byte[].class, or DbObject.class, we handle it
        // in a special, but simple way (convert to String from UTF-8 bytes, return raw
        // bytes, parse to a DbObject).
        // 
        // If c is Object.class, we handle a mix of value types.
        //      isObject()       -> DbObject
        //      .txt             -> String
        //      others           -> byte[]
        //
        // Otherwise, use the dbObject.toJavaObject() to convert to an object
        // of the specified type.
        //
        
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
            result = (TYPE) entryToString(value);
        } else if (c.equals(byte[].class)) {
            result = (TYPE) value;      // the database's own array, bergdb 015-47
        } else if (c.equals(DbObject.class)) {
            result = (TYPE) entryToDbObject(ukey, value);
        } else if (c.equals(Object.class)) {
            result = (TYPE) entryToMixedTypeObject(ikey, ukey, value);
        } else {
            result = (TYPE) entryToDbObject(ukey, value).toJavaObject(c, this);
        }
        
        return result;
    }

    /** Converts a database value to a String, UTF-8 encoding assumed. */
    private String entryToString(byte[] value) {
        return StringUtil.toString(value);
    }

    /**
     * Converts an entry to a Java Object when c is Object.class: a DbObject if the value is a
     * stored object by the full check; a byte[] that starts with the header but is not one
     * stays a byte[] (bergdb 020-08, section 3).
     */
    private Object entryToMixedTypeObject(String ikey, String ukey, byte[] value) {
        Object result;
        boolean isObject = Entries.isProbablyDbObject(ikey, value);
        
        if (isObject) {
            try {
                result = ukey == null ? new DbObject(value) : new DbObject(value, ukey);
            } catch (BadFormatException e) {
                result = value;     // the database's own array, bergdb 015-47
            }
        } else if (ikey.endsWith(".txt")) {
            result = entryToString(value);
        } else {
            result = value;     // the database's own array, bergdb 015-47
        }
        return result;
    }
    
    private DbObject entryToDbObject(String ukey, byte[] value) {
        DbObject dbObject;
        try {
            if (ukey == null) {
                dbObject = new DbObject(value);
            } else {
                dbObject = new DbObject(value, ukey);
            }
        } catch (BadFormatException e) {
            throw new ObjectCreationException(e.getMessage() + " ukey=" + ukey);
        }
        
        return dbObject;
    }
    
    /**
     * Creates and returns a new object of the specified class.
     * The newly created object is typically used as a template; its fields will be set
     * through reflection to match data in the database.
     * 
     * @throws ObjectCreationException  If the objection could not be created.
     */
    @SuppressWarnings("unchecked")
    public <TYPE> TYPE newObject(Class<TYPE> c) {
        BlankConstructorFactory f;
        synchronized  (factories) {
            f = factories.get(c);
            
            if (f == null) {
                try {
                    f = new BlankConstructorFactory(c);
                    factories.put(c, f);
                } catch (IllegalArgumentException e) {
                    throw new ObjectCreationException(e.getMessage());
                }
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
    
    @Nano
    public static void test0() {
        KvToObjectImp k = new KvToObjectImp();
        
        ClassA a0 = new ClassA();
        a0.count = 200;
        byte[] value = DbObject.toDbObject(a0).getBytes();
        String ukey = "/classA/1";
        
        ClassA a1 = k.createObject(KvToObjectImp.ClassA.class, PubKeys.u2i(ukey), value);
        
        Assert.assertEquals(200, a1.count);
        Assert.assertEquals("hello", a1.greeting);
    }
    
    @Nano
    public static void testByteArray() {
        KvToObjectImp k = new KvToObjectImp();
        
        ClassA a0 = new ClassA();
        a0.count = 200;
        byte[] value = DbObject.toDbObject(a0).getBytes();
        String key = "/classA/1";
        
        byte[] value2 = k.createObject(byte[].class, PubKeys.u2i(key), value);
        
        Assert.assertEquals(value, value2);
    }
    
    @Nano
    public static void testString() throws UnsupportedEncodingException {
        KvToObjectImp k = new KvToObjectImp();
        String s0 = "hello";
        byte[] value = s0.getBytes("UTF-8");
        String key = "classA/1";
        
        String s1 = k.createObject(String.class, key, value);
        
        Assert.assertEquals(s1, s0);
    }
    
    @Nano
    public static void testNull() throws UnsupportedEncodingException {
        KvToObjectImp k = new KvToObjectImp();
        String s1 = k.createObject(String.class, "key", null);
        Assert.assertNull(s1);
    }
    
    @Nano
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
