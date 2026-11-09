package bergdb.pubimp;

import java.io.UnsupportedEncodingException;

import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.DataFormatException;
import bergdb.pub.DbObject;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.util.BadFormatException;

/**
 * Default implementation of KvToObject.
 * Special handling is used when c is byte[].class, java.lang.String, DbObject.class or
 * java.lang.Object. Otherwise, c must be a Data Object class, a primitive or a wrapper, or
 * an array class, and the stored object is converted by DataObjects (bergdb 020-09).
 * 
 * @author Frans Lundberg
 */
class KvToObjectImp implements KvToObjectConverter {
    
    public KvToObjectImp() {
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
        // Otherwise, the class is checked first, also for a key without a value, and the
        // stored object converted by DataObjects (bergdb 020-09, sections 3.3 and 5).
        //
        
        if (c == null) {
            throw new IllegalArgumentException("clazz == null not allowed");
        }
        
        if (ikey == null) {
            throw new IllegalArgumentException("ikey == null not allowed");
        }
        
        boolean dataObject = !c.equals(String.class) && !c.equals(byte[].class) 
                && !c.equals(DbObject.class) && !c.equals(Object.class);
        if (dataObject) {
            DataObjects.checkGet(c);
        }
        
        if (value == null) {
            return null;
        }
        
        String ukey = PubKeys.i2uOrNull(ikey);     // for messages; null if none (020-22)
        String key = ukey == null ? ikey : ukey;    // the user's key, for messages
        
        TYPE result;
        
        if (c.equals(String.class)) {
            result = (TYPE) entryToString(key, value, isStoredObject(ikey, value));
        } else if (c.equals(byte[].class)) {
            result = (TYPE) value;      // the database's own array, bergdb 015-47
        } else if (c.equals(DbObject.class)) {
            result = (TYPE) entryToDbObject(key, value);
        } else if (c.equals(Object.class)) {
            result = (TYPE) entryToMixedTypeObject(ikey, key, value);
        } else {
            // From the stored bytes, after the full check: no DbObject, no copy (the review
            // of bergdb 020-10, B3).
            try {
                ObjectFormat.checkStored(value);
            } catch (BadFormatException e) {
                throw notAnObject(key, e);
            }
            result = DataObjects.toJavaObject(value, 1, c);
        }
        
        return result;
    }

    /**
     * Converts a database value to a String: its UTF-8 bytes decoded. Bytes that are not
     * well-formed UTF-8 (written through the Core API, or by another writer) are reported,
     * never repaired (bergdb 021-06); they were decoded with U+FFFD in place of each
     * ill-formed sequence. A stored object is never well-formed UTF-8 (its header, 0x82):
     * the message says that it is an object (bergdb 020-24-05, U5-9).
     * 
     * @param key  The user's key, for the message.
     * @param object  True if the value is a stored object at an object key.
     * @throws DataFormatException  If the value is not well-formed UTF-8.
     */
    private String entryToString(String key, byte[] value, boolean object) {
        if (!StringUtil.isWellFormedUtf8(value)) {
            if (object) {
                throw new DataFormatException("The value at " + key + " is an object, not a "
                        + "String; it can be read as a DbObject, as a Data Object class or as "
                        + "a byte[].");
            }
            throw new DataFormatException("The value at " + key + " is not well-formed UTF-8, "
                    + "so it is not a String; it can be read as a byte[] (bergdb 021-06).");
        }
        return StringUtil.toString(value);
    }

    /** True if the value is a stored object at an object key, by the full check. */
    private static boolean isStoredObject(String ikey, byte[] value) {
        if (!Entries.isProbablyDbObject(ikey, value)) {
            return false;
        }
        try {
            ObjectFormat.checkStored(value);
            return true;
        } catch (BadFormatException e) {
            return false;
        }
    }

    /**
     * The refusal of a value that is not a stored object, read as an object; its message
     * names the user's key (bergdb 020-24-05, U5-9: it ended with " ukey=" and the key).
     */
    private static ObjectCreationException notAnObject(String key, BadFormatException e) {
        return new ObjectCreationException("The value at " + key + " cannot be read as an "
                + "object: " + e.getMessage());
    }

    /**
     * Converts an entry to a Java Object when c is Object.class: a DbObject if the value is a
     * stored object by the full check; a byte[] that starts with the header but is not one
     * stays a byte[] (bergdb 020-08, section 3). An object of format 1 is refused with
     * ObjectCreationException, naming the format (bergdb 020-02, section 4.11).
     */
    private Object entryToMixedTypeObject(String ikey, String key, byte[] value) {
        Object result;
        boolean isObject = Entries.isProbablyDbObject(ikey, value);
        
        if (Entries.isFormat1Object(ikey, value)) {
            result = entryToDbObject(key, value);       // throws, naming format 1
        } else if (isObject) {
            try {
                result = new DbObject(value);
            } catch (BadFormatException e) {
                result = value;     // the database's own array, bergdb 015-47
            }
        } else if (ikey.endsWith(".txt")) {
            result = entryToString(key, value, false);
        } else {
            result = value;     // the database's own array, bergdb 015-47
        }
        return result;
    }
    
    private DbObject entryToDbObject(String key, byte[] value) {
        DbObject dbObject;
        try {
            dbObject = new DbObject(value);     // the stored object exactly (bergdb 020-02)
        } catch (BadFormatException e) {
            throw notAnObject(key, e);
        }
        
        return dbObject;
    }
    
    // -------- Testing ---------------
    
    public static class ClassA {
        public ClassA() {}
        public String greeting = "hello";
        public long count = 123L;
    }
    
    @SuppressWarnings("unused")
    public static class ClassB {
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
