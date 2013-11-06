package bergdb.pubimp;

import java.lang.reflect.Field;

import bergdb.common.Bug;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.MissingKeyFieldException;

/**
 * Static utility methods for this package.
 * 
 * @author Frans Lundberg
 */
public class PubUtil {
    /**
     * "key" - name of field used to store the database key; the value is "key" and is not 
     * expected to change.
     */
    public static final String KEY_FIELD = "key";
    
    /**
     * Reads value of "String key"-field of the object.
     * Assumes such a field exists; otherwise it throws a MissingKeyFieldException.
     * 
     * @throws MissingKeyFieldException  If no such field exists in the object.
     */
    public static String readExistingKeyField(Object object) throws MissingKeyFieldException {
        assert object != null;
        
        Class<?> clazz = object.getClass();
        Field field;
        String key;
        
        field = getField(clazz, KEY_FIELD);
        if (field == null) {
            throw new MissingKeyFieldException("No field named 'key' in object.");
        }
        field.setAccessible(true);
        
        Class<?> fieldType = field.getType();
        if (fieldType.equals(String.class)) {
            try {
                key = (String) field.get(object);
            } catch (IllegalArgumentException e) {
                throw new Bug("Never happens, " + e.getMessage());
            } catch (IllegalAccessException e) {
                throw new Error("Should not happen, " + e.getMessage());
            }
        } else {
            throw new MissingKeyFieldException("Field 'key' in the object is not a String.");
        }
        
        if (key == null) {
            throw new MissingKeyFieldException("The value of field 'key' is null.");
        }
        
        return key;
    }
    
    /**
     * Returns a field of a class with a given name. The field may be private and may
     * exist in a super class. Fields in the class Object.class are not considered.
     * 
     * @return The found field, or null if no field with the given name could be found.
     */
    private static Field getField(Class<?> c, String fieldName) {
        Field result = null;
        
        while (!c.equals(Object.class)) {
            try {
                result = c.getDeclaredField(fieldName);
            } catch (SecurityException e) {
                throw new Error(e);
            } catch (NoSuchFieldException e) {
                // Empty
            }
            
            if (result != null) {
                break;
            }
            
            c = c.getSuperclass();
        }
        
        return result;
    }

    /**
     * Sets the "String key"-field of 'object' to the provided value ('key') if such a field
     * exists.
     * 
     * @param object    The object to try to set the field for.
     * @param key       The String to set the field to, if found.
     */
    public static void setKeyFieldIfItExists(Object object, String key) {
        assert object != null : "object is null";
        assert key != null : "key is null";
        
        Class<?> c = object.getClass();
        Field field = getField(c, KEY_FIELD);
        
        if (field != null && field.getType().equals(String.class)) {
            field.setAccessible(true);
            try {
                field.set(object, key);
            } catch (IllegalArgumentException e) {
                throw new Bug("Never happens, " + e.getMessage());
            } catch (IllegalAccessException e) {
                throw new Error(e);
            }
        }
    }
    
    
    // ======================= Tests ================
    
    private static class A {
        String key = "a";
    }
    
    private static class B {
        @SuppressWarnings("unused")
        String myKey = "a";
    }
    
    private static class C {
        @SuppressWarnings("unused")
        int key = 123;
    }
    
    private static class D {
        @SuppressWarnings("unused")
        private int myField = 2;
    }
    
    private static class E extends D {
        @SuppressWarnings("unused")
        private double d = 1.2;
    }
    
    private static class F extends A {
        @SuppressWarnings("unused")
        private String s = "s";
    }
    
    @T
    public static void testReadExistingKeyField0() {
        Assert.assertEquals("a", readExistingKeyField(new A()));
    }
    
    @T
    public static void testReadExistingKeyField1() {
        Exception ex = null;
        try {
            readExistingKeyField(new B());
        } catch (MissingKeyFieldException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    @T
    public static void testReadExistingKeyField2() {
        Exception ex = null;
        try {
            readExistingKeyField(new C());
        } catch (MissingKeyFieldException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    @T
    public static void testGetField0() {
        Field f = getField(A.class, "key");
        Assert.assertTrue(f != null);
        Assert.assertEquals("key", f.getName());
        Assert.assertEquals(String.class, f.getType());
    }
    
    @T
    public static void testGetField1() {
        // private field
        
        Field f = getField(D.class, "myField");
        Assert.assertTrue(f != null);
        Assert.assertEquals("myField", f.getName());
        Assert.assertEquals(int.class, f.getType());
    }
    
    @T
    public static void testGetField2() {
        // private field in superclass
        
        Field f = getField(E.class, "myField");
        Assert.assertTrue(f != null);
        Assert.assertEquals("myField", f.getName());
        Assert.assertEquals(int.class, f.getType());
        
        f = getField(E.class, "d");
        Assert.assertTrue(f != null);
        Assert.assertEquals("d", f.getName());
        Assert.assertEquals(double.class, f.getType());
    }
    
    @T
    public static void testSet0() {
        A obj = new A();
        setKeyFieldIfItExists(obj, "k20");
        Assert.assertEquals("k20", obj.key);
    }
    
    @T
    public static void testSet1() {
        // Does nothing
        B obj = new B();
        setKeyFieldIfItExists(obj, "k20");
    }
    
    @T
    public static void testSet2() {
        // Sets field in superclass.
        F obj = new F();
        setKeyFieldIfItExists(obj, "k20");
        Assert.assertEquals("k20", obj.key);
    }
}
