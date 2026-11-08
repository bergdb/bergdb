package bergdb.pubimp;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Class with functions that handles database entries; for example, this
 * class is responsible categorizing key-value entries into types: 
 * object (DbObject), string (UTF-8 bytes) and bytes (raw bytes).
 * 
 * @author Frans Lundberg
 */
public class Entries {
    private Entries() {}

    static final int TYPE_OBJECT = 1;
    static final int TYPE_DB_OBJECT = 2;
    static final int TYPE_BYTE_ARRAY = 3;
    static final int TYPE_ORDINARY = 4;

    static int classify(Class<?> clazz) {
        int result;
        
        if (clazz.equals(Object.class)) {
            result = TYPE_OBJECT;
        } else if (clazz.equals(DbObject.class)) {
            result = TYPE_DB_OBJECT;
        } else if (clazz.equals(byte[].class)) {
            result = TYPE_BYTE_ARRAY;
        } else {
            result = TYPE_ORDINARY;
        }
        return result;
    }
    
    /**
     * Returns the suffix of the key string, s.
     * The suffix is the part of the key's last part, after its last '/', that follows the
     * part's last '.' character, or the empty string if the last part does not contain a '.'.
     * A part with a single '.' as the first character does not have a suffix. A '.' in a
     * directory's name is not a suffix (2026-11-09, bergdb 021-10: the whole key's last '.'
     * was taken, so no key under "/v1.2/" was an object key).
     */
    public static final String suffix(String s) {
        int part = s.lastIndexOf('/') + 1;
        int index = s.lastIndexOf('.');
        String result;
        
        if (index <= part) index = -1;
        
        if (index == -1) result = Entries.EMPTY;
        else result = s.substring(index + 1);
        
        return result;
    }

    public static final String EMPTY = "";
    
    
    /**
     * <p>Returns true if the key is "an object key".
     * An object key, has suffix ".obj" or no suffix at all.
     * Note: the use of ".obj" is obsolete, prefer to use no suffix for
     * database objects. All objects stored in the database must have a key that is an 
     * object key according to this method.</p>
     * 
     * @param key  A non-null ukey or ikey.
     */
    public static boolean isObjectKey(String key) {
        assert key != null;
        assert key.length() > 0;
        String suffix = suffix(key);
        return suffix.length() == 0 || suffix.equals("obj");
    }
    
    /**
     * Returns true if the entry is probably a DbObject.
     * This is the case when the key is an object key
     * (see isObjectKey()) and the value starts with the header of a stored object of format
     * 2, DbObject.HEADER (0x82), with at least an empty object after it (bergdb 020-07). A
     * String value never does: no UTF-8 starts with a byte of 0x80 to 0xbf. A byte[] may, so
     * a caller that must tell reads the value with the full check (bergdb 020-08, section 3).
     */
    public static boolean isProbablyDbObject(String key, byte[] value) {
        assert key != null;
        assert key.length() > 0;
        assert value != null;
        
        return isObjectKey(key)
                && value.length >= 3
                && value[0] == DbObject.HEADER;
    }
    
    /**
     * Returns true if the entry is an object of format 1, BergDB 2026.3's and before: an
     * object key and a value that starts with "bergo" and the version 1 (bergdb 020-07,
     * section 9). It is not read: a reader refuses it, naming the format (bergdb 020-02,
     * section 4.11; 020-08, section 4.8), so a caller that classifies values lets it reach
     * the reader rather than take it for a byte[] or skip it.
     */
    public static boolean isFormat1Object(String key, byte[] value) {
        return isObjectKey(key) && value.length >= 6 && value[0] == 'b' && value[1] == 'e'
                && value[2] == 'r' && value[3] == 'g' && value[4] == 'o' && value[5] == 1;
    }

    // ======== Tests ========
    
    @Nano
    public static void testIsObject1() {
        Assert.assertTrue(isProbablyDbObject("/dir/1.obj", 
                new DbObject.Builder().addString("name", "Foo").build().getBytes()));
    }
    
    @Nano
    public static void testIsObject2() {
        Assert.assertTrue(isProbablyDbObject("/dir/1", 
                new DbObject.Builder().addString("name", "Foo").build().getBytes()));
    }
    
    @Nano
    public static void testIsObject3() {
        Assert.assertFalse(isProbablyDbObject("/dir/1.txt", 
                new DbObject.Builder().addString("name", "Foo").build().getBytes()));
    }
    
    @Nano
    public static void testIsObject4() {
        Assert.assertFalse(isProbablyDbObject("/dir/1", new byte[10]));
    }
    
    /** The header and at least 2 bytes more (bergdb 020-07): 82 48 00 is the empty object. */
    @Nano
    public static void testIsObject5() {
        Assert.assertTrue(isProbablyDbObject("/dir/1", new byte[] {(byte) 0x82, 0x48, 0}));
        Assert.assertFalse(isProbablyDbObject("/dir/1", new byte[] {(byte) 0x82, 0x48}));
        Assert.assertFalse(isProbablyDbObject("/dir/1", new byte[] {'b', 'e', 'r', 'g', 'o', 
                1, 0, 0}));
    }
    
    @Nano
    public static void testSuffix1() {
        // No suffix.
        Assert.assertEquals("", suffix("abcd"));
        Assert.assertEquals("", suffix(""));
        Assert.assertEquals("", suffix("myName."));
        Assert.assertEquals("", suffix(".hidden"));
    }

    /**
     * bergdb 021-10: the suffix is the key's last part's, so a '.' in a directory's name does
     * not make every key there a key with a suffix; it was the whole key's.
     */
    @Nano
    public static void testSuffixOfTheLastPart() {
        Assert.assertEquals("", suffix("/v1.2/k"));
        Assert.assertTrue(isObjectKey("/v1.2/k"));
        Assert.assertTrue(isObjectKey(PubKeys.u2i("/v1.2/k")));
        Assert.assertEquals("txt", suffix("/v1.2/k.txt"));
        Assert.assertFalse(isObjectKey(PubKeys.u2i("/v1.2/k.txt")));
        Assert.assertTrue(isObjectKey(PubKeys.u2i("/a.b/c.d/k.obj")));
        Assert.assertEquals("", suffix("/a.b/"));
    }
    
    /** An object of format 1: an object key and "bergo" with the version 1 (020-07, 9). */
    @Nano
    public static void testIsFormat1Object() {
        byte[] f1 = {'b', 'e', 'r', 'g', 'o', 1, 0, 0};
        Assert.assertTrue(isFormat1Object("/dir/1", f1));
        Assert.assertFalse(isFormat1Object("/dir/1.txt", f1));
        Assert.assertFalse(isFormat1Object("/dir/1", new byte[] {'b', 'e', 'r', 'g', 'o', 2}));
        Assert.assertFalse(isFormat1Object("/dir/1", new byte[] {'b', 'e', 'r', 'g', 'o'}));
        Assert.assertFalse(isFormat1Object("/dir/1", 
                new DbObject.Builder().addString("name", "Foo").build().getBytes()));
    }
    
    @Nano
    public static void testSuffix2() {
        Assert.assertEquals("g", suffix("graph.g"));
        Assert.assertEquals("txt", suffix(".hidden.txt"));
        Assert.assertEquals("t", suffix("www.bergdb.gson.as.t"));
    }
    
    @Nano
    private static void testClassify() {
        Assert.assertEquals(classify(DbObject.class), Entries.TYPE_DB_OBJECT);
        Assert.assertEquals(classify(Object.class), Entries.TYPE_OBJECT);
        Assert.assertEquals(classify(Entries.class), Entries.TYPE_ORDINARY);
        Assert.assertEquals(classify(byte[].class), Entries.TYPE_BYTE_ARRAY);
    }
}
