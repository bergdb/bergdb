package bergdb.pubimp;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * Class with functions that handles database entries; for example, this
 * class is responsible categorizing key-value entries into types: 
 * object (DbObject), string (UTF-8 bytes) and bytes (raw bytes).
 * 
 * @author Frans Lundberg
 */
public class Entries {

    /**
     * Returns the suffix of the key string, s.
     * The suffix is the part of the string after the last '.' character
     * or the empty string if s does not contain a '.'.
     * A string with a single '.' as the first character does not have a suffix.
     */
    public static final String suffix(String s) {
        int index = s.lastIndexOf('.');
        String result;
        
        if (index == 0) index = -1;
        
        if (index == -1) result = Entries.EMPTY;
        else result = s.substring(index + 1);
        
        return result;
    }

    public static final String EMPTY = "";
    
    
    /**
     * <p>Returns true if the key is "an object key".
     * An object key, has suffix ".obj" or no suffix at all.
     * The use of ".obj" is obsolete, prefer to use no suffix for
     * database objects.</p>
     * 
     * <p>All objects stored in the database must have a key that is an 
     * object key according to this method.</p>
     * 
     * @param key  A ukey/ikey, not null.
     */
    public static boolean isObjectKey(String key) {
        assert key != null;
        assert key.length() > 0;
        String suffix = suffix(key);
        return suffix.length() == 0 || suffix.equals(".obj");
    }
    
    /**
     * Returns true if the key-value entry is a DbObject.
     * We assume this is the case when the key is an object key
     * (see isObjectKey()) and the value starts with the byte signature for
     * DbObjects (DbObject.MAGIC).
     */
    public static boolean isObject(String key, byte[] value) {
        assert key != null;
        assert key.length() > 0;
        assert value != null;
        
        return isObjectKey(key)
                && value.length > DbObject.MAGIC.length
                && startsWithMagic(value);
    }
    
    private static boolean startsWithMagic(byte[] arr) {
        boolean result = true;
        for (int i = 0; i < DbObject.MAGIC.length; i++) {
            if (arr[i] != DbObject.MAGIC[i]) {
                result = false;
                break;
            }
        }
        return result;
    }

    // ======== Tests ========
    
    @T
    public static void testSuffix1() {
        // No suffix.
        Assert.assertEquals("", suffix("abcd"));
        Assert.assertEquals("", suffix(""));
        Assert.assertEquals("", suffix("myName."));
        Assert.assertEquals("", suffix(".hidden"));
    }

    @T
    public static void testSuffix2() {
        Assert.assertEquals("g", suffix("graph.g"));
        Assert.assertEquals("txt", suffix(".hidden.txt"));
        Assert.assertEquals("t", suffix("www.bergdb.gson.as.t"));
    }
}
