package bergdb.coreds;

import java.io.UnsupportedEncodingException;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * <p>This class has static methods used for handling database keys.
 * They include methods for converting a key between three key formats:
 * string key, byte key, and segment key.
 * This class is the authority on the key formats and should always be used to convert 
 * a key between different formats.</p>
 * 
 * @author Frans Lundberg
 */
public class Keys {
    
    public int compare(long[] arr1, long[] arr2) {
        return compareArrays(arr1, arr2);
    }
    
    /**
     * Returns the hash value for a key. This hash is used in the KeyModSet.
     * 
     * @param keySegments
     * @return The hash value, always non-negative.
     */
    public static final long hash(long[] keySegments) {
        // 
        // Note that the hash should be possible and easy to compute by all DB clients.
        // See http://www.javapractices.com/topic/TopicAction.do?Id=28.
        // Code below is based on Effective Java, by Joshua Bloch. 
        // The hash values are only used for a short time in-memory. 
        // So, this algorithm should be possible to change between versions without affecting
        // the possibility of reading older database data.
        //
        
        long value = 37;
        for (long l : keySegments) {
            value = value * 37 + l;
        }
        value = value < 0 ? -value : value;    // always non-negative
        assert value >= 0;
        return value;
    }

    /**
     * Converts a String key to its segmented key representation by first converting
     * the String to bytes and than to segments with the method toSegments(byte[]).
     */
    public static final long[] toSegments(String key) {
        return toSegments(toBytes(key));
    }

    /**
     * Converts a segmented key to a String key.
     * 
     * @param key  The key segments, null is not allowed.
     */
    public static final String toString(long[] key) {
        return toString(toBytes(key));
    }

    /**
     * Converts a bkey to an ikey.
     * bytes == 'null' is not allowed.
     */
    public static final String toString(byte[] bytes) {
        assert bytes != null;
        assert bytes.length != 0;
        byte[] bytes2 = toStringBytes(bytes);
        return Util.toString(bytes2);
    }
    
    private static final byte[] toStringBytes(byte[] bytes) {
        assert bytes != null;
        assert bytes.length != 0;
        
        byte[] result = bytes.clone();
        
        for (int i = 0; i < bytes.length; i++) {
            byte b = bytes[i];
            if (b == 1) {
                b = '/';
            } else {
                b--;
                b--;
            }
            result[i] = b;
        }
        return result;
    }
    
    /**
     * Checks whether a bkey has a corresponding ikey of printable ASCII characters.
     */
    public static final boolean isPrintableAscii(byte[] bytes) {
        byte[] bytes2 = toStringBytes(bytes);
        return Util.isPrintableAscii(bytes2);
    }
    
    public static final String toDisplayString(byte[] bytes) {
        assert bytes != null;
        bytes = bytes.clone();
        
        for (int i = 0; i < bytes.length; i++) {
            byte b = bytes[i];
            if (b == 0) {
                b = '!';
            } else if (b == 1) {
                b = '/';
            } else {
                b--;
                b--;
            }
            bytes[i] = b;
        }
        
        return Util.toString(bytes);
    }
    
    public static final String toStringWithSubstitute(long[] segments) {
        return toStringWithSubstitute(toBytes(segments));
    }
    
    public static final String toStringWithSubstitute(byte[] bytes) {
        assert bytes != null;
        bytes = bytes.clone();
        
        for (int i = 0; i < bytes.length; i++) {
            byte b = bytes[i];
            if (b == 0) {
                b = 0x1a;    // Unicode Character 'SUBSTITUTE' (U+001A)
            } else if (b == 1) {
                b = '/';
            } else {
                b--;
                b--;
            }
            bytes[i] = b;
        }
        
        return Util.toString(bytes);
    }

    /**
     * Converts ikey to bkey according to specification in 2013-key-encoding.txt.
     */
    public static byte[] toBytes(String s) {        
        assert s != null : "s == null not allowed";
        byte[] bytes;
        try {
            bytes = s.getBytes("UTF-8");
        } catch (UnsupportedEncodingException e) {
            throw new Error("Never happens, UTF-8 must be supported by JVM.");
        }
        
        if (bytes.length == 0) {
            throw new IllegalArgumentException("The empty string is not a valid key.");
        }
        
        for (int i = 0; i < bytes.length; i++) {
            byte b = bytes[i];
            if (b == (byte) 0xff || b == (byte) 0xfe) {
                throw new Error("Should not happen, illegal UTF-8 byte value, s = " + s);
            }
            
            if (b == '/') {
                b = 0x01;
            } else {
                b++;
                b++;
            }
            bytes[i] = b;
        }
        
        return bytes;
    }

    /**
     * Converts a key to its segmented key representation - an array of long
     * compare values. Always use this method to create key segments from a byte array key.
     * This method defines the segmented key representation format.
     */
    public static final long[] toSegments(byte[] key) {
        //
        // Note, a key of size 7 will be *two* segments long. The last key segment will have a
        // key length of 0. This way, we can differentiate between a value node klong (length 0-6) 
        // and a key node klong (length 7).
        // Also, it has the advantage that two key klongs in the same key node for the same time 
        // never have the same compare value (same "key").
        //
        
        int size = (key.length + Klong.MAX_SIZE) / Klong.MAX_SIZE;
        long[] segments = new long[size];
        int offset = 0;
        int length;
        
        for (int i = 0; i < size; i++) {
            length = key.length - offset;
            length = length > Klong.MAX_SIZE ? Klong.MAX_SIZE : length;
            segments[i] = Klong.createCompareValue(key, offset, length);
            offset += Klong.MAX_SIZE;
        }
        
        return segments;
    }
    
    /**
     * Converts a key in the the segmented form (long[]) to its byte array form.
     * Always use this method to convert a segmented key to a byte array.
     */
    public static byte[] toBytes(long[] segments) {
        assert segments != null : "segments == null not allowed";
        assert segments.length > 0 : "segments.length == 0 not allowed";
        assert Klong.getLength(segments[segments.length - 1]) < 7;
            // Last key segment should be < 7 long.
        
        int length = Klong.getLength(segments[segments.length - 1]);
        length += Klong.MAX_SIZE * (segments.length - 1);
        
        byte[] result = new byte[length];
        int offset = 0;
        
        for (int i = 0; i < segments.length; i++) {
            Klong.getKey(segments[i], result, offset);
            offset += Klong.getLength(segments[i]);
        }
        
        return result;
    }
    
    public static final int compareArrays(long[] arr1, long[] arr2) {
        //
        // arr1 < arr2  --> neg
        // arr1 == arr2 --> 0
        // arr1 > arr2  --> pos
        //
        
        int result = 0;
        int length = Math.min(arr1.length, arr2.length);
        
        for (int i = 0; i < length; i++) {
            result = compareUnsignedLongs(arr1[i], arr2[i]);
            if (result != 0) {
                break;
            }
        }
        
        if (result == 0 && arr1.length != arr2.length) {
            result = arr1.length < arr2.length ? -1 : +1;
        }
        
        return result;
    }
    
    /**
     * A simpler version assuming that a Klong compare value is always non-negative. 
     * Currently they are defined to be in the range [0, 2^59] (2012-08).
     * Returns 0 if k1 == k2, returns -1 if k1 < k2, and +1 if k1 > k2.
     */
    public static final int compareKeys(long[] k1, long[] k2) {
        //
        // arr1 < arr2  --> neg
        // arr1 == arr2 --> 0
        // arr1 > arr2  --> pos
        //
        
        int result = 0;
        int length = Math.min(k1.length, k2.length);
        
        for (int i = 0; i < length; i++) {
            result = compareLongs(k1[i], k2[i]);
            if (result != 0) {
                break;
            }
        }
        
        if (result == 0 && k1.length != k2.length) {
            result = k1.length < k2.length ? -1 : +1;
        }
        
        return result;
    }
    
    /**
     * Returns true iff 'prefix' is a strict prefix of 'key'.
     * 
     * @param prefix
     * @param key
     */
    public static final boolean isPrefix(long[] prefix, long[] key) {
        //
        // * Check input.
        // * Compute lengths.
        // * Check all klongs but the last.
        // * Check the last klong.
        //
        assert prefix != null : "prefix is null, not allowed";
        assert key != null;
        assert prefix.length > 0;
        assert key.length > 0;
        
        final long lastPrefixKlong = prefix[prefix.length - 1];
        final long lastKeyKlong = key[key.length - 1];
        final int prefixLength = Klong.MAX_SIZE * (prefix.length - 1) + Klong.getLength(lastPrefixKlong);
        final int keyLength = Klong.MAX_SIZE * (key.length - 1) + Klong.getLength(lastKeyKlong);
        
        if (keyLength <= prefixLength) {
            return false;
        }
        
        for (int i = 0; i < prefix.length - 1; i++) {
            if (key[i] != prefix[i]) {
                return false;
            }
        }
        
        final int length = Klong.getLength(lastPrefixKlong);
        final int prefixLen = Klong.prefixLength(lastPrefixKlong, key[prefix.length - 1]);
        assert prefixLen <= length : "Bad prefixLen " + prefixLen + ", " + length + ".";
        boolean result = prefixLen == length;
        return result;
    }
    
    /**
     * Checks whether two keys are equal.
     */
    public static final boolean equals(long[] k1, long[] k2) {
        assert k1 != null;
        assert k2 != null;
        
        return compareKeys(k1, k2) == 0;
    }
    
    private static int compareLongs(long n1, long n2) {
        return n1 == n2 ? 0 : n1 < n2 ? -1 : +1;
    }
    
    private static int compareUnsignedLongs(long n1, long n2) {
        // Yes, a bit hairy, see bottom of source file.
        return n1 == n2 ? 0 : ((n1 < n2) ^ ((n1 < 0) != (n2 < 0)) ? -1 : +1);
    }
    
    // ======== Testing ========
    
    @T
    public static void testConversion0() {
        String[] strings = new String[] { "a", "dir/f1.txt", " ", "Stange\n\r  next line" };
        
        for (int i = 0; i < strings.length; i++) {
            long[] segments = toSegments(strings[i]);
            Assert.assertEquals(strings[i], toString(segments));
        }
    }
    
    @T
    public static void testConversion1() {
        Exception ex = null;
        
        try {
            toSegments("");
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    @T
    public static void testLongs() {
        Assert.assertEquals(true, compareUnsignedLongs(3, 1) > 0);
        Assert.assertEquals(true, compareUnsignedLongs(111222333444L, 111222333444L) == 0);
        Assert.assertEquals(true, compareUnsignedLongs(-1, -1) == 0);
        Assert.assertEquals(true, compareUnsignedLongs(0, 0) == 0);
        Assert.assertEquals(true, compareUnsignedLongs(-1, 111222333444L) > 0);
        Assert.assertEquals(true, compareUnsignedLongs(111222333444L, -1) < 0);
        Assert.assertEquals(true, compareUnsignedLongs(1, 44) < 0);
    }
    
    @T
    public static void testArrays() {
        Assert.assertEquals(true, compareArrays(new long[]{}, new long[]{}) == 0);
        Assert.assertEquals(true, compareArrays(new long[]{123}, new long[]{123}) == 0);
        Assert.assertEquals(true, compareArrays(new long[]{-111222333444L}, new long[]{-111222333444L}) == 0);
        
        Assert.assertEquals(true, compareArrays(new long[]{}, new long[]{1}) < 0);
        Assert.assertEquals(true, compareArrays(new long[]{1}, new long[]{0}) > 0);
        Assert.assertEquals(true, compareArrays(new long[]{0}, new long[]{1}) < 0);
        Assert.assertEquals(true, compareArrays(new long[]{1}, new long[]{0}) > 0);
        
        Assert.assertEquals(true, compareArrays(new long[]{1, 2, 3}, new long[]{1, 2, 4}) < 0);
        Assert.assertEquals(true, compareArrays(new long[]{1, 2, 4}, new long[]{1, 2, 3}) > 0);
        
        Assert.assertEquals(true, compareArrays(new long[]{1, 2, 3}, new long[]{1, 2, 3, 4}) < 0);
        Assert.assertEquals(true, compareArrays(new long[]{1, 2, 3, 4}, new long[]{1, 2, 3}) > 0);
    }
    
    @T
    public static void testPrefix1() {
        long[] k1 = Keys.toSegments("dir/customers/");
        long[] k2 = Keys.toSegments("dir/customers/anna.obj");
        
        Assert.assertTrue(Keys.isPrefix(k1, k2));
        Assert.assertFalse(Keys.isPrefix(k2, k1));
    }
    
    @T
    public static void testPrefix2() {
        long[] k1 = Keys.toSegments("dir/customers/");
        long[] k2 = Keys.toSegments("dir/customers/anna.obj");
        long[] k3 = Keys.toSegments("dir/customers/");
        long[] k4 = Keys.toSegments("dir/cust");
        
        Assert.assertTrue(Keys.isPrefix(k1, k2));
        Assert.assertTrue(Keys.isPrefix(k4, k1));
        Assert.assertTrue(Keys.isPrefix(k4, k2));
        Assert.assertFalse(Keys.isPrefix(k1, k3));
        Assert.assertFalse(Keys.isPrefix(k2, k1));
        Assert.assertFalse(Keys.isPrefix(k1, k4));
        Assert.assertFalse(Keys.isPrefix(k2, k4));
    }
    
    public static void main(String[] args) {
        testPrefix2();
    }
}

/*

-- 2012-08 --

Hmmm, compare value definition may have changed. It is always non-negative and limited to range 
[0, 2^59].

-- 2011 --

See http://www.javamex.com/java_equivalents/unsigned_arithmetic.shtml

public static boolean isLessThanUnsigned(long n1, long n2) {
  boolean comp = (n1 < n2);
  if ((n1 < 0) != (n2 < 0)) {
    comp = !comp;
  }
  return comp;
}

public static boolean isLessThanUnsigned(long n1, long n2) {
    return (n1 < n2) ^ ((n1 < 0) != (n2 < 0));
}

*/
