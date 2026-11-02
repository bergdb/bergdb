package bergdb.dag;

import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Random;

import bergdb.common.ByteArrayComparator;
import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * <p>A class for creating and reading long:s in the node array, "klongs".
 * Static final methods based on long. Memory allocation is avoided. 
 * Performance is a concern. Checking is normally done with assert instead
 * of throwing exceptions for highest possible performance.</p>
 * 
 * <pre>
 * ---- FORMAT ----
 * Consider a long as 64 bits, Bit 0 is the least significant bit. 
 * Similarly, Byte 0 is the least significant byte.
 * Bit 3:4 means Bit 4 of Byte 3.
 * 
 * KEY KLONG
 * VERSION, 3 bits at 0:0-0:2.
 * No longer used! Always set to 0 in a key klong.
 * 
 * LENGTH, 3 bits at 0:3-0:5
 * Length of key in bytes.
 * 0 - length 0 (empty key) - can happen also when DB key is non-empty
 * 1 - length 1
 * ..
 * 7 - length 7
 * 
 * DATA, 56 bits at 0:6-7:5
 * Up to seven data bytes. First byte is stored in bits 6:6-7:5.
 * Bytes (often characters) of the key. Zero padded at the end.
 * 
 * TYPE, 2 bits at 7:6-7:7
 * 0 - time, indicates new version
 * 1 - key, 0-7 bytes of key. Klong has a pointer to a key node or a value node.
 * 2 - DEPRECATED! not used
 * 3 - delete bitmap. 62 bits at 0:0-7:5 are deleted-or-not bits for klongs at index 0 to 61.
 * 
 * TIME KLONG
 * Type = 0, time value in 56 bits (bits 0:0-6:7). The 6 bits at 7:0-7:5 are reserved
 * and must be zero in stored times.
 * </pre>
 */
public class Klong {
    //
    // Beware of constant in-lining. Library recompiled, client code not recompiled for new
    // library version --> problem. 
    // Do we want [MAX_TIME = identity(0x00ffffffffffffffL);] instead?
    // That way, the expression is not constant and will never be in-lined.
    // These constants are not part of the Pub API. Less important to keep DB API constant.
    //
    
    public static final long MIN_TIME = 0;
    public static final long MAX_TIME = 0x00ffffffffffffffL;
    
    public static final long TYPE_TIME   = 0L << (7*8 + 6);
    public static final long TYPE_KEY    = 1L << (7*8 + 6);
    public static final long TYPE_DELETE_BITMAP = 3L << (7*8 + 6);
    
    public static final int INT_TYPE_TIME   = 0;
    public static final int INT_TYPE_KEY    = 1;
    public static final int INT_TYPE_DELETE_BITMAP = 3;
    
    /** The maximum number of key bytes in one klong. */
    public static final int MAX_SIZE = 7;
    
    /** Marker klong that indicates "null" - no klong value. */
    public static final long NULL = privateCreateTime(MAX_TIME + 1);
    
    /** A KEY klong with the empty (zero-length) key and version = 0. */
    public static final long EMPTY_KEY = createKey(new byte[0]);
    
    /** A delete bitmap klong with no delete bits set. */
    public static final long DELETE_NONE_BITMAP = TYPE_DELETE_BITMAP;
    
    /** A delete bitmap klong with all delete bits set. */
    public static final long DELETE_ALL_BITMAP = TYPE_DELETE_BITMAP | 0x3fffffffffffffffL;
    
    /** Pre-computed array of longs, each with a value of 2^arrayIndex. */
    public static final long[] DELETE_BITS = new long[62];
    
    // 1408 Frans: Does this really increase performance? 
    // Was it measured? We could even decrease performance because of more cache-misses.
    static {
        long del = 1;
        for (int i = 0; i < DELETE_BITS.length; i++) {
            DELETE_BITS[i] = del;
            del <<= 1;
        }
    }
    
    private Klong() {}
    
    /**
     * Creates a TIME klong with a 56-bit time value.
     */
    public static final long createTime(long time) {
        assert time >= MIN_TIME;
        assert time <= MAX_TIME;
        long klong = setType(time, TYPE_TIME);
        return klong;
    }
    
    private static long privateCreateTime(long time) {
        long klong = setType(time, TYPE_TIME);
        return klong;
    }
    
    /**
     * Creates a KEY klong given the key as a byte array.
     */
    public static final long createKey(byte[] key) {
        assert key.length <= MAX_SIZE;
        return createKey(key, 0, key.length);
    }
    
    /**
     * Returns an empty DELETE bitmap klong. No bits have been set, no deletes made.
     */
    public static final long createDelete() {
        return DELETE_NONE_BITMAP;
    }
    
    /**
     * Sets one delete bit of a DELETE_BITMAP klong.
     */
    public static final long delete(long klong, int bitIndex) {
        assert bitIndex >= 0 && bitIndex < 62 : "index out of range: " + bitIndex;
        return klong | DELETE_BITS[bitIndex];
    }
    
    /**
     * Queries a DELETE_BITMAP klong.
     */
    public static final boolean isDeleted(long klong, int bitIndex) {
        assert bitIndex >= 0 && bitIndex < 62 : "index out of range: " + bitIndex;
        return (klong & DELETE_BITS[bitIndex]) != 0;
    }
    
    /**
     * Creates a KEY klong.
     */
    private static final long createKey(byte[] key, int keyOffset, int keyLength) {
        long value = 0;
        int shift = 6*8 + 6;
        assert keyLength < 8;
        
        for (int i = 0; i < keyLength; i++) {
            value |= (0x00ffL & key[keyOffset++]) << shift;
            shift -= 8;   // shifts 54, 46, 38, 30, 22, 14, 6 bits.
        }
        
        // Before inline: 
        //value = setHeader(value, TYPE_KEY, keyLength);
        value = (TYPE_KEY | ((long) keyLength << 3)) | (value & 0x3fffffffffffffc0L);
        return value;
    }
    
    /**
     * Creates a key klong from an ikey.
     * Useful for testing, normally byte arrays should be used.
     */
    private static long createKey(String key) {
        return createKey(Keys.toBytes(key));
    }
    
    /**
     * Gets time, assumes a TIME klong.
     */
    public static final long getTime(long value) {
        assert getType(value) == TYPE_TIME : "Not a TIME klong, '" + Klong.toString(value) + "'.";
        return value & 0x00ffffffffffffffL;
    }

    /**
     * Sets a key klong's type and length, and clears its reserved version bits.
     * length must be 0-7 (not checked).
     */
    public static final long setHeader(long klong, long type, long length) {
        // 2 zero bits in beginning, 6 at end
        // Byte 7: 0011 1111 = 3f, Byte 0: 1100 0000 = c0
        return (type | (length << 3)) | (klong & 0x3fffffffffffffc0L);
    }
    
    public static final long getType(long value) {
        return value & 0xc000000000000000L;  // Byte 7: 1100 0000 = c0
    }
    
    public static final long setType(long klong, long type) {
        return (klong & 0x3fffffffffffffffL) | type;
                // 0x3f = 0011 1111
    }
    
    public static final boolean isKey(long klong) {
        return getType(klong) == TYPE_KEY;
    }
    
    public static final boolean isTime(long klong) {
        return getType(klong) == TYPE_TIME;
    }
    
    /**
     * Gets the two-bit type as an int for a switch: 0 (time), 1 (key), or 3 (delete
     * bitmap). Type 2 is unused.
     */
    public static final int getIntType(long value) {
        return (int) ((value & 0xc000000000000000L) >>> (7*8 + 6));
    }
    
    public static final int getLength(long value) {
        // Length mask: 0011 1000 = 38
        return (int) ((value & 0x0000000000000038L) >>> 3);
    }
    
    /**
     * Slow test method for getting a UTF-8 string key.
     * Converts from bkey to ikey.
     */
    public static String getKeyString(long value) {
        byte[] bytes = new byte[getLength(value)];
        getKey(value, bytes);
        String result = Keys.bkey2ikey(bytes);
        return result;
    }
    
    public static final int getKey(long value, byte[] output) {
        return getKey(value, output, 0);
    }
    
    /**
     * Writes key bytes to 'output'.
     */
    public static final int getKey(long value, byte[] output, int offset) {
        int length = getLength(value);
        int shift = 6*8 + 6;
        long b;
        
        for (int i = 0; i < length; i++) {
            b = (value >>> shift) & 0x00000000000000ff;
            shift -= 8;
            output[offset + i] = (byte) b;
        }
        
        return length;
    }
    
    /**
     * Returns the key data in bytes 0-6. No length, no version, no type.
     */
    public static final long getKeyValue(long klong) {
        // All, but type in Byte 7 and version/length in Byte 0
        // Byte 7 mask: 0011 1111 = 3f, Byte 0 mask: 1100 0000 = c0
        return (klong & 0x3fffffffffffffc0L) >>> 6;
    }
    
    /**
     * Returns the compare value of a key klong. The compare value contains the key 
     * bytes (0-7 bytes in 7*8 bits) and their length (3 bits)
     * at the end. Version is not included.
     * A compare value is non-negative and below 2^62; its lowest three bits are zero.
     */
    public static final long getCompareValue(long value) {
        // All, but type bits in Byte 7 and version bits in Byte 0
        // Byte 7 mask: 0011 1111 = 3f, Byte 0 mask: 1111 1000 = f8
        return value & 0x3ffffffffffffff8L;
    }
    
    /**
     * Creates a compare value. No checks are made.
     */
    public static final long createCompareValue(byte[] key, int offset, int length) {
        long value = 0;
        int shift = 6*8 + 6;
        assert length < 8;
        
        for (int i = 0; i < length; i++) {
            value |= (0x00ffL & key[offset++]) << shift;
            shift -= 8;   // shifts 54, 46, 38, 30, 22, 14, 6 bits.
        }
        return value | (length << 3);
    }
    
    /**
     * Creates a compare value. No checks are made.
     */
    public static final long createCompareValue(byte[] key) {
        long value = 0;
        int shift = 6*8 + 6;
        int length = key.length;
        int offset = 0;
        assert length < 8;
        
        for (int i = 0; i < length; i++) {
            value |= (0x00ffL & key[offset++]) << shift;
            shift -= 8;   // shifts 54, 46, 38, 30, 22, 14, 6 bits.
        }
        return value | (length << 3);
    }
    
    public static long compareValueToKeyKlong(long compareValue) {
        return compareValue | TYPE_KEY;
    }
    
    public static String toString(final long klong) {
        if (klong == Klong.NULL) {
            return "Klong.NULL";
        }
        
        int type = Klong.getIntType(klong);
        StringBuilder b = new StringBuilder();
        
        switch (type) {
        case Klong.INT_TYPE_TIME:
            long arrayTime = Klong.getTime(klong);
            b.append("t=" + arrayTime);
            break;
        case Klong.INT_TYPE_KEY:
            String keyString = Klong.getKeyString(klong);
            b.append(String.format("%-7s", keyString));
            break;
            
        case Klong.INT_TYPE_DELETE_BITMAP:
            // 3f = 0011 1111
            b.append("DEL " + StringUtil.toHexString(klong));
            break;
        default:
            assert false : "Bad klong type: " + type;
            break;
        }
        
        return b.toString();
    }
    
    /**
     * Given two KEY klongs, this method returns the length of the common 
     * prefix (0-7).
     */
    public static final int prefixLength(long k1, long k2) {
        //
        // Prefix     Masks
        // Char 1-7   0x00ff000000000000L
        // Char 2-7   0x00ffff0000000000L
        // Char 3-7   0x00ffffff00000000L
        // Char 4-7   0x00ffffffff000000L
        // Char 5-7   0x00ffffffffff0000L
        // Char 6-7   0x00ffffffffffff00L
        // Char 7     0x00ffffffffffffffL
        //
        
        int length1 = getLength(k1);
        int length2 = getLength(k2);
        
        //int length = length2 > length1 ? length2 : length1; 
            // Above line used before 2012-09-11, but changed to one below, tests ran 
            // both before and after.
        int length = length2 > length1 ? length1 : length2;
        
        long v1 = getKeyValue(k1);
        long v2 = getKeyValue(k2);
        int result = 0;
        
        // If prefix length at least 3
        if (length >= 3 && ((v1 & 0x00ffffff00000000L) == (v2 & 0x00ffffff00000000L))) {
            result = 3;
            result += (v1 & 0x00ffffffff000000L) == (v2 & 0x00ffffffff000000L) ? 1 : 0;
            result += (v1 & 0x00ffffffffff0000L) == (v2 & 0x00ffffffffff0000L) ? 1 : 0;
            result += (v1 & 0x00ffffffffffff00L) == (v2 & 0x00ffffffffffff00L) ? 1 : 0;
            result += (v1 & 0x00ffffffffffffffL) == (v2 & 0x00ffffffffffffffL) ? 1 : 0;
        } else {
            result =  (v1 & 0x00ff000000000000L) == (v2 & 0x00ff000000000000L) ? 1 : 0;
            result += (v1 & 0x00ffff0000000000L) == (v2 & 0x00ffff0000000000L) ? 1 : 0;
        }
        result = result > length ? length : result;
        
        return result;
    }
    
    
    // =========================== Testing =================
    
    @Nano
    public static void testPrefixLength1() {
        long k1 = createKey(StringUtil.toBytes("ab1"));
        long k2 = createKey(StringUtil.toBytes("ab2"));
        Assert.assertEquals(2, prefixLength(k1, k2));
        Assert.assertEquals(2, prefixLength(k2, k1));
    }
    
    @Nano
    public static void testPrefixLength2() {
        long k1 = createKey(StringUtil.toBytes("abc"));
        long k2 = createKey(StringUtil.toBytes("abcd11"));
        long k3 = createKey(StringUtil.toBytes(""));
        long k4 = createKey(StringUtil.toBytes("abcdefg"));
        long k5 = createKey(StringUtil.toBytes("abcdefg"));
        long k6 = createKey(StringUtil.toBytes("Prag"));
        
        Assert.assertEquals(3, prefixLength(k1, k2));
        Assert.assertEquals(3, prefixLength(k2, k1));
        
        Assert.assertEquals(0, prefixLength(k1, k3));
        Assert.assertEquals(0, prefixLength(k1, k3));
        
        Assert.assertEquals(0, prefixLength(k1, k6));
        Assert.assertEquals(7, prefixLength(k4, k5));
        
        Assert.assertEquals(4, prefixLength(k2, k4));
    }
    
    @Nano
    public static void testPrefixLength3() {
        long k1 = createKey(StringUtil.toBytes("a1"));
        long k2 = createKey(StringUtil.toBytes("a2"));
        Assert.assertEquals(1, prefixLength(k1, k2));
        Assert.assertEquals(1, prefixLength(k2, k1));
    }
    
    @Nano
    public static void testTime() {
        long[] times = new long[]{1, 123, 123456789012345L, 2222222233333L};
        
        for (long time : times) {
            long value = createTime(time);
            long time2 = getTime(value);
            Assert.assertEquals(time, time2);
            Assert.assertEquals(Klong.TYPE_TIME, Klong.getType(value));
        }
    }
    
    @Nano
    public static void testLength() {
        long v = 0;
        v = setHeader(v, TYPE_KEY, 4);        
        Assert.assertEquals(4, getLength(v));       
        
        v = setHeader(v, TYPE_KEY, 1);
        Assert.assertEquals(1, getLength(v));       
        
        v = setHeader(v, TYPE_KEY, 7);
        Assert.assertEquals(7, getLength(v));       
    }
    
    @Nano
    public static void testHeader() {
        long v = createKey("abc");
        Assert.assertEquals(3, getLength(v));
        Assert.assertEquals(TYPE_KEY, getType(v));
        
        v = createKey("a");        
        Assert.assertEquals(1, getLength(v));
        Assert.assertEquals(TYPE_KEY, getType(v));
        
        v = createKey("1234567");        
        Assert.assertEquals(7, getLength(v));
    }
    
    @Nano
    public static void testIntType() {
        long v = createKey("abc");
        Assert.assertEquals(INT_TYPE_KEY, getIntType(v));
        
        v = createTime(1);  
        Assert.assertEquals(INT_TYPE_TIME, getIntType(v));
        
        v = Klong.createDelete();
        Assert.assertEquals(Klong.INT_TYPE_DELETE_BITMAP, Klong.getIntType(v));
    }
    
    @Nano
    public static void testKey1() {
        long v = createKey("aaa");
        String s = getKeyString(v);
        Assert.assertEquals("aaa", s);
    }
    
    @Nano
    public static void testKey2() {
        long v = createKey("z");
        String s = getKeyString(v);
        Assert.assertEquals("z", s);
    }

    @Nano
    public static void testKey3() {   
        long v = createKey("1234567");
        String s = getKeyString(v);
        Assert.assertEquals("1234567", s);
    }
    
    @Nano
    public static void testKey4() {
        byte[] bytes = new byte[]{0, 1, 3, 127, (byte) 200, (byte) 255};
        long v = createKey(bytes, 0, bytes.length);
        byte[] output = new byte[bytes.length];
        int length = getKey(v, output);
        Assert.assertEquals(bytes.length, length);
        Assert.assertArrayEquals(bytes, output);
    }
    
    @Nano
    public static void testKey5() {
        byte[] bytes = new byte[]{3};
        long v = createKey(bytes, 0, bytes.length);
        byte[] output = new byte[1];
        int length = getKey(v, output);
        Assert.assertEquals(1, length);
        Assert.assertArrayEquals(bytes, output);
    }
    
    @Nano
    public static void testSortOrder1() throws UnsupportedEncodingException {
        //
        // Two sort methods compared
        //
        
        String[] stringKeys = new String[]{"gust", "", "bertil", "abc", "frasse", "gustav", "a", "gu"};
        ArrayList<byte[]> keys1 = new ArrayList<byte[]>();
        
        for (String s : stringKeys) {
            keys1.add(s.getBytes("UTF-8"));
        }
        
        keys1.add(new byte[]{'a', 0, 0});
        keys1.add(new byte[]{'a', 0});
        keys1.add(new byte[]{0, 1});
        
        ArrayList<byte[]> keys2 = new ArrayList<byte[]>();
        for (byte[] key : keys1) {
            keys2.add(key);
        }
        
        Comparator<byte[]> comp1 = new ByteArrayComparator();
        
        Comparator<byte[]> comp2 = new Comparator<byte[]>() {
            public int compare(byte[] arr1, byte[] arr2) {
                long v1 = createKey(arr1, 0, arr1.length);
                long v2 = createKey(arr2, 0, arr2.length);
                v1 = getCompareValue(v1);
                v2 = getCompareValue(v2);
                long diff = v1 - v2;
                int result = diff > 0 ? +1 : 0;
                result = diff < 0 ? -1 : result;
                return result;
            }
        };
        
        Collections.sort(keys1, comp1);
        Collections.sort(keys2, comp2);
        
        for (int i = 0; i < keys1.size(); i++) {
            Assert.assertEquals(StringUtil.toString(keys1.get(i)), StringUtil.toString(keys2.get(i)));
        }
    }
    
    @Nano
    public static void testCreateKlongs() {
        byte[] bytes0 = new byte[2];
        bytes0[0] = 0;
        byte[] bytes1 = new byte[2];
        bytes1[0] = 1;
        
        long k0 = Klong.createKey(bytes0, 0, 2);
        long k1 = Klong.createKey(bytes1, 0, 2);
        
        long c0 = Klong.getCompareValue(k0);
        long c1 = Klong.getCompareValue(k1);
        
        Assert.assertTrue(k0 != k1);
        Assert.assertTrue(c1 > c0);
    }
    
    @Nano
    public static void testCreateCompareValueTwoWays() {
        // Two ways to create a compare value.
        Random r = new Random(0);
        int n = 100;
        
        for (int i = 0; i < n; i++) {
            int length = r.nextInt(6) + 1;
            byte[] buffer = new byte[length];
            r.nextBytes(buffer);
            long c1 = Klong.createCompareValue(buffer, 0, length);
            long c2 = Klong.getCompareValue(
                    Klong.createKey(buffer, 0, length));
            Assert.assertEquals("i=" + i, c1, c2);
        }
    }
    
    @Nano
    public static void tDeleteBits() {
        long bit = Math.round(Math.pow(2, 15));
        Assert.assertEquals(bit, Klong.DELETE_BITS[15]);
        
        bit = Math.round(Math.pow(2, 61));
        Assert.assertEquals(bit, Klong.DELETE_BITS[61]);
    }
    
    @Nano
    public static void tDelete1() {
        long k = createDelete();
        k = Klong.delete(k, 5);
        k = Klong.delete(k, 33);
        
        Assert.assertEquals(false, Klong.isDeleted(k, 0));
        Assert.assertEquals(false, Klong.isDeleted(k, 4));
        Assert.assertEquals(true, Klong.isDeleted(k, 5));
        Assert.assertEquals(false, Klong.isDeleted(k, 20));
        Assert.assertEquals(true, Klong.isDeleted(k, 33));
        Assert.assertEquals(false, Klong.isDeleted(k, 34));
        Assert.assertEquals(false, Klong.isDeleted(k, 61));
    }
    
    @Nano
    public static void testIsKey() {
        long k1 = Klong.createKey(new byte[]{1, 2, 3});
        Assert.assertTrue(Klong.isKey(k1));
        long k2 = Klong.createTime(1000);
        Assert.assertFalse(Klong.isKey(k2));
    }
}

/*
== 130522 ==

Removed support for 3-bit "version". Not used.

== 120918 ==

About TIME klongs and time unit. Historical proposal copied from the log:
the current format uses 56 time bits, not the 58 proposed below (see MAX_TIME
and the class comment), for about 228 years at 100 ns resolution.

Deciding on time resolution. We want to be able to store
a time in 58 bits (7 bytes + 2 bits). So, we have 2^58-1 as largest value (~2.88e17).
There are 32e6 s/year.

    Res (ns)    Range (years)
    1             9
    10           90
    100         900
    1000       9000
    
DECISION: Use 100 ns resolution. 

This resolution is high enough for anything I can imaging, allows up to 
10 Mtrans/s with a 900 year range.

MIN time value is 0.
MAX time value is 2^58-1 = 0x03ffffffffffffffL.

*/