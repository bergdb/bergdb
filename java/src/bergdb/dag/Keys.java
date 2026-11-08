package bergdb.dag;

import java.io.UnsupportedEncodingException;
import java.nio.charset.StandardCharsets;

import bergdb.common.StringUtil;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * This class has static methods used for handling database keys.
 * They include methods for converting a key between three key formats:
 * ikey, bkey, and skey.
 * This class should always be used to convert a key between these representations.
 * See bergdb.core/doc-files/key-encoding.md.
 * 
 * @author Frans Lundberg
 */
public class Keys {
    
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
        value = value < 0 ? -value : value;
        value &= Long.MAX_VALUE;    // always non-negative, also for Long.MIN_VALUE (005-21)
        assert value >= 0;
        return value;
    }

    /**
     * Converts an ikey to its segmented key representation by first converting
     * the String to bytes and than to segments with the method toSegments(byte[]).
     */
    public static final long[] toSegments(String ikey) {
        return toSegments(toBytes(ikey));
    }

    /**
     * Converts a segmented key to its ikey, as bkey2ikey() does.
     * 
     * @param key  The key segments, null is not allowed.
     * @throws IllegalArgumentException  If the key has no ikey (bkey2ikeyOrNull()).
     */
    public static final String toString(long[] key) {
        return bkey2ikey(toBytes(key));
    }

    /**
     * Converts a bkey to its ikey, as bkey2ikeyOrNull() does. bytes == null is not allowed.
     * 
     * @throws IllegalArgumentException  If the bkey has no ikey.
     */
    public static final String bkey2ikey(byte[] bytes) {
        String ikey = bkey2ikeyOrNull(bytes);
        if (ikey == null) {
            throw new IllegalArgumentException("The bkey has no ikey: it is not the bkey of a "
                    + "string of well-formed UTF-8 (bergdb 021-06), " + StringUtil.toHex(bytes) 
                    + ".");
        }
        return ikey;
    }
    
    /**
     * Converts a bkey to its ikey (key-encoding.md, "Conversion bkey --> ikey"), or returns
     * null if it has none (bergdb 021-06): if it has the byte 0, or 0x31 ('/' + 2, which no
     * ikey's bkey has, as '/' is 1), or if its bytes, each 1 as '/' and every other less 2,
     * are not well-formed UTF-8 (StringUtil.isWellFormedUtf8()). Such a bkey, written with
     * the Core API or by another writer, is reached by its bytes only; its bytes are never
     * repaired, with U+FFFD or otherwise, so two bkeys never give one ikey: the bkey of the
     * ikey returned, toBytes(), is 'bytes'. Until 2026-11-08 the bytes were decoded with
     * U+FFFD in place of each ill-formed sequence: the bkeys of "a" ED A0 80 and "a" EF BF BD
     * (021-04's CK1 and CK2) read as one String, whose bkey is the second's.
     * 
     * @param bytes  The bkey, not null.
     */
    public static final String bkey2ikeyOrNull(byte[] bytes) {
        assert bytes != null;
        byte[] result = new byte[bytes.length];
        for (int i = 0; i < bytes.length; i++) {
            int b = bytes[i] & 0xff;
            if (b == 0 || b == '/' + 2) {
                return null;
            }
            result[i] = b == 1 ? (byte) '/' : (byte) (b - 2);
        }
        if (!StringUtil.isWellFormedUtf8(result)) {
            return null;
        }
        return new String(result, StandardCharsets.UTF_8);
    }
    
    private static final byte[] toStringBytes(byte[] bytes) {
        assert bytes != null;
        
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
        return StringUtil.isPrintableAscii(bytes2);
    }
    
    /**
     * The bkey as text, for messages and debugging only: as bkey2ikey(), but the byte 0
     * shows as '!' and bytes that are not well-formed UTF-8 as U+FFFD. Never a key: two
     * bkeys can show as one (bergdb 021-06).
     */
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
        
        return StringUtil.toString(bytes);
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
        
        return StringUtil.toString(bytes);
    }

    /**
     * Converts ikey to bkey according to specification in 2013-key-encoding.txt.
     * An ikey is Unicode text, stored as well-formed UTF-8 (bergdb 021-04, 021-05).
     *
     * @throws IllegalArgumentException  If s is empty, or has a lone surrogate, a char of
     *      U+D800 to U+DFFF that is not part of a surrogate pair: UTF-8 cannot hold it, and
     *      its encoding would write '?', so that two keys would be one (bergdb 021-05).
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
        
        boolean question = false;       // a '?', maybe written for a lone surrogate
        for (int i = 0; i < bytes.length; i++) {
            byte b = bytes[i];
            if (b == (byte) 0xff || b == (byte) 0xfe) {
                throw new Error("Should not happen, illegal UTF-8 byte value, s = " + s);
            }
            
            if (b == '?') {
                question = true;
            }
            
            if (b == '/') {
                b = 0x01;
            } else {
                b++;
                b++;
            }
            bytes[i] = b;
        }
        
        // The encoder writes '?' for a lone surrogate: without a '?', the key has none, and
        // the chars are scanned only when there is one (bergdb 021-05).
        if (question && StringUtil.hasLoneSurrogate(s)) {
            throw new IllegalArgumentException("The key has a lone surrogate, a char of "
                    + "U+D800 to U+DFFF that is not part of a surrogate pair. BergDB stores "
                    + "every string as well-formed UTF-8, which cannot hold one (bergdb "
                    + "021-04, 021-05).");
        }
        
        return bytes;
    }

    /**
     * Converts a bkey to an skey (segmented key representation).
     * See spec in 2013-key-encoding.txt.
     * Always use this method to create key segments from a byte array key.
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
     * Converts a key in the the segmented form (long[]) to its byte array form (bkey).
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
    
    
    /**
     * Converts a key in the the segmented form (long[]) to its byte array form.
     * Always use this method to convert a segmented key to a byte array.
     */
    public static int getByteSize(long[] segments) {
        // Note, in theory, we could get int overflow here.
        int size = Klong.MAX_SIZE * (segments.length - 1)
                     + Klong.getLength(segments[segments.length - 1]);
        return size;
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
    
    public static final boolean areEqual(long[] key1, long[] key2) {
        return compareKeys(key1, key2) == 0;
    }
    
    /**
     * A simpler version assuming that a Klong compare value is always non-negative. 
     * Currently they are defined to be in the range [0, 2^59] (2012-08).
     * Returns 0 if key1 == key2, returns -1 if key1 < key2, and +1 if key1 > key2.
     */
    public static final int compareKeys(long[] key1, long[] key2) {
        //
        // arr1 < arr2  --> neg
        // arr1 == arr2 --> 0
        // arr1 > arr2  --> pos
        //
        
        int result = 0;
        int length = Math.min(key1.length, key2.length);
        
        for (int i = 0; i < length; i++) {
            result = compareLongs(key1[i], key2[i]);
            if (result != 0) {
                break;
            }
        }
        
        if (result == 0 && key1.length != key2.length) {
            result = key1.length < key2.length ? -1 : +1;
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
    
    private static int compareLongs(long n1, long n2) {
        return n1 == n2 ? 0 : n1 < n2 ? -1 : +1;
    }
    
    private static int compareUnsignedLongs(long n1, long n2) {
        // Yes, a bit hairy, see bottom of source file.
        return n1 == n2 ? 0 : ((n1 < n2) ^ ((n1 < 0) != (n2 < 0)) ? -1 : +1);
    }
    
    // ======== Testing ========
    
    @Nano
    public static void testByteSize0() {
        int[] sizes = new int[]{0, 1, 6, 7, 8, 40, 27, 28, 29};
        
        for (int i = 0; i < sizes.length; i++) {
            byte[] bytes = new byte[sizes[i]];
            long[] segments = Keys.toSegments(bytes);
            Assert.assertEquals(sizes[i], Keys.getByteSize(segments));
        }
    }
    
    @Nano
    public static void testConversion0() {
        String[] strings = new String[] { "a", "dir/f1.txt", " ", "Stange\n\r  next line" };
        
        for (int i = 0; i < strings.length; i++) {
            long[] segments = toSegments(strings[i]);
            Assert.assertEquals(strings[i], toString(segments));
        }
    }
    
    @Nano
    public static void testConversion1() {
        Exception ex = null;
        
        try {
            toSegments("");
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    /** bergdb 021-05: a lone surrogate is refused; it was written as '?', the key "a?". */
    @Nano
    public static void testLoneSurrogate() {
        String[] refused = {"a\uD800", "\uDC00", "?\uD83D", "\uDE00\uD83D\uDE00"};
        for (String s : refused) {
            try {
                toBytes(s);
                throw new AssertionError("no exception");
            } catch (IllegalArgumentException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("lone surrogate"));
            }
        }
        Assert.assertEquals("a?\uD83D\uDE00", bkey2ikey(toBytes("a?\uD83D\uDE00")));
    }
    
    /**
     * bergdb 021-06: a bkey without an ikey. CK1 of 021-04, an ikey with ED A0 80 (U+D800 in
     * WTF-8, from the C clone), was read as CK2, the ikey with EF BF BD (U+FFFD): two keys as
     * one String, and that String's bkey was CK2's. Now CK1 has no ikey, and so has a bkey
     * with an overlong form, a cut sequence, a value above U+10FFFF, the byte 0 or 0x31 ('/' +
     * 2, which no ikey gives: '/' is 1), 0xFE or 0xFF.
     */
    @Nano
    public static void testBkeyWithoutIkey() {
        byte[] ck1 = bkey("/dd/-a", 0xef, 0xa2, 0x82);
        byte[] ck2 = toBytes("/dd/-a\uFFFD");
        Assert.assertArrayEquals(bkey("/dd/-a", 0xf1, 0xc1, 0xbf), ck2);
        Assert.assertEquals("/dd/-a\uFFFD", bkey2ikey(ck2));
        Assert.assertEquals("/dd/-a\uFFFD", bkey2ikeyOrNull(ck2));
        Assert.assertEquals("/dd/-a\uFFFD", Keys.toString(toSegments(ck2)));
        
        byte[][] none = {ck1, bkey("/dd/-a", 0xc2, 0x82), bkey("/dd/-a", 0xe4, 0x84), 
                bkey("/dd/-a", 0xf6, 0x92, 0x82, 0x82), bkey("/dd/-a", 0x00), 
                bkey("/dd/-a", 0x31), bkey("/dd/-a", 0xfe), bkey("/dd/-a", 0xff), 
                bkey("", 0xe4, 0x84, 0x63)};
        for (byte[] b : none) {
            Assert.assertNull(bkey2ikeyOrNull(b));
            for (int k = 0; k < 2; k++) {
                IllegalArgumentException ex = null;
                try {
                    if (k == 0) {
                        bkey2ikey(b);
                    } else {
                        Keys.toString(toSegments(b));
                    }
                } catch (IllegalArgumentException e) {
                    ex = e;
                }
                Assert.assertTrue("no exception for " + StringUtil.toHex(b), ex != null);
                Assert.assertTrue(ex.getMessage(), ex.getMessage().contains("no ikey"));
            }
        }
    }
    
    /**
     * bergdb 021-06: two bkeys never give one ikey. Random bkeys of bytes near UTF-8's
     * edges: each has no ikey, or its ikey's bkey is itself.
     */
    @Nano
    public static void testBkeyIkeyRoundTrip() {
        int[] near = {0x00, 0x01, 0x02, 0x03, 0x31, 0x33, 0x63, 0x81, 0x82, 0x91, 0x92, 0xa1, 
                0xa2, 0xc1, 0xc2, 0xc3, 0xc4, 0xe1, 0xe2, 0xe3, 0xee, 0xef, 0xf0, 0xf1, 0xf2, 
                0xf3, 0xf5, 0xf6, 0xf7, 0xfe, 0xff};
        java.util.Random random = new java.util.Random(21_06);
        int withIkey = 0;
        for (int n = 0; n < 100000; n++) {
            byte[] b = new byte[1 + random.nextInt(6)];
            for (int i = 0; i < b.length; i++) {
                b[i] = (byte) near[random.nextInt(near.length)];
            }
            String ikey = bkey2ikeyOrNull(b);
            if (ikey != null) {
                withIkey++;
                Assert.assertArrayEquals(StringUtil.toHex(b), b, toBytes(ikey));
            }
        }
        Assert.assertTrue("only " + withIkey + " bkeys with an ikey", withIkey > 2000);
    }
    
    /** The bkey of ikey, then the given bytes. */
    private static byte[] bkey(String ikey, int... more) {
        byte[] start = ikey.isEmpty() ? new byte[0] : toBytes(ikey);
        byte[] result = java.util.Arrays.copyOf(start, start.length + more.length);
        for (int i = 0; i < more.length; i++) {
            result[start.length + i] = (byte) more[i];
        }
        return result;
    }
    
    @Nano
    public static void testLongs() {
        Assert.assertEquals(true, compareUnsignedLongs(3, 1) > 0);
        Assert.assertEquals(true, compareUnsignedLongs(111222333444L, 111222333444L) == 0);
        Assert.assertEquals(true, compareUnsignedLongs(-1, -1) == 0);
        Assert.assertEquals(true, compareUnsignedLongs(0, 0) == 0);
        Assert.assertEquals(true, compareUnsignedLongs(-1, 111222333444L) > 0);
        Assert.assertEquals(true, compareUnsignedLongs(111222333444L, -1) < 0);
        Assert.assertEquals(true, compareUnsignedLongs(1, 44) < 0);
    }
    
    @Nano
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
    
    @Nano
    public static void testPrefix1() {
        long[] k1 = Keys.toSegments("dir/customers/");
        long[] k2 = Keys.toSegments("dir/customers/anna");
        
        Assert.assertTrue(Keys.isPrefix(k1, k2));
        Assert.assertFalse(Keys.isPrefix(k2, k1));
    }
    
    @Nano
    public static void testPrefix2() {
        long[] k1 = Keys.toSegments("dir/customers/");
        long[] k2 = Keys.toSegments("dir/customers/anna");
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
