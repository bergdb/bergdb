package bergdb.common;

import java.io.UnsupportedEncodingException;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharsetEncoder;
import java.nio.charset.CoderResult;
import java.nio.charset.StandardCharsets;
import java.util.Locale;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * String functions; mostly formatting.
 * Some functions avoid using Java's printf functionality since it
 * did not work well for GCJ. However, GCJ is no longer supported, so this is 
 * a historical reason.
 * 
 * @author Frans Lundberg
 */
public class StringUtil {
    
    /**
     * Formats double to one decimal.
     * Works for GCJ build.
     */
    public static String oneDecimal(double value) {
        // Printf formatting avoided to make it work on GCJ build.        
        double d = Math.round(value * 10.0) / 10.0;
        String s = "" + d;
        int index = s.indexOf('.');
        if (index == -1) {
            s = s + ".0";
        } else if (index == s.length() - 1) {
            s = s + "0";
        }
        
        return s;
    }
    
    @Nano
    public static void testOneDecimal() {
        Assert.assertEquals("1.2", oneDecimal(1.23456));
        Assert.assertEquals("1.3", oneDecimal(1.29999));
        Assert.assertEquals("1.2", oneDecimal(1.16));
        Assert.assertEquals("1.0", oneDecimal(1.01));
    }
    
    /**
     * Formats double to two decimals.
     * Works for GCJ build.
     */
    public static String twoDecimals(double value) {
        // Printf formatting avoided to make it work on GCJ build.        
        double d = Math.round(value * 100.0) / 100.0;
        String s = "" + d;
        int index = s.indexOf('.');
        if (index == -1) {
            s = s + ".00";
        } else if (index == s.length() - 1) {
            s = s + "00";
        } else if (index == s.length() - 2) {
            s = s + "0";
        }
        return s;
    }
    
    @Nano
    public static void testTwoDecimals() {
        Assert.assertEquals("1.23", twoDecimals(1.23456));
        Assert.assertEquals("1.30", twoDecimals(1.29999));
        Assert.assertEquals("1.16", twoDecimals(1.16));
        Assert.assertEquals("20.00", twoDecimals(20));
        Assert.assertEquals("0.06", twoDecimals(0.055));
    }
    
    public static String spaceFill(String s, int totalSize) {
        if (s == null) {
            s = "null";
        }
        
        int toAdd = totalSize - s.length();
        if (toAdd < 0) {
            toAdd = 0;
        }
        
        StringBuilder b = new StringBuilder(s);
        for (int i = 0; i < toAdd; i++) {
            b.append(' ');
        }
        return b.toString();
    }
    
    @Nano
    public static void testSpaceFill() {
        Assert.assertEquals("outer     ", spaceFill("outer", 10));
    }
    
    /**
     * Format double to whole number.
     */
    public static String wholeNumber(double value) {
        return "" + Math.round(value);
    }
    
    @Nano
    public static void testWholeNumber() {
        Assert.assertEquals("2", wholeNumber(1.93456));
        Assert.assertEquals("2", wholeNumber(2.29999));
        Assert.assertEquals("2", wholeNumber(2.00001));
    }

    /**
     * Converts a string to UTF-8 bytes.
     * Note: use core.Keys to convert DB keys.
     * 
     * @throws NullPointerException if s == null.
     */
    public static final byte[] toBytes(String s) {
        //
        // NOTE We could possibly improve performance by using code in
        // http://javasourcecode.org/html/open-source/jdk/jdk-5.0/sun/nio/cs/UTF_8.java.html
        // (Method encodeArrayLoop()).
        //
        
        byte[] result;
        try {
            result = s.getBytes("UTF-8");
        } catch (UnsupportedEncodingException e) {
            throw new Error("Never happens, UTF-8 must be supported be a valid JVM.");
        }
        return result;
    }

    /**
     * The UTF-8 of 's', a string with no lone surrogate, encoded into an array of exactly
     * 'size' bytes, its utf8Size(): no larger buffer on the way, as String.getBytes() may
     * allocate (2026-11-09, bergdb 020-08, section 3; the review of 02995d9: 2 bytes a char for
     * a Latin-1 String with a char above U+007F in JDK 27, 3 in JDK 17, so a String whose
     * UTF-8 fits a Java array could throw OutOfMemoryError). For a String of a size that may
     * pass that: getBytes() is faster.
     *
     * @throws IllegalArgumentException  If 's' has a lone surrogate, or its UTF-8 does not
     *      take exactly 'size' bytes.
     */
    public static byte[] toBytes(String s, int size) {
        byte[] result = new byte[size];
        ByteBuffer out = ByteBuffer.wrap(result);
        CharsetEncoder encoder = StandardCharsets.UTF_8.newEncoder();
        CoderResult r = encoder.encode(CharBuffer.wrap(s), out, true);
        if (r.isUnderflow()) {
            r = encoder.flush(out);
        }
        if (!r.isUnderflow() || out.position() != size) {
            throw new IllegalArgumentException("toBytes: the UTF-8 of the string does not take "
                    + size + " bytes" + (r.isMalformed() || r.isUnmappable() 
                    ? " (a lone surrogate)" : "") + ".");
        }
        return result;
    }

    /**
     * Returns the number of bytes needed to encoding the string in UTF-8 encoding: a long,
     * as a String may need more than 2^31 - 1 bytes, up to 3 a char (2026-11-09, bergdb
     * 020-08, section 3: an int, which wrapped).
     * 
     * @param s
     *            The string, cannot be null.
     * @throws NullPointerException
     *             if s == null.
     */
    public static final long utf8Size(String s) {
        // Inspired by:
        // http://stackoverflow.com/questions/8511490/calculating-length-in-utf-8-of-java-string-without-actually-encoding-it
        //
    
        int length = s.length();
        long count = 0;
        
        for (int i = 0; i < length; i++) {
            char ch = s.charAt(i);
            if (ch <= 0x7f) {
                count++;
            } else if (ch <= 0x07ff) {
                count += 2;
            } else if (Character.isSurrogate(ch)) {
                // 2026-10-21 (bergdb 005-26): as the encoder writes. A pair is 4 bytes; a
                // lone surrogate is '?', 1 byte. Every high surrogate counted 4 and skipped
                // the next char, so the size differed from the bytes written.
                if (Character.isHighSurrogate(ch) && i + 1 < length 
                        && Character.isLowSurrogate(s.charAt(i + 1))) {
                    count += 4;
                    ++i;
                } else {
                    count += 1;
                }
            } else {
                count += 3;
            }
        }
    
        return count;
    }

    @Nano
    public static void testUtf8Size() throws UnsupportedEncodingException {
        String[] strings = { "", "a", "å", "Alban", "Snöslask", "być", "العربية", "\u0000abc",
                "x\uD800", "x\uD800y", "\uDC00a", "\uD83D\uDE00", "a\uD83D\uDE00\uD83D", 
                "\uDC00\uD800", "\uD800\uD800\uDC00" };
            // Last word is "Arabic" in Arabic.
        
        for (int i = 0; i < strings.length; i++) {
            int len = strings[i].getBytes("UTF-8").length;
            Assert.assertEquals(len, utf8Size(strings[i]));
        }
    }

    /**
     * toBytes(s, size): the UTF-8 of well-formed strings, as getBytes() makes it; a size that
     * is not the string's is refused (bergdb 020-08, section 3; the review of 02995d9).
     */
    @Nano
    public static void testToBytesOfAKnownSize() throws UnsupportedEncodingException {
        String[] strings = {"", "a", "\u00e5", "Sn\u00f6slask", "\u00e9" + "a".repeat(300),
                "\u0800\uffff", "a\ud83d\ude00b", "\u0000abc"};
        for (String s : strings) {
            byte[] b = s.getBytes("UTF-8");
            Assert.assertArrayEquals(b, toBytes(s, (int) utf8Size(s)));
            for (int size : new int[] {b.length - 1, b.length + 1}) {
                if (size < 0) {
                    continue;
                }
                try {
                    toBytes(s, size);
                    throw new AssertionError(s + ", size " + size + ": not refused");
                } catch (IllegalArgumentException e) {
                    // refused
                }
            }
        }
    }

    public static boolean isPrintableAscii(byte[] bytes) {
        if (bytes == null) {
            return false;
        }
        
        boolean result = true;
        for (int i = 0; i < bytes.length; i++) {
            byte b = bytes[i];
            if (!(b >= ' ' && b <= '~')) {
                result = false;
                break;
            }
        }
        return result;
    }

    @Nano
    public static void testIsPrintableAscii() throws UnsupportedEncodingException {
        Assert.assertEquals(false, isPrintableAscii(null));
        Assert.assertEquals(false, isPrintableAscii(new byte[]{3}));
        Assert.assertEquals(true, isPrintableAscii(new byte[]{(byte) 'a'}));
        Assert.assertEquals(true, isPrintableAscii("hi there! ;:()/".getBytes("US-ASCII")));
        Assert.assertEquals(false, isPrintableAscii("abc\n".getBytes("US-ASCII")));
    }

    /**
     * True if 's' has a lone surrogate: a char of U+D800 to U+DFFF that is not part of a
     * surrogate pair, a high surrogate followed by a low one. BergDB stores every string as
     * well-formed UTF-8 (RFC 3629), which cannot hold one, so a put refuses such a string
     * (bergdb 021-04); toBytes() would write '?' in its place.
     *
     * @throws NullPointerException if s == null.
     */
    public static boolean hasLoneSurrogate(String s) {
        int length = s.length();
        for (int i = 0; i < length; i++) {
            char c = s.charAt(i);
            if (Character.isSurrogate(c)) {
                if (Character.isHighSurrogate(c) && i + 1 < length
                        && Character.isLowSurrogate(s.charAt(i + 1))) {
                    i++;
                } else {
                    return true;
                }
            }
        }
        return false;
    }

    @Nano
    public static void testHasLoneSurrogate() {
        Assert.assertEquals(false, hasLoneSurrogate(""));
        Assert.assertEquals(false, hasLoneSurrogate("x\uD83D\uDE00y"));
        Assert.assertEquals(true, hasLoneSurrogate("x\uD83D"));
        Assert.assertEquals(true, hasLoneSurrogate("\uDE00x"));
        Assert.assertEquals(true, hasLoneSurrogate("\uD83D\uD83D\uDE00"));
    }

    /** As isWellFormedUtf8(b, 0, b.length). */
    public static boolean isWellFormedUtf8(byte[] b) {
        return isWellFormedUtf8(b, 0, b.length);
    }
    
    /**
     * True if the 'length' bytes of 'b' from 'offset' are well-formed UTF-8 (RFC 3629; the
     * Unicode Standard, chapter 3, table 3-7): Unicode scalar values only, each in its
     * shortest form. Not well-formed: a cut sequence, an overlong form (C0 80), a surrogate
     * (ED A0 80), a value above U+10FFFF, and the bytes C0, C1 and F5 to FF. BergDB stores
     * every string so, and a reader reports the bytes that are not, rather than repair
     * them (bergdb 021-04, 021-06).
     */
    public static boolean isWellFormedUtf8(byte[] b, int offset, int length) {
        final int end = offset + length;
        int i = offset;
        while (i < end) {
            int c = b[i] & 0xff;
            if (c < 0x80) {
                i++;
                continue;
            }
            int more;           // the continuation bytes
            int low = 0x80;     // the first continuation byte's range
            int high = 0xbf;
            if (c >= 0xc2 && c <= 0xdf) {
                more = 1;
            } else if (c == 0xe0) {
                more = 2;
                low = 0xa0;
            } else if (c == 0xed) {
                more = 2;
                high = 0x9f;
            } else if (c >= 0xe1 && c <= 0xef) {
                more = 2;
            } else if (c == 0xf0) {
                more = 3;
                low = 0x90;
            } else if (c == 0xf4) {
                more = 3;
                high = 0x8f;
            } else if (c >= 0xf1 && c <= 0xf3) {
                more = 3;
            } else {
                return false;
            }
            if (end - i <= more) {
                return false;
            }
            int c1 = b[i + 1] & 0xff;
            if (c1 < low || c1 > high) {
                return false;
            }
            for (int k = 2; k <= more; k++) {
                int ck = b[i + k] & 0xff;
                if (ck < 0x80 || ck > 0xbf) {
                    return false;
                }
            }
            i += more + 1;
        }
        return true;
    }
    
    /**
     * isWellFormedUtf8() against the JDK's UTF-8 decoder set to report malformed input:
     * every sequence of 1 and 2 bytes, the edges, and random sequences of up to 8 bytes
     * from bytes near the edges.
     */
    @Nano
    public static void testIsWellFormedUtf8() {
        for (int a = 0; a < 256; a++) {
            checkWellFormed(new byte[] {(byte) a});
            for (int b = 0; b < 256; b++) {
                checkWellFormed(new byte[] {(byte) a, (byte) b});
            }
        }
        int[][] edges = {{0xed, 0x9f, 0xbf}, {0xed, 0xa0, 0x80}, {0xee, 0x80, 0x80}, 
                {0xe0, 0x9f, 0xbf}, {0xe0, 0xa0, 0x80}, {0xc0, 0x80}, {0xc1, 0xbf}, 
                {0xc2, 0x80}, {0xf0, 0x8f, 0xbf, 0xbf}, {0xf0, 0x90, 0x80, 0x80}, 
                {0xf4, 0x8f, 0xbf, 0xbf}, {0xf4, 0x90, 0x80, 0x80}, {0xf5, 0x80, 0x80, 0x80}, 
                {0xef, 0xbf, 0xbd}, {0xe2, 0x82}, {0x61, 0xe2, 0x82, 0xac, 0x62}, {}};
        for (int[] e : edges) {
            byte[] bytes = new byte[e.length];
            for (int i = 0; i < e.length; i++) {
                bytes[i] = (byte) e[i];
            }
            checkWellFormed(bytes);
        }
        Assert.assertEquals(false, isWellFormedUtf8(new byte[] {(byte) 0xed, (byte) 0xa0, 
                (byte) 0x80}));
        Assert.assertEquals(true, isWellFormedUtf8(new byte[] {(byte) 0xef, (byte) 0xbf, 
                (byte) 0xbd}));
        Assert.assertEquals(true, isWellFormedUtf8(new byte[] {'x', 'a', 'b', 'y'}, 1, 2));
        Assert.assertEquals(false, isWellFormedUtf8(new byte[] {'x', (byte) 0xe2, (byte) 0x82, 
                (byte) 0xac}, 0, 3));
        
        int[] near = {0x00, 0x41, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf, 0xc0, 0xc1, 0xc2, 
                0xdf, 0xe0, 0xe1, 0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf3, 0xf4, 0xf5, 0xff};
        java.util.Random random = new java.util.Random(21_06);
        for (int n = 0; n < 50000; n++) {
            byte[] bytes = new byte[1 + random.nextInt(8)];
            for (int i = 0; i < bytes.length; i++) {
                bytes[i] = (byte) near[random.nextInt(near.length)];
            }
            checkWellFormed(bytes);
        }
    }
    
    private static void checkWellFormed(byte[] bytes) {
        boolean jdk;
        try {
            java.nio.charset.StandardCharsets.UTF_8.newDecoder()
                    .onMalformedInput(java.nio.charset.CodingErrorAction.REPORT)
                    .onUnmappableCharacter(java.nio.charset.CodingErrorAction.REPORT)
                    .decode(java.nio.ByteBuffer.wrap(bytes));
            jdk = true;
        } catch (java.nio.charset.CharacterCodingException e) {
            jdk = false;
        }
        if (jdk != isWellFormedUtf8(bytes)) {
            throw new AssertionError("isWellFormedUtf8 " + !jdk + ", the JDK's decoder " + jdk 
                    + ", for " + toHex(bytes));
        }
    }

    /**
     * Converts UTF-8 bytes to a String.
     * If 'bytes' is null, null will be returned.
     */
    public static final String toString(byte[] bytes) {
        // new String(bytes, utf8);   // Cannot be used until Java 1.6.
        // NOTE The behavior of "new String(bytes, "UTF-8")" for illegal bytes is not specified
        // according to Java 5 API.
        // NOTE Consider custom explicit code for bytes-to-utf8-string conversion.
        // We would like to control behavior for bad input data. Also for string-to-bytes, we 
        // would like to know result size without need to allocate space for result.
        
        try {
            return bytes == null ? null : new String(bytes, "UTF-8");
        } catch (UnsupportedEncodingException e) {
            throw new Error("Never happens, UTF-8 must be supported by any JVM.");
        }
    }

    @Nano
    public static void testToString() throws UnsupportedEncodingException {
        byte[] bytes = "hello!".getBytes("UTF-8");
        Assert.assertEquals("hello!", toString(bytes));
    }

    /**
     * Returns a hex string (two lowercase hex chars per byte) given a byte array.
     */
    public static String toHex(byte[] bytes) {
        if (bytes == null) {
            throw new IllegalArgumentException("bytes == null not allowed");
        }
        return StringUtil.toHex(bytes, 0, bytes.length);
    }

    /**
     * Returns a char array (string) with hex chars of given a byte array.
     */
    public static char[] toHexCharArray(byte[] bytes, int offset, int length) {
        char[] hexArray = StringUtil.HEX_ARRAY;
        char[] hexChars = new char[length * 2];
        int v;
        for (int i = 0; i < length; i++) {
            v = bytes[offset + i] & 0xff;
            hexChars[i*2] = hexArray[v/16];
            hexChars[i*2 + 1] = hexArray[v%16];
        }
        return hexChars;
    }

    static final char[] HEX_ARRAY = {
    '0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f'};

    /**
     * Long to hex string.
     */
    public static String toHexString(long l) {
        byte[] bytes = new byte[8];
        Bytes.longToBytesBE(l, bytes, 0);
        return toHex(bytes);
    }

    static int hexCharToInt(char c) {
        int result = -1;
        
        if ((c >= '0') && (c <= '9')) {
            result = c - '0';
        } else if (c >= 'a' && c <= 'f') {
            result = 10 + c - 'a';
        }
        
        return result;
    }

    /**
     * Returns a hex string (two lowercase hex chars per byte) given a byte array.
     */
    public static String toHex(byte[] bytes, int offset, int length) {
        return new String(toHexCharArray(bytes, offset, length));
    }

    /**
     * Converts hex string to bytes.
     * 
     * @throws IllegalArgumentException If argument 'hexString' is not a valid hex string.
     */
    public static byte[] hexStringToBytes(String hexString) {
        if (hexString == null) {
            return null;
        }
        
        if (hexString.length() % 2 != 0) {
            throw new IllegalArgumentException("Bad length of hexString, was: " + hexString);
        }
        
        hexString = hexString.toLowerCase(Locale.US);
        
        int byteCount = hexString.length() / 2;
        byte[] result = new byte[byteCount];
        for (int i = 0; i < byteCount; i++) {
            int c0 = hexCharToInt(hexString.charAt(i * 2));
            int c1 = hexCharToInt(hexString.charAt(i * 2 + 1));
            
            if (c0 == -1 || c1 == -1) {
                throw new IllegalArgumentException("String has an invalid char (not hex char): " 
                        + hexString);
            }
            
            result[i] = (byte) (c0 * 16 + c1);
        }
        
        return result;
    }

    @Nano
    public static void testHex() {
        byte[][] arrays = new byte[][] {
                new byte[0],
                new byte[1],
                null,
                new byte[] {0, 123, (byte) 255, -1}
        };
        
        byte[] b = new byte[256];
        for (int i = 0; i < b.length; i++) {
            b[i] = (byte) i;
        }
        arrays[2] = b;
        
        for (int i = 0; i < arrays.length; i++) {
            String hex = toHex(arrays[i]);
            byte[] back = hexStringToBytes(hex);
            Assert.assertArrayEquals(arrays[i], back);
        }
    }
}
