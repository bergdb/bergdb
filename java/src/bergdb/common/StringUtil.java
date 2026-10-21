package bergdb.common;

import java.io.UnsupportedEncodingException;
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
     * Returns the number of bytes needed to encoding the string in UTF-8 encoding.
     * 
     * @param s
     *            The string, cannot be null.
     * @throws NullPointerException
     *             if s == null.
     */
    public static final int utf8Size(String s) {
        // Inspired by:
        // http://stackoverflow.com/questions/8511490/calculating-length-in-utf-8-of-java-string-without-actually-encoding-it
        //
    
        int length = s.length();
        int count = 0;
        
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
