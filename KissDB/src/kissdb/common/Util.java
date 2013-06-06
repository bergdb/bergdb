package kissdb.common;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.UnsupportedEncodingException;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Random;

import kissdb.nanotest.Assert;
import kissdb.nanotest.T;
import kissdb.nanotest.TestCollector;


/**
 * Static utility methods for general-purpose.
 */
public class Util {
    /**
     * Deletes a single file or a whole directory, if 'file' is a directory.
     * An IOException is thrown if the file(s) cannot be deleted.
     * If 'file' does not exist, or is 'null' this method returns silently.
     * 
     * @param file The file or directory to delete.
     * @throws IOException 
     */
    public static void delete(File file) throws IOException {
        boolean ok;

        if(file == null) {
            return;
        }
        
        if(!file.exists()) {
            return;
        }
        
        if(file.isDirectory()) {
            File[] files;
            
            files = file.listFiles();
            for(int i=0; i<files.length; i++) {
                delete(files[i]);
            }
            ok = file.delete();
            if(!ok) {
                throw new IOException("cannot delete file " + file);
            }
        } else {
            ok = file.delete();
            if(!ok) {
                throw new IOException("cannot delete file " + file);
            }
        }
    }
    
    public static byte[] getTestBytes(int size) {
        byte[] result = new byte[size];
        for (int i = 0; i < size; i++) {
            result[i] = (byte) i;
        }
        return result;
    }
    
    public static byte[] getRandomTestBytes(int size) {
        Random r = new Random(0);
        byte[] result = new byte[size];
        r.nextBytes(result);
        return result;
    }
    
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
    
    @T
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
    
    @T
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
    
    @T
    public static void testSpaceFill() {
        Assert.assertEquals("outer     ", spaceFill("outer", 10));
    }
    
    /**
     * Format double to whole number.
     */
    public static String wholeNumber(double value) {
        return "" + Math.round(value);
    }
    
    @T
    public static void testWholeNumber() {
        Assert.assertEquals("2", wholeNumber(1.93456));
        Assert.assertEquals("2", wholeNumber(2.29999));
        Assert.assertEquals("2", wholeNumber(2.00001));
    }
    
    /**
     * Loads a UTF-8 string from a resource.
     * 
     * @param clazz
     *            Class to used when getting the resource.
     *            clazz.getResourceAsStream is used.
     * @param name
     *            Name of the resource to load.
     * @return The String or 'null' if there is no such resource.
     * @throws IOException
     */
    public static String resourceToString(Class< ? > clazz, String name)
            throws IOException {
        byte[] bytes = resourceToBytes(clazz, name);
        if (bytes == null) {
            return null;
        }
        return new String(bytes, "UTF-8");
    }
    
    /**
     * Loads a resource to a byte array.
     * 
     * @param clazz
     *            Class to used when getting the resource.
     *            clazz.getResourceAsStream is used.
     * @param name
     *            Name of the resource to load.
     * @return The bytes or 'null' if there is no such resource.
     * @throws IOException
     */
    public static byte[] resourceToBytes(Class< ? > clazz, String name)
            throws IOException {
        InputStream in = null;
        ByteArrayOutputStream out = null;

        if (clazz == null) {
            throw new IllegalArgumentException("clazz == null");
        }

        try {
            out = new ByteArrayOutputStream();
            in = clazz.getResourceAsStream(name);
            if (in == null) {
                return null;
            }
            copyStream(in, out);
        } finally {
            if (out != null) {
                try {
                    out.close();
                } catch (IOException e) {}
            }
            
            if (in != null) {
                try {
                    in.close();
                } catch (IOException e) {}
            }
        }

        return out.toByteArray();
    }
    
    /**
     * Copies data from in to out as long as there is still data to read from
     * in. The streams are never closed by this method.
     */
    public static void copyStream(InputStream in, OutputStream out)
            throws IOException {
        byte[] buffer;
        int n;

        buffer = new byte[1024];
        while (true) {
            n = in.read(buffer);
            if (n == -1) {
                break;
            }
            out.write(buffer, 0, n);
        }
    }
    
    /**
     * Converts a string to UTF-8 bytes.
     * Note: use core.Keys to convert DB keys.
     * 
     * @throws NullPointerException if s == null.
     */
    public static final byte[] toBytes(String s) {
        // result = s.getBytes(utf8);      
        // Above code not allowed, since it requires Java 1.6.
        //
        // NOTE We could improve performance by using code in
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
     * @param s  The string, cannot be null.
     * @throws NullPointerException if s == null.
     */
    public static final int utf8Size(String s) {
        // Taken from 
        // http://stackoverflow.com/questions/8511490/calculating-length-in-utf-8-of-java-string-without-actually-encoding-it
        //
        
        assert s != null;
        final int sLength = s.length();
        int count = 0;
        for (int i = 0, len = sLength; i < len; i++) {
          char ch = s.charAt(i);
          if (ch <= 0x7F) {
            count++;
          } else if (ch <= 0x7FF) {
            count += 2;
          } else if (Character.isHighSurrogate(ch)) {
            count += 4;
            ++i;
          } else {
            count += 3;
          }
        }
        return count;
    }
    
    @T
    public static void testUtf8Size() throws UnsupportedEncodingException {
        String[] strings = { "", "a", "å", "Alban", "Snöslask", "być", "العربية", "\u0000abc" };
            // Last word is "Arabic" in Arabic.
        
        for (int i = 0; i < strings.length; i++) {
            int len = strings[i].getBytes("UTF-8").length;
            Assert.assertEquals(len, utf8Size(strings[i]));
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
        //
        
        try {
            return bytes == null ? null : new String(bytes, "UTF-8");
        } catch (UnsupportedEncodingException e) {
            throw new Error("Never happens, UTF-8 must be supported by a JVM.");
        }
    }
    
    /**
     * Converts UTF-8 bytes to a String.
     * If 'bytes' is null, null will be returned.
     * Note: use core.Keys for DB keys.
     */
    public static final String toString(byte[] bytes, int offset, int length) {
        //return bytes == null ? null : new String(bytes, offset, length, utf8);
        // Above code requires Java 1.6.
        
        try {
            return bytes == null ? null : new String(bytes, offset, length, "UTF-8");
        } catch (UnsupportedEncodingException e) {
            throw new Error("Never happens, UTF-8 must be supported by a JVM.");
        }
    }
    
    public static String toString(long[] array) {
        if (array == null) {
            return "null";
        }
        
        StringBuilder b = new StringBuilder();
        b.append('[');
        for (int i = 0; i < array.length; i++) {
            b.append(Long.toString(array[i]));
            if (i != array.length - 1) {
                b.append(' ');
            }
        }
        b.append(']');
        return b.toString();
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
    
    @T
    public static void testIsPrintableAscii() throws UnsupportedEncodingException {
        Assert.assertEquals(false, isPrintableAscii(null));
        Assert.assertEquals(false, isPrintableAscii(new byte[]{3}));
        Assert.assertEquals(true, isPrintableAscii(new byte[]{(byte) 'a'}));
        Assert.assertEquals(true, isPrintableAscii("hi there! ;:()/".getBytes("US-ASCII")));
        Assert.assertEquals(false, isPrintableAscii("abc\n".getBytes("US-ASCII")));
    }
    
    /**
     * Replaces characters in string so result is printable ASCII characters
     * without whitespace.
     */
    public static String toPrintableAscii(String s) {
        char[] chars = s.toCharArray();
        for (int i = 0; i < chars.length; i++) {
            char c = chars[i];
            if (!(c >= ' ' && c <= '~')) {
                chars[i] = c == ' ' ? '_' : '?';
            }
        }
        return new String(chars);
    }
    
    private static final char[] hexArray = {
            '0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f'};
    
    /**
     * Returns a hex string (two lowercase hex chars per byte) given a byte array.
     */
    public static String toHexString(byte[] bytes) {
        if (bytes == null) {
            throw new IllegalArgumentException("bytes == null not allowed");
        }
        return toHexString(bytes, 0, bytes.length);
    }
    
    /**
     * Returns a hex string (two lowercase hex chars per byte) given a byte array.
     */
    public static String toHexString(byte[] bytes, int offset, int length) {
        char[] hexArray = Util.hexArray;
        char[] hexChars = new char[length * 2];
        int v;
        for (int i = 0; i < length; i++) {
            v = bytes[offset + i] & 0xff;
            hexChars[i*2] = hexArray[v/16];
            hexChars[i*2 + 1] = hexArray[v%16];
        }
        return new String(hexChars);
    }

    /**
     * Long to hex string.
     */
    public static String toHexString(long l) {
        byte[] bytes = new byte[8];
        Bytes.longToBytesBE(l, bytes, 0);
        return toHexString(bytes);
    }
    
    private static int hexCharToInt(char c) {
        int result = -1;
        
        if ((c >= '0') && (c <= '9')) {
            result = c - '0';
        } else if (c >= 'a' && c <= 'f') {
            result = 10 + c - 'a';
        }
        
        return result;
    }
    
    /**
     * Converts hex string to bytes.
     * 
     * @throws BadFormatException If argument 'hexString' is not a valid hex string.
     */
    public static byte[] hexStringToBytes(String hexString) {
        if (hexString == null) {
            return null;
        }
        
        if (hexString.length() % 2 != 0) {
            throw new BadFormatException("Bad length of hexString, was: " + hexString);
        }
        
        hexString = hexString.toLowerCase(Locale.US);
        
        int byteCount = hexString.length() / 2;
        byte[] result = new byte[byteCount];
        for (int i = 0; i < byteCount; i++) {
            int c0 = hexCharToInt(hexString.charAt(i * 2));
            int c1 = hexCharToInt(hexString.charAt(i * 2 + 1));
            
            if (c0 == -1 || c1 == -1) {
                throw new BadFormatException("String has an invalid char (not hex char): " 
                        + hexString);
            }
            
            result[i] = (byte) (c0 * 16 + c1);
        }
        
        return result;
    }
    
    @T
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
            String hex = Util.toHexString(arrays[i]);
            byte[] back = Util.hexStringToBytes(hex);
            Assert.assertArrayEquals(arrays[i], back);
        }
    }
    
    /**
     * Returns how much memory is used (1.0 = all, 0.0 = nothing).
     * If max memory is not available (set to Long.MAX_VALUE), 1e9 bytes is assumed to be 
     * max available memory.
     */
    public static double getMemoryUse() {
        Runtime runtime = Runtime.getRuntime();
        long max = runtime.maxMemory();
        if (max == Long.MAX_VALUE) {
            max = 1000L * 1000000;
        }
        long used = runtime.totalMemory() - runtime.freeMemory();
        double result = ((double) used) / max;
        return result;
    }
    
    /**
     * Returns the name of this computer (localhost) or "unknown" if not known.
     */
    public static String getComputerName() {
        String computer = "'unknown'";
        try {
            computer = InetAddress.getLocalHost().getHostName();
        } catch (UnknownHostException e) {
            // empty
        }
        return computer;
    }
    
    /**
     * Concatenates two byte arrays.
     */
    public static byte[] concat(byte[] arr1, byte[] arr2) {
        byte[] result = new byte[arr1.length + arr2.length];
        System.arraycopy(arr1, 0, result, 0, arr1.length);
        System.arraycopy(arr2, 0, result, arr1.length, arr2.length);
        return result;
    }
    
    /**
     * Concatenates two byte arrays.
     */
    public static byte[] concat(byte[] arr1, int offset1, int len1, byte[] arr2, int offset2, int len2) {
        byte[] result = new byte[len1 + len2];
        System.arraycopy(arr1, offset1, result, 0, len1);
        System.arraycopy(arr2, offset2, result, len1, len2);
        return result;
    }
    
    private static boolean runsIkvm = false;
    private static volatile boolean runsIkvmSet = false;
    
    /**
     * Returns true if this software is IKVM-created CIL (.NET) code.
     */
    public static boolean runsIkvm() {
        if (!runsIkvmSet) {
            String name = "java.vm.name";
            String vm = System.getProperty(name);
            if (vm == null) {
                throw new Error("Property " + name + " is mandatory and still missing.");
            }
            runsIkvm = vm.toLowerCase(Locale.US).contains("ikvm");
            runsIkvmSet = true;
        }
        
        return runsIkvm;
    }
    
    private static boolean runsGcj = false;
    private static volatile boolean runsGcjSet = false;
    
    public static boolean runsGcj() {
        if (!runsGcjSet) {
            String name = "java.vm.name";
            String vm = System.getProperty(name);
            if (vm == null) {
                throw new Error("Property " + name + " is mandatory and still missing.");
            }
            runsGcj = vm.toLowerCase(Locale.US).contains("gcj");
            runsGcjSet = true;
        }
        
        return runsGcj;
    }
    
    private static boolean runsAndroid = false;
    private static volatile boolean runsAndroidSet = false;
    
    public static boolean runsAndroid() {
        if (!runsAndroidSet) {
            String name = "java.vm.name";
            String vm = System.getProperty(name);
            if (vm == null) {
                throw new Error("Property " + name + " is mandatory and missing.");
            }
            runsAndroid = vm.toLowerCase(Locale.US).contains("dalvik");
            runsAndroidSet = true;
        }
        
        return runsAndroid;
    }
    
    public static boolean hasOnlyZeros(byte[] array) {
        if (array == null) {
            throw new IllegalArgumentException("array == null not allowed");
        }
        
        for (int i = 0; i < array.length; i++) {
            if (array[i] != 0) {
                return false;
            }
        }
        
        return true;
    }
    
    /**
     * Writes an array of bytes to a file.
     * 
     * @param bytes The bytes to write to file.
     * @param filename The name of the file.
     * @throws IllegalArgumentException if either of the arguments is null or if filename is an 
     * empty string.
     * @throws IOException If there is an IO problem.
     */
    public static void bytesToFile(byte[] bytes, String filename) throws IOException {
        FileOutputStream out;

        if (bytes == null) {
            throw new IllegalArgumentException("bytes == null not allowed");
        }
        if (filename == null) {
            throw new IllegalArgumentException("filename == null not allowed");
        }
        if (filename.length() == 0) {
            throw new IllegalArgumentException(
                    "Empty string not allowed as filename.");
        }

        out = new FileOutputStream(filename);
        try {
            out.write(bytes);
        } finally {
            if (out != null) {
                try {
                    out.close();
                } catch (IOException e) {
                    // silent
                }
            }
        }
    }
    
    public static byte[] fileToBytes(String filename) throws IOException {
        File file = new File(filename);
        if (!file.exists()) {
            throw new IOException("File " + filename + " does not exist.");
        }
        
        if (file.isDirectory()) {
            throw new IOException(filename + " is a directory.");
        }
        
        FileInputStream in = new FileInputStream(new File(filename));
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        copyStream(in, out);
        return out.toByteArray();
    }
    
    @T
    public static void testBytesToFileToBytes(TestCollector c) throws IOException {
        File dir = c.createTempDir();
        File file = new File(dir, "file1.dat");
        byte[] bytes = "hello".getBytes("UTF-8");
        bytesToFile(bytes, file.getPath());
        
        Assert.assertEquals(bytes.length, file.length());
        byte[] bytes2 = fileToBytes(file.getPath());
        
        Assert.assertArrayEquals(bytes, bytes2);
    }
    
    /**
     * Returns 's'; useful for avoiding compiler inlining of a final field.
     */
    public static String identity(String s) {
        return s;
    }
    
    /**
     * Returns 'a'; useful for avoiding compiler inlining of a final field.
     */
    public static int identity(int a) {
        return a;
    }
    
    /**
     * Returns 'a'; useful for avoiding compiler inlining of a final field.
     */
    public static long identity(long a) {
        return a;
    }
    
    /**
     * Returns 'a'; useful for avoiding compiler inlining of a final field.
     */
    public static long[] identity(long[] a) {
        return a;
    }
    
    /**
     * Returns 'a'; useful for avoiding compiler inlining of a final field.
     */
    public static byte[] identity(byte[] a) {
        return a;
    }

    public static boolean areEqual(byte[] a1, byte[] a2) {
        if (a1 == null && a2 == null) {
            return true;
        }
        
        if (a1 == null) {
            return false;
        }
        
        if (a2 == null) {
            return false;
        }
        
        if (a1.length != a2.length) {
            return false;
        }
        
        // Neither is null, and they have the same size.
        
        for (int i = 0; i < a1.length; i++) {
            if (a1[i] != a2[i]) {
                return false;
            }
        }
        
        return true;
    }

    
    @T
    public static void testAreEqual1() {
        Assert.assertTrue(areEqual(null, null));
        Assert.assertFalse(areEqual(null, new byte[0]));
        Assert.assertTrue(areEqual(new byte[0], new byte[0]));
        Assert.assertTrue(areEqual(new byte[1], new byte[1]));
    }
    
    @T
    public static void testAreEqual2() {
        byte[] a1 = new byte[] { 1, 2, 3 };
        byte[] a2 = new byte[] { 1, 2, 3, 4 };
        byte[] a3 = new byte[] { 1, 2, 3 };
        byte[] a4 = new byte[] { 2, 0 };
        
        Assert.assertTrue(areEqual(a1, a3));
        Assert.assertFalse(areEqual(a1, a2));
        Assert.assertFalse(areEqual(a1, a4));
        Assert.assertFalse(areEqual(a3, a2));
        Assert.assertTrue(areEqual(a3, a1));
    }
    
    /**
     * Times the execution of a runnable. Returns number of seconds that elapsed.
     */
    public static double time(Runnable r) {
        long t = System.nanoTime();
        r.run();
        double time = (System.nanoTime() - t) * 1e-9;
        return time;
    }
    
    /**
     * Converts List of Longs to long[]. list == null input results in null returned.
     * Null values in the List are converted to 0.
     */
    public static long[] toArray(List<Long> list) {
        if (list == null) {
            return null;
        }
        
        long[] result = new long[list.size()];
        for (int i = 0; i < list.size(); i++) {
            Long l = list.get(i);
            result[i] = l == null ? 0 : l.longValue();
        }
        return result;
    }
    
    @T
    public static void testToArray0() {
        Assert.assertNull(toArray(null));
    }
    
    @T
    public static void testToArray1() {
        ArrayList<Long> list = new ArrayList<Long>();
        list.add(1L);
        list.add(123L);
        Assert.assertArrayEquals(new long[]{1, 123}, toArray(list));
    }
    
    @T
    public static void testToArray2() {
        ArrayList<Long> list = new ArrayList<Long>();
        list.add(null);
        Assert.assertArrayEquals(new long[]{0}, toArray(list));
    }
    
    /**
     * Returns true if 'prefix' is a prefix of 'bytes'.
     */
    public static boolean isPrefix(byte[] prefix, byte[] bytes) {
        assert prefix != null;
        assert bytes != null;
        
        if (prefix.length > bytes.length) {
            return false;
        }
        
        boolean result = true;
        for (int i = 0; i < prefix.length; i++) {
            if (prefix[i] != bytes[i]) {
                result = false;
                break;
            }
        }
        return result;
    }
    
    @T
    public static void testIsPrefix0() {
        Assert.assertEquals(true, isPrefix(
                new byte[]{'a', 'b'}, 
                new byte[]{'a', 'b', 'c'}));
    }
    
    @T
    public static void testIsPrefix1() {
        Assert.assertEquals(false, isPrefix(
                new byte[]{'a', 'x'}, 
                new byte[]{'a', 'b', 'c'}));
    }
    
    @T
    public static void testIsPrefix2() {
        Assert.assertEquals(true, isPrefix(new byte[]{}, new byte[]{'a', 'b', 'c'}));
        Assert.assertEquals(true, isPrefix(new byte[]{}, new byte[]{}));
        Assert.assertEquals(true, isPrefix(new byte[]{'#'}, new byte[]{'#'}));
        Assert.assertEquals(false, isPrefix(new byte[]{'#'}, new byte[]{}));
        Assert.assertEquals(true, isPrefix(new byte[100], new byte[150]));
    }

    public static boolean isSuffix(byte[] suffix, byte[] bytes) {
        assert suffix != null;
        assert bytes != null;
        
        if (suffix.length > bytes.length) {
            return false;
        }
        
        int index = bytes.length - suffix.length;
        
        boolean result = true;
        for (int i = 0; i < suffix.length; i++) {
            if (suffix[i] != bytes[index++]) {
                result = false;
                break;
            }
        }
        return result;
    }
    
    @T
    public static void testIsSuffix0() {
        Assert.assertEquals(true, isSuffix(new byte[]{'b', 'c'}, new byte[]{'a', 'b', 'c'}));
        Assert.assertEquals(false, isSuffix(new byte[]{'x', 'c'}, new byte[]{'a', 'b', 'c'}));
    }
    
    @T
    public static void testIsSuffix1() {
        Assert.assertEquals(true, isSuffix(new byte[]{}, new byte[]{'a', 'b', 'c'}));
        Assert.assertEquals(true, isSuffix(new byte[]{}, new byte[]{}));
        Assert.assertEquals(true, isSuffix(new byte[]{'a'}, new byte[]{'a'}));
        Assert.assertEquals(false, isSuffix(new byte[]{1, 1}, new byte[]{1}));
        Assert.assertEquals(true, isSuffix(new byte[]{-23, 10}, new byte[]{123, 122, -23, 10}));
    }
    
    /**
     * Returns the index to the last occurrence of byte value 'b' in 'bytes', or -1 if no
     * such byte exists.
     */
    public static int lastIndexOf(byte[] bytes, int b) {
        assert bytes != null;
        int result = -1;
        
        for (int i = bytes.length - 1; i >= 0; i--) {
            if (bytes[i] == b) {
                result = i;
                break;
            }
        }
        return result;
    }
    
    /** Returns a deep copy. */
    public static byte[][] copy(byte[][] bytes) {
        if (bytes == null) {
            return null;
        }
        
        byte[][] copy = new byte[bytes.length][];
        for (int i = 0; i < bytes.length; i++) {
            if (bytes[i] == null) {
                copy[i] = null;
            } else {
                copy[i] = new byte[bytes[i].length];
                System.arraycopy(bytes, 0, copy, 0, bytes.length);
            }
        }
        return copy;
    }
    
    /**
     * Returns true if 'b' byte string is contained in 'bytes'.
     */
    public static boolean contains(byte[] b, byte[] bytes) {
        assert b != null;
        assert bytes != null;
        
        if (b.length > bytes.length) {
            return false;
        }
        
        if (b.length == 0) {
            return true;
        }
        
        int searchSize = bytes.length - b.length;
        boolean result = true;
        for (int start = 0; start < searchSize; start++)  {
            result = true;
            for (int i = 0; i < b.length; i++) {
                if (bytes[start + i] != b[i]) {
                    result = false;
                    break;
                }
            }
            
            if (result == true) {
                break;
            }
        }
        
        return result;
    }
    
    @T
    public static void testContains0() {
        Assert.assertTrue(contains(new byte[]{'a'}, new byte[]{'0', 'a', 'b', 'c'}));
        Assert.assertFalse(contains(new byte[]{'a', 'z'}, new byte[]{'0', 'a', 'b', 'c'}));
    }
    
    @T
    public static void testContains1() {
        Assert.assertTrue(contains(new byte[]{}, new byte[]{'0', 'a', 'b', 'c'}));
        Assert.assertTrue(contains(new byte[]{}, new byte[]{}));
        Assert.assertTrue(contains(new byte[]{'a', 'a'}, new byte[]{'g', 'a', 'b', 'a', 'a', 'b'}));
        Assert.assertFalse(contains(new byte[]{'a', 'q'}, new byte[]{'g', 'a', 'b', 'a', 'a', 'b'}));
        Assert.assertFalse(contains(new byte[]{'a', 'q'}, new byte[]{'a'}));
    }
}
