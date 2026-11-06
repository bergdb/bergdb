package bergdb.common;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.GregorianCalendar;
import java.util.List;
import java.util.Locale;
import java.util.TimeZone;
import java.util.function.Consumer;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;

/**
 * Static utility methods for general-purpose.
 * 
 * @author Frans Lundberg
 */
public class Util {

    /** No reason to create an instance. */
    private Util() {
    }
    
    /**
     * For tests (2026-11-06, bergdb 019-39): called with each thread that start() starts,
     * before its start(), and may throw, as start() itself may (an OutOfMemoryError). null,
     * the default, does nothing.
     */
    public static volatile Consumer<Thread> testHookStart = null;
    
    /** Starts 't', after testHookStart (bergdb 019-39). */
    public static void start(Thread t) {
        Consumer<Thread> hook = testHookStart;
        if (hook != null) hook.accept(t);
        t.start();
    }
    
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
    
    @Nano
    private static void testDelete(TestEnvironment env) throws IOException {
        File dir = env.createTempDir();
        File dir2 = new File(dir, "dir2");
        dir2.mkdir();
        File file = new File(dir2, "file1");
        FileOutputStream out = new FileOutputStream(file);
        out.write(1);
        out.close();
        
        Util.delete(dir2);
        Assert.assertFalse(file.exists());
    }
    
    public static byte[] getTestBytes(int size) {
        byte[] result = new byte[size];
        for (int i = 0; i < size; i++) {
            result[i] = (byte) i;
        }
        return result;
    }
    
    /**
     * Copies data from in to out as long as there is still data to read from
     * in. The streams are not closed by this method.
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
    
    /**
     * Refuses a range that is not in 'array': a negative 'offset' or 'length', or an
     * 'offset' + 'length' greater than array.length, with IllegalArgumentException. For the
     * streams' read() and append(), whose Javadoc in AppendOnlyStream promises it, before
     * anything changes (2026-11-05, bergdb 019-02).
     */
    public static void checkRange(byte[] array, int offset, int length) {
        if (offset < 0 || length < 0 || length > array.length - offset) {
            throw new IllegalArgumentException("bad offset or length, offset " + offset
                    + ", length " + length + ", array length " + array.length);
        }
    }
    
    /** Bergdb 019-02: the ranges that checkRange() refuses, and those it accepts. */
    @Nano private static void testCheckRange() {
        byte[] a = new byte[4];
        int[][] refused = {{0, -1}, {-1, 0}, {-1, 2}, {0, 5}, {1, 4}, {5, 0},
                {2, Integer.MAX_VALUE}, {Integer.MAX_VALUE, 1}};
        for (int[] r : refused) {
            try {
                checkRange(a, r[0], r[1]);
                throw new AssertionError("accepted offset " + r[0] + ", length " + r[1]);
            } catch (IllegalArgumentException e) {
                // Expected.
            }
        }
        for (int[] r : new int[][] {{0, 0}, {0, 4}, {1, 3}, {4, 0}}) {
            checkRange(a, r[0], r[1]);
        }
    }
    
    public static byte[] subarray(byte[] arr, int offset, int size) {
        byte[] result = new byte[size];
        System.arraycopy(arr, offset, result, 0, size);
        return result;
    }
    
    @Nano private static void testSubarray1() {
        byte[] bytes = new byte[]{1, 2, 3, 4, 5};
        Assert.assertArrayEquals(new byte[]{2, 3}, subarray(bytes, 1, 2));
    }
    
    @Nano private static void testSubarray2() {
        byte[] bytes = new byte[]{1, 2, 3, 4, 5};
        Assert.assertArrayEquals(new byte[]{}, subarray(bytes, 1, 0));
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
    
    @Nano
    public static void testBytesToFileToBytes(TestEnvironment c) throws IOException {
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

    
    @Nano
    public static void testAreEqual1() {
        Assert.assertTrue(areEqual(null, null));
        Assert.assertFalse(areEqual(null, new byte[0]));
        Assert.assertTrue(areEqual(new byte[0], new byte[0]));
        Assert.assertTrue(areEqual(new byte[1], new byte[1]));
    }
    
    @Nano
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
    
    @Nano
    public static void testToArray0() {
        Assert.assertNull(toArray(null));
    }
    
    @Nano
    public static void testToArray1() {
        ArrayList<Long> list = new ArrayList<Long>();
        list.add(1L);
        list.add(123L);
        Assert.assertArrayEquals(new long[]{1, 123}, toArray(list));
    }
    
    @Nano
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
    
    @Nano
    public static void testIsPrefix0() {
        Assert.assertEquals(true, isPrefix(
                new byte[]{'a', 'b'}, 
                new byte[]{'a', 'b', 'c'}));
    }
    
    @Nano
    public static void testIsPrefix1() {
        Assert.assertEquals(false, isPrefix(
                new byte[]{'a', 'x'}, 
                new byte[]{'a', 'b', 'c'}));
    }
    
    @Nano
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
    
    @Nano
    public static void testIsSuffix0() {
        Assert.assertEquals(true, isSuffix(new byte[]{'b', 'c'}, new byte[]{'a', 'b', 'c'}));
        Assert.assertEquals(false, isSuffix(new byte[]{'x', 'c'}, new byte[]{'a', 'b', 'c'}));
    }
    
    @Nano
    public static void testIsSuffix1() {
        Assert.assertEquals(true, isSuffix(new byte[]{}, new byte[]{'a', 'b', 'c'}));
        Assert.assertEquals(true, isSuffix(new byte[]{}, new byte[]{}));
        Assert.assertEquals(true, isSuffix(new byte[]{'a'}, new byte[]{'a'}));
        Assert.assertEquals(false, isSuffix(new byte[]{1, 1}, new byte[]{1}));
        Assert.assertEquals(true, isSuffix(new byte[]{-23, 10}, new byte[]{123, 122, -23, 10}));
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
    
    @Nano
    public static void testContains0() {
        Assert.assertTrue(contains(new byte[]{'a'}, new byte[]{'0', 'a', 'b', 'c'}));
        Assert.assertFalse(contains(new byte[]{'a', 'z'}, new byte[]{'0', 'a', 'b', 'c'}));
    }
    
    @Nano
    public static void testContains1() {
        Assert.assertTrue(contains(new byte[]{}, new byte[]{'0', 'a', 'b', 'c'}));
        Assert.assertTrue(contains(new byte[]{}, new byte[]{}));
        Assert.assertTrue(contains(new byte[]{'a', 'a'}, new byte[]{'g', 'a', 'b', 'a', 'a', 'b'}));
        Assert.assertFalse(contains(new byte[]{'a', 'q'}, new byte[]{'g', 'a', 'b', 'a', 'a', 'b'}));
        Assert.assertFalse(contains(new byte[]{'a', 'q'}, new byte[]{'a'}));
    }
    
    /**
     * Returns milliseconds since Epoch for a certain UTC date/time.
     * 
     * @param year    The year.
     * @param month   The month, January = 1
     * @param date    The date of the month.
     * @param hour    The hour (0-23)
     * @param min     The minutes (0-59)
     * @param sec     The second (0-29)
     * @param millis  Milliseconds of the second (0-999).
     * @return The number of milliseconds since Epoch (1 Jan 1970 UTC).
     */
    public static long getMillisSinceEpoch(TimeZone zone, 
            int year, int month, int date, 
            int hour, int min, int sec, int millis) {
        GregorianCalendar c = new GregorianCalendar(zone, Locale.US);
        c.setTimeInMillis(0);
        c.set(Calendar.YEAR, year);
        c.set(Calendar.MONTH, month - 1);
        c.set(Calendar.DATE, date);
        c.set(Calendar.HOUR_OF_DAY, hour);
        c.set(Calendar.MINUTE, min);
        c.set(Calendar.SECOND, sec);
        c.set(Calendar.MILLISECOND, millis);
        return c.getTimeInMillis();
    }
    
    /**
     * Removes the first string in a String array.
     * If in is null or the empty array, in itself is returned.
     */
    public static String[] removeFirst(String[] in) {
        if (in == null || in.length == 0) {
            return in;
        }

        String[] out = new String[in.length - 1];
        for (int i = 0; i < out.length; i++) {
            out[i] = in[i + 1];
        }
        return out;
    }
    
    /**
     * Returns the hostname of the computer or "unknown" if unknown.
     */
    public static String hostname() {
        String name;
        try {
            name = InetAddress.getLocalHost().getHostName();
        } catch (UnknownHostException e) {
            name = "unknown";
        }
        return name;
    }

    
    private static SimpleDateFormat compactDateFormat = new SimpleDateFormat("yyMMdd");
    private static SimpleDateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd");
    
    /**
     * Returns the current date formatted as "YYYY-MM-DD".
     * The timezone of the default locale is used.
     */
    public static String today() {
        long now = System.currentTimeMillis();
        return dateFormat.format(new Date(now));
    }

    private static SimpleDateFormat dateAndTimeFormat = new SimpleDateFormat("yyMMdd HH:mm");
    
    /**
     * Returns current date and time formatted as yyMMdd HH:mm.
     * The timezone of the default locale is used.
     */
    public static String dateAndTime() {
        long now = System.currentTimeMillis();
        return dateAndTimeFormat.format(new Date(now));
    }
    
    /**
     * Returns a one-line description of the JVM running this code.
     */
    public static String jvm() {
        String jvm = System.getProperty("java.vm.name") + " " 
                + System.getProperty("java.vm.version");
        String javaVersion = "java " + System.getProperty("java.version");
        
        return jvm + ", " + javaVersion;
    }
    
    public static void main(String[] args) {
        System.out.println(dateAndTime());
    }
    
    /**
     * Writes bytes to new file.
     */
    public static void bytesToFile(byte[] bytes, File file) throws IOException {
        FileOutputStream out = new FileOutputStream(file);
        
        try {
            out.write(bytes);
        } finally {
            out.close();
        }
    }
}
