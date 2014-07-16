package bergdb.common;

import java.io.UnsupportedEncodingException;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.util.Random;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;


/**
 * Utility class for storing primitive types: long, double, int, short, ushort in byte arrays.
 * 
 * @author Frans Lundberg
 */
public class Bytes {
    //
    // My testing (bergdb.common.perf.BytesToLong) show that this class is faster
    // to use instead of Java's ByteBuffer.
    //
    
    // --- long ----
    
    /**
     * Creates a long from an array of bytes. Little-endian-first byte order is
     * assumed.
     */
    public static final long bytesToLongLE(byte[] arr, int offset) {
        int i = offset;
        long result = (arr[i++] & 0x000000ffL);
        result |= (arr[i++] & 0x000000ffL) << 8;
        result |= (arr[i++] & 0x000000ffL) << 16;
        result |= (arr[i++] & 0x000000ffL) << 24;
        result |= (arr[i++] & 0x000000ffL) << 32;
        result |= (arr[i++] & 0x000000ffL) << 40;
        result |= (arr[i++] & 0x000000ffL) << 48;
        result |= (arr[i]   & 0x000000ffL) << 56;
        return result;
    }
    
    /**
     * Writes a long to a byte array. Little endian first byte order is used.
     */
    public static final void longToBytesLE(final long value, final byte[] arr, int offset) {
        // 121213 Frans:
        // Why is longToBytesXX 10 times slower than bytesToLongXX?
        // This method runs in 52 ns on Rose, bytesToLongLE runs in 6 ns.
        // 6 ns almost seems suspiciously fast, however. At 1.66 GHz, its only 10 cycles.
        //
        
        int i = offset;
        arr[i++] = (byte) value;
        arr[i++] = (byte) (value >>> 8);
        arr[i++] = (byte) (value >>> 16);
        arr[i++] = (byte) (value >>> 24);
        arr[i++] = (byte) (value >>> 32);
        arr[i++] = (byte) (value >>> 40);
        arr[i++] = (byte) (value >>> 48);
        arr[i]   = (byte) (value >>> 56);
    }

    /**
     * Creates a long from an array of bytes. Big-endian-first byte order is
     * assumed.
     */
    public static final long bytesToLongBE(byte[] arr, int offset) {
        int i = offset;
        long result = (arr[i++] & 0x000000ffL) << 56;
        result |= (arr[i++] & 0x000000ffL) << 48;
        result |= (arr[i++] & 0x000000ffL) << 40;
        result |= (arr[i++] & 0x000000ffL) << 32;
        result |= (arr[i++] & 0x000000ffL) << 24;
        result |= (arr[i++] & 0x000000ffL) << 16;
        result |= (arr[i++] & 0x000000ffL) << 8;
        result |= (arr[i++] & 0x000000ffL);
        return result;
    }
    
    /**
     * Writes a long to a byte array. Big-endian byte order is used.
     */
    public static final void longToBytesBE(final long v, final byte[] bytes, int offset) {
        // Inspired by Sun's implementation of java.io.DataInputStream.
        int i = offset;
        bytes[i++] = (byte)(v >>> 56);
        bytes[i++] = (byte)(v >>> 48);
        bytes[i++] = (byte)(v >>> 40);
        bytes[i++] = (byte)(v >>> 32);
        bytes[i++] = (byte)(v >>> 24);
        bytes[i++] = (byte)(v >>> 16);
        bytes[i++] = (byte)(v >>>  8);
        bytes[i] = (byte) v;
    }
    
    // ---- float ----
    
    public static void floatToBytesLE(final float v, final byte[] bytes, final int offset) {
        Bytes.intToBytesLE(Float.floatToRawIntBits(v), bytes, offset);
    }
    
    public static float bytesToFloatLE(byte[] arr, int offset) {
        int myInt = Bytes.bytesToIntLE(arr, offset);
        return Float.intBitsToFloat(myInt);
    }
    
    @T
    public static void testFloatLE() {
        float[] values = new float[] {1.0f, 0.0f, Float.MIN_VALUE, Float.MAX_VALUE, Float.NaN, 
                123.45f, -0.0012f};
        byte[] array = new byte[10 + values.length];
        
        for (int i = 0; i < values.length; i++) {
            Bytes.floatToBytesLE(values[i], array, i);
            float d = Bytes.bytesToFloatLE(array, i);
            Assert.assertEquals(values[i], d);
        }
    }
    
    // ---- double ----
    
    public static void doubleToBytesLE(final double v, final byte[] bytes, final int offset) {
        Bytes.longToBytesLE(Double.doubleToRawLongBits(v), bytes, offset);
    }
    
    public static double bytesToDoubleLE(byte[] arr, int offset) {
        long myLong = Bytes.bytesToLongLE(arr, offset);
        return Double.longBitsToDouble(myLong);
    }
    
    @T
    public static void testDoubleLE() {
        double[] values = new double[] {1.0, 0.0, Double.MIN_VALUE, Double.MAX_VALUE, Double.NaN, 
                123.45, -0.0012};
        byte[] array = new byte[10 + values.length];
        
        for (int i = 0; i < values.length; i++) {
            Bytes.doubleToBytesLE(values[i], array, i);
            double d = Bytes.bytesToDoubleLE(array, i);
            Assert.assertEquals(values[i], d);
        }
    }
    
    // ---- short ----
    
    /**
     * Creates a short from an array of bytes. Little-endian-first byte order is
     * assumed.
     */
    public static final short bytesToShortLE(final byte[] arr, int offset) {
        int off = offset;
        int result = (arr[off++] & 0x00ff);
        result |= (arr[off++] & 0x00ff) << 8;
        return (short) result;
    }
    
    
    public static final void shortToBytesLE(final long value, final byte[] arr, int offset) {
        int i = offset;
        arr[i++] = (byte) value;
        arr[i++] = (byte) (value >>> 8);
    }
    
    @T
    public static void testShortLE() {
        short[] shorts = new short[] {0, Short.MIN_VALUE, Short.MAX_VALUE, 12345, -1, -32000, 32000};
        byte[] array = new byte[10 + shorts.length];
        
        for (int i = 0; i < shorts.length; i++) {
            short s = shorts[i];
            Bytes.shortToBytesLE(s, array, i);
            short s2 = Bytes.bytesToShortLE(array, i);
            Assert.assertEquals(s, s2);
        }
    }
    
    // shortBE not implemented
    
    // ---- ushort ----
    // Unsigned short, value range: [0, 2^16-1].
    
    public static final int bytesToUShortLE(byte[] arr, int offset) {
        int result = 0;
        int b0 = arr[offset];
        int b1 = arr[offset + 1];

        if (b0 < 0) {
            b0 += 256;
        }
        if (b1 < 0) {
            b1 += 256;
        }
        result = b0 + 256 * b1;
        return result;
    }

    /**
     * Writes an unsigned short integer (0..2^16-1) to a byte array using little
     * endian first byte order.
     * 
     * @param value
     *            Integer value, must be between 0 and 2^16-1 (65536-1)
     * @throws IllegalArgumentException
     *             if value is not in the valid range.
     */
    public static final void ushortToBytesLE(int value, byte[] arr, int offset) 
            throws IllegalArgumentException {
        if (value < 0 || value >= 65536) {
            throw new IllegalArgumentException("bad value, " + value);
        }
        arr[offset] = (byte) (value % 256);
        arr[offset + 1] = (byte) (value / 256);
    }
    
    // ---- int ----

    /**
     * Creates an integer from a byte array. Little endian byte order is used.
     */
    public static final int bytesToIntLE(byte[] arr, int offset) {
        int i = offset;
        int result = (arr[i++] & 0x00ff);
        result |= (arr[i++] & 0x00ff) << 8;
        result |= (arr[i++] & 0x00ff) << 16;
        result |= (arr[i] & 0x00ff) << 24;
        return result;
    }
    
    /**
     * Converts an int to four bytes in a byte array. Little endian
     * first byte order is used.
     */
    public static final void intToBytesLE(int value, byte[] arr, int offset) {
        arr[offset++] = (byte) value;
        arr[offset++] = (byte) (value >>> 8);
        arr[offset++] = (byte) (value >>> 16);
        arr[offset] = (byte) (value >>> 24);
    }

    /**
     * Creates an integer from a byte array. Big endian byte order is used.
     */
    public static final int bytesToIntBE(byte[] arr, int offset) {
        int off = offset;
        int result = (arr[off++] & 0x00ff) << 24;
        result |= (arr[off++] & 0x00ff) << 16;
        result |= (arr[off++] & 0x00ff) << 8;
        result |= (arr[off++] & 0x00ff);
        return result;
    }

    /**
     * Converts a non-negative int to four bytes in a byte array. Little endian
     * first byte order is used.
     */
    public static void intToBytesBE(int v, byte[] arr, int offset) {
        // According to the Java VM specification
        // the (byte) cast simply discards all but the
        // least significant 8 bits.*/
        
        int off = offset;
        arr[off++] = (byte)(v >>> 24);
        arr[off++] = (byte)(v >>> 16);
        arr[off++] = (byte)(v >>>  8);
        arr[off] = (byte) v;
    }
    
    // ---- string ----
    // Not complete. Do we need it?
    
    public static void stringToBytes(String s, byte[] arr, int offset) {
        byte[] bytes;
        try {
            bytes = s.getBytes("UTF-8");
        } catch (UnsupportedEncodingException e) {
            throw new Error("UTF-8 should always be available.");
        }
        System.arraycopy(bytes, 0, arr, offset, bytes.length);
    }

    // ---- Testing ----
    

    
    @T
    public static void testLongToBytesBE() {
        long long1;
        byte[] bytes1 = new byte[12];
        byte[] bytes2 = new byte[12];
        ByteBuffer buffer = ByteBuffer.wrap(bytes2, 3, 8);

        buffer.order(ByteOrder.BIG_ENDIAN);
        long1 = (long) ((Math.random() * 2.0 - 1.0) * Long.MAX_VALUE);
        Bytes.longToBytesBE(long1, bytes1, 3);
        buffer.putLong(3, long1);
        for (int i = 0; i < 12; i++) {
            if (bytes1[i] != bytes2[i]) {
                throw new RuntimeException("i=" + i);
            }
        }
    }

    @T
    public static void testLongToBytesLE() {
        long long1;
        byte[] bytes1 = new byte[12];
        byte[] bytes2 = new byte[12];
        ByteBuffer buffer = ByteBuffer.wrap(bytes2, 3, 8);

        buffer.order(ByteOrder.LITTLE_ENDIAN);
        long1 = (long) ((Math.random() * 2.0 - 1.0) * Long.MAX_VALUE);
        Bytes.longToBytesLE(long1, bytes1, 3);
        buffer.putLong(3, long1);
        for (int i = 0; i < 12; i++) {
            if (bytes1[i] != bytes2[i]) {
                throw new RuntimeException("i=" + i);
            }
        }
    }

    @T
    public static void testLongBE() {
        long long3 = Long.MAX_VALUE - 1000;
        long long4 = 0;
        byte[] temp = new byte[16];
        Bytes.longToBytesBE(28000000L, temp, 0);
        Bytes.longToBytesBE(long3, temp, 8);
        long4 = Bytes.bytesToLongBE(temp, 8);

        if (long3 != long4) {
            throw new RuntimeException("long3 != long4, " + long3 + " != "
                    + long4);
        }
    }
    
    @T
    public static void testLongBE2() {
        long long1, long2;
        byte[] bytes = new byte[12];

        for (int i = 0; i < 10; i++) {
            long1 = (long) ((Math.random() * 2.0 - 1.0) * Long.MAX_VALUE);
            Bytes.longToBytesBE(long1, bytes, 3);
            long2 = Bytes.bytesToLongBE(bytes, 3);
            if (long1 != long2) {
                throw new RuntimeException(long1 + " != " + long2 + ", i=" + i);
            }
        }
    }

    @T
    public static void testLongLE() {
        long long1, long2;
        byte[] bytes = new byte[12];

        for (int i = 0; i < 10; i++) {
            long1 = (long) ((Math.random() * 2.0 - 1.0) * Long.MAX_VALUE);
            Bytes.longToBytesLE(long1, bytes, 3);
            long2 = Bytes.bytesToLongLE(bytes, 3);
            if (long1 != long2) {
                throw new RuntimeException(long1 + " != " + long2 + ", i=" + i);
            }
        }
    }
    
    @T
    public static void testLongLE2() {
        long long1, long2;
        byte[] bytes = new byte[110];
        Random random = new Random(0);
        int offset;
        
        for (int i = 0; i < 100; i++) {
            offset = (i % (bytes.length - 10));
            long1 = random.nextLong();
            Bytes.longToBytesLE(long1, bytes, offset);
            long2 = Bytes.bytesToLongLE(bytes, offset);
            if (long1 != long2) {
                throw new RuntimeException(long1 + " != " + long2 + ", i=" + i);
            }
        }
    }
    
    @T
    public static void testIntLE() {
        Random r = new Random(0);
        byte[] buffer = new byte[110];
        
        for (int i = 0; i < 100; i++) {
            int myInt = r.nextInt();
            int offset = i % 100;
            Bytes.intToBytesLE(myInt, buffer, offset);
            Assert.assertEquals("i=" + i, myInt, Bytes.bytesToIntLE(buffer, offset));
        }
    }
    
    @T
    public static void testIntBE() {
        Random r = new Random(0);
        byte[] buffer = new byte[110];
        
        for (int i = 0; i < 100; i++) {
            int myInt = r.nextInt();
            int offset = i % 100;
            Bytes.intToBytesBE(myInt, buffer, offset);
            Assert.assertEquals("i=" + i, myInt, Bytes.bytesToIntBE(buffer, offset));
        }
    }

    @T
    public static void testUShortLE() {
        byte[] bytes = new byte[5];
        int value = (int) (Math.random() * (1 << 16));
        Bytes.ushortToBytesLE(value, bytes, 1);
        int value1 = Bytes.bytesToUShortLE(bytes, 1);
        if (value1 != value) {
            throw new RuntimeException(value1 + " != " + value);
        }
    }

    @T
    public static void testUShortLE2() {
        for (int i = 0; i < 20; i++) {
            testUShortLE();
        }
    }
    
    @T("perf")
    public static void perfBytesToLongBE(TestCollector c) {
        byte[] arr = new byte[]{0, 0, 1, 2, 3, 4, 5, 6, 3, 3, 3, 3, 3, 3, 3, 3};
        long t0, t1;
        int n = 100*1000*1000;
        
        t0 = System.nanoTime();
        for (int i = 0; i < n/5; i++) {
            Bytes.bytesToLongBE(arr, 0);
            Bytes.bytesToLongBE(arr, 1);
            Bytes.bytesToLongBE(arr, 2);
            Bytes.bytesToLongBE(arr, 3);
            Bytes.bytesToLongBE(arr, 4);
            arr[0] = (byte) i;
        }
        t1 = System.nanoTime();
        
        c.report("timePerLong",  1e-9*(t1-t0)/n);
        c.report("n", n);
    }
    
    @T("perf")
    public static void perfBytesToLongLE(TestCollector c) {
        byte[] arr = new byte[]{0, 0, 1, 2, 3, 4, 5, 6, 3, 3, 3, 3, 3, 3, 3};
        long t0, t1;
        int n = 100*1000*1000;
        
        t0 = System.nanoTime();
        for (int i = 0; i < n/5; i++) {
            Bytes.bytesToLongLE(arr, 0);
            Bytes.bytesToLongLE(arr, 1);
            Bytes.bytesToLongLE(arr, 2);
            Bytes.bytesToLongLE(arr, 3);
            Bytes.bytesToLongLE(arr, 4);
            arr[0] = (byte) i;
        }
        t1 = System.nanoTime();
        
        c.report("timePerLong",  1e-9*(t1-t0)/n);
        c.report("n", n);
    }
    
    @T("perf")
    public static void perfLongToBytesBE(TestCollector c) {
        byte[] arr = new byte[16];
        long t0, t1;
        int n = 20*1000*1000;
        
        t0 = System.nanoTime();
        for (int i = 0; i < n/5; i++) {
            Bytes.longToBytesBE(444333222111L, arr, 0);
            Bytes.longToBytesBE(444333222111L, arr, 1);
            Bytes.longToBytesBE(444333222111L, arr, 2);
            Bytes.longToBytesBE(444333222111L, arr, 3);
            Bytes.longToBytesBE(444333222111L, arr, 4);
            arr[0] = (byte) i;
        }
        t1 = System.nanoTime();
        
        c.report("timePerLong",  1e-9*(t1-t0)/n);
        c.report("n", n);
    }
    
    @T("perf")
    public static void perfLongToBytesLE(TestCollector c) {
        byte[] arr = new byte[16];
        long t0, t1;
        int n = 20*1000*1000;
        
        t0 = System.nanoTime();
        for (int i = 0; i < n/5; i++) {
            Bytes.longToBytesLE(444333222111L, arr, 0);
            Bytes.longToBytesLE(444333222111L, arr, 1);
            Bytes.longToBytesLE(444333222111L, arr, 2);
            Bytes.longToBytesLE(444333222111L, arr, 3);
            Bytes.longToBytesLE(444333222111L, arr, 4);
            arr[0] = (byte) i;
        }
        t1 = System.nanoTime();
        
        c.report("timePerLong",  1e-9*(t1-t0)/n);
        c.report("n", n);
    }
    
    /**
     * Performance testing.
     */
    public static void main(String[] args) {
        byte[] arr = new byte[]{0, 0, 1, 2, 3, 4, 5, 6, 3, 3, 3, 3, 3, 3, 3, 3};
        long t0, t1;
        int n = 100*1000*1000;
        
        t0 = System.nanoTime();
        for (int i = 0; i < n; i++) {
            Bytes.bytesToLongBE(arr, 0);
            arr[0] = (byte) i;
        }
        t1 = System.nanoTime();
        System.out.println("bytesToLongBE " + 1e-9*(t1-t0)/n);
        
        t0 = System.nanoTime();
        for (int i = 0; i < n/5; i++) {
            Bytes.bytesToLongLE(arr, 0);
            Bytes.bytesToLongLE(arr, 1);
            Bytes.bytesToLongLE(arr, 2);
            Bytes.bytesToLongLE(arr, 3);
            Bytes.bytesToLongLE(arr, 4);
            arr[0] = (byte) i;
        }
        t1 = System.nanoTime();
        System.out.println("bytesToLongLE " + 1e-9*(t1-t0)/n);
        
        
        t0 = System.nanoTime();
        for (int i = 0; i < n/5; i++) {
            Bytes.longToBytesLE(444333222111L, arr, 0);
            Bytes.longToBytesLE(444333222111L, arr, 1);
            Bytes.longToBytesLE(444333222111L, arr, 2);
            Bytes.longToBytesLE(444333222111L, arr, 3);
            Bytes.longToBytesLE(444333222111L, arr, 4);
            arr[0] = (byte) i;
        }
        t1 = System.nanoTime();
        System.out.println("longToBytesLE " + 1e-9*(t1-t0)/n);
        
        t0 = System.nanoTime();
        for (int i = 0; i < n/5; i++) {
            Bytes.longToBytesBE(444333222111L, arr, 0);
            Bytes.longToBytesBE(444333222111L, arr, 1);
            Bytes.longToBytesBE(444333222111L, arr, 2);
            Bytes.longToBytesBE(444333222111L, arr, 3);
            Bytes.longToBytesBE(444333222111L, arr, 4);
            arr[0] = (byte) i;
        }
        t1 = System.nanoTime();
        System.out.println("longToBytesBE " + 1e-9*(t1-t0)/n);
    }
}
