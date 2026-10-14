package bergdb.test.java;

import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.LongBuffer;

import bergdb.common.Bytes;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;


public class BytesToLong {

    @Nano("perf")
    public static void run(TestEnvironment c) throws Exception {
        long t0, t1;
        double time;
        final int N = 50*1000*1000;
        byte[] arr = new byte[100];
        
        for (int i = 0; i < arr.length; i++) {
            arr[i] = (byte) i;
        }
        
        // byte[] to long
        
        long sum = 0;
        final int ND4 = N/4;
        t0 = System.nanoTime();
        for (int i = 0; i < ND4; i++) {
            sum += Bytes.bytesToLongLE(arr, 0);
            sum += Bytes.bytesToLongLE(arr, 8);
            sum += Bytes.bytesToLongLE(arr, 16);
            sum += Bytes.bytesToLongLE(arr, 24);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N);
        c.report("bytesToLongLE", time);
        c.report("sum", sum);
        
        t0 = System.nanoTime();
        for (int i = 0; i < ND4; i++) {
            sum += Bytes.bytesToLongBE(arr, 0);
            sum += Bytes.bytesToLongBE(arr, 8);
            sum += Bytes.bytesToLongBE(arr, 16);
            sum += Bytes.bytesToLongBE(arr, 24);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N);
        c.report("bytesToLongBE", time);
        c.report("sum", sum);
        
        // long to byte[]
        
        final int offsetMax = arr.length - 10;
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; ) {
            Bytes.longToBytesBE(123456789012345L, arr, i++ % offsetMax);
            Bytes.longToBytesBE(123456789012346L, arr, i++ % offsetMax);
            Bytes.longToBytesBE(123456789012347L, arr, i++ % offsetMax);
            Bytes.longToBytesBE(123456789012348L, arr, i++ % offsetMax);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / N;
        c.report("longToBytesBE", time);
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; ) {
            Bytes.longToBytesLE(123456789012345L, arr, i++ % offsetMax);
            Bytes.longToBytesLE(123456789012346L, arr, i++ % offsetMax);
            Bytes.longToBytesLE(123456789012347L, arr, i++ % offsetMax);
            Bytes.longToBytesLE(123456789012348L, arr, i++ % offsetMax);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / N;
        c.report("longToBytesLE", time);
        c.report("longToBytesLE-total-time", (t1-t0) * 1e-9);
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; ) {
            longToBytes(123456789012345L, arr, i++ % offsetMax);
            longToBytes(123456789012345L, arr, i++ % offsetMax);
            longToBytes(123456789012345L, arr, i++ % offsetMax);
            longToBytes(123456789012345L, arr, i++ % offsetMax);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / N;
        c.report("longToBytesBuffer", time);
    }
    
    private static final ByteBuffer byteBuffer = ByteBuffer.allocate(100);
    
    private static void longToBytes(long value, byte[] arr, int offset) {
        byteBuffer.putLong(offset, value);
    }
    
    @Nano("perf")
    public static void byteBuffer(TestEnvironment c) {
        // Converting between byte array and long array and other direction.
        
        final int longCount = 100;
        final int n = 1*1000000;
        final byte[] arr = new byte[8 * longCount];
        long t0, t1;
        double time;
        ByteOrder order = ByteOrder.BIG_ENDIAN;
        
        // getLong
        
        for (int i = 0; i < longCount; i++) {
            Bytes.longToBytesBE(i, arr, i * 8);
        }
        long sum = 0;
        
        t0 = System.nanoTime();
        for (int k = 0; k < n; k++) {
            final ByteBuffer byteBuffer = ByteBuffer.wrap(arr);
            byteBuffer.order(order);
            
            for (int i = 0; i < longCount / 4; ) {
                sum += byteBuffer.getLong();  i++;
                sum += byteBuffer.getLong();  i++;
                sum += byteBuffer.getLong();  i++;
                sum += byteBuffer.getLong();  i++;
            }
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (n * longCount);
        
        c.report("getLong", time);
        
        // setLong
        
        final byte[] arr2 = new byte[8 * longCount];
        
        t0 = System.nanoTime();
        for (int k = 0; k < n; k++) {
            final ByteBuffer byteBuffer = ByteBuffer.wrap(arr2);
            byteBuffer.order(order);
            
            for (int i = 0; i < longCount / 4; ) {
                byteBuffer.putLong(i);  i++;
                byteBuffer.putLong(i);  i++;
                byteBuffer.putLong(i);  i++;
                byteBuffer.putLong(i);  i++;
            }
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (n * longCount);
        
        c.report("setLong", time);
        c.report("sum", sum);
        
        
        // asLongBuffer, get long, bulk
        
        long[] longArray = new long[longCount];
        
        t0 = System.nanoTime();
        for (int k = 0; k < n; k++) {
            final LongBuffer longBuffer = ByteBuffer.wrap(arr2).asLongBuffer();
            longBuffer.get(longArray);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (n * longCount);
        c.report("byte-array-to-long-array", time);   // time per long
        
        // asLongArray, set long, bulk
        
        t0 = System.nanoTime();
        for (int k = 0; k < n; k++) {
            final LongBuffer longBuffer = ByteBuffer.wrap(arr2).asLongBuffer();
            longBuffer.put(longArray, 0, longArray.length);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (n * longCount);
        c.report("long-array-to-byte-array", time);   // time per long
    }
}

/*

121213. On rose, HotSpot JVM 1.7.0. 
The methods to encode a long to bytes is slow. Bytes.longToBytesLE(), Bytes.intToBytesLE() are 
problematically slow for BergDB.
  52 ns for Bytes.longToBytesLE
  159 ns when ByteBuffer is used.
From bytes -> long is fast enough (4 ns)

120830. $ nice -10 java -server -cp p/BergDB/ com.bergdb.dev.Perf "com.bergdb.common.perf.BytesToLong"
com.bergdb.common.perf.BytesToLong.run.bytesToLongLE-time-per-long: 3.5e-9
com.bergdb.common.perf.BytesToLong.run.bytesToLongBE-time-per-long: 3.8e-9
com.bergdb.common.perf.BytesToLong.run.longToBytesBE-time-per-long: 51e-9
com.bergdb.common.perf.BytesToLong.run.longToBytesLE-time-per-long: 50e-9
com.bergdb.common.perf.BytesToLong.run.longToBytes: 160e-9
WHY is longToBytesLE so slow? Anything we can do? And use of ByteBuffer is even slower
but could potentially be good for larger arrays.

120426, Frans rose laptop. Oracle JVM 7 -server
  $ java -server -cp . com.bergdb.perf.BytesToLong
  com.bergdb.perf.BytesToLong.arr2long-time-per-long = 3.035623454E-8 
  com.bergdb.perf.BytesToLong.arr2longFaster-time-per-long = 6.905537340000001E-9
  com.bergdb.perf.BytesToLong.longToBytesBE-time-per-long = 5.2672362920000005E-8
  com.bergdb.perf.BytesToLong.longToBytesLE-time-per-long = 5.405076998E-8
080907, Frans's Acer Extenda 5220, Sun JVM 1.6 -server
  timePerLong = 43 ns
100712, same computer, new Ubuntu, same JVM. 100 times more operations.
  timePerLong = 13 ns.
  This is equivalent to processing 615e6 bytes/s.
100712, saw there was memory allocation in the method! Removed it (arr2longFaster method).
  timePerLong = 13 ns. (610e6 bytes/s).
  timePerLongFaster = 3.0 ns (2700e6 bytes/s) - nice! Computing on cached data is fast!
*/
