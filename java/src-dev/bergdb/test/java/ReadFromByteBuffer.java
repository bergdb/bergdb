package bergdb.test.java;

import java.nio.ByteBuffer;
import java.nio.ByteOrder;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;


/**
 * Tests performance of reading from ByteArray.
 * 
 * @author Frans Lundberg
 */
public class ReadFromByteBuffer {
    
    @Nano("perf")
    public static void p1(TestEnvironment c) {
        ByteBuffer bytes = ByteBuffer.allocateDirect(1024*1024);
        //ByteBuffer bytes = ByteBuffer.allocate(1024*1024);
        long t0, t1;
        double time;
        MyLong l = new MyLong();
        long N = 1000*1000;
        long sum = 0;
        
        bytes.order(ByteOrder.LITTLE_ENDIAN);
        
        t0 = System.nanoTime();
        for (long i = 0; i < N; i++) {
            bytes.position(0);
            sum += bytes.getLong(0);
            sum += bytes.getLong(10);
            sum += bytes.getLong(0);
            sum += bytes.getLong(33333);
            sum += bytes.getLong(234);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (5*N);
        c.report("timePerLongRead", time);
        
        t0 = System.nanoTime();
        for (long i = 0; i < N; i++) {
            bytes.position(0);
            sum += bytes.getInt(0);
            sum += bytes.getInt(10);
            sum += bytes.getInt(0);
            sum += bytes.getInt(33333);
            sum += bytes.getInt(234);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (5*N);
        c.report("timePerIntRead", time);
        
        N = 10 * N;
        t0 = System.nanoTime();
        for (long i = 0; i < N; i++) {
            sum += l.getLong();
            sum += l.getLong();
            sum += l.getLong();
            sum += l.getLong();
            sum += l.getLong();
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N*5);
        c.report("timePerGetLong", time);   
        c.report("sum-not-of-importance", sum);   
    }
    
    /**
     * Tests reading certain "file structure" from a byte array.
     * The file starts with a 256x4 pointers (byte offsets) to hash bins.
     * The test key is "/com.skycash.lnode/accounts/phone:46700000000/balance".
     * And the suffix part (not stored in atom header) is 
     * "phone:46700000000/balance".
     * Hash value for suffix is 100. Offset to that bin is 12000.
     */
    @Nano("perf")
    public static void p2(TestEnvironment c) throws Exception {
        ByteBuffer bytes = ByteBuffer.allocateDirect(1024*1024);
        //ByteBuffer bytes = ByteBuffer.allocate(1024*1024);
        bytes.order(ByteOrder.LITTLE_ENDIAN);
        String key = "phone:46700000000/balance";
        int hashValue = 100;
        byte[] keyBytes = key.getBytes("UTF-8");
        bytes.putInt(hashValue*4, 12000);
        bytes.position(12000);
        bytes.putInt(keyBytes.length); // size of key
        bytes.put(keyBytes);        // key
        bytes.putInt(8);            // size of value
        bytes.putLong(123);         // balance
        
        long t0, t1;
        double time;
        int N = 1000000;
        t0 = System.nanoTime();
        
        for (int i = 0; i < N; i++) {
            int offset = bytes.getInt(hashValue*4);
            //System.out.println("offset = " + offset);
            bytes.position(offset);
            int keySize = bytes.getInt();
            //System.out.println("keySize = " + keySize);
            label: if (keySize == keyBytes.length) {
                for (int j = 0; j < keySize; j++) {
                    if (bytes.get() != keyBytes[j]) {
                        break label;
                    }
                }
                
                // Right key, read the value!
                @SuppressWarnings("unused")
                int valueSize = bytes.getInt();
                //System.out.println("valueSize = " + valueSize);
                @SuppressWarnings("unused")
                long value = bytes.getLong();
                //System.out.println("value = " + value);
            }
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / N;
        c.report("timePerRead", time);
    }
    
    static class MyLong {
        private long l = 1234567890L;
        
        public long getLong() {
            l--;
            return l;
        }
    }
}

/*
080907, Frans's Acer Extenda 5220, Sun JVM 1.6 -server
  Reading a long from a direct byte buffer (little endian) takes 14 ns on my 
  Same with big endian takes around 50 percent longer.
  Reading an int instead of a long is slightly faster (12 ns).
  With non direct buffer same thing takes twice as long or so (21 and 46 ns).
  Reading using a getLong() method takes 3 ns.
  Reading from non-direct buffer takes 137 ns independent of byte order.

p2() 080806:
Reading takes 0.3 us for N = 1,000,000.
Java VM 1.6 from Sun, -server flag used.

Even in the case there are many, say 100 key-value pairs in the bin before
the right one, the lookup will still be reasonably fast.
- getInt, get key size
- possibly one or a few get needed here
- position, move to value
- getInt, get value size
- position, move to new key-value pair
Roughly we should have to do around 3 getInt per key that is not matching.
This means 12*3*100 ~= 4000 ns = 4 us. Acceptable! Compare to 10000 us seek
time of a harddrive.
*/