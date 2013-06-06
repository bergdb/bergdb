package kissdb.test.java;

import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.LongBuffer;

import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;


/**
 * Tests performance of NIO buffers.
 */
public class NioBuffer {
    
    @T("perf")
    public static void run(TestCollector c) throws Exception {
        long t0, t1;
        double time;
        int n = 100*1000;
        
        ByteBuffer bb1 = ByteBuffer.allocate(8*n + 100);
        bb1.order(ByteOrder.BIG_ENDIAN);
        bb1.put((byte) 123);
        
        ByteBuffer bb2 = ByteBuffer.allocate(8*n + 100);
        bb2.order(ByteOrder.LITTLE_ENDIAN);
        bb1.put((byte) 123);
        
        LongBuffer lb = LongBuffer.allocate(n);
        
        t0 = System.nanoTime();
        for (long i = 0; i < n; i++) {
            bb1.position(10);
            bb1.putLong(i);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / n;
        c.report("time-per-putLong-ByteBuffer-big-endian", time);
        
        t0 = System.nanoTime();
        for (long i = 0; i < n; i++) {
            bb2.position(10);
            bb2.putLong(i);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / n;
        c.report("time-per-putLong-ByteBuffer-little-endian", time);
        
        t0 = System.nanoTime();
        for (long i = 0; i < n; i++) {
            lb.position(10);
            lb.put(i);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / n;
        c.report("time-per-put-LongBuffer", time);
    }
}

/*
rose laptop 2012-04-26.
$ java -cp . com.kissdb.perf.NIOBuffer
com.kissdb.perf.NIOBuffer.time-per-putLong-ByteBuffer-big-endian = 8.16E-7
com.kissdb.perf.NIOBuffer.time-per-putLong-ByteBuffer-little-endian = 7.94E-7
com.kissdb.perf.NIOBuffer.time-per-put-LongBuffer = 3.48E-7

Conclusions: 
- endianess for ByteBuffer does not matter much.
- LongBuffer is twice as fast and allows for bulk long[] transfer.
- It is slow!
*/