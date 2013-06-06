package kissdb.test.java;

import java.nio.ByteBuffer;
import java.nio.ByteOrder;

import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;


public class AllocateByteBuffer {
    
    @T("perf")
    public static void run(TestCollector c) throws Exception {
        long t0, t1;
        double time;
        int N = 10*1000;
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            ByteBuffer b = ByteBuffer.allocate(100);
            b.order(ByteOrder.LITTLE_ENDIAN);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N);
        c.report("timePerAllocate", time);
        
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            ByteBuffer b = ByteBuffer.allocateDirect(100);
            b.order(ByteOrder.LITTLE_ENDIAN);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N);
        c.report("timePerAllocateDirect", time);
        
        byte[] someBytes = new byte[1000];
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            ByteBuffer b = ByteBuffer.wrap(someBytes, 0, someBytes.length);
            b.order(ByteOrder.LITTLE_ENDIAN);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N);
        c.report("timePerWrap", time);
        
        
        N = 10*1000;
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            someBytes = new byte[1024];
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N);
        c.report("timePerArray", time);
        c.report("timePerByte", time/someBytes.length);
        
        N = 10*1000;
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            someBytes = new byte[1];
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N);
        c.report("arrayOverhead", time);
    }
}

/*
080904, On Acer Extensa 5220, Sun 1.6 JVM with -server.
timePerAllocate = 5 us
timePerDirectAllocate = 15 us.
timePerWrap = 0.25 us.
*/