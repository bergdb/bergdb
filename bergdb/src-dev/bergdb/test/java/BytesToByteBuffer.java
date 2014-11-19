package bergdb.test.java;

import java.nio.ByteBuffer;
import java.nio.ByteOrder;

import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;

public class BytesToByteBuffer {
    @T("perf")
    public static void run(TestEnvironment c) throws Exception {
        int bufferSize = 128*1024;
        ByteBuffer bytes = ByteBuffer.allocateDirect(bufferSize);
        bytes.order(ByteOrder.LITTLE_ENDIAN);
        
        long t0, t1;
        double time;
        int N = 1000*1000;
        byte[] interval1 = new byte[8];
        byte[] interval2 = new byte[100];
        byte[] interval3 = new byte[1000];
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            bytes.position(20000);
            bytes.put(interval1);
            bytes.position(123000);
            bytes.put(interval2);
            bytes.position(10000);
            bytes.put(interval3);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N);
        c.report("timePerOperation", time);
        
        N = 100;
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            copy(bytes);
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N);
        c.report("timePerCopy", time);
        c.report("timePerByte", time/bufferSize);
    }

    private static ByteBuffer copy(ByteBuffer in) {
        ByteBuffer out = ByteBuffer.allocateDirect(in.capacity());        
        in.position(0);
        out.position(0);
        out.put(in);
        return out;
    }
}

/*
080904. On Acer Extensa 5220, Sun 1.6 JVM with -server.
timePerOperation = 0.6 us
timePerCopy = 190 us
timePerByte = 1.4 ns
*/
