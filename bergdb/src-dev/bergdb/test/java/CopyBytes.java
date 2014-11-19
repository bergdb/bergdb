package bergdb.test.java;

import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;

public class CopyBytes {
    @T("perf")
    public static void run(TestEnvironment c) throws Exception {
        long t0, t1;
        int N = 1000000;
        int byteCount;
        byte[] array = new byte[100*64];
        byte[] dest = new byte[64];
        
        array[12] = 1;
        array[123] = 2;
        array[1234] = 3;
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            System.arraycopy(array, (i % array.length) / 2, dest, 0, 64);
        }
        t1 = System.nanoTime();
        
        byteCount = 64*N;
        c.report("timePerByte64", (1e-9*(t1-t0)) / byteCount);
       
        array = new byte[100*4*1024];
        dest = new byte[4*1024];
        
        N = 10000;
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            System.arraycopy(array, (i % array.length) / 2, dest, 0, 4*1024);
        }
        t1 = System.nanoTime();
        
        byteCount = 4*1024*N;
        c.report("timePerByte4k", (1e-9*(t1-t0)) / byteCount);
    }
}

/*
080907, Frans's Acer Extenda 5220, Sun JVM 1.6 -server flag
Copy64.timePerByte64 = 1.07E-9. Max transfer is 1 GB per sec.
Copy64.timePerByte4k = 4.0E-10. Max transfer is 2.5 GB per sec.
*/
