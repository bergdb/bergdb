package bergdb.test.java;

import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;

/**
 * Performance of parsing integers (string to binary).
 * 
 * @author Frans Lundberg
 */
public class ParseIntegers {
    @T("perf")
    public static void run(TestCollector c) throws Exception {
        int N = 100;
        double t0, t1, time;
        
        t0 = System.nanoTime();
        for (int i=0; i<N; i++) {
            Long.parseLong("123456789012345678");
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / N;
        c.report("timePerLong", time);
        c.report("timePerBinaryByte", time/8);
    }
}

/*
This is really slow! Throughput on Acer Extensa 5220 is only in the order of 
0.2e6 bytes/s (27000 longs/s, 37 us/long). 080701.
*/