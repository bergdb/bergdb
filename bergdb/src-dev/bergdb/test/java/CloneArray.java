package bergdb.test.java;

import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;

public class CloneArray {
    @T("perf")
    public static void run(TestCollector c) throws Exception {
        byte[] bytes = new byte[4096];
        int N = 100000;
        long t0, t1;
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            bytes.clone();
        }
        t1 = System.nanoTime();
        
        double time = (t1 - t0) * 1e-9;
        c.report("timePerByte", time / (5 * N * bytes.length));
    }
}
