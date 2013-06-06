package kissdb.test.java;

import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;

/**
 * Tests performance of String.hashCode().
 */
public class StringHash {

    @T("perf")
    public static void run(TestCollector c) throws Exception {
        long t0, t1;
        double time;
        int N = 1000*1000;
        t0 = System.nanoTime();
        String key = "phone:46700000000/balance";
        long sum = 0;
        
        for (int i = 0; i < N; i++) {
            sum += key.hashCode();
            sum += key.hashCode();
            sum += key.hashCode();
            sum += key.hashCode();
            sum += key.hashCode();
        }
        t1 = System.nanoTime();
        time = (t1-t0) * 1e-9 / (N*5);
        c.report("timePerHash", time);
        c.report("sum-not-of-importance", sum);
    }
}

/*
080806
On my laptop, Acer Extensa, timePerHash is 22 ns. Nice!
*/