package bergdb.test.java;

import java.util.HashMap;
import java.util.Random;
import bergdb.common.StringUtil;
import bergdb.nanotest.Nano;
import bergdb.nanotest.SimpleTestEnvironment;
import bergdb.nanotest.TestEnvironment;

/**
 * Testing the performance of Java's HashMap implementation.
 * 
 * @author Frans Lundberg
 */
public class PerfHashMap {
    
    @Nano("perf")
    public static void go(TestEnvironment r) {
        Random random = new Random(1);
        int n = 1000*1000;
        int reps = 5;
        long t0, t1;
        HashMap<byte[], byte[]> map = new HashMap<byte[], byte[]>();
        byte[][] keys = new byte[n][];
        byte[][] values = new byte[n][];
        
        for (int i = 0; i < n; i++) {
            int anInt = random.nextInt();
            keys[i] = StringUtil.toBytes("" + anInt);
            values[i] = StringUtil.toBytes("v" + anInt);
        }
        
        r.out().println("Starting, put...");
        reps = reps * 4;
        t0 = System.nanoTime();
        for (int i0 = 0; i0 < reps; i0++) {
            for (int i = 0; i < n; i++) {
                map.put(keys[i], values[i]);
            }
        }
        t1 = System.nanoTime();
        
        double totalTime = (t1 - t0) * 1e-9;
        r.report("n", n);
        r.report("map.size", map.size());
        r.report("time-per-set", totalTime / (reps*n));
        r.report("total-time", totalTime);
        
        r.out().println("Starting, get...");
        t0 = System.nanoTime();
        for (int i0 = 0; i0 < reps; i0++) {
            for (int i = 0; i < n; i++) {
                map.get(keys[i]);
            }
        }
        t1 = System.nanoTime();
        
        totalTime = (t1 - t0) * 1e-9;
        r.report("time-per-get", totalTime / (reps*n));
        r.report("total-time", totalTime);
    }
    
    public static void main(String[] args) throws Exception {
        go(new SimpleTestEnvironment());
    }
}

/*

2017-07-31
==========

Perf on cissi, Ubuntu, 2.1 GHz i7 CPU (4 core). 1M entries.
Put takes 115 ns, Get takes 47 ns.

    Starting, put...
    * bergdb.test.java.PerfHashMap.go.n: 1000000
    * bergdb.test.java.PerfHashMap.go.time-per-set: 1.1476296755000002E-7
    Starting, get...
    * bergdb.test.java.PerfHashMap.go.time-per-get: 4.67529002E-8

A custom implementation of long->byte[] could be faster. Not sure how much
though. The HashMap code is already really fast.

*/