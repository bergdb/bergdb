package bergdb.test.java;

import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.common.ByteArrayComparator;
import bergdb.common.StringUtil;
import bergdb.nanotest.SimpleTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;


/**
 * Performance putting key-value pairs to a TreeMap.
 * 
 * @author Frans Lundberg
 */
public class PerfTreeMapSet {
    
    @Nano("perf")
    public static void go(TestEnvironment r) {
        Random random = new Random(1);
        int n = 1000*1000;
        int reps = 5;
        long t0, t1;
        Map<byte[], byte[]> map = new TreeMap<byte[], byte[]>(new ByteArrayComparator());
        byte[][] keys = new byte[n][];
        byte[][] values = new byte[n][];
        
        for (int i = 0; i < n; i++) {
            int anInt = random.nextInt();
            keys[i] = StringUtil.toBytes("" + anInt);
            values[i] = StringUtil.toBytes("v" + anInt);
        }
        
        r.out().println("Starting...");
        t0 = System.nanoTime();
        for (int i0 = 0; i0 < reps; i0++) {
            for (int i = 0; i < n; i++) {
                map.put(keys[i], values[i]);
            }
        }
        t1 = System.nanoTime();
        
        double totalTime = (t1 - t0) * 1e-9;
        r.report("count", (reps*n));
        r.report("time-per-set", totalTime / (reps*n));
        r.report("total-time", totalTime);
    }
    
    public static void main(String[] args) throws Exception {
        go(new SimpleTestEnvironment());
    }
}

/*

2017-07-31
==========

With i7 @ 2.1 GHz (cissi), we get 0.47 us with n = 50k.
Increasing size to 1M. Then we get:

    time-per-set: 1.0 us.

First 1M are new nodes, then 4M overwritten.


2012-08-21
==========

time-per-set: 3 us. (n = 50k)

*/