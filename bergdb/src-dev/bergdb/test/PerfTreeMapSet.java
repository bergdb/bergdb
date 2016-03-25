package bergdb.test;

import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.common.ByteArrayComparator;
import bergdb.common.Util;
import bergdb.nanotest.SimpleTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;


/**
 * Performance writing transactions.
 */
public class PerfTreeMapSet {
    
    @Nano("perf")
    public static void go(TestEnvironment r) {
        Random random = new Random(1);
        int n = 100*1000;
        int m = 20;   // 1 or 2 normally
        long t0, t1;
        Map<byte[], byte[]> map = new TreeMap<byte[], byte[]>(new ByteArrayComparator());
        byte[][] keys = new byte[n][];
        byte[][] values = new byte[n][];
        
        for (int i = 0; i < n; i++) {
            int anInt = random.nextInt();
            keys[i] = Util.toBytes("" + anInt);
            values[i] = Util.toBytes("v" + anInt);
        }
        
        r.out().println("Starting...");
        t0 = System.nanoTime();
        for (int i0 = 0; i0 < m; i0++) {
            for (int i = 0; i < n; i++) {
                map.put(keys[i], values[i]);
            }
        }
        t1 = System.nanoTime();
        
        double totalTime = (t1 - t0) * 1e-9;
        r.report("mn", (m*n));
        r.report("time-per-set", totalTime / (m*n));
        r.report("total-time", totalTime);
    }
    
    public static void main(String[] args) throws Exception {
        go(new SimpleTestEnvironment());
    }
}

/*

---- 120821 ----
time-per-set: 3 us. (n = 50k)

*/