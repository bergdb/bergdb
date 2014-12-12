package bergdb.test.java;

import java.util.HashMap;
import java.util.Random;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;


/**
 * Testing something that could be used for a Judy-like
 * data structure in Java.
 * 
 * @author Frans Lundberg
 */
public class JudyPerf {
    
    @Nano("perf")
    public static void testJudy(TestEnvironment c) {
        long t0, t1;
        int n = 100000;
        Random r = new Random(0);
        double time;
        
        byte[] values = new byte[256];
        r.nextBytes(values);
        for (int i = 0; i < values.length; i++) {
            if (values[i] < 0) {
                values[i] += 128;
            }
        }

        t0 = System.nanoTime();
        for (int i = 0; i < 128; i++) {
            for (int j = 0; j < n; j++) {           // Just to make test run longer
                for (int k = 0; k < 128; k++) {
                    if (i == values[k]) {
                        // Found it!
                        break;
                    }
                }
            }
        }
        t1 = System.nanoTime();
        time = 1e-9 * (t1 - t0);
        
        c.report("judyLookupTime", time / (128*n));
    }
    
    @Nano("perf")
    public static void testHash(TestEnvironment c) {
        long t0, t1;
        int n = 1000 * 1000;
        Random r = new Random(0);
        double time;
        HashMap<Long, Long> map = new HashMap<Long, Long>();
        
        for (int i = 0; i < 1000 * 1000; i++) {
            map.put(r.nextLong(), r.nextLong());
        }
        
        r = new Random(0);
        t0 = System.nanoTime();
        for (int i = 0; i < n; i++) {
            long l = r.nextLong();
            r.nextLong();
            map.get(l);
        }
        t1 = System.nanoTime();
        time = 1e-9 * (t1 - t0);
        
        c.report("hashLookupTime", time / n);
    }
}

/*

081126

$ nice java -server JudyPerformance 
Time per lookup: 52 ns. This is actually pretty good! Probably, we will have 
more time consuming things in the nodes anyway.
Loop unrolling tested but does not improve.
We don't expect more than 5 such worst-case lookups when traversing prefix tree.
This means a total overhead of 250 ns (0.25 us) per lookup.
This is really OK.
A hash map lookup (hit) for map with 1 million entries takes 330 ns. So, 
the VERY simple approach with just storing in an array (unsorted) is actually 
comparable in speed to HashMap implementation!

$ (Acer Extensa 5220, Sun's JVM 1.6):
Judy lookup takes 107 ns, hash lookup 902 ns. 
    The -server flag was important for speed in this case.

*/