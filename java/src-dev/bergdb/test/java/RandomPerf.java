package bergdb.test.java;

import java.util.Random;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;


/**
 * Performance of java.util.Random class.
 */
public class RandomPerf {
    
    @Nano("perf")
    public static void bytes(TestEnvironment c) {
        long t;
        int n = 100 * 1000;
        Random rand = new Random();
        byte[] array = new byte[1000];
        
        c.report("notes", "Calls Random.nextBytes() " + n + " times.");
        c.report("n", n);
        c.report("total-amount", array.length * n);
        
        t = System.nanoTime();
        for (int i = 0; i < n; ) {
            rand.nextBytes(array); i++;
            rand.nextBytes(array); i++;
            rand.nextBytes(array); i++;
            rand.nextBytes(array); i++;
            rand.nextBytes(array); i++;
        }
        
        t = System.nanoTime() - t;
        double time = t * 1e-9 / n;
        
        c.report("time-per-call", time);
        c.report("total-time", t*1e-9);
        c.report("time-per-byte", time / array.length);
        //c.report("sum-not-interesting", sum);
    }
    
    
    @Nano("perf")
    public static void nextInt(TestEnvironment c) {
        long t;
        int n = 10*1000000;
        Random rand = new Random();
        int sum = 0;
        c.report("notes", "Calls Random.nextInt() " + n + " times.");
        
        t = System.nanoTime();
        for (int i = 0; i < n; ) {
            sum += rand.nextInt();  i++;
            sum += rand.nextInt();  i++;
            sum += rand.nextInt();  i++;
            sum += rand.nextInt();  i++;
            sum += rand.nextInt();  i++;
        }
        
        t = System.nanoTime() - t;
        double time = t * 1e-9 / n;
        
        c.report("n", n);
        c.report("time-per-call", time);
        c.report("total-time", t*1e-9);
        c.report("sum-not-interesting", sum);
    }
    
    @Nano("perf")
    public static void nextLong(TestEnvironment c) {
        long t;
        int n = 10*1000000;
        Random rand = new Random();
        int sum = 0;
        c.report("notes", "Calls Random.nextLong() " + n + " times.");
        
        t = System.nanoTime();
        for (int i = 0; i < n; ) {
            sum += rand.nextLong();  i++;
            sum += rand.nextLong();  i++;
            sum += rand.nextLong();  i++;
            sum += rand.nextLong();  i++;
            sum += rand.nextLong();  i++;
        }
        
        t = System.nanoTime() - t;
        double time = t * 1e-9 / n;
        
        c.report("n", n);
        c.report("time-per-call", time);
        c.report("total-time", t*1e-9);
        c.report("sum-not-interesting", sum);
    }
}
