package bergdb.test.java;

import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;

/**
 * Tests performance of calling System.currentTimeMillis() and System.nanoTime().
 */
public class SystemClock {
    
    @T("perf")
    public static void currentTimeMillis(TestEnvironment c) {
        long t = System.nanoTime();
        int n = 1000*1000;
        long sum = 0;
        
        c.report("notes", "Calls System.currentTimeMillis(), " + n + " times.");
        
        for (int i = 0; i < n; ) {
            sum += System.currentTimeMillis();  i++;
            sum += System.currentTimeMillis();  i++;
            sum += System.currentTimeMillis();  i++;
            sum += System.currentTimeMillis();  i++;
            sum += System.currentTimeMillis();  i++;
        }
        
        t = System.nanoTime() - t;
        double time = t * 1e-9 / n;
        
        c.report("n", n);
        c.report("time-per-call", time);
        c.report("total-time", t*1e-9);
        c.report("sum-not-interesting", sum);
    }
    
    @T("perf")
    public static void nanoTime(TestEnvironment c) {
        long t = System.nanoTime();
        int n = 1000*1000;
        long sum = 0;
        
        c.report("notes", "Calls System.nanoTime(), " + n + " times.");
        
        for (int i = 0; i < n; ) {
            sum += System.nanoTime();  i++;
            sum += System.nanoTime();  i++;
            sum += System.nanoTime();  i++;
            sum += System.nanoTime();  i++;
            sum += System.nanoTime();  i++;
        }
        
        t = System.nanoTime() - t;
        double time = t * 1e-9 / n;
        
        c.report("n", n);
        c.report("time-per-call", time);
        c.report("total-time", t*1e-9);
        c.report("sum-not-interesting", sum);
    }
}

/*
120605 - on Rose. Very slow, it takes 1-2 us to call currentTimeMillis or nanoTime.
$ java -cp p/BergDB/ -Xmx1000m -server com.bergdb.main.Perf com.bergdb.common.perf.SystemClock
* com.bergdb.common.perf.SystemClock.currentTimeMillis.notes: Calls System.currentTimeMillis(), 100000 times.
* com.bergdb.common.perf.SystemClock.currentTimeMillis.n: 100000
* com.bergdb.common.perf.SystemClock.currentTimeMillis.time-per-call: 1.7813152400000002E-6
* com.bergdb.common.perf.SystemClock.currentTimeMillis.total-time: 0.178131524
* com.bergdb.common.perf.SystemClock.currentTimeMillis.exeTime: 0.188389671
* com.bergdb.common.perf.SystemClock.nanoTime.notes: Calls System.nanoTime(), 100000 times.
* com.bergdb.common.perf.SystemClock.nanoTime.n: 100000
* com.bergdb.common.perf.SystemClock.nanoTime.time-per-call: 1.81646842E-6
* com.bergdb.common.perf.SystemClock.nanoTime.total-time: 0.181646842
* com.bergdb.common.perf.SystemClock.nanoTime.exeTime: 0.18296034600000002

*/