package bergdb.test;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;

/**
 * Performance of get operations.
 */
public class GetThreaded extends Get {
    
    public GetThreaded() {
    }
    
    private void go(TestEnvironment c) throws InterruptedException {
        c.report("note", "Increasing number of threads running DB.get(), DB size: 100k.");
        
        createDB(100*1000);
        
        c.report("n", n);
        
        int[] threadCount = new int[] {1, 2, 3, 4, 8, 16};
        
        for (int tCount : threadCount) {
            runGetTest(c, tCount);
        }
    }
    
    public static double corePerfMethod() {
        int tCount = 4;
        int n = 100*1000;
        GetThreaded g = new GetThreaded();
        g.createDB(n);
        
        Timed[] timed = new Timed[tCount];
        for (int i = 0; i < tCount; i++) {
            timed[i] = g.new Timed(i * n/tCount);
        }
        
        g.warmup();
        g.done = false;
        
        for (Timed t : timed) {
            t.start();
        }
        
        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            throw new Error(e);
        }
        g.done = true;
        
        for (Timed t : timed) {
            try {
                t.join();
            } catch (InterruptedException e) {
                throw new Error(e);
            }
        }
        
        long count = 0;
        double time = 0.0;
        for (Timed t : timed) {
            count += t.count;
            time += t.time;
        }
        time = time / tCount;
        
        double getTime = time / count;
        return getTime;
    }
    
    @Nano("perf")
    public static void get4t(TestEnvironment c) throws InterruptedException {
        GetThreaded t = new GetThreaded();
        t.createDB(100*1000);
        t.runGetTest(c, 4);
    }

    private void runGetTest(TestEnvironment c, int tCount) throws InterruptedException {
        Timed[] timed = new Timed[tCount];
        for (int i = 0; i < tCount; i++) {
            timed[i] = new Timed(i * n/tCount);
        }
        
        warmup();
        
        this.done = false;
        
        for (Timed t : timed) {
            t.start();
        }
        
        Thread.sleep(1000);
        done = true;
        
        for (Timed t : timed) {
            t.join();
        }
        
        long count = 0;
        double time = 0.0;
        for (Timed t : timed) {
            count += t.count;
            time += t.time;
        }
        time = time / tCount;
        
        c.report("get-count-" + tCount, count);
        c.report("time", time);
        c.report("get-time-" + tCount, time / count);
        
        this.done = false;
    }

    @Nano("perf")
    public static void run(TestEnvironment c) throws InterruptedException {
        new GetThreaded().go(c);
    }
}
