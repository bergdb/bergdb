package kissdb.test;

import kissdb.nanotest.BasicCollector;
import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;

/**
 * Performance of get operations.
 */
public class GetThreaded extends Get {
    
    public GetThreaded() {
    }
    
    private void go(TestCollector c) throws InterruptedException {
        c.report("note", "Increasing number of threads running DB.get(), DB size: 100k.");
        
        createDB(100*1000);
        
        c.report("n", n);
        
        int[] threadCount = new int[] {1, 2, 3, 4, 8, 16};
        
        for (int tCount : threadCount) {
            runGetTest(c, tCount);
        }
    }
    
    @T("perf")
    public static void get4t(TestCollector c) throws InterruptedException {
        GetThreaded t = new GetThreaded();
        t.createDB(100*1000);
        t.runGetTest(c, 4);
    }

    private void runGetTest(TestCollector c, int tCount) throws InterruptedException {
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

    @T("perf")
    public static void run(TestCollector c) throws InterruptedException {
        new GetThreaded().go(c);
    }
    
    public static void main(String[] args) throws Exception {
        run(new BasicCollector());
    }
}

