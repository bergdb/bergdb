package bergdb.test;

import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;

/**
 * Performance of get operations.
 */
public class GetManyScalability extends PerfGetMany {
    
    public GetManyScalability() {
    }
    
    private void run(TestCollector c, boolean forward) throws InterruptedException {
        this.c = c;
        
        c.report("note", "One thread, GetMany measured with increasing DB size.");
        
        int[] sizes = new int[] {100, 1000, 10*1000, 100*1000};
        
        for (int i = 0; i < sizes.length; i++) {
            int size = sizes[i];

            setup(size);
             
            Timed timed = new Timed(true);
            warmup();
            timed.start();
            Thread.sleep(1000);
            done = true;
            timed.join();
            
            c.report("time-per-kv-" + size, timed.time / timed.count);
        }
    }

    @T("perf")
    public static void standard(TestCollector c) throws InterruptedException {
        GetManyScalability p = new GetManyScalability();
        p.run(c, true);
    }
    
    public static void main(String[] args) throws Exception {
        standard(new BasicCollector());
    }
}

