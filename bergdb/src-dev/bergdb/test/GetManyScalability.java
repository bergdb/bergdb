package bergdb.test;

import bergdb.nanotest.BasicTestEnvironment;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;

/**
 * Performance of get operations.
 */
public class GetManyScalability extends PerfGetMany {
    
    public GetManyScalability() {
    }
    
    private void run(TestEnvironment c, boolean forward) throws InterruptedException {
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

    @Nano("perf")
    public static void standard(TestEnvironment c) throws InterruptedException {
        GetManyScalability p = new GetManyScalability();
        p.run(c, true);
    }
    
    public static void main(String[] args) throws Exception {
        standard(new BasicTestEnvironment());
    }
}

