package kissdb.test;

import kissdb.nanotest.BasicCollector;
import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;

/**
 * Performance of get operations.
 */
public class GetScalability extends Get {
    
    public GetScalability() {
    }
    
    private void go(TestCollector c) throws InterruptedException {
        c.report("note", "One thread, get-time measured with increasing DB size.");
        
        int[] sizes = new int[] {100, 1000, 10*1000, 100*1000, 1*1000000};
        
        for (int i = 0; i < sizes.length; i++) {
            int size = sizes[i];

            createDB(size);
            
            Timed tg = new Timed(0);
            warmup();
            tg.start();
            Thread.sleep(1000);
            done = true;
            tg.join();
            
            c.report("get-time-" + size, tg.time / tg.count);
            c.report("count-" + size, tg.count);
        }
    }

    @T("perf")
    public static void run(TestCollector c) throws InterruptedException {
        new GetScalability().go(c);
    }
    
    public static void main(String[] args) throws Exception {
        run(new BasicCollector());
    }
}

