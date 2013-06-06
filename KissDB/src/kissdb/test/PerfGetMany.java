package kissdb.test;

import kissdb.core.Db;
import kissdb.core.FixedDurationEvictBoss;
import kissdb.core.GetData;
import kissdb.core.GetMany;
import kissdb.core.IEvictBoss;
import kissdb.core.KeyFactory;
import kissdb.core.Kvt;
import kissdb.core.SystemClock;
import kissdb.core.Trans;
import kissdb.nanotest.BasicCollector;
import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;
import kissdb.stream.MemoryStream;

/**
 * Performance of getMany operations.
 * 100k short KVs in database, all cached in memory. KVs added in order in batch transactions.
 * 
 * @author Frans Lundberg
 */
public class PerfGetMany {
    Db db;
    int n;
    TestCollector c;
    volatile boolean done;
    
    public PerfGetMany() {
    }
    
    public void setup(int n) {
        this.n = n;
        this.done = false;
        
        IEvictBoss boss = new FixedDurationEvictBoss();
        
        db = Db.builder().stream("m", new MemoryStream())
                .clock(new SystemClock())
                .evictBoss(boss).retainForever().build();
        db.start();
        
        int batchSize = 10000;
        if (batchSize > n) {
            batchSize = n;
        }
        assert n % batchSize == 0;
        byte[] value = new byte[0];
        
        for (int i = 0; i < n / batchSize; i++) {
            Trans.Builder b = Trans.builder();
            
            for (int j = 0; j < batchSize; j++) {
                int index = i * batchSize + j;
                b.set(KeyFactory.binaryIntKey(index), value);
            }
            
            Trans t = b.build();
            db.execute(t);
        }
    }
    
    private int getManyTillDone(boolean forward) {
        long[] startKey = null;
        int loopCount;
        int totalCount = 0;
        int batchSize = 10*1000;
        
        if (n >= batchSize) {
            assert n % batchSize == 0;
            loopCount = n / batchSize;
        } else {
            batchSize = n;
            loopCount = 1;
        }
        
        final int finalBatchSize = batchSize;
        
        A: while (!done) {
            for (int i = 0; i < loopCount; i++) {
                GetMany g = new GetMany();
                g.startKey = startKey;
                g.lookupTime = Long.MAX_VALUE;
                g.forward = forward;   // direction, forward / backward
                g.stopCondition = new GetMany.StopCondition() {
                    private int count = 0;
                    public int handleKvt(Kvt kvt) {
                        count++;
                        assert count <= finalBatchSize;
                        if (done || count == finalBatchSize) {
                            return GetMany.StopCondition.ADD_AND_STOP;
                        } else {
                            return GetMany.StopCondition.ADD;
                        }
                    }
    
                    public void eod() {
                    }
                };
                
                db.getMany(g);
                totalCount += g.result.size();
                if (done) {
                    break A;
                }
            }
        }
        
        return totalCount;
    }
    
    public void warmup() throws InterruptedException {
        Timed timed = new Timed(true);
        timed.start();
        Thread.sleep(500);
        done = true;
        timed.join();
        done = false;
    }
    
    private void run(TestCollector c, boolean forward) throws InterruptedException {
        this.c = c;
        
        setup(100*1000);
        
        warmup();
        
        Timed timed = new Timed(forward);
        timed.start();
        Thread.sleep(2000);
        done = true;
        timed.join();
        
        c.report("time-per-kv", timed.time / timed.count);
    }
    
    @T("perf")
    public static void standard(TestCollector c) throws InterruptedException {
        PerfGetMany p = new PerfGetMany();
        p.run(c, true);
    }
    
    public static void main(String[] args) throws Exception {
        standard(new BasicCollector());
    }
    
    /**
     * Class used to run timed gets until PerfDBGet.this.done == true.
     */
    class Timed implements Runnable {
        GetData gd;
        double time;
        long count;
        Thread thread;
        boolean forward;
        
        public Timed(boolean forward) {
            gd = new GetData();
            count = 0;
            thread = null;
            this.forward = forward;
        }
        
        /**
         * Starts the gets in a new thread.
         */
        public void start() {
            thread = new Thread(this);
            thread.start();
        }
        
        public void join() throws InterruptedException {
            if (thread != null) {
                thread.join();
            }
        }
        
        /**
         * Runs gets until done == true.
         */
        public void run() {
            long t0 = System.nanoTime();
            count = getManyTillDone(forward);
            time = 1e-9 * (System.nanoTime() - t0);
        }
    }
}

/*

== 130405 ==
1.44 us on rose. JVM 1.7.0_02-b13 with -server.


*/