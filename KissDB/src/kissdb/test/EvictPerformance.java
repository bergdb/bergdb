package kissdb.test;

import java.util.Random;

import kissdb.core.Db;
import kissdb.core.EvictData;
import kissdb.core.FixedDurationEvictBoss;
import kissdb.core.IEvictBoss;
import kissdb.core.KeyFactory;
import kissdb.core.Keys;
import kissdb.core.Trans;
import kissdb.nanotest.BasicCollector;
import kissdb.nanotest.TestCollector;
import kissdb.storage.StreamIoException;
import kissdb.stream.MemoryStream;


/**
 * Tests performance of DB.evict().
 * 
 * @author Frans Lundberg
 */
public class EvictPerformance {
    Db db;
    long[][] keys;
    int n;                  // number of KVs
    
    private void go(TestCollector c, IEvictBoss boss) {
        
        try {
            createDB(100*1000, boss);
        } catch (StreamIoException e) {
            c.out().println("db stream size: " + db.getStreamLength());
            throw e;
        }
        
        EvictData ed = new EvictData();
        final int m = 100*1000;
        int evictedCount = 0;
        
        long t = System.nanoTime();
        for (int i = 0; i < m; i++) {
            db.evict(ed);
            evictedCount += ed.evictCount;
        }
        t = System.nanoTime() - t;
        
        c.report("time", t*1e-9);
        c.report("timePerEvictCall", t*1e-9 / m);
        c.report("evictedCount", evictedCount);
        if (evictedCount > 0){
            c.report("timePerEvict", t*1e-9 / evictedCount);
        }
    }
    
    /**
     * Creates 'db', 'keys', sets done = false; prepares for calls to warmup() and 
     * TimedGets.start/run.
     */
    private void createDB(int n, IEvictBoss evictBoss) {
        assert n > 0 : "Bad n: " + n;
        this.n = n;
        
        db = Db.builder()
                .mainStream(new MemoryStream())
                .systemClock()
                .retainForever().evictBoss(evictBoss).start();
        
        int bs = 10000;   // batch size
        if (bs > n) {
            bs = n;
        }
        assert n % bs == 0;
        byte[] value = new byte[0];
        
        for (int outer = 0; outer < 1; outer++) {
            for (int i = 0; i < n / bs; i++) {
                Trans.Builder b = Trans.builder();
                for (int j = 0; j < bs; j++) {
                    byte[] key = KeyFactory.binaryIntKey(i * bs + j);
                    b.set(key, value);
                }
                Trans t = b.build();
                db.execute(t);
            }
        }
        
        keys = new long[n][];
        Random random = new Random(1);
        for (int i = 0; i < n; i++) {
            int keyIndex = random.nextInt(n);
            byte[] key = KeyFactory.binaryIntKey(keyIndex);
            keys[i] = Keys.toSegments(key);
        }
    }
    
    public static void main(String[] args) {
        TestCollector collector = new BasicCollector();
        
        //collector.out().println("With new FixedDurationEvictBoss(Long.MAX_VALUE)...");
        //new EvictPerformance().go(new Collector(), new FixedDurationEvictBoss(Long.MAX_VALUE));
            // No real evictions will be made since duration ≃ infinity.
        
        int duration = 1000;
        collector.out().println("With new FixedDurationEvictBoss(" + duration + ")");
        IEvictBoss boss = new FixedDurationEvictBoss(duration);
        
        EvictPerformance p = new EvictPerformance();
        p.go(new BasicCollector(), boss);
        
        //p.db.printGraph(System.out);
    }
}
