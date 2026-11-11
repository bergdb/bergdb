package bergdb.test;

import java.util.Random;

import bergdb.core.Db;
import bergdb.core.KeyFactory;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.stream.DummyStream;

/**
 * Performance of get operations.
 * 
 * @author Frans Lundberg
 */
public class Get {    
    Db db;
    long[][] keys;
    int n;                  // number of KVs
    volatile boolean done;
    
    public Get() {
    }
    
    /**
     * Creates 'db', 'keys', sets done = false; prepares for calls to warmup() and 
     * TimedGets.start/run.
     */
    public void createDB(int n) {
        assert n > 0 : "Bad n: " + n;
        this.n = n;
        done = false;
        
        db = Db.builder()
                .stream("main", new DummyStream())
                .systemClock()
                .start();
        
        int bs = 500;   // batch size: L1 (bergdb 024-24; 10,000 until then)
        if (bs > n) {
            bs = n;
        }
        assert n % bs == 0;
        byte[] value = new byte[0];
        for (int i = 0; i < n / bs; i++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < bs; j++) {
                byte[] key = KeyFactory.binaryIntKey(i * bs + j);
                b.put(key, value);
            }
            Trans t = b.build();
            db.execute(t);
        }
        
        keys = new long[n][];
        Random random = new Random(1);
        for (int i = 0; i < n; i++) {
            int keyIndex = random.nextInt(n);
            byte[] key = KeyFactory.binaryIntKey(keyIndex);
            keys[i] = Keys.toSegments(key);
        }
    }
    
    public void warmup() {
        GetData gd = db.newGetData();
        int limit = n > 10*1000 ? 10*1000 : n;
        
        for (int i = 0; i < limit; i++) {
            db.getOne(Long.MAX_VALUE, keys[i], gd);
        }
    }
    
    private void go(TestEnvironment c, int n) throws InterruptedException {
        c.report("note", "One thread running get(), db size: " + n);

        createDB(n);
        
        Timed tg = new Timed();
        warmup();
        tg.start();
        
        Thread.sleep(2000);
        done = true;
        
        tg.join();
        
        c.report("get-n", n);
        c.report("get-count", tg.count);
        c.report("get-time", tg.time / tg.count);
        c.report("get-total-time", tg.time);
    }
    
    /**
     * Used by CorePerf.
     */
    public static double corePerfMethod() {
        Get get = new Get();

        get.createDB(100*1000);
        
        Timed tg = get.new Timed();
        get.warmup();
        tg.start();
        
        try {
            Thread.sleep(2000);
        } catch (InterruptedException e) {
            throw new Error(e);
        }
        
        get.done = true;
        
        try {
            tg.join();
        } catch (InterruptedException e) {
            throw new Error(e);
        }
        
        double result = tg.time / tg.count;
        return result;
    }
    
    @Nano("perf")
    public static void run(TestEnvironment c) throws InterruptedException {
        new Get().go(c, 100*1000);
    }
    
    @Nano("perf")
    public static void run1M(TestEnvironment c) throws InterruptedException {
        new Get().go(c, 1000*1000);
    }
    
    /**
     * Class used to run timed gets until Get.this.done == true.
     */
    class Timed implements Runnable {
        GetData gd;
        volatile double time;
        volatile long count;
        Thread thread;
        int indexOffset;
        
        public Timed() {
            this(0);
        }
        
        public Timed(int indexOffset) {
            gd = db.newGetData();
            count = 0;
            thread = null;
            this.indexOffset = indexOffset;
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
            final int offset = indexOffset;
            long t0 = System.nanoTime();
            
            A: while (!done) {
                for (int i = 0; i < n; i++) {
                    int index = (i + offset) % n;
                    byte[] v = db.getOne(Long.MAX_VALUE, keys[index], gd);
                    count++;
                    assert v != null;
                    if (done) {
                        break A;
                    }
                }
            }
            time = 1e-9 * (System.nanoTime() - t0);
        }
    }
}

/*

2017-07-31
==========

On cissi 170731 13:24, OpenJDK 64-Bit Java 8, server, i7 CPU at 2.1 GHz.

    * bergdb.test.Get.run.get-n: 100000
    * bergdb.test.Get.run.get-time: 0.855e-6
    * bergdb.test.Get.run1M.get-n: 1000000
    * bergdb.test.Get.run1M.get-time: 0.996e-6

Nice, still under 1 us for one out of a million.


2013-11-24
==========

Running it from CorePerf on Cissi, the typical get-time is 0.9 us for 100k db size
and 1.1 us for 1M db size.


2013-04-04
==========

Testing on rose again.
* get-time: 6.4 us.


2013-01-21
==========

DB.followPointer() changed to synchronize node pointer access properly. Best get-time:
* get-time: 6.1 us on Rose.
The performance degradation is fine. We need to synch to support multiple concurrent readers.


2012-08-23
==========

Refactored significantly and changed n from 50k to 100k for alignment with GetScalability
and to be more realistic.
Changed class name to com.bergdb.test.Get.
* get-time: 5.2 us (on linode: 1.6 us)


2012-08-05
==========

$ java -cp p/BergDB/ -server -Xmx1000m com.bergdb.db.perf.PerfDBGet
---- com.bergdb.db.perf.PerfDBGet ----
One thread running get(). DB size: 50000, m=10
* node-depth-average: 5.0, * get-n: 50000, * get-m: 10
* get-time: 6.402708054E-6

I do not know why get-time increased from 4.14 to 6.40 us. Possibly the delete bitmap approach.
We need two iterations for KeyNode.searchLTE, first we must find the delete bitmap for the given
lookup time. Inserts should be faster, however.


2012-05-28
==========

$ java -cp p/BergDB/ -server -Xmx1000m com.bergdb.db.perf.PerfDBGet
---- com.bergdb.db.perf.PerfDBGet ----
One thread running get(). DB size: 50000, m=10
com.bergdb.db.perf.PerfDBGet Start
com.bergdb.db.perf.PerfDBGet.node-depth-average = 5.0
com.bergdb.db.perf.PerfDBGet.get-n = 50000
com.bergdb.db.perf.PerfDBGet.get-m = 10
com.bergdb.db.perf.PerfDBGet.get-time = 4.14258754E-6

Testing the new "Linear" branch (refactoring). Great! Faster, before I even start to optimize :-)
Probably fewer pointers (no IPointer objects) makes the difference.


2012-04-06
==========

$ java -server -cp . com.bergdb.klong.PerfDBGet
com.bergdb.klong.PerfDBGet Start
com.bergdb.klong.PerfDBGet.get-n = 50000
com.bergdb.klong.PerfDBGet.get-m = 10
com.bergdb.klong.PerfDBGet.get-time = 3.554066904E-6
com.bergdb.klong.PerfDBGet.get-total-time = 1.77703345200000


*/
