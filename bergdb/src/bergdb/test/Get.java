package bergdb.test;

import java.util.Random;

import bergdb.core.Db;
import bergdb.core.FixedDurationEvictBoss;
import bergdb.core.IEvictBoss;
import bergdb.core.KeyFactory;
import bergdb.core.Trans;
import bergdb.coreds.GetData;
import bergdb.coreds.Keys;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.stream.NullStream;

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
        
        IEvictBoss boss = new FixedDurationEvictBoss();
        
        db = Db.builder()
                .stream("main", new NullStream())
                .disableStreamWrite()
                .systemClock()
                .retainForever().evictBoss(boss).start();
        
        int bs = 10000;   // batch size
        if (bs > n) {
            bs = n;
        }
        assert n % bs == 0;
        byte[] value = new byte[0];
        for (int i = 0; i < n / bs; i++) {
            Trans.Builder b = Trans.builder();
            for (int j = 0; j < bs; j++) {
                byte[] key = KeyFactory.binaryIntKey(i * bs + j);
                b.set(key, value);
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
        GetData gd = new GetData();
        int limit = n > 10*1000 ? 10*1000 : n;
        
        for (int i = 0; i < limit; i++) {
            db.get(Long.MAX_VALUE, keys[i], gd);
        }
    }
    
    private void go(TestCollector c) throws InterruptedException {
        c.report("note", "One thread running get(), db size: 100k.");
        
        createDB(100*1000);
        
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
    
    @T("perf")
    public static void run(TestCollector c) throws InterruptedException {
        new Get().go(c);
    }
    
    public static void main(String[] args) throws Exception {
        run(new BasicCollector());
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
            gd = new GetData();
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
                    byte[] v = db.get(Long.MAX_VALUE, keys[index], gd);
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

======== 2013-04-05 ========
Tested a variation. Same as before, but only first 1000, 100, 10 kvs read. This increased 
performance, but not much.
    1000 - 6.3 us   1.0 %
    100  - 5.7 us   0.1 %
    10   - 5.2 us   0.01%
Code was erased, not so interesting. Small speedup.

======== 2013-04-04 ========
Testing on rose again.
* get-time: 6.4 us.

======== 2013-01-30 ========
Changed test to run for 2.0 s instead of 1.0 s. Testing on rose and JVM 1.7 
from Oracle with -server flag.
* get-time: 5.9 us.

Then I also changed Get class to use "new FixedDurationEvictBoss()" instead of new NoEvictBoss().
* get-time: 6.2 us.

======== 2013-01-21 ========
DB.followPointer() changed to synchronize node pointer access properly. Best get-time:
* get-time: 6.1 us on Rose.
The performance degradation is fine. We need to synch to support multiple concurrent readers.

======== 2013-01-16 ========
* get-time: 5.3 us on Rose.

======== 2012-12-13 ========
Still getting: "get-time: 5.2 us" on Rose.
Tip: "sudo nice --19 java -server -cp p/BergDB com.bergdb.test.Get".
    "sudo nice --19" for highest process priority.

======== 2012-08-23 ========
Refactored significantly and changed n from 50k to 100k for alignment with GetScalability
and to be more realistic.
Changed class name to com.bergdb.test.Get.
* get-time: 5.2 us (on linode: 1.6 us)

======== 2012-08-22 ========
Changed to add batches of KVs. 10000 KVs in one transaction. This makes time klongs
less frequent than before. It improves performance significantly.
* get-time: 4.5 us.

======== 2012-08-05 ========
$ java -cp p/BergDB/ -server -Xmx1000m com.bergdb.db.perf.PerfDBGet
---- com.bergdb.db.perf.PerfDBGet ----
One thread running get(). DB size: 50000, m=10
* node-depth-average: 5.0, * get-n: 50000, * get-m: 10
* get-time: 6.402708054E-6

I do not know why get-time increased from 4.14 to 6.40 us. Possibly the delete bitmap approach.
We need two iterations for KeyNode.searchLTE, first we must find the delete bitmap for the given
lookup time. Inserts should be faster, however.

======== 2012-05-28 ========
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

======== 2012-05-24 ========
$ java -cp p/BergDB/ -server com.bergdb.db.perf.PerfDBGet
---- com.bergdb.db.perf.PerfDBGet ----
One thread running get(). DB size: 50000, m=10
com.bergdb.db.perf.PerfDBGet Start
com.bergdb.db.perf.PerfDBGet.node-depth-average = 5.0
com.bergdb.db.perf.PerfDBGet.get-n = 50000
com.bergdb.db.perf.PerfDBGet.get-m = 10
com.bergdb.db.perf.PerfDBGet.get-time = 4.61719511E-6
com.bergdb.db.perf.PerfDBGet.get-total-time = 2.308597555

Some increase in get time. A small part of this is the accessPath (2-3%) and evictIfNeeded, but
there is something more that has degraded the performance. Possible, make dirty method or something
like that. We are still very fine :-). Below 10 us on my notebook is really fine.

======== 2012-04-06 ========
$ java -server -cp . com.bergdb.klong.PerfDBGet
com.bergdb.klong.PerfDBGet Start
com.bergdb.klong.PerfDBGet.get-n = 50000
com.bergdb.klong.PerfDBGet.get-m = 10
com.bergdb.klong.PerfDBGet.get-time = 3.554066904E-6
com.bergdb.klong.PerfDBGet.get-total-time = 1.77703345200000
*/
