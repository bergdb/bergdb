package bergdb.test;

import java.io.PrintStream;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.NoEvictBoss;
import bergdb.core.Trans;
import bergdb.dag.Keys;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.TestClock;
import bergdb.stream.NullStream;

/**
 * Performance writing small transactions.
 * 
 * @author Frans Lundberg
 */
public class Set {
    @SuppressWarnings("unused") private PrintStream out;
    private TestEnvironment c;
    private Db db;
    
    @T("perf")
    public static void normal(TestEnvironment c) {
        new Set(c).run(100000, true, 2);
    }
    
    @T("perf")
    public static void noWritesToStream(TestEnvironment c) {
        new Set(c).run(100000, false, 2);
    }
    
    public Set(TestEnvironment c) {
        this.c = c;
        this.out = c.out();
    }

    public Db createDB(boolean enableWrite) {
        NullStream nullStream = new NullStream();
        
        DbBuilder b = Db.builder()
                .clock(new TestClock())
                .retainForever()
                .evictBoss(new NoEvictBoss())
                .stream("main", nullStream);
        
        //db.setRetainDuration(Long.MAX_VALUE);  --> // 30 us
        //db.setReclaimInternalFraction(0.001);      // 32 us
        //db.setReclaimInternalFraction(0.10);       // 36 us
        //db.setReclaimInternalFraction(0.25);       // 54 us
        //db.setReclaimInternalFraction(0.50);       // 99 us
        Db db = b.start();
        //out.println("test.Set, internal fraction: " + db.getInternalFraction());
        return db;
    }
    
    private void run(int size, boolean enableWrite, int repetitions) {
        // repetitions = 2 for standard test.
        
        if (db == null) {
            db = createDB(enableWrite);
        }
        
        Random random = new Random(1);
        int n = size;
        long t0, t1;
        Trans[] ts = new Trans[n];
        PrintStream out = c.out();
        
        out.println("---- " + Set.class.getName() + " ----");
        out.println("Runs set transactions. DB size: " + n + ".");
        
        byte[] empty = new byte[0];
        byte[] bytes = new byte[4];
        
        for (int i = 0; i < n; i++) {
            int anInt = random.nextInt();
            Bytes.intToBytesBE(anInt, bytes, 0);
            long[] key = Keys.toSegments(bytes);
            ts[i] = db.trans().put(key, empty).build();
        }
        
        // Warmup
        for (int i = 0; i < n / 2; i++) {
            db.execute(ts[i]);
        }
        
        db = null;
        
        db = createDB(enableWrite);
        out.println("Starting...");
        
        //splitCount = 0;
        t0 = System.nanoTime();
        for (int i0 = 0; i0 < repetitions; i0++) {
            for (int i1 = 0; i1 < n; i1++) {
                //ts[i].splitCount = 0;
                db.execute(ts[i1]);
                //splitCount += ts[i].splitCount;
            }
        }
        t1 = System.nanoTime();
        
        double totalTime = (t1 - t0) * 1e-9;
        long transCount = n * repetitions;
        
        c.report("transCount", transCount);
        c.report("time-per-trans", totalTime / transCount);
        c.report("total-time", totalTime);
        //c.report("splits-per-trans", (double) splitCount / (double) transCount);
    }
    
    public static void main(String[] args) throws Exception {
        Set.normal(new BasicCollector());
        
        System.out.println("*** Now running Set.noWritesToStream ****");
        Set.noWritesToStream(new BasicCollector());
        
        System.out.println("AGAIN!");
        Set.normal(new BasicCollector());
        
        System.out.println("*** Now running Set.noWritesToStream ****");
        Set.noWritesToStream(new BasicCollector());
    }
}

/*

======== 2013-07-07 ========
Running on Cissi instead. 
* 4.1 us, normal
* 3.0 us, noWritesToStream

======== 2013-04-29 ========
Testing on rose again. Runs slower from main() in this class then from dev.CorePerf.main() 
for some unknown reason.

======== 2013-04-04 ========
Testing on rose again.
* 29 us, normal test.
* 18 us, noWritesToStream

======== 2013-02-07 ========
Test on Rose. Now with a NullStream wrapped with a BufferedStream as output.
DB.Builder.retainForever() is used.
* 28 us, normal test (trans count 200k, retainForever (no reclaim), no evict).
* 19 us, noWritesToStream.

======== 2013-01-15 ========
Test on Rose. Now using DBStorageManager.
* 25.3 us, standard (normal()).
* 15.1 us, noWritesToStream().

======== 2012-12-13 ========
* Renamed class to "Set".
"time-per-trans" times, on Rose, Ubuntu, HotSpot build 1.7.0_02-b13.
* 25 us, 50k KVs. 
* Changed to 100k KVs in database.
* 27 us, 100k KVs
* 14 us, with noWritesToStream(), no serialization, no writes to stream.
* 25 us, normal test with NullStream instead of MemoryStream (instead of 27 us).
* 15 us, with noWritesToStream(), the "return;" in NodeStream.addNodes() moved to after transaction
    size is known.
* Changed normal test to use NullStream instead of MemoryStream 
    db = DB.create().clock(new TestClock()).evictBoss(new NoEvictBoss()).noReclaim()
    .stream(new NullStream()).start();
** 25 us, standard test.
* 33 us, (+8 us, +30%) if we use standard clock (System.currentTimeMillis()). Kurwa!
* 23 us, (-2 us). Some memory reuse (NodeStream.addNodesBuffer).
* 47 us, (+22 us). Run with JVM 1.5 (instead of HotSpot build 1.7.0_02-b13).
35% (8 us) of the time to serialize the nodes, holding DB.writeLock! Can we optimize? Separate thread?

======== 2012-10-25 ========
Running at 26 us per trans. Before adding support for value transformations.
The overhead of adding null key transformations and value transformations could not be 
measured with this test.

======== 2012-08-05 ========
Reproduced 25 us per trans. When I tested with "db.getStream().setWriteEnabled(false);"
the time is reduced with over 50% to 11 us. The serialization (NodeStream.addNodes()) takes 
most of the time. Note, we do not consider actual physical IO. An ordinary Java TreeMap runs a 
set in 3 us. And that is for serialized access only, and no persistent data structure. Great that 
our code is only 4x slower. Good for in-memory-only database.

======== 2012-08-05 ========
$ java -cp p/BergDB/ -server -Xmx1000m com.bergdb.db.perf.PerfDBSet
Runs set transactions. DB size: 50000.
* transCount: 400000
* outerCount: 4
* time-per-trans: 2.39008949725E-5
* total-time: 9.560357989
* splits-per-trans: 0.0474375

======== 2012-05-28 ========
After the "linear" refactoring it is a bit faster. It seems like the serialization is still a 
performance bottleneck for set operations.

$ java -cp p/BergDB/ -server -Xmx1000m com.bergdb.db.perf.PerfDBSet
Runs set transactions. DB size: 50000.
com.bergdb.db.perf.PerfDBSet.transCount = 400000
com.bergdb.db.perf.PerfDBSet.outerCount = 4
com.bergdb.db.perf.PerfDBSet.time-per-trans = 2.65079525775E-5
com.bergdb.db.perf.PerfDBSet.total-time = 10.603181031
com.bergdb.db.perf.PerfDBSet.splits-per-trans = 0.0480625

======== 2012-05-24: On Rose. With serialization to MemoryStream ========
com.bergdb.klong.PerfDBSet.time-per-trans = 3.0E-5
com.bergdb.db.perf.PerfDBSet.splits-per-trans = 0.087275

======== 2012-04-06: After refactoring to use DB.insertKlongs() ========
$ java -server -cp . com.bergdb.klong.PerfDBSet
Starting...
com.bergdb.klong.PerfDBSet.transCount = 2000000
com.bergdb.klong.PerfDBSet.outerCount = 20
com.bergdb.klong.PerfDBSet.time-per-trans = 1.0314691240000001E-5
com.bergdb.klong.PerfDBSet.total-time = 20.62938248
com.bergdb.klong.PerfDBSet.splits-per-trans = 0.083784
Note, no serialization at all (dummy node stream) was used for this test.
*/
