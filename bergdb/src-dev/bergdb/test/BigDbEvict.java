package bergdb.test;

import bergdb.common.Util;
import bergdb.core.*;
import bergdb.dag.EvictData;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.stream.MemoryStream;


/**
 * Tests large DB, but still in memory, with node evict.
 * 
 * @author Frans Lundberg
 */
public class BigDbEvict {
    
    @T("f perf")
    public static void t100KV(TestCollector c) throws InterruptedException {
        runTest(100, c);
    }
    
    @T("perf")
    public static void t1000KV(TestCollector c) throws InterruptedException {
        runTest(1000, c);
    }
    
    @T("f perf")
    public static void t10000KV(TestCollector c) throws InterruptedException {
        runTest(10*1000, c);
    }
    
    /** 
     * Returns memory usage in bytes.
     */
    private static long getMem() throws InterruptedException {
        System.gc();
        Thread.sleep(100);
        System.gc();
        Thread.sleep(100);
        System.gc();
        Runtime rt = Runtime.getRuntime();
        return rt.totalMemory() - rt.freeMemory();
    }
    
    private static double toMB(long bytes) {
        double mb = (double) (bytes / 1.0e6);
        mb = Math.round(mb * 100.0) / 100.0;
        return mb;
    }
    
    /**
     * Runs the test with a total of 100 MB payload in the DB and a variable 
     * number of KV.
     * 
     * @param n Number of KVs. 10, 100, 1000, 10000 are suitable.
     */
    private static void runTest(int n, TestCollector c) throws InterruptedException {
        MemoryStream ms = new MemoryStream();
        KTestClock clock = new KTestClock();
        Db db = Db.builder().mainStream(ms).clock(clock).evictBoss(new FixedDurationEvictBoss(10*1000000)).start();
        db.setRetainDuration(Long.MAX_VALUE);
        final int valueSize = 100 * 1000*1000 / n;
        
        long emptyMem = getMem();
        
        c.report("note", "Total size of all values is 100e6 bytes.");
        c.report("kv-count", n);
        c.report("empty-db-memory-use", toMB(emptyMem));
        
        int i = 0;
        for (String keyString : KeyFactory.shortRandomKeys(n)) {
            clock.setTime(1*1000000 + i);
            byte[] key = Util.toBytes(keyString);
            byte[] value = new byte[valueSize];
            value[0] = (byte) keyString.hashCode();
            Trans t = Trans.builder().put(key, value).build();
            db.execute(t);
            i++;
        }
        
        c.report("memory-used-after-100MB-of-data", toMB(getMem()));
        
        int nEvict = 500;
        long nano = System.nanoTime();
        long evictCount = 0;
        
        EvictData ed = new EvictData();
        for (int k = 0; k < nEvict; k++) {
            db.evict(ed);
            evictCount += ed.evictCount;
        }
        nano = System.nanoTime() - nano;
        
        c.report("time-per-evict-call", 1e-9*nano / nEvict);
        c.report("memory-use-after-evict", toMB(getMem()));
        c.report("stream-size-after-evict", toMB(db.getStreamLength()));
        c.report("evictCount", evictCount);
        
        // Tests db after evicts
        
        GetData gd2 = db.newGetData();
        gd2.evictData.enableEvict = false;
        byte[] expectedValue = new byte[valueSize];
        i = 0;
        
        for (String keyString : KeyFactory.shortRandomKeys(n)) {
            byte[] key = Util.toBytes(keyString);
            expectedValue[0] = (byte) keyString.hashCode();
            assert gd2.evictData.enableEvict == false;
            byte[] value = db.getOne(4*1000*1000, Keys.toSegments(key), gd2);
            Assert.assertArrayEquals("i=" + i + ", n=" + n, expectedValue, value);
            i++;
        }
        
        // --
        
        db = null;
        c.report("memory-use-after-db-null", toMB(getMem()));
        
        clock = new KTestClock();
        Db db2 = Db.builder().testSetup().mainStream(ms).clock(clock).build();
        long t = System.nanoTime();
        db2.start();
        t = System.nanoTime() - t;
        clock.setTime(3*1000000);
        
        c.report("startup-time", 1e-9 * t);
        c.report("memory-after-restart", toMB(getMem()));
        
        // Tests the restarted database (db2).
        
        expectedValue = new byte[valueSize];
        for (String keyString : KeyFactory.shortRandomKeys(n)) {
            byte[] key = Util.toBytes(keyString);
            expectedValue[0] = (byte) keyString.hashCode();
            
            assert gd2.evictData.enableEvict == false;
            byte[] value = db2.getOne(4*1000*1000, Keys.toSegments(key), gd2);
            Assert.assertArrayEquals(expectedValue, value);
        }
        
        // --
        
        db2 = null;
        ms = null;
        System.gc();
    }
}
