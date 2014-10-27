package bergdb.test;

import bergdb.common.Util;
import bergdb.core.*;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;
import bergdb.stream.MemoryStream;

/**
 * Tests large DB (100 MB), still in memory.
 * Tests with different number of KVs: 10, 100, 1000, 10000, 100000.
 * 
 * @author Frans Lundberg
 */
public class BigDb {
    
    // TODO A. Make as-simple-as-possible version of t10kv, and fix it!
    
    @T("f perf")
    public static void t10kv(TestCollector c) throws InterruptedException {
        runTest(10, c);
    }
    
    @T("perf")
    public static void t100kv(TestCollector c) throws InterruptedException {
        runTest(100, c);
    }
    
    @T("perf")
    public static void t1000kv(TestCollector c) throws InterruptedException {
        runTest(1000, c);
    }
    
    @T("f perf")
    public static void t10000kv(TestCollector c) throws InterruptedException {
        runTest(10*1000, c);
    }
    
    @T("perf")
    public static void t100000kv(TestCollector c) throws InterruptedException {
        runTest(100*1000, c);
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
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(ms).clock(clock).start();
        final int valueSize = 100 * 1000*1000 / n;
        
        long emptyMem = getMem();
        
        c.report("note", "Stores KVs in an in-memory db (MemoryStream), total value size " +
        		"is 100e6 bytes.");
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
        
        c.report("memory-used-after-100MB-of-data", getMem());
        
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        c.report("memory-use-after-db-null", toMB(getMem()));
        
        Db db2 = Db.builder().testSetup(ms).build();
        long t = System.nanoTime();
        db2.start();
        t = System.nanoTime() - t;
        clock.setTime(3*1000000);
        
        c.report("startup-time", 1e-9 * t);
        c.report("memory-after-restart", toMB(getMem()));
        
        // Tests the restarted database (db2).
        
        byte[] expectedValue = new byte[valueSize];
        
        for (String keyString : KeyFactory.shortRandomKeys(n)) {
            byte[] key = Util.toBytes(keyString);
            expectedValue[0] = (byte) keyString.hashCode();
            
            byte[] value = DbUtil.get(db2, 4*1000*1000, key);
            Assert.assertArrayEquals(expectedValue, value);
        }
        
        db2.sync(SyncLevel.ORDINARY);
        db2.stop();
        db2 = null;
        ms = null;
        System.gc();
    }
}
