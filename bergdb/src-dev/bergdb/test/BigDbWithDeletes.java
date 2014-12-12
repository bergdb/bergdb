package bergdb.test;

import bergdb.common.Util;
import bergdb.core.*;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.stream.MemoryStream;

/**
 * Tests large DB with deletes. The database is stored in memory 
 * (..stream.MemoryStream).
 * 
 * @author Frans Lundberg
 */
public class BigDbWithDeletes {    
    @Nano("f perf")
    public static void test100MB10KV(TestEnvironment c) throws InterruptedException {
        run(10, c);
    }
    
    @Nano("f perf")
    public static void test100MB100KV(TestEnvironment c) throws InterruptedException {
        run(100, c);
    }
    
    @Nano("f perf")
    public static void test100MB1000KV(TestEnvironment c) throws InterruptedException {
        run(1000, c);
    }
    
    @Nano("perf")
    public static void test100MB10000KV(TestEnvironment c) throws InterruptedException {
        run(10000, c);
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
    
    private static double toMb(long bytes) {
        double mb = (double) (bytes / 1.0e6);
        mb = Math.round(mb * 100.0) / 100.0;
        return mb;
    }
    
    /**
     * @param n Number of KVs. 10, 100, 1000, 10000 are suitable.
     */
    private static void run(int n, TestEnvironment c) throws InterruptedException {
        MemoryStream ms = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().mainStream(ms).clock(clock).evictBoss(new NoEvictBoss()).start();
        final int valueSize = 100 * 1000*1000 / n;
        
        c.report("empty-db-memory-use", toMb(getMem()));
        
        c.report("kv-count", n);
        
        for (int i = 0; i < n; i++) {
            clock.setTime(1*1000000 + i);
            byte[] key = KeyFactory.intKey(i);
            byte[] value = new byte[valueSize];
            value[0] = (byte) Util.toString(key).hashCode();
            Trans t = db.trans().put(key, value).build();
            db.execute(t);
        }
        
        c.report("memory-used-after-100MB-of-data", toMb(getMem()));
        
        // Erases some values.
        
        for (int i = 0; i < n; i += 4) {
            clock.setTime(2*1000000 + i);
            byte[] key = KeyFactory.intKey(i);
            Trans t = db.trans().delete(key).build();
            db.execute(t);
        }
        
        c.report("memory-used-after-delete", toMb(getMem()));
        
        // Tests database after some deletes.
        
        byte[] expectedValue = new byte[valueSize];
        
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.intKey(i);
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
            
            if (i % 4 == 0) {
                Assert.assertNull(value);
            } else {
                if (value == null) {
                    throw new RuntimeException("value == null, i = " + i + ".");
                }
                
                expectedValue[0] = (byte) Util.toString(key).hashCode();
                Assert.assertEquals("i=" + i, expectedValue[0], value[0]);
            }
        }
        
        db = null;
        c.report("memory-use-after-db-null", toMb(getMem()));
        
        Db db2 = Db.builder().testSetup().mainStream(ms).build();
        long t = System.nanoTime();
        db2.start();
        t = System.nanoTime() - t;
        clock.setTime(3*1000000);
        
        c.report("startup-time", 1e-9 * t);
        c.report("memory-after-restart", toMb(getMem()));
        
        // Tests the restarted database (db2).
        
        expectedValue = new byte[valueSize];
        
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.intKey(i);
            byte[] value = DbUtil.get(db2, Long.MAX_VALUE, key);
            
            if (i % 4 == 0) {
                if (value != null) {
                    throw new RuntimeException("Expected null value, got non-null for i = " + i + ".");
                }
            } else {
                if (value == null) {
                    throw new RuntimeException("value == null, i = " + i + ".");
                }
                
                expectedValue[0] = (byte) Util.toString(key).hashCode();
                Assert.assertEquals("i=" + i, expectedValue[0], value[0]);
            }
        }
        
        db2 = null;
        ms = null;
        System.gc();
    }
}
