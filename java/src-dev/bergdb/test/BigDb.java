package bergdb.test;

import bergdb.core.*;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * Tests large DB (100 MB), still in memory.
 * Tests with different number of KVs: 10, 100, 1000, 10000, 100000.
 * 
 * @author Frans Lundberg
 */
public class BigDb {
    
    @Nano("f perf")
    public static void t10kv(TestEnvironment c) throws InterruptedException {
        runTest(10, c);
    }
    
    @Nano("f perf")
    public static void t100kv(TestEnvironment c) throws InterruptedException {
        runTest(100, c);
    }
    
    @Nano("f perf")
    public static void t1000kv(TestEnvironment c) throws InterruptedException {
        runTest(1000, c);
    }
    
    @Nano("f perf")
    public static void t10000kv(TestEnvironment c) throws InterruptedException {
        runTest(10*1000, c);
    }
    
    @Nano("perf")
    public static void t100000kv(TestEnvironment c) throws InterruptedException {
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
     * number of KVs.
     * 
     * @param n  Number of KVs. 10, 100, 1000, 10000 are suitable.
     */
    private static void runTest(int n, TestEnvironment c) throws InterruptedException {
        MemoryStream ms = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(ms).clock(clock).start();
        // At most 8 MiB, L4 (bergdb 024-24): at 10 KVs 8,388,608 bytes, not 10 MB.
        final int valueSize = Math.min(100 * 1000*1000 / n, Db.MAX_VALUE_BYTES);
        
        long emptyMem = getMem();
        
        c.report("note", "Stores KVs in an in-memory db (MemoryStream), total value size " +
        		"is 100e6 bytes.");
        c.report("kv-count", n);
        c.report("empty-db-memory-use", toMB(emptyMem));
        
        int i = 0;
        for (String keyString : KeyFactory.shortRandomKeys(n)) {
            clock.setTime(1*1000000 + i);
            byte[] value = new byte[valueSize];
            value[0] = (byte) keyString.hashCode();
            Trans t = db.trans().put(keyString, value).build();
            db.execute(t);
            i++;
        }
        
        long sum1 = DbUtil.checksum(db);
        
        c.report("memory-used-after-100MB-of-data", getMem());
        
        db.sync(SyncLevel.ORDINARY);
         
        //System.out.println("\n==== db");
        //db.printDag(System.out);
        
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
        
        //System.out.println("\n==== db2");
        //db2.printDag(System.out);
        
        // Tests the restarted database (db2).
        
        byte[] expectedValue = new byte[valueSize];
        int index = 0;
        
        for (String keyString : KeyFactory.shortRandomKeys(n)) {
            expectedValue[0] = (byte) keyString.hashCode();
            byte[] value = DbUtil.get(db2, 4*1000*1000, keyString);
            Assert.assertArrayEquals(
                    "index=" + index + ", keyString=" + keyString, expectedValue, value);
            index++;
        }
        
        long sum2 = DbUtil.checksum(db2);
        
        db2.sync(SyncLevel.ORDINARY);
        db2.stop();
        db2 = null;
        ms = null;
        System.gc();
        
        Assert.assertEquals(sum1, sum2);
    }
}
