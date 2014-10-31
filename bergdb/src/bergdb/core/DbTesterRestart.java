package bergdb.core;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * Class that tests restarting Db from an in-memory stream.
 * Typically a short startupDistance is used and eviction is often disabled.
 * 
 * @author Frans Lundberg
 */
public class DbTesterRestart {

    @T
    public static void test0() {
        // Simple restart, Db with one single value.
        
        byte[] value;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().mainStream(stream).clock(clock).start();
        clock.setTime(10);
        Trans trans = Trans.builder().put("admin1", "Sanna").build();
        db.execute(trans);
        db.sync(SyncLevel.ORDINARY);
        long tt = trans.time;
        stream = stream.copy();
        
        db = null;
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        
        value = DbUtil.get(db2, Long.MAX_VALUE, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, tt-1, Util.toBytes("admin1"));
        Assert.assertNull(value);
        
        value = DbUtil.get(db2, tt, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
    }
    
    @T
    public static void longerThanStartup() {
        // Stream is longer than startupDistance, single key, value updated.
        
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(2);
        Db db = Db.builder().mainStream(stream).clock(clock).startupDistance(10*1000)
                .evictBoss(new NoEvictBoss()).start();
        byte[] bytes = new byte[1000];
        
        for (int i = 0; i < 20; i++) {
            clock.setTime(1000000 + i*10);
            bytes[0] = (byte) i;
            Trans trans = Trans.builder().put("k", bytes).build();
            db.execute(trans);
        }
        db.sync(SyncLevel.ORDINARY);
        
        db = null;
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        Assert.assertNull(DbUtil.get(db2, 5, "k"));
        
        for (int i = 0; i < 20; i++) {
            long lookupTime = 1000000 + i*10 + 5;
            byte[] v = DbUtil.get(db2, lookupTime, "k");
            Assert.assertTrue(v != null);
            Assert.assertEquals(i, v[0]);
        }
    }
    
    /**
     * Db should remember startupDistance after restart of initial state database.
     */
    @T
    private static void dbShouldRememberStartupDistance() throws InterruptedException {
        int startupDistance = 400 * 1000;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        
        Db db = Db.builder()
                .mainStream(stream)
                .clock(clock)
                .startupDistance(startupDistance)
                .start();
        
        Assert.assertEquals("before restart", startupDistance, db.getStartupDistance());
        db.sync(SyncLevel.STRONG);
        
        // Restart
        
        stream = stream.copy();
        db = Db.builder()
                .mainStream(stream)
                .clock(clock)
                .start();
        
        Assert.assertEquals("after restart", startupDistance, db.getStartupDistance());
    }
    
    /**
     * Db should remember startupDistance after one user transaction.
     */
    @T
    private static void dbShouldRememberStartupDistance2() throws InterruptedException {
        int startupDistance = 400 * 1000;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        
        Db db = Db.builder()
                .mainStream(stream)
                .clock(clock)
                .startupDistance(startupDistance)
                .start();
        
        db.execute(Trans.builder().put("key", "value"));
        Assert.assertEquals("before restart", startupDistance, db.getStartupDistance());
        db.sync(SyncLevel.STRONG);
        
        // Restart
        
        stream = stream.copy();
        db = Db.builder()
                .mainStream(stream)
                .clock(clock)
                .start();
        
        Assert.assertEquals("after restart", startupDistance, db.getStartupDistance());
    }
    
    /** Simplest possible delete-and-restart test. */
    @T private static void testDelete1() {
        AppendOnlyStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(s).clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().put("k1", "k1-value"));
        
        clock.setTime(20);
        db.execute(Trans.builder().delete("k1"));
        db.sync(SyncLevel.ORDINARY);
        
        //db.printGraph(System.out);
        //db.getStream().print(System.out);
        
        db = null;
        
        // Restart
        
        Db db2 = Db.builder().testSetup().mainStream(s).start();        
        //db2.printGraph(System.out);
        
        byte[] v1 = DbUtil.get(db2, 15, "k1");
        Assert.assertArrayEquals(Util.toBytes("k1-value"), v1);
        v1 = DbUtil.get(db2, 25, "k1");
        Assert.assertNull(v1);
    }
    
    /** Multiple deletes in a single transaction. */
    @T private static void testDelete2() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(s).clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().put("k1", "k1-value").put("k2", "k2-value"));
        
        clock.setTime(20);
        db.execute(Trans.builder().delete("k1").delete("k2").delete("kk").put("k3", "k3-value").build());
        
        long sum1 = DbUtil.checksum(db);
        db.sync(SyncLevel.ORDINARY);
        
        // Restart
        
        Db db2 = Db.builder().testSetup().mainStream(s.copy()).start();        
        long sum2 = DbUtil.checksum(db2);
        
        Assert.assertEquals(sum1, sum2);
    }
}
