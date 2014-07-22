package bergdb.core;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.stream.MemoryStream;

// TODO LATER. Work in progress... Much more we could do.

/**
 * Class that tests restarting Db from an in-memory stream.
 * Typically a short startupDistance is used and eviction is often disabled.
 * 
 * @author Frans Lundberg
 */
public class DbTesterRestart {

    @T
    public static void simple0() {
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
}
