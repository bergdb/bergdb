package bergdb.test;

import java.io.PrintStream;

import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.FixedDurationEvictBoss;
import bergdb.core.IEvictBoss;
import bergdb.core.CoreTestClock;
import bergdb.core.KeyFactory;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;
import bergdb.stream.MemoryStream;

/**
 * "Crazy" tests. Different operations are mixed, different types of keys
 * and ordering of operations.
 * An in-memory stream is used. Max size around 100 MB.
 * Eviction is done based on a fixed cache duration of 20 MB to make sure we get some
 * cache evictions. Startup distance is 10 MB. A test clock is used. 
 * The whole thing should be deterministic since no clock or Runtime.freeMemory is used, 
 * just deterministic input, I believe.
 * 
 * @author Frans Lundberg
 */
public class Crazy {
    
    @T("f")
    public static void run(TestEnvironment c) {
        PrintStream out = c.out();
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        IEvictBoss boss = new FixedDurationEvictBoss(20*1000000);
        int n = 50;
        
        out.println("---- Crazy.run ----");
        
        Db db = Db.builder().clock(clock).startupDistance(10*1000000).mainStream(s)
                .evictBoss(boss).start();
        
        // Creates some KVs, 0 - 999.
        
        for (int i = 0; i < n; i++) {
            clock.setTime(1000000 + i * 10 + 1);
            Trans t = db.trans().put(KeyFactory.crazyKey(i), Util.toBytes("v" + i)).build();
            db.execute(t);
        }
        db.sync(0, SyncLevel.ORDINARY);
        
        out.println("Wrote 1000 crazy kvs, stream size: " + db.getStreamLength() + ".");
        
        // Checks keys 0 - 999.
        
        for (int i = 0; i < n; i++) {
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, KeyFactory.crazyKey(i));
            Assert.assertEquals("i=" + i, "v" + i, Util.toString(value));
        }
        
        out.println("Deletes some of the keys.");
        
        for (int i = 0; i < n; i += 10) {
            clock.setTime(2000000 + i * 10 + 1);
            Trans t = db.trans().delete(KeyFactory.crazyKey(i)).build();
            db.execute(t);
        }
        
        // Checks that they were removed.
        
        for (int i = 0; i < n; i += 10) {
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, KeyFactory.crazyKey(i));
            Assert.assertNull(value);
        }
        
        // Checks that they existed before they were removed.
        
        for (int i = 0; i < n; i += 10) {
            byte[] value = DbUtil.get(db, 2000000 - 1, KeyFactory.crazyKey(i));
            Assert.assertEquals("i=" + i, "v" + i, Util.toString(value));
        }
        
        // Adds deleted keys back again.
        
        for (int i = 0; i < n; i += 10) {
            clock.setTime(3000000 + i * 10 + 1);
            Trans t = db.trans().put(KeyFactory.crazyKey(i), Util.toBytes("v" + i)).build();
            db.execute(t);
        }
        
        // Checks all keys, 0 - 999.
        
        for (int i = 0; i < n; i++) {
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, KeyFactory.crazyKey(i));
            Assert.assertEquals("i=" + i, "v" + i, Util.toString(value));
        }
        
        out.println("Overwrites some keys with large values.");
        
        byte[] value;
        clock.setTime(4000000);
        Trans.Builder b = db.trans();
        
        value = new byte[1*1000000];
        value[0] = 1;
        b.put(KeyFactory.crazyKey(100), value).build();
        
        value = new byte[1*1000000];
        value[0] = 2;
        b.put(KeyFactory.crazyKey(101), value).build();
        
        value = new byte[1*1000000];
        value[0] = 3;
        b.put(KeyFactory.crazyKey(123), value).build();
        
        db.execute(b.build());
        
        // Checks last KVs written.
        
        value = DbUtil.get(db, Long.MAX_VALUE, KeyFactory.crazyKey(100));
        Assert.assertEquals("key 100", 1*1000000, value.length);
        Assert.assertEquals(1, value[0]);
        
        value = DbUtil.get(db, Long.MAX_VALUE, KeyFactory.crazyKey(101));
        Assert.assertEquals("key 101", 1*1000000, value.length);
        Assert.assertEquals(2, value[0]);
        
        value = DbUtil.get(db, Long.MAX_VALUE, KeyFactory.crazyKey(123));
        Assert.assertEquals("key 123", 1*1000000, value.length);
        Assert.assertEquals(3, value[0]);
        
        // ----
        out.println("A very large transaction.");
        clock.setTime(5*1000000);
        b = db.trans();
        b.put(KeyFactory.crazyKey(1001), new byte[20*1000000]);
        db.execute(b.build());
        db.sync(0, SyncLevel.ORDINARY);
        
        out.println("Stream size: " + db.getStreamLength() + ".");
        
        // ----
        int keySize = 10*1000;
        out.println("An unsusually large key, size: " + keySize + " bytes.");
        clock.setTime(6*1000000);
        long streamSize1 = db.getStreamLength();
        b = db.trans();
        byte[] key = new byte[keySize];
        key[0] = 44;
        b.put(key, new byte[3]);
        db.execute(b.build());
        long streamSize2 = db.getStreamLength();
        double keySizeOverheadFactor = ((double)(streamSize2 - streamSize1)) / ((double) keySize);
        c.report("keySizeOverheadFactor", keySizeOverheadFactor);
        
        value = DbUtil.get(db, Long.MAX_VALUE, key);
        Assert.assertEquals(3, value.length);
        db.sync(0, SyncLevel.ORDINARY);
        
        // ---- Restarting 
        
        db = null;
        System.gc();
        s = s.copy();    
            // Makes sure we do not use a stream that may be closed soon (when db garbage collected).
        
        out.println("Restarting database");
        db = Db.builder().clock(clock).startupDistance(10*1000000).mainStream(s)
                .evictBoss(boss).build();
        long t = System.nanoTime();
        db.start();
        t = System.nanoTime() - t;
        c.report("startupTime", t*1e-9);
        
        // Checks some keys, 124 - 999.
        
        for (int i = 124; i < n; i++) {
            value = DbUtil.get(db, Long.MAX_VALUE, KeyFactory.crazyKey(i));
            Assert.assertEquals("i=" + i, "v" + i, Util.toString(value));
        }
    }
}
