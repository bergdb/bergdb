package bergdb.test;

import bergdb.common.Util;
import bergdb.core.CoreTestClock;
import bergdb.core.Db;
import bergdb.core.Db.StartParams;
import bergdb.core.DbUtil;
import bergdb.core.KeyFactory;
import bergdb.core.NoEvictBoss;
import bergdb.core.StartupPosUpdater;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.dag.GetMany;
import bergdb.nanotest.Assert;
import bergdb.nanotest.TestCollector;
import static bergdb.nanotest.Assert.assertEquals;
import bergdb.nanotest.T;
import bergdb.stream.MemoryStream;

/**
 * Numbered scenarios tested. Referred to as ScenarioNNN.
 * 
 * @author Frans Lundberg
 */
public class ScenarioTester {
    
    /**
     * A restart scenario with 0.4M startup distances and 8 KVs 
     * with values of size 0.1M.
     */
    @T private static void testScenario100() {
        // Developed 2013-10.
        
        int n = 8;
        int startupDistance = 400 * 1000;
        int valueSize = 100 * 1000;
        
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        
        Db db = Db.builder()
                .mainStream(stream)
                .clock(clock)
                .startupDistance(startupDistance)
                .evictBoss(new NoEvictBoss())
                .start();
        
        for (int i = 0; i < n; i++) {
            byte[] value = new byte[valueSize];
            value[0] = (byte) i;
            clock.setTime(i * 100 + 5);
            
            Trans trans = Trans.builder().put("/k" + i, value).build();
            db.execute(trans);
        }
        
        long checksum1 = DbUtil.checksum(db);
        db.sync(SyncLevel.STRONG);
        
        // Restart
        
        stream = stream.copy();
        db = Db.builder()
                .mainStream(stream)
                .clock(clock)
                .evictBoss(new NoEvictBoss())
                .start();
        
        Assert.assertEquals(startupDistance, db.getStartupDistance());
        long checksum2 = DbUtil.checksum(db);  
        Assert.assertEquals(checksum1, checksum2);
    }
    
    @T public static void testScenario101() {
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(10);
        MemoryStream stream = new MemoryStream();
        byte[] value = new byte[100*1000];
        int size = 40;
        
        Db db = Db.builder().testSetup().mainStream(stream).clock(clock)
                .startupDistance(100*1000).start();
        
        for (int i = 0; i < size; i++) {
            long time = 1000 + i * 10;
            clock.setTime(time);
            Trans t = Trans.builder().put("" + i, value).build();
            db.execute(t);
        }
        
        GetMany g = db.newGetMany();
        g.lookupTime = Long.MAX_VALUE;
        g.startKey = null;
        db.getMany(g);
        Assert.assertTrue(g.result.size() == size || g.result.size() == size + 1);
    }
    
    /**
     * A scenario with a multi-klong key, an increase of startupPos and a restart.
     */
    @T private static void testScenario102() {        
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(10);
        MemoryStream stream = new MemoryStream();

        Db db = Db.builder().testSetup().mainStream(stream).clock(clock)
                .startupDistance(100*1000).start();
        
        db.execute(Trans.builder().put("/direct/key1", "v1"));
        db.execute(Trans.builder().put("/z1", new byte[200*1000]));
        db.execute(Trans.builder().put("/direct/key2", "v2"));     
        db.execute(Trans.builder().put("/z2", new byte[200*1000]));
        long sum1 = DbUtil.checksum(db, Long.MAX_VALUE, true);
        db.sync(SyncLevel.STRONG);
        
        //System.out.println("==== printGraph");
        //db.printGraph(System.out);
        db = null;
        
        // Restart
        stream = stream.copy();
        
        db = Db.builder().testSetup().mainStream(stream).clock(clock).build();
        db.start();
        long sum2 = DbUtil.checksum(db, Long.MAX_VALUE, true);
        
        assertEquals(100*1000, db.getStartupDistance());
        assertEquals(sum1, sum2);
        
        //System.out.println("==== printGraph after restart");
        //db.printGraph(System.out);
    }
    
    /**
     * Restart scenario with six large transactions.
     */
    @T private static void testScenario103() {
        //
        // NOTES issue. No index nodes at all in startup transactions.
        //
        
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(10);
        MemoryStream stream = new MemoryStream();
        int n = 6;
        int valueSize = 100*1000;

        Db db = Db.builder().testSetup().mainStream(stream).clock(clock)
                .startupDistance(10*1000).build();
        db.start();
        
        for (int i = 0; i < n; i++) {
            Trans trans = Trans.builder().put("/z" + i, new byte[valueSize + i]).build();
            db.execute(trans);
            //print103(db, trans);
        }
        
        long sum1 = DbUtil.checksum(db, Long.MAX_VALUE, true);
        db.sync(SyncLevel.STRONG);
        
        //System.out.println("==== printGraph");
        //db.printGraph(System.out);
        db = null;
        
        // Restart
        stream = stream.copy();
        db = Db.builder().testSetup().mainStream(stream).clock(clock).build();
        db.start();
        long sum2 = DbUtil.checksum(db, Long.MAX_VALUE, true);
        
        assertEquals(sum1, sum2);
    }
    
    @T private static void testScenario104() {
        // Demonstrates bug 141027:
        // bergdb.storage.StreamFormatException: Could not find super root node within startup node set.
        // at bergdb.core.DagStarter.createMapsAndSearchForSuperRoot(DagStarter.java:357)
        // ...
        // at bergdb.test.ScenarioTester.testScenario104(ScenarioTester.java:210)
        //
        
        MemoryStream stream = new MemoryStream();
        StartupPosUpdater.TestUpdater updater = new StartupPosUpdater.TestUpdater();
        long startupPos;
        
        Db db = Db.builder().testSetup().mainStream(stream).clock(new CoreTestClock()).build();
        db.internal().setStartupPosUpdater(updater);
        db.start();
        
        Trans t1 = Trans.builder().put("/key1", "v1").build();
        db.execute(t1);
        
        startupPos = t1.pos;
        updater.setNextPos(startupPos);
        Trans t2 = Trans.builder().put("/key2", "v2").build();
        db.execute(t2);
        long sum1 = DbUtil.checksum(db);
        db.sync(SyncLevel.ORDINARY);
        
        // Restart
        
        db = Db.builder().testSetup().mainStream(stream.copy()).build();
        
        StartParams params = new StartParams();
        params.startupDistance = 20*1000000;
        params.startupPos = startupPos;
        
        db.start(params, Db.PrintStartListener.DO_NOTHING);
        long sum2 = DbUtil.checksum(db);
        db.stop();
        
        Assert.assertEquals(sum1, sum2);
    }
    
    @T private static void testScenario105() {
        // Demonstrates bug 141027:
        // bergdb.storage.StreamFormatException: Bad spos (-1) of Pointer 3 from key node
        // At startup time.

        MemoryStream stream = new MemoryStream();
        StartupPosUpdater.TestUpdater updater = new StartupPosUpdater.TestUpdater();
        long startupPos;
        
        Db db = Db.builder().testSetup().mainStream(stream).clock(new CoreTestClock()).build();
        db.internal().setStartupPosUpdater(updater);
        db.start();
        
        Trans t1 = Trans.builder().put("/dir100/key1", "v1").build();
        db.execute(t1);
        
        Trans t2 = Trans.builder().put("/dir200/key2", "v2").build();
        db.execute(t2);
        
        startupPos = t2.pos;
        updater.setNextPos(startupPos);
        Trans t3 = Trans.builder().put("/z", "zzz5").build();
        db.execute(t3);
        db.sync(SyncLevel.ORDINARY);
        long sum1 = DbUtil.checksum(db);
        db.stop();
        
        // Restart
        
        StartParams params = new StartParams();
        params.startupDistance = 20*1000000;
        params.startupPos = startupPos;
        
        db = Db.builder().testSetup().mainStream(stream.copy()).build();
        db.start(params, Db.StartListener.DO_NOTHING);
        long sum2 = DbUtil.checksum(db);
        db.stop();
        
        Assert.assertEquals(sum1, sum2);
    }
    
    @T private static void testScenario106(TestCollector c) throws InterruptedException {
        int n = 6;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(5*1000).start();
        final int valueSize = 1000;
        
        int i = 0;
        for (String keyString : KeyFactory.shortRandomKeys(n)) {
            clock.setTime(1000 + i);
            byte[] key = Util.toBytes(keyString);
            byte[] value = new byte[valueSize];
            value[0] = (byte) keyString.hashCode();
            Trans t = Trans.builder().put(key, value).build();
            db.execute(t);
            i++;
        }
        
        System.out.println("---- printGraph ----");
        db.printGraph(System.out);
        long sum1 = DbUtil.checksum(db);
        
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        
        // Restart
        
        db = Db.builder().testSetup(stream).build();
        db.start();
        long sum2 = DbUtil.checksum(db);
        db.stop();
        
        Assert.assertEquals(sum1, sum2);
        
    }
}
