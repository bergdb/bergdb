package bergdb.test;

import bergdb.common.Util;
import bergdb.core.CoreTestClock;
import bergdb.core.Db;
import bergdb.core.Db.ExecuteData;
import bergdb.core.Db.StartParams;
import bergdb.core.DbUtil;
import bergdb.core.StartupPosUpdater;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.dag.GetMany;
import bergdb.nanotest.Assert;
import bergdb.nanotest.TestEnvironment;
import static bergdb.nanotest.Assert.assertEquals;
import bergdb.nanotest.Nano;
import bergdb.stream.MemoryStream;

/**
 * Numbered scenarios that can be references. Referred to as ScenarioNNN.
 * Written test scenarios are not much changed; they should be thought of
 * as static, but may have to evolve as the database evolves.
 * 
 * @author Frans Lundberg
 */
public class ScenarioTester {
    
    /**
     * A restart scenario with 0.4M startup distances and 8 KVs 
     * with values of size 0.1M.
     */
    @Nano
    private static void scenario100() {
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
                .noEvict()
                .start();
        
        for (int i = 0; i < n; i++) {
            byte[] value = new byte[valueSize];
            value[0] = (byte) i;
            clock.setTime(i * 100 + 5);
            
            Trans trans = db.trans().put("/k" + i, value).build();
            db.execute(trans);
        }
        
        long checksum1 = DbUtil.checksum(db);
        db.sync(SyncLevel.STRONG);
        
        //db.getStream().print(System.out);
        
        // Restart
        
        stream = stream.copy();
        db = Db.builder()
                .mainStream(stream)
                .clock(clock)
                .noEvict()
                .start();
        
        Assert.assertEquals(startupDistance, db.getStartupDistance());
        long checksum2 = DbUtil.checksum(db);  
        Assert.assertEquals(checksum1, checksum2);
    }

    /**
     * Scenario with a 100k startup distance and 40 KVs 
     * written one by one to the stream. Each KV has a value of size 10k.
     */
    @Nano
    private static void scenario101() {
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(10);
        MemoryStream stream = new MemoryStream();
        byte[] value = new byte[10*1000];
        int n = 40;
        
        Db db = Db.builder().testSetup().mainStream(stream)
                .clock(clock).noEvict().startupDistance(100*1000)
                .start();
        
        for (int i = 0; i < n; i++) {
            long time = 1000 + i * 10;
            clock.setTime(time);
            String key = key101(i);
            Trans t = db.trans().put(key, value).build();
            db.execute(t);
        }
        
        GetMany g = db.newGetMany();
        g.lookupTime = Long.MAX_VALUE;
        g.startKey = null;
        db.getMany(g);
        
        Assert.assertTrue(g.result.size() == n);
    }
    
    /**
     * Playing with 101.
     */
    private static void scenario101b() {
        // Removing Db.store()/addUnstoredDescendants()... testing. Bad pointer at i=32.
        
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(10);
        MemoryStream stream = new MemoryStream();
        byte[] value = new byte[10*1000];
        int n = 16;
        
        Db db = Db.builder().testSetup().mainStream(stream)
                .clock(clock).noEvict().startupDistance(100*1000)
                .maxNodeSize8()
                .start();
        
        Trans.Listener listener = new Trans.Listener() {
            public void transExecuted(ExecuteData x) {
                System.out.println("t" + x.trans.time + ", tpos:" + x.trans.pos 
                        + ", start:" + x.transInfo.startupPos);
                for (int i = 0; i < x.transNodes.size(); i++) {
                    System.out.println(x.transNodes.get(i));
                }
            }
        };
        
        for (int i = 0; i < n; i++) {
            long time = 100 + i;
            clock.setTime(time);
            String key = key101(i);
            
            System.out.println("\n== i:" + i + ", " + key + " ==");
            
            Trans t = db.trans().put(key, value).build();
            t.listener = listener;
            
            db.execute(t);
        }
        
        System.out.println("==== db ====");
        db.printDag(System.out);
        
        GetMany g = db.newGetMany();
        g.lookupTime = Long.MAX_VALUE;
        g.startKey = null;
        db.getMany(g);
        
        Assert.assertTrue(g.result.size() == n);
    }
    
    private static String key101(int i) {
        String key = "" + i;
        if (i < 10) {
            key = "0" + key;
        }
        return "k" + key;
    }
    
    /**
     * A scenario with a multi-klong key, an increase of startupPos and a restart.
     */
    @Nano
    private static void scenario102() {        
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(10);
        MemoryStream stream = new MemoryStream();

        Db db = Db.builder().testSetup().mainStream(stream).clock(clock)
                .startupDistance(100*1000).start();
        
        db.execute(db.trans().put("/direct/key1", "v1"));
        db.execute(db.trans().put("/z1", new byte[200*1000]));
        db.execute(db.trans().put("/direct/key2", "v2"));     
        db.execute(db.trans().put("/z2", new byte[200*1000]));
        long sum1 = DbUtil.checksum(db, Long.MAX_VALUE, true, true);
        db.sync(SyncLevel.STRONG);
        
        //System.out.println("==== printGraph");
        //db.printGraph(System.out);
        db = null;
        
        // Restart
        stream = stream.copy();
        
        db = Db.builder().testSetup().mainStream(stream).clock(clock).build();
        db.start();
        long sum2 = DbUtil.checksum(db, Long.MAX_VALUE, true, true);
        
        assertEquals(100*1000, db.getStartupDistance());
        assertEquals(sum1, sum2);
        
        //System.out.println("==== printGraph after restart");
        //db.printGraph(System.out);
    }
    
    /**
     * Restart scenario with six large transactions.
     */
    @Nano
    private static void scenario103() {
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(10);
        MemoryStream stream = new MemoryStream();
        int n = 6;
        int valueSize = 100*1000;

        Db db = Db.builder().testSetup().mainStream(stream).clock(clock)
                .startupDistance(10*1000).build();
        db.start();
        
        for (int i = 0; i < n; i++) {
            Trans trans = db.trans().put("/z" + i, new byte[valueSize + i]).build();
            db.execute(trans);
        }
        
        long sum1 = DbUtil.checksum(db, Long.MAX_VALUE, true, true);
        db.sync(SyncLevel.STRONG);
        
        db = null;
        
        // Restart
        stream = stream.copy();
        db = Db.builder().testSetup().mainStream(stream).clock(clock).build();
        db.start();
        long sum2 = DbUtil.checksum(db, Long.MAX_VALUE, true, true);
        
        assertEquals(sum1, sum2);
    }
    
    @Nano
    private static void scenario104() {        
        MemoryStream stream = new MemoryStream();
        StartupPosUpdater.TestUpdater updater = new StartupPosUpdater.TestUpdater();
        long startupPos;
        
        CoreTestClock clock = new CoreTestClock();
        Db db1 = Db.builder().testSetup().mainStream(stream).clock(clock).build();
        db1.internal().setStartupPosUpdater(updater);
        db1.start();
        
        clock.setTime(100);
        Trans t1 = db1.trans().put("/key1", "v1").build();
        db1.execute(t1);
        
        clock.setTime(200);
        startupPos = t1.pos;
        updater.setNextPos(startupPos);
        Trans t2 = db1.trans().put("/key2", "v2").build();
        db1.execute(t2);
        long sum1 = DbUtil.checksum(db1);
        db1.sync(SyncLevel.ORDINARY);
        
        // Restart
        
        Db db2 = Db.builder().testSetup().mainStream(stream.copy()).build();
        
        StartParams params = new StartParams();
        params.startupDistance = 20*1000000;
        params.startupPos = startupPos;
        
        db2.start(params, Db.PrintStartListener.DO_NOTHING);
        long sum2 = DbUtil.checksum(db2);
        
        //System.out.println("== db1:");
        //db1.printGraph(System.out);
        //System.out.println("== db2:");
        //db2.printGraph(System.out);
        
        //db2.getStream().print(System.out);
        
        db1.stop();
        db2.stop();
        
        Assert.assertEquals("checksum", sum1, sum2);
    }
    
    @Nano
    private static void scenario105() {
        // Demonstrates bug 141027:
        // bergdb.storage.StreamFormatException: Bad spos (-1) of Pointer 3 from key node
        // At startup time.

        MemoryStream stream = new MemoryStream();
        StartupPosUpdater.TestUpdater updater = new StartupPosUpdater.TestUpdater();
        long startupPos;
        
        Db db = Db.builder().testSetup().mainStream(stream).clock(new CoreTestClock()).build();
        db.internal().setStartupPosUpdater(updater);
        db.start();
        
        Trans t1 = db.trans().put("/dir100/key1", "v1").build();
        db.execute(t1);
        
        Trans t2 = db.trans().put("/dir200/key2", "v2").build();
        db.execute(t2);
        
        startupPos = t2.pos;
        updater.setNextPos(startupPos);
        Trans t3 = db.trans().put("/z", "zzz5").build();
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
    
    /**
     * Two transactions with multi-klong keys: t1, t2. t2 sets startup pos to t1.pos.
     */
    @Nano
    private static void scenario106(TestEnvironment c) throws InterruptedException {
        
        //System.out.println("======== testScenario106 ========");
        
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        StartupPosUpdater.TestUpdater updater = new StartupPosUpdater.TestUpdater();
        
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(5*1000).start();
        db.internal().setStartupPosUpdater(updater);
        
        Trans t1 = db.trans().put("/key1-suffix1", Util.toBytes("v1")).build();
        db.execute(t1);
        
        updater.setNextPos(t1.pos);
        Trans t2 = db.trans().put("/key2-suffix2", Util.toBytes("v2")).build();
        db.execute(t2);
        
        //System.out.println("---- printGraph ----");
        //db.printGraph(System.out);
        long sum1 = DbUtil.checksum(db);
        
        db.sync(SyncLevel.ORDINARY);
        
        //System.out.println("\nSTREAM: [[");
        //db.getStream().print(System.out);
        //System.out.println("]]");
        
        db.stop();
        
        // Restart
        
        db = Db.builder().testSetup(stream).build();
        db.start();
        
        //System.out.println("---- printGraph ----");
        //db.printGraph(System.out);
        
        long sum2 = DbUtil.checksum(db);
        db.stop();
        
        Assert.assertEquals(sum1, sum2);
    }
}
