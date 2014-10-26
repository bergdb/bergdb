package bergdb.test;

import bergdb.core.CoreTestClock;
import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.NoEvictBoss;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.dag.GetMany;
import bergdb.nanotest.Assert;
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
        
        //System.out.println("==== printGraph after restart");
        //db.printGraph(System.out);
    }
    
    @T private static void testScenario104() {
        // Trying to recreate the issue with stream pointer == -1.
        
        
    }
}
