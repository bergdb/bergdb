package bergdb.test;

import static bergdb.nanotest.Assert.assertEquals;
import bergdb.core.CoreTestClock;
import bergdb.core.DagComparison;
import bergdb.core.Db;
import bergdb.core.Db.ExecuteData;
import bergdb.core.DbUtil;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.dag.GetMany;
import bergdb.dag.Node;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.MemoryStream;

/**
 * Numbered scenarios that can be referenced. Referred to as ScenarioNNN, or SNNN.
 * Written test scenarios are not much changed; they should be thought of
 * as static, but may have to evolve slowly as the database evolves.
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
    
    /**
     * Scenario with few transaction that demonstrates a dag diff
     * before we fixed an issue.
     */
    @SuppressWarnings("unused")
    @Nano
    private static void scenario107() throws InterruptedException {
        // Created 2015-05.
        
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(10*1000).start();
        
        String[] keys = new String[] {
                "/seven1/seven2/key1",
                "/seven1/seven2/seven3/key2",
                "/whatever1"};
        
        int[] sizes = new int[] {
                5002, 
                5003, 
                5004};
        
        Trans[] trans = new Trans[keys.length];
        
        Trans.Listener printListener = new Trans.Listener() {
            public void transExecuted(ExecuteData x) {
                System.out.println("== t" + x.trans.tt + ", tpos:" + x.trans.tpos 
                        + ", stpos:" + x.transInfo.startupPos);
                int size = x.transNodes.size();
                for (int i = 0; i < size; i++) {
                    System.out.println(x.transNodes.get(i));
                }
                
                if (x.transInfo.gotDirtyNodes.size() > 0) {
                    System.out.print("Got dirty: ");
                    for (Node node : x.transInfo.gotDirtyNodes) {
                        System.out.print(node + "; ");
                    }
                    System.out.println();
                }
                
                System.out.println();
            }
        };
        
        for (int i = 0; i < trans.length; i++) {
            Trans t = db.trans().put(keys[i], new byte[sizes[i]]).build();
            //t.listener = printListener;
            db.execute(t);
        }
        db.sync(SyncLevel.ORDINARY);
        
        //System.out.println("---- printGraph ----");
        //db.printDag(System.out);
        
        long sum1 = DbUtil.checksum(db);
        db.stop();
        
        // Restart
        
        Db db2 = Db.builder().testSetup(stream).build();
        db2.start();
        
        //System.out.println("---- printGraph db2 ----");
        //db2.printDag(System.out);
        
        long sum2 = DbUtil.checksum(db2);
        db2.stop();
        
        Assert.assertEquals("kv checksums equal?", sum1, sum2);
        
        boolean equal = new DagComparison(db.internal().dag(), db2.internal().dag()).printDiffs(true).compare();
        Assert.assertTrue("dags equal?", equal);
    }
}


/*

LOG

150809 Removed Scenarios 104, 105, 106 because they use the now obsolete 
db.internal().setStartupPosUpdater(updater). Interface core.StartupPosUpdater has been removed.

*/
