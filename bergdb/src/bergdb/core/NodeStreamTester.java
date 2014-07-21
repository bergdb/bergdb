package bergdb.core;

import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * Class with nanotests for NodeStream.
 * 
 * @author Frans Lundberg
 */
public class NodeStreamTester {
    
    @T
    public static void testSimpleRestart() {
        AppendOnlyStream mstream = new MemoryStream();
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().mainStream(mstream).startupDistance(10000).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(Trans.builder().put("admin1", "Sanna").build());

        byte[] value;
        value = DbUtil.get(db, 99, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        db.sync(SyncLevel.ORDINARY);
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(mstream).build();
        db2.start();
        
        value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, 5, "admin1");
        Assert.assertNull(value);
    }
    
    @T
    public static void testSimpleRestart2() {
        //
        // Like testSimpleRestart, but 2-segment key
        //
        byte[] value;
        AppendOnlyStream mstream = new MemoryStream();
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().mainStream(mstream).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(Trans.builder().put("admin10", "Sanna").build());
        
        value = DbUtil.get(db, 99, "admin10");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        db.sync(SyncLevel.ORDINARY);
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(mstream).build();
        db2.start();
        
        value = DbUtil.get(db2, 99, "admin10");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, 5, "admin10");
        Assert.assertNull(value);
    }
    
    @T
    public static void testRestartWithMultipleTransactions() {
        AppendOnlyStream s = new MemoryStream();
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().mainStream(s).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(Trans.builder().put("admin1", "Sanna1").build());
        clock.setTime(20);
        db.execute(Trans.builder().put("admin2", "Sanna2").build());
        db.sync(SyncLevel.ORDINARY);
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(s).build();
        db2.start();
        byte[] value;
        
        value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna1"), value);
        value = DbUtil.get(db2, 5, "admin1");
        Assert.assertNull(value);
        
        value = DbUtil.get(db2, 99, "admin2");
        Assert.assertArrayEquals(Util.toBytes("Sanna2"), value);
        value = DbUtil.get(db2, 15, "admin2");
        Assert.assertNull(value);
    }
    
    @T
    public static void tIterators1() {
        AppendOnlyStream s = new MemoryStream();
        Db db = Db.builder().testSetup().mainStream(s).build();
        db.start();
        db.execute(Trans.builder().put("admin1", "a1").put("admin2", "a2"));
        db.execute(Trans.builder().put("admin3", "a3"));
        db.execute(Trans.builder().put("admin4", "a4"));
        
        NodeStream.TransIterator ti = db.getStream().new TransIterator(0);
        
        synchronized (db.getWriteLock()) {
            for (int i = 0; i < 4; i++) {
                Assert.assertTrue(ti.next());
                //System.out.println("---- trans: " + ti.transPos);
                //NodeStream.NodeIterator ni = ti.getNodeIterator();
                //while (ni.next()) {
                    //System.out.println(ni.transPos);
                    //System.out.println("node: " + ni.node);
                //}
            }
        
            Assert.assertTrue(ti.next() == false);
        }
    }
}
