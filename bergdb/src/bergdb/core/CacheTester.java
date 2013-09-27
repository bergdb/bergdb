package bergdb.core;

import bergdb.common.Util;
import bergdb.core.Trans.Builder;
import bergdb.coreds.EvictData;
import bergdb.coreds.GetData;
import bergdb.coreds.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.storage.BufferedStream;
import bergdb.stream.MemoryStream;


/**
 * Unit tests for cache and evict.
 * 
 * @author Frans Lundberg
 */
@SuppressWarnings("unused")
public class CacheTester {
    /** 
     * Returns memory usage in bytes.
     */
    private static long getMem() {
        System.gc();
        try {
            Thread.sleep(50);
        } catch (InterruptedException e) {
            throw new Error(e);
        }
        System.gc();
        try {
            Thread.sleep(50);
        } catch (InterruptedException e) {
            throw new Error(e);
        }
        System.gc();
        Runtime rt = Runtime.getRuntime();
        return rt.totalMemory() - rt.freeMemory();
    }
    
    private static double getMemMb() {
        return toMb(getMem());
    }
    
    private static double toMb(long bytes) {
        double mb = (double) (bytes / 1.0e6);
        mb = Math.round(mb * 100.0) / 100.0;
        return mb;
    }
    
    private static void checkDb(Db db, int size) {
        for (int i = 0; i < size; i++) {
            byte[] key = KeyFactory.intKey(i);
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
            Assert.assertArrayEquals("i=" + i, key, value);
        }
    }
    
    private static void checkCrazyDb(Db db, int[] ids) {
        for (int i = 0; i < ids.length; i++) {
            byte[] key = KeyFactory.crazyKey(ids[i]);
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
            Assert.assertArrayEquals("i=" + i + ", id=" + ids[i], key, value);
        }
    }
    
    @T
    public static void tEvictCrazy() {
        MemoryStream m = new MemoryStream();
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup(m).clock(clock).start();
        
        int[] ids = new int[50];
        for (int i = 0; i < ids.length; i++) { ids[i] = i; }
        
        for (int i = 0; i < ids.length; i++) {
            byte[] key = KeyFactory.crazyKey(ids[i]);
            byte[] value = key;
            Trans t = Trans.builder().set(key, value).build();
            clock.setTime(i * 10 + 1000);
            db.execute(t);
        }
        
        checkCrazyDb(db, ids);
        
        EvictData ed = new EvictData();
        for (int i = 0; i < ids.length; i++) {
            db.evict(ed);
        }
        
        //System.out.println("---- CacheTester.testEvictCrazy ----");
        //System.out.println("key23 = " + Util.toString(Keys.crazyKey(23)));
        //System.out.println("key5 = " + Util.toString(Keys.crazyKey(5)));
        //System.out.println("key49 = " + Util.toString(Keys.crazyKey(49)));
        //System.out.println("key50 = " + Util.toString(Keys.crazyKey(50)));
        
        GetData gd1 = new GetData();
        
        {
            byte[] value = db.get(Long.MAX_VALUE, Keys.toSegments(KeyFactory.crazyKey(23)), gd1);
        }
        
        for (int i = 0; i < ids.length*10; i++) {
            db.evict(gd1.evictData);
        }
        
        { 
            GetData d = new GetData();
            byte[] value = db.get(Long.MAX_VALUE, Keys.toSegments(KeyFactory.crazyKey(23)), d);
        }
        
        checkCrazyDb(db, ids);
        
        int count = db.getSuperRoot().getMemoryPointerCount();
        Assert.assertTrue("count=" + count, count > 0);
    }
    
    @T
    public static void tEvict23() {
        int[] ids = new int[] { 5, 23, 50 }; 
        MemoryStream m = new MemoryStream();
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup(m).clock(clock).start();
        
        db.execute(Trans.builder().set("key-hello-there1", "v1").build());
        db.execute(Trans.builder().set("key-hello-there2", "v2").build());
        
        for (int i = 0; i < ids.length; i++) {
            byte[] key = KeyFactory.crazyKey(ids[i]);
            byte[] value = KeyFactory.crazyKey(ids[i]);
            clock.setTime(1000 + i*10);
            db.execute(Trans.builder().set(key, value).build());
        }
        
        // Checks DB
        {
            for (int i = 0; i < ids.length; i++) {
                byte[] key = KeyFactory.crazyKey(ids[i]);
                byte[] expected = key;
                byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
                Assert.assertArrayEquals("i=" + i, expected, value);
            }
        }
        
        EvictData gd = new EvictData();
        for (int i = 0; i < ids.length * 10; i++) {
            db.evict(gd);
        }
        
        // Checks DB
        {
            for (int i = 0; i < ids.length; i++) {
                byte[] key = KeyFactory.crazyKey(ids[i]);
                byte[] expected = key;
                byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
                Assert.assertArrayEquals("i=" + i, expected, value);
            }
        }
    }
    
    @T
    public static void tEvict23B() {       
        byte[][] keys = new byte[][]{ 
                Keys.toBytes("dir/key1"),
                Keys.toBytes("dir/key2")
        };
        
        MemoryStream m = new MemoryStream();
        KTestClock clock = new KTestClock();
        Db db = Db.builder().mainStream(m).clock(clock).evictBoss(new FixedDurationEvictBoss(0)).start();
        
        //System.out.println("---- CacheTester.evict23B ----");
        
        for (int i = 0; i < keys.length; i++) {
            byte[] key = keys[i];
            byte[] value = keys[i];
            clock.setTime(1000 + i*10);
            db.execute(Trans.builder().set(key, value).build());
        }
        
        // Checks DB
        {
            for (int i = 0; i < keys.length; i++) {
                byte[] key = keys[i];
                byte[] expected = key;
                byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
                Assert.assertArrayEquals("i=" + i, expected, value);
            }
        }
        
        //System.out.println("-- db orig --");  db.printGraph(System.out);
        
        EvictData gd = new EvictData();
        
        for (int i = 0; i < 2; i++) {
            db.evict(gd);
        }
        
        //System.out.println("-- db after 2 evicts --");  db.printGraph(System.out);
        
        for (int i = 0; i < 2; i++) {
            db.evict(gd);
        }
        
        //System.out.println("-- db after 4 evicts --");  db.printGraph(System.out);
        
        DbUtil.get(db, Long.MAX_VALUE, keys[0]);
        DbUtil.get(db, Long.MAX_VALUE, keys[1]);
        
        //System.out.println("-- db after get() --\n");  db.printGraph(System.out);
        
        // Checks DB after evicts
        {
            for (int i = 0; i < keys.length; i++) {
                byte[] key = keys[i];
                byte[] expected = key;
                byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
                Assert.assertArrayEquals("i=" + i, expected, value);
            }
        }
    }
    
    @T
    public static void test50() {
        Db db = Db.builder().clock(new TestClock()).retainForever()
                .evictBoss(new FixedDurationEvictBoss(0))
                .mainStream(new MemoryStream())
                .start();
        
        Trans.Builder b = Trans.builder();
        
        for (int i = 0; i < 50; i++) {
            b.set("" + i, "v" + i);
        }
        
        db.execute(b.build());
        
        //System.out.println("-- db orig --");  db.printGraph(System.out);
        
        EvictData ed = new EvictData();
        int evictCount = 0;
        
        for (int i = 0; i < 10; i++) {
            db.evict(ed);
            evictCount += ed.evictCount;
        }
        
        //System.out.println("-- after evict --");  
        //System.out.println("Evict count: " + evictCount);
        //db.printGraph(System.out);
    }
}
