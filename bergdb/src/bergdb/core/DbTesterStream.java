package bergdb.core;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.OneFileStream;

/**
 * Tests the database with a stream.
 * 
 * @author Frans Lundberg
 */
public class DbTesterStream {
    
    public static void test1() {
        Db db = Db.builder().testSetup().build();
        db.start();
    }
    
    public static void test2() {
        Db db = Db.builder().testSetup().build();
        db.start();
        
        db.execute(db.trans().put("admin1", "Sanna").build());
        byte[] value = DbUtil.get(db, 99, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
    }
    
    public static void testSimpleRestart1() {
        byte[] value;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("admin1", "Sanna").build());
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup(stream).start();
        
        value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, 5, Util.toBytes("admin1"));
        Assert.assertNull(value);
        db2.stop();
    }
    
    public static void testSimpleRestart2() {
        //
        // Like testSimpleRestart1, but 2-segment key
        //
        byte[] value;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(db.trans().put("admin10", "Sanna").build());
        db.sync(SyncLevel.ORDINARY);
        
        value = DbUtil.get(db, 99, "admin10");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        
        db.stop();
        db = null;
        Db db2 = Db.builder().testSetup().mainStream(stream).build();
        db2.start();
        
        value = DbUtil.get(db2, 99, "admin10");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, 5, "admin10");
        Assert.assertNull(value);
        db2.stop();
    }
    
    public static void testRestartWithMultipleTransactions() {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(db.trans().put("admin1", "Sanna1").build());
        clock.setTime(20);
        db.execute(db.trans().put("admin2", "Sanna2").build());
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup(stream).build();
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
        db2.stop();
    }
    
    public static void testRestart2() {
        //
        // Like testRestartWithMultipleTransactions, but keys are
        // one char longer, "admin10" instead of "admin1".
        //
        MemoryStream stream = new MemoryStream();
        byte[] value;
        Db db;
        
        db = Db.builder().testSetup(stream).build();
        db.start();
        
        db.execute(db.trans().put("admin10", "Sanna1").build());
        db.execute(db.trans().put("admin20", "Sanna2").build());
        
        value = DbUtil.get(db, 999, "admin10");
        Assert.assertEquals("Sanna1", Util.toString(value));
        value = DbUtil.get(db, 999, "admin20");
        Assert.assertEquals("Sanna2", Util.toString(value));
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(stream).build();
        db2.start();
        
        value = DbUtil.get(db2, 999, "admin10");
        Assert.assertEquals("Sanna1", Util.toString(value));
        value = DbUtil.get(db2, 999, "admin20");
        Assert.assertEquals("Sanna2", Util.toString(value));
        db2.stop();
    }
    
    public static void testRestartWithTimeSplit() {
        MemoryStream stream = new MemoryStream();
        byte[] value;
        long time;
        Db db;
        int n = 10;
        
        CoreTestClock clock = new CoreTestClock();
        db = Db.builder().testSetup(stream).clock(clock).build();
        db.start();
        
        time = 100;
        for (int i = 0; i < n; i++) {
            clock.setTime(time);
            db.execute(db.trans().put("admin" + time, "Sanna" + time).build());
            time += 10;
        }
        
        time = 100;
        for (int i = 0; i < n; i++) {
            value = DbUtil.get(db, 999, "admin" + time);
            Assert.assertArrayEquals("i=" + i, Util.toBytes("Sanna" + time), value);
            time += 10;
        }
        
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup(stream).build();
        db2.start();
        
        time = 100;
        for (int i = 0; i < n; i++) {
            value = DbUtil.get(db2, 999, "admin" + time);
            Assert.assertEquals("i=" + i, "Sanna" + time, Util.toString(value));
            time += 10;
        }
        db2.stop();
    }
    
    public static void testRestartWithTwoSuperRoots() {
        MemoryStream stream = new MemoryStream();
        byte[] value;
        long time;
        Db db;
        int n = 10;
        CoreTestClock clock = new CoreTestClock();
        db = Db.builder().testSetup(stream).clock(clock).build();
        db.start();
        
        time = 100;
        for (int i = 0; i < n; i++) {
            clock.setTime(time);
            db.execute(db.trans().put("a" + time, "v" + time).build());
            time += 10;
        }
        
        time = 100;
        for (int i = 0; i < n; i++) {
            value = DbUtil.get(db, 999,"a" + time);
            Assert.assertArrayEquals("i=" + i, Util.toBytes("v" + time), value);
            time += 10;
        }
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(stream).build();
        db2.start();
        
        time = 100;
        for (int i = 0; i < n; i++) {
            value = DbUtil.get(db2, 999, "a" + time);
            Assert.assertEquals("i=" + i, "v" + time, Util.toString(value));
            time += 10;
        }
        db2.stop();
    }
    
    public static Db createRandomDb(int n, AppendOnlyStream stream) {
        Random random = new Random(1);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).build();
        db.start();
        
        for (int i = 0; i < n; i++) {
            String key = "" + random.nextInt();
            Trans t = db.trans().put(key, "v" + key).build();
            clock.setTime(i * 10 + 10);
            db.execute(t);
            
            byte[] value = DbUtil.get(db, n * 10 + 999, key);
            Assert.assertEquals("i=" + i, "v" + key, Util.toString(value));
        }
        return db;
    }
    
    public static void checkRandomDb(Db db, int n) {
        Random random = new Random(1);
        
        for (int i = 0; i < n; i++) {
            String key = "" + random.nextInt();
            byte[] value = DbUtil.get(db, n * 10 + 999, key);
            Assert.assertEquals("i=" + i, "v" + key, Util.toString(value));
        }
    }
    
    public static void testMoreData0() {
        int n = 50;
        MemoryStream stream = new MemoryStream();
        Db db = createRandomDb(n, stream);
        checkRandomDb(db, n);
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        checkRandomDb(db2, n);
        db2.stop();
    }
    
    public static void testMoreData1() {
        int n = 100;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        
        for (int i = 0; i < n; i++) {
            clock.setTime(100 + i * 10);
            Trans t = db.trans().put("" + i, "v" + i).build();
            db.execute(t);
        }
        
        for (int i = 0; i < n; i++) {
            String valueString = Util.toString(DbUtil.get(db, n * 10 + 9999, "" + i));
            Assert.assertEquals("v" + i, valueString);
        }
        
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup(stream).start();
        
        for (int i = 0; i < n; i++) {
            String valueString = Util.toString(DbUtil.get(db2, n * 10 + 9999, "" + i));
            Assert.assertEquals("v" + i, valueString);
        }
        db2.stop();
    }
    
    @Nano("f")   // Too slow to be "unit".
    public static void testMoreData2() {
        int n = 2000;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(stream).clock(clock).start();

        for (int i = 0; i < n; i++) {
            int k = i + 100;
            clock.setTime(100 + k * 10);
            Trans t = db.trans().put("" + k, "v" + k).build();
            db.execute(t);
        }
        
        for (int i = 0; i < n; i++) {
            int k = i + 100;
            String valueString = Util.toString(DbUtil.get(db, n * 10 + 9999, "" + k));
            Assert.assertEquals("v" + k, valueString);
        }
        
        db.sync(SyncLevel.ORDINARY);
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        
        for (int i = 0; i < n; i++) {
            int k = i + 100;
            String valueString = Util.toString(DbUtil.get(db2, n * 10 + 9999, "" + k));
            Assert.assertEquals("v" + k, valueString);
        }   
    }
    
    public static void testDbOnMemStream() throws IOException {
        AppendOnlyStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("k", "k-value"));
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup(s).start();
        
        byte[]value = DbUtil.get(db2, 99, "k");
        Assert.assertArrayEquals(Util.toBytes("k-value"), value);
        
        value = DbUtil.get(db2, 5, "k");
        Assert.assertNull(value);
        db2.stop();
    }
    
    public static void testDbOnFile() throws IOException {
        // 
        // Tests writing db data to file.
        //
        
        if (Util.runsAndroid()) {
            return;
        }
        
        File f = File.createTempFile(DbTesterStream.class.getSimpleName() + ".testDbOnFile.", ".bergdb");
        f.deleteOnExit();
        
        try {
            AppendOnlyStream s = new OneFileStream(f);
            CoreTestClock clock = new CoreTestClock();
            Db db = Db.builder().testSetup(s).clock(clock).start();
            clock.setTime(10);
            db.execute(db.trans().put("k", "k-value"));
            db.sync(SyncLevel.ORDINARY);
            db = null;
            s = null;
            
            AppendOnlyStream s2 = new OneFileStream(f);
            Db db2 = Db.builder().testSetup(s2).start();
            
            byte[] value = DbUtil.get(db2, 99, "k");
            Assert.assertArrayEquals(Util.toBytes("k-value"), value);
            
            value = DbUtil.get(db2, 5, Util.toBytes("k"));
            Assert.assertNull(value);
        } finally {
            f.delete();
        }
    }
    
    public static void testDbOnFileMultipleTransactions() throws FileNotFoundException, IOException {
        
        if (Util.runsAndroid()) {
            return;
        }
        
        File f = File.createTempFile(DbTesterStream.class.getSimpleName() + ".testDbOnFileMultipleTransactions.", ".bergdb");
        f.deleteOnExit();
        
        AppendOnlyStream s = new OneFileStream(f);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("admin1", "Sanna1").build());
        clock.setTime(20);
        db.execute(db.trans().put("admin2", "Sanna2").build());
        db.sync(SyncLevel.ORDINARY);
        db = null;
        s = null;
        
        AppendOnlyStream s2 = new OneFileStream(f);
        Db db2 = Db.builder().testSetup(s2).start();
        
        byte[] value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna1"), value);
        value = DbUtil.get(db2, 5, "admin1");
        Assert.assertNull(value);
        
        value = DbUtil.get(db2, 99, "admin2");
        Assert.assertArrayEquals(Util.toBytes("Sanna2"), value);
        value = DbUtil.get(db2, 15, "admin2");
        Assert.assertNull(value);
        
        f.delete();
    }
    
    public static void testOverwriteAndRestart() {
        AppendOnlyStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        
        clock.setTime(10);
        db.execute(db.trans().put("k1", "k1-value").put("k2", "k2-value"));
        
        clock.setTime(20);
        db.execute(db.trans().put("k1", "k1-value-b"));
        
        clock.setTime(30);
        db.execute(db.trans().put("k2", "k2-value-b"));
        db.sync(SyncLevel.ORDINARY);
        db = null;
        
        Db db2 = Db.builder().testSetup(s).start();
        
        // t = 15
        
        byte[] value = DbUtil.get(db2, 15, "k2");
        Assert.assertArrayEquals(Util.toBytes("k2-value"), value);
        
        value = DbUtil.get(db2, 15, "k1");
        Assert.assertArrayEquals(Util.toBytes("k1-value"), value);
        
        // t = 25
        
        value = DbUtil.get(db2, 25, "k1");
        Assert.assertArrayEquals(Util.toBytes("k1-value-b"), value);
        
        value = DbUtil.get(db2, 25, "k2");
        Assert.assertArrayEquals(Util.toBytes("k2-value"), value);
        
        // t = 35
        
        value = DbUtil.get(db2, 35, "k1");
        Assert.assertArrayEquals(Util.toBytes("k1-value-b"), value);
        
        value = DbUtil.get(db2, 35, "k2");
        Assert.assertEquals("k2-value-b", Util.toString(value));
    }

    @Nano
    public static void testTwoKvsInOneTransaction() {
        AppendOnlyStream s = new MemoryStream();
        TestClock clock = new TestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        int n = 2;
        Trans.Builder b = db.trans();
            
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.intKey(n - i);
            byte[] value = new byte[4];
            Bytes.intToBytesLE(i, value, 0);
            b.put(key, value);
        }
        
        db.execute(b);
        
        // Check
        
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.intKey(n - i);
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
            Assert.assertTrue("i=" + i, value != null);
            Assert.assertEquals(4, value.length);
            int valueInt = Bytes.bytesToIntLE(value, 0);
            Assert.assertEquals(i, valueInt);
        }
        
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        // Now, let's create a new Db from stream.
        
        db = Db.builder().testSetup(s).start();
        
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.intKey(n - i);
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
            Assert.assertTrue("i=" + i, value != null);
            Assert.assertEquals(4, value.length);
            int valueInt = Bytes.bytesToIntLE(value, 0);
            Assert.assertEquals(i, valueInt);
        }
    }
    
    @Nano("f")     // Too slow to be "unit".
    public static void testLargeTransaction() {
        AppendOnlyStream s = new MemoryStream();
        int n = 2;
        int valueSize = 20*1000*1000;
        Db db = createRandomDb(n, s);  // Make sure we have some data
        
        db.execute(db.trans().put("/large", new byte[valueSize]));
        db.sync(SyncLevel.ORDINARY);
        db = null;
        
        db = Db.builder().testSetup().mainStream(s).start();
        checkRandomDb(db, n);
        byte[] value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("/large"));
        Assert.assertTrue(value != null);
        Assert.assertEquals(valueSize, value.length);
    }
    
    @Nano("f")    // Too slow to be "unit".
    public static void testLargeTransactions() {
        MemoryStream s = new MemoryStream();
        int valueSize = 1000*1000;
        Db db = Db.builder().testSetup().startupDistance(100*1000).mainStream(s).start();
        int n = 5;
        
        db.execute(db.trans().put("/small1", "v-small1"));
        
        for (int i = 0; i < n; i++) {
            db.execute(db.trans().put("/large-" + i, new byte[valueSize + i]));
        }
        
        db.execute(db.trans().put("/small2", "v-small2"));
        db.sync(SyncLevel.ORDINARY);
        
        //System.out.println("---- Before restart ----");
        //db.printGraph(System.out);
        db = null;
        
        // ---- Restart
        
        s = s.copy();
        db = Db.builder().testSetup().mainStream(s).build();
        db.start();
        //System.out.println("Stream length: " + s.getLength());
        
        //System.out.println("---- After restart ----");
        //db.printGraph(System.out);
        
        Assert.assertEquals("v-small1", DbUtil.getString(db, "/small1"));
        Assert.assertEquals("v-small2", DbUtil.getString(db, "/small2"));
        
        for (int i = 0; i < n; i++) {
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("/large-" + i));
            Assert.assertEquals(valueSize + i, value.length);
        }
    }
}
