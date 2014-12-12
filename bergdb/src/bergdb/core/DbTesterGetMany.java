package bergdb.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import bergdb.common.Util;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.MemoryStream;


/**
 * Class for unit testing the GetMany functionality of Db.
 * 
 * @author Frans Lundberg
 */
public class DbTesterGetMany {
    
    @Nano
    public static void test1() {
        //
        // Simple test with three short keys added in reverse order.
        //
        
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        assertResultValues(d.result, "1", "2", "3");
    }
    
    @Nano
    public static void test1Backward() {
        //
        // Like test1(), but backward iteration direction.
        //
        
        Db db = createDbWithKeys("a", "b", "c");
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        assertResultValues(d.result, "3", "2", "1");
        
        Kvt kvt = d.result.get(2);
        Assert.assertEquals("1", Util.toString(kvt.value));
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("a", Keys.toString(kvt.key));
    }
    
    @Nano
    public static void test2() {
        //
        // Test keys with multiple segments. One single parent segment of all keys.
        //
        
        Db db = createDbWithKvs(
                "c", "basedir/c",
                "b", "basedir/b", 
                "a", "basedir/a");
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        
        db.getMany(d);
        
        assertResultValues(d.result, "basedir/a", "basedir/b", "basedir/c");
        
        Kvt kvt = d.result.get(2);
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("c", Keys.toString(kvt.key));
    }
    
    @Nano
    public static void test2Backward() {
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        
        db.getMany(d);
        
        assertResultValues(d.result, "3", "2", "1");
        
        Assert.assertEquals(3, d.result.size());
        
        Kvt kvt = d.result.get(2);
        Assert.assertEquals("1", Util.toString(kvt.value));
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("a", Keys.toString(kvt.key));
    }
    
    @Nano
    public static void test3() {
        //
        // Historic lookups.
        //
        
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 1;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(0, d.result.size());
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 25;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        assertResultValues(d.result, "2", "3");
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        assertResultValues(d.result, "1", "2", "3");
    }
    
    @Nano
    public static void test3Backward() {
        //
        // Like test3(), but backward.
        //
        
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 1;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(0, d.result.size());
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 25;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        assertResultValues(d.result, "3", "2");
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = Long.MAX_VALUE;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        assertResultValues(d.result, "3", "2", "1");
    }
    
    @Nano
    public static void test4() {
        //
        // Lookup after a restart. Nodes will be read from stream.
        //
        
        CoreTestClock clock = new CoreTestClock();
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup().clock(clock).mainStream(stream).start();
        
        clock.setTime(10);
        db.execute(db.trans().put("c", "3"));
        clock.setTime(20);
        db.execute(db.trans().put("b", "2"));
        clock.setTime(30);
        db.execute(db.trans().put("a", "1"));
        
        db.sync(0, SyncLevel.ORDINARY);
        db = null;
        
        db = Db.builder().testSetup().clock(clock).mainStream(stream).start();
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        assertResultValues(d.result, "1", "2", "3");
        
        Kvt kvt = d.result.get(2);
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("c", Keys.toString(kvt.key));
    }
    
    public static void testStopCondition1() {
        //
        // Tests a stop condition. Only 2 KVTs will be returned.
        //
        
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.StopCondition() {
            int count = 0;
            public int handleKvt(Kvt kvt) {
                count++;
                return count > 2 ? STOP : ADD;
            }
            public void eod() {}
        };
        db.getMany(d);
        
        assertResultValues(d.result, "1", "2");
    }
    
    @Nano
    public static void testEndpoint1() {
        //
        // Tests an endpoint stop condition.
        //
        
        Db db = createDbWithKeys("e", "c", "a");  // 5, 3, 1
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("c"), true);
        db.getMany(d);
        
        assertResultValues(d.result, "1", "3");
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("c"), false);
        db.getMany(d);
        
        assertResultValues(d.result, "1");
    }
    
    @Nano
    public static void testEndpoint2() {
        //
        // Tests an endpoint stop condition. Longer keys.
        //
        
        Db db = createDbWithKvs("segments/e", "3",  "segment/c", "2",  "a", "1",  "z", "4");

        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("z - should be the last"));
        db.getMany(d);
        
        assertResultValues(d.result, "1", "2", "3", "4");
    }
    
    @Nano
    public static void testEndpoint3() {
        Db db = createDbWithKvs("segments/e", "3",  "segment/c", "2",  "a", "1",  "z", "4");
      
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("a"), false);
        db.getMany(d);
        
        Assert.assertEquals(0, d.result.size());
    }
    
    @Nano
    public static void testEndpointBackward() {
        //
        // Tests an endpoint stop condition.
        //
        
        Db db = createDbWithKvs("e", "3",  "c", "2",  "a", "1");
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("c"), true, true);
        db.getMany(d);
        
        assertResultValues(d.result, "3", "2");
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("c"), false, true);
        db.getMany(d);
        
        assertResultValues(d.result, "3");
    }
    
    @Nano
    public static void testCrazyKeys() {
        Db db = Db.builder().testSetup().start();
        int size = 20;
        
        ArrayList<long[]> keys = new ArrayList<long[]>();
        for (int i = 0; i < size; i++) {
            keys.add(Keys.toSegments(KeyFactory.crazyKey(i)));
        }
        
        Collections.sort(keys, new Comparator<long[]>() {
            public int compare(long[] key1, long[] key2) {
                return Keys.compareKeys(key1, key2);
            }
        });
        
        Trans.Builder b = db.trans();
        for (int i = 0; i < size; i++) {
            b.put(KeyFactory.crazyKey(i), Util.toBytes("" + i));
        }
        db.execute(b);
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(size, d.result.size());
        
        for (int i = 0; i < size; i++) {
            long[] k1 = keys.get(i);
            long[] k2 = d.result.get(i).key;
            Assert.assertEquals(0, Keys.compareKeys(k1, k2));
        }
    }
    
    @Nano
    public static void testDeepSegment() {
        //
        // Tests with tree segments of depth > 1.
        // KVs added backwards.
        //
        
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        long time = 100;
        clock.setTime(time);
        int size = 100;
        
        for (int i = 0; i < size; i++) {
            db.execute(db.trans().put(KeyFactory.binaryIntKey(size - i), 
                    Util.toBytes("" + (size - i))));
            time += 10;
            clock.setTime(time);
        }
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = time + 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(size, d.result.size());
        
        for (int i = 0; i < size; i++) {
            Kvt kvt = d.result.get(i);
            Assert.assertEquals("" + (i + 1), Util.toString(kvt.value));
        }
    }
    
    @Nano
    public static void testStart1() {
        //
        // Tests setting d.key1 to non-null.
        //
        
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = Keys.toSegments("b");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        assertResultValues(d.result, "2", "3");
    }
    
    @Nano
    public static void testStart1Backward() {
        //
        // Tests setting d.startKey to non-null.
        //
        
        /*KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().put("c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().put("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().put("a", "1"));
        */
        
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = Keys.toSegments("b");
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("1", Util.toString(kvt.value));
    }
    
    @Nano
    public static void testStart2() {
        //
        // Tests setting d.startKey to non-null.
        //
        
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = Keys.toSegments("bbb");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        Assert.assertEquals(1, d.result.size());
        assertValueEquals("3", d.result.get(0).value);
        
        d = db.newGetMany();
        d.startKey = Keys.toSegments("aa");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        assertValueEquals("2", d.result.get(0).value);
        assertValueEquals("3", d.result.get(1).value);
    }
    
    @Nano
    public static void testStart3() {
        //
        // A start key less than any existing key.
        //
        
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = Keys.toSegments("0");    // '0' < 'a'
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(3, d.result.size());
    }
    
    @Nano
    public static void testStart4() {
        //
        // A start key greater than any existing key.
        //
        
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = Keys.toSegments("z");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(0, d.result.size());
    }
    
    @Nano
    public static void testStart5() {
        //
        // Two top nodes created.
        //
        
        Db db = Db.builder().testSetup().start();
        byte[] value = new byte[100];
        
        for (int i = 0; i < 16; i++) {
            db.execute(db.trans().put("" + i, value));
        }
        
        GetMany g = db.newGetMany();
        g.startKey = null;
        g.inclusive = true;
        db.getMany(g);
        
        Assert.assertEquals(16, g.result.size());
        
        g = db.newGetMany();
        g.startKey = Keys.toSegments("0");
        g.inclusive = false;
        db.getMany(g);
        
        Assert.assertEquals(15, g.result.size());
    }
    
    @Nano
    public static void testStartWithLongerKeys() {
        Db db = Db.builder().testSetup().start();
        
        db.execute(db.trans()
                .put("directory/10", "10")
                .put("directory/20", "20")
                .put("directory/30", "30")
                .put("a40", "40"));
        
        GetMany d = db.newGetMany();
        d.startKey = Keys.toSegments("directory/19");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        Assert.assertTrue(Keys.areEqual(
                Keys.toSegments("directory/20"), d.result.get(0).key));
        Assert.assertEquals("20", Util.toString(d.result.get(0).value));
        Assert.assertTrue(Keys.areEqual(
                Keys.toSegments("directory/30"), d.result.get(1).key));
        Assert.assertEquals("30", Util.toString(d.result.get(1).value));
    }
    
    @Nano
    public static void testStartWith7() {
        //
        // Test with key of size % 7 == 0.
        //
        
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(db.trans()
                .put("directory/10", "10")
                .put("directory/2000", "20")
                .put("directory/30", "30")
                .put("a40", "40"));
        
        GetMany d = db.newGetMany();
        d.startKey = Keys.toSegments("directory/19");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        Assert.assertEquals(0, Keys.compareKeys(
                Keys.toSegments("directory/2000"), d.result.get(0).key));
        Assert.assertEquals("20", Util.toString(d.result.get(0).value));
        Assert.assertEquals(0, Keys.compareKeys(
                Keys.toSegments("directory/30"), d.result.get(1).key));
        Assert.assertEquals("30", Util.toString(d.result.get(1).value));
    }
    
    @Nano
    public static void testStartWithCrazyKeys1() {
        Db db = Db.builder().testSetup().start();
        int size = 10;
        
        ArrayList<long[]> keys = putCrazyKeys(db, size);
        
        // Starting at Key 0. Gets all KVs.
        GetMany d = db.newGetMany();
        d.startKey = keys.get(0);
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        Assert.assertEquals(size, d.result.size());
        for (int i = 0; i < size; i++) {
            long[] k1 = keys.get(i);
            long[] k2 = d.result.get(i).key;
            Assert.assertEquals(0, Keys.compareKeys(k1, k2));
        }
    }

    private static ArrayList<long[]> putCrazyKeys(Db db, int size) {
        ArrayList<long[]> keys = new ArrayList<long[]>();
        for (int i = 0; i < size; i++) {
            keys.add(Keys.toSegments(KeyFactory.crazyKey(i)));
        }
        
        // Sorts the keys
        
        Collections.sort(keys, new Comparator<long[]>() {
            public int compare(long[] key1, long[] key2) {
                return Keys.compareKeys(key1, key2);
            }
        });
        
        Trans.Builder b = db.trans();
        for (int i = 0; i < size; i++) {
            b.put(KeyFactory.crazyKey(i), Util.toBytes("" + i));
        }
        db.execute(b);
        return keys;
    }
    
    @Nano
    public static void testStartWithCrazyKeys2() {
        Db db = Db.builder().testSetup().start();
        int size = 10;
        
        ArrayList<long[]> keys = putCrazyKeys(db, size);
        
        GetMany d;
        
        // Starting at last key. 
        d = db.newGetMany();
        d.startKey = keys.get(size - 1);
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        Assert.assertEquals(1, d.result.size());
        Assert.assertEquals(0, Keys.compareKeys(keys.get(size - 1), d.result.get(0).key));
        
        
        // Starting at Key 5.
        d = db.newGetMany();
        d.startKey = keys.get(5);
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        Assert.assertEquals(size - 5, d.result.size());
        for (int i = 5; i < size; i++) {
            long[] k1 = keys.get(i);
            long[] k2 = d.result.get(i - 5).key;
            Assert.assertEquals("i=" + i, 0, Keys.compareKeys(k1, k2));
        }
    }
    
    @Nano
    public static void testGt1() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        byte[] value = new byte[100];
        GetMany g;
        
        for (int i = 0; i < 10; i++) {
            clock.setTime(1000 + i*10);
            db.execute(db.trans().put("" + i, value));
        }
        
        g = db.newGetMany();
        g.startKey = Keys.toSegments("0");
        g.inclusive = true;
        db.getMany(g);
        Assert.assertEquals(10, g.result.size());
    }
    
    @Nano
    public static void testFromIndexing1() {
        //
        // Replicates a bug that occurred when g.startKey is shorter than the actual keys.
        //
        testFromIndexing(true);
    }
    
    @Nano
    public static void testFromIndexing2() {
        testFromIndexing(false);
    }
    
    public static void testFromIndexing(boolean forward) {
        String[] keys = new String[]{
                "001.object",
                "002.object",
                "003.object"
        };
        
        Db db = Db.builder().testSetup().start();
        Trans.Builder b = db.trans();
        
        for (int i = 0; i < keys.length; i++) {
            long[] segments = Keys.toSegments(keys[i]);
            Assert.assertEquals(2, segments.length);
            b.put(segments, new byte[0]);
        }
        
        db.execute(b.build());
        
        GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments("002");
        g.forward = forward;
        Assert.assertEquals(1, g.startKey.length);
        db.getMany(g);

        if (forward) {
            Assert.assertEquals(2, g.result.size());
            Assert.assertEquals(keys[1], Keys.toString(g.result.get(0).key));
            Assert.assertEquals(keys[2], Keys.toString(g.result.get(1).key));
        } else {
            Assert.assertEquals(1, g.result.size());
            Assert.assertEquals(keys[0], Keys.toString(g.result.get(0).key));
        }
    }

    /**
     * Bug I fixed 130606 - day of first release :-).
     * Simplified version of pub.PubTesterIndex.tStartAtLong2c().
     */
    @Nano
    public static void bug130606() {        
        String[] hexKeys = new String[] { 
                "00000000000000", 
                "00000000000004" 
        };
        
        byte[][] bkeys = new byte[hexKeys.length][];
        for (int i = 0; i < hexKeys.length; i++) {
            bkeys[i] = Util.hexStringToBytes(hexKeys[i]);
        };
        
        long[][] skeys = new long[bkeys.length][];
        for (int i = 0; i < bkeys.length; i++) {
            skeys[i] = Keys.toSegments(bkeys[i]);
        }
        
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put(skeys[0], new byte[]{0})
                .put(skeys[1], new byte[]{1}));
        
        long[] startSkey = Keys.toSegments(Util.hexStringToBytes("00000000000002"));
        GetMany g = db.newGetMany();
        g.inclusive = true;
        g.forward = true;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        
        db.getMany(g);
        
        Assert.assertEquals(1, g.result.size());
        Assert.assertArrayEquals(skeys[1], g.result.get(0).key);
        
        db.stop();
    }
    
    /**
     * Bug I fixed 130606 - day of first release :-).
     * Same index keys as for pub.PubTesterIndex.tStartAtLong2c().
     */
    @Nano
    public static void bug130606b() {
        
        String[] hexKeys = new String[] { 
                "0000000000000200012f633071646c", 
                "0000000000000400012f643071646c",
                "0000000000000600012f653071646c"
        };
        
        byte[][] bkeys = new byte[hexKeys.length][];
        for (int i = 0; i < hexKeys.length; i++) {
            bkeys[i] = Util.hexStringToBytes(hexKeys[i]);
        };
        
        long[][] skeys = new long[bkeys.length][];
        for (int i = 0; i < bkeys.length; i++) {
            skeys[i] = Keys.toSegments(bkeys[i]);
        }
        
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put(skeys[0], new byte[]{0})
                .put(skeys[1], new byte[]{1})
                .put(skeys[2], new byte[]{2}));
        
        long[] startSkey = Keys.toSegments(
                  Util.hexStringToBytes("00000000000005"));
        GetMany g = db.newGetMany();
        g.inclusive = true;
        g.forward = true;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        
        db.getMany(g);
        Assert.assertEquals(1, g.result.size());
        Assert.assertArrayEquals(skeys[2], g.result.get(0).key);
        
        db.stop();
    }
    
    /**
     * Bug I fixed 130606 - day of first release :-).
     * Simplified version of pub.PubTesterIndex.tStartAtLong2c().
     */
    @Nano
    public static void bug130606c() { 
        // Same as bug130606 but start key is exact match with a key in db.
        
        String[] hexKeys = new String[] { 
                "00000000000000", 
                "00000000000004" 
        };
        
        byte[][] bkeys = new byte[hexKeys.length][];
        for (int i = 0; i < hexKeys.length; i++) {
            bkeys[i] = Util.hexStringToBytes(hexKeys[i]);
        };
        
        long[][] skeys = new long[bkeys.length][];
        for (int i = 0; i < bkeys.length; i++) {
            skeys[i] = Keys.toSegments(bkeys[i]);
        }
        
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put(skeys[0], new byte[]{0})
                .put(skeys[1], new byte[]{1}));
        
        long[] startSkey = Keys.toSegments(Util.hexStringToBytes("00000000000004"));
        GetMany g = db.newGetMany();
        g.inclusive = true;
        g.forward = true;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        
        db.getMany(g);
        
        Assert.assertEquals(1, g.result.size());
        Assert.assertArrayEquals(skeys[1], g.result.get(0).key);
        
        db.stop();
    }
    
    /**
     * Bug I fixed 130606 - day of first release :-).
     * Simplified version of pub.PubTesterIndex.tStartAtLong2c().
     */
    @Nano
    public static void bug130606backwards() {        
        String[] hexKeys = new String[] { 
                "00000000000000", 
                "00000000000004" 
        };
        
        byte[][] bkeys = new byte[hexKeys.length][];
        for (int i = 0; i < hexKeys.length; i++) {
            bkeys[i] = Util.hexStringToBytes(hexKeys[i]);
        };
        
        long[][] skeys = new long[bkeys.length][];
        for (int i = 0; i < bkeys.length; i++) {
            skeys[i] = Keys.toSegments(bkeys[i]);
        }
        
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put(skeys[0], new byte[]{0})
                .put(skeys[1], new byte[]{1}));
        
        long[] startSkey = Keys.toSegments(Util.hexStringToBytes("00000000000002"));
        
        GetMany g = db.newGetMany();
        g.inclusive = true;
        g.forward = false;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        db.getMany(g);
        
        Assert.assertEquals(1, g.result.size());
        Assert.assertArrayEquals(skeys[0], g.result.get(0).key);
        
        db.stop();
    }
    
    @Nano
    public static void testGetOpCount() {
        Db db = createDbWithKeys("a", "b", "c", "d");
        
        GetMany g = db.newGetMany();
        g.startKey = null;
        g.lookupTime = 100;
        g.stopCondition = new GetMany.DontStop();
        db.getMany(g);
        
        Assert.assertEquals(4, g.getOpCount);
    }
    
    // ======== Helpers ========
    
    /**
     * For example, for args a, b, c, this method returns a 
     * database with the following time-key-value triplets:
     * (10 a 1), (20 b 2), (30 c 3).
     */
    private static Db createDbWithKeys(String... keys) {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        for (int i = 0; i < keys.length; i++) {
            String key = keys[i];
            clock.setTime(10 + i*10);
            db.execute(db.trans().put(key, getValueGivenKey(key)));
        }
        
        return db;
    }

    private static String getValueGivenKey(String key) {
        return Integer.toString(key.charAt(0) - 'a' + 1);
    }
    
    private static Db createDbWithKvs(String... kvs) {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        int n = kvs.length / 2;
        
        for (int i = 0; i < n; i++) {
            String key   = kvs[i*2 + 0];
            String value = kvs[i*2 + 1];
            clock.setTime(10 + i*10);
            db.execute(db.trans().put(key, value));
        }
        
        return db;
    }
    
    private static void assertResultValues(List<Kvt> result, String... values) {
        int n = result.size();
        Assert.assertEquals(values.length, n);
        
        for (int i = 0; i < n; i++) {
            assertValueEquals(values[i], result.get(i).value);
        }
    }
    
    private static void assertValueEquals(String expected, byte[] value) {
        String stringValue = Util.toString(value);
        Assert.assertEquals(expected, stringValue);
    }
}
