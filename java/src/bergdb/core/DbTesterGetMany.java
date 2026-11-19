package bergdb.core;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Random;
import java.util.TreeSet;

import bergdb.common.StringUtil;
import bergdb.dag.Dag;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.KeyNode;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.SyncLevel;
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
        getMany(db, d);
        
        assertResultValues(d.result, "1", "2", "3");
        db.close();
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
        getMany(db, d);
        
        assertResultValues(d.result, "3", "2", "1");
        
        Kvt kvt = d.result.get(2);
        Assert.assertEquals("1", StringUtil.toString(kvt.value));
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("a", Keys.toString(kvt.key));
        db.close();
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
        
        getMany(db, d);
        
        assertResultValues(d.result, "basedir/a", "basedir/b", "basedir/c");
        
        Kvt kvt = d.result.get(2);
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("c", Keys.toString(kvt.key));
        db.close();
    }
    
    @Nano
    public static void test2Backward() {
        Db db = createDbWithKeys("c", "b", "a");
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        
        getMany(db, d);
        
        assertResultValues(d.result, "3", "2", "1");
        
        Assert.assertEquals(3, d.result.size());
        
        Kvt kvt = d.result.get(2);
        Assert.assertEquals("1", StringUtil.toString(kvt.value));
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("a", Keys.toString(kvt.key));
        db.close();
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
        getMany(db, d);
        
        Assert.assertEquals(0, d.result.size());
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 25;
        d.stopCondition = new GetMany.DontStop();
        getMany(db, d);
        
        assertResultValues(d.result, "2", "3");
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.DontStop();
        getMany(db, d);
        
        assertResultValues(d.result, "1", "2", "3");
        db.close();
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
        getMany(db, d);
        
        Assert.assertEquals(0, d.result.size());
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 25;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        getMany(db, d);
        
        assertResultValues(d.result, "3", "2");
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = Long.MAX_VALUE;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        getMany(db, d);
        
        assertResultValues(d.result, "3", "2", "1");
        db.close();
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
        db.close();
        
        db = Db.builder().testSetup().clock(clock).mainStream(stream.copy()).start();
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        getMany(db, d);
        
        assertResultValues(d.result, "1", "2", "3");
        
        Kvt kvt = d.result.get(2);
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("c", Keys.toString(kvt.key));
        db.close();
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
                if (DbTesterJavadoc.bergDbKey(kvt.key)) {
                    return CONTINUE;        // the startup distance's KV (bergdb 028-15)
                }
                count++;
                return count > 2 ? STOP : ADD;
            }
            public void eod() {}
        };
        getMany(db, d);
        
        assertResultValues(d.result, "1", "2");
        db.close();
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
        getMany(db, d);
        
        assertResultValues(d.result, "1", "3");
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("c"), false);
        getMany(db, d);
        
        assertResultValues(d.result, "1");
        db.close();
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
        getMany(db, d);
        
        assertResultValues(d.result, "1", "2", "3", "4");
        db.close();
    }
    
    @Nano
    public static void testEndpoint3() {
        Db db = createDbWithKvs("segments/e", "3",  "segment/c", "2",  "a", "1",  "z", "4");
      
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("a"), false);
        getMany(db, d);
        
        Assert.assertEquals(0, d.result.size());
        db.close();
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
        getMany(db, d);
        
        assertResultValues(d.result, "3", "2");
        
        d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("c"), false, true);
        getMany(db, d);
        
        assertResultValues(d.result, "3");
        db.close();
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
            b.put(KeyFactory.crazyKey(i), StringUtil.toBytes("" + i));
        }
        db.execute(b);
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.DontStop();
        getMany(db, d);
        
        Assert.assertEquals(size, d.result.size());
        
        for (int i = 0; i < size; i++) {
            long[] k1 = keys.get(i);
            long[] k2 = d.result.get(i).key;
            Assert.assertEquals(0, Keys.compareKeys(k1, k2));
        }
        db.close();
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
                    StringUtil.toBytes("" + (size - i))));
            time += 10;
            clock.setTime(time);
        }
        
        GetMany d = db.newGetMany();
        d.startKey = null;
        d.lookupTime = time + 100;
        d.stopCondition = new GetMany.DontStop();
        getMany(db, d);
        
        Assert.assertEquals(size, d.result.size());
        
        for (int i = 0; i < size; i++) {
            Kvt kvt = d.result.get(i);
            Assert.assertEquals("" + (i + 1), StringUtil.toString(kvt.value));
        }
        db.close();
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
        getMany(db, d);
        
        assertResultValues(d.result, "2", "3");
        db.close();
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
        getMany(db, d);
        
        Assert.assertEquals(2, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("2", StringUtil.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("1", StringUtil.toString(kvt.value));
        db.close();
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
        getMany(db, d);
        Assert.assertEquals(1, d.result.size());
        assertValueEquals("3", d.result.get(0).value);
        
        d = db.newGetMany();
        d.startKey = Keys.toSegments("aa");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        getMany(db, d);
        
        Assert.assertEquals(2, d.result.size());
        assertValueEquals("2", d.result.get(0).value);
        assertValueEquals("3", d.result.get(1).value);
        db.close();
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
        getMany(db, d);
        
        Assert.assertEquals(3, d.result.size());
        db.close();
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
        getMany(db, d);
        
        Assert.assertEquals(0, d.result.size());
        db.close();
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
        getMany(db, g);
        
        Assert.assertEquals(16, g.result.size());
        
        g = db.newGetMany();
        g.startKey = Keys.toSegments("0");
        g.inclusive = false;
        getMany(db, g);
        
        Assert.assertEquals(15, g.result.size());
        db.close();
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
        getMany(db, d);
        
        Assert.assertEquals(2, d.result.size());
        Assert.assertTrue(Keys.areEqual(
                Keys.toSegments("directory/20"), d.result.get(0).key));
        Assert.assertEquals("20", StringUtil.toString(d.result.get(0).value));
        Assert.assertTrue(Keys.areEqual(
                Keys.toSegments("directory/30"), d.result.get(1).key));
        Assert.assertEquals("30", StringUtil.toString(d.result.get(1).value));
        db.close();
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
        getMany(db, d);
        
        Assert.assertEquals(2, d.result.size());
        Assert.assertEquals(0, Keys.compareKeys(
                Keys.toSegments("directory/2000"), d.result.get(0).key));
        Assert.assertEquals("20", StringUtil.toString(d.result.get(0).value));
        Assert.assertEquals(0, Keys.compareKeys(
                Keys.toSegments("directory/30"), d.result.get(1).key));
        Assert.assertEquals("30", StringUtil.toString(d.result.get(1).value));
        db.close();
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
        getMany(db, d);
        Assert.assertEquals(size, d.result.size());
        for (int i = 0; i < size; i++) {
            long[] k1 = keys.get(i);
            long[] k2 = d.result.get(i).key;
            Assert.assertEquals(0, Keys.compareKeys(k1, k2));
        }
        db.close();
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
            b.put(KeyFactory.crazyKey(i), StringUtil.toBytes("" + i));
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
        getMany(db, d);
        Assert.assertEquals(1, d.result.size());
        Assert.assertEquals(0, Keys.compareKeys(keys.get(size - 1), d.result.get(0).key));
        
        
        // Starting at Key 5.
        d = db.newGetMany();
        d.startKey = keys.get(5);
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.DontStop();
        getMany(db, d);
        Assert.assertEquals(size - 5, d.result.size());
        for (int i = 5; i < size; i++) {
            long[] k1 = keys.get(i);
            long[] k2 = d.result.get(i - 5).key;
            Assert.assertEquals("i=" + i, 0, Keys.compareKeys(k1, k2));
        }
        db.close();
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
        getMany(db, g);
        Assert.assertEquals(10, g.result.size());
        db.close();
    }
    
    /**
     * Regression test for a bug found 2026-10-13 (java/stress/ReclaimReaders.java; see
     * bergdb 011-04, "Level 3 follow-up"): with an inclusive start key (the default), the start key itself
     * was not returned when the tree of its segment had more than one node level, that is,
     * with more than about 30 keys. The setup of the chain compared the number of nodes in
     * the chain, not the number of key segments, with the length of the start key.
     */
    @Nano
    public static void testInclusiveStartKeyWithDeepTree() {
        for (int maxNode : new int[] {0, 8, 14}) {
            for (boolean longKeys : new boolean[] {false, true}) {
                for (boolean forward : new boolean[] {true, false}) {
                    CoreTestClock clock = new CoreTestClock();
                    DbBuilder b = Db.builder().testSetup().clock(clock);
                    if (maxNode == 8) b.maxNodeSize8();
                    if (maxNode == 14) b.maxNodeSize14();
                    Db db = b.start();
                    db.setStartupDistance(10000);
                    int n = 120;
                    for (int i = 0; i < n; i++) {
                        clock.setTime(1000 + i * 10);
                        String key = longKeys ? "/long/key/" + i : "/k/" + i;
                        db.execute(db.trans().put(key, new byte[10]).build());
                    }

                    for (int i = 0; i < n; i++) {
                        String key = longKeys ? "/long/key/" + i : "/k/" + i;
                        GetMany g = db.newGetMany();
                        g.startKey = Keys.toSegments(key);
                        g.inclusive = true;
                        g.forward = forward;
                        getMany(db, g);
                        String what = "maxNode " + maxNode + ", long " + longKeys + ", forward "
                                + forward + ", key " + key;
                        Assert.assertTrue(what + ": no result", g.result.size() > 0);
                        Assert.assertEquals(what, 0,
                                Keys.compareKeys(g.startKey, g.result.get(0).key));

                        g = db.newGetMany();
                        g.startKey = Keys.toSegments(key);
                        g.inclusive = false;
                        g.forward = forward;
                        getMany(db, g);
                        if (g.result.size() > 0) {
                            Assert.assertTrue(what + ": exclusive returned the start key",
                                    Keys.compareKeys(g.startKey, g.result.get(0).key) != 0);
                        }
                    }
                    db.stop();
                }
            }
        }
    }

    /**
     * Scans from a random start key, in both directions, inclusive and exclusive, against a
     * sorted list of the keys: trees of several node levels, keys of one and of several
     * segments, start keys that exist and that do not (2026-10-13, found by
     * java/stress/ReclaimReaders.java; see bergdb 011-04, "Level 3 follow-up").
     */
    @Nano
    public static void testStartKeyRandom() {
        for (int seed = 0; seed < 12; seed++) {
            java.util.Random r = new java.util.Random(seed);
            int[] nodeSizes = {0, 8, 14};
            CoreTestClock clock = new CoreTestClock();
            DbBuilder b = Db.builder().testSetup().clock(clock);
            if (nodeSizes[seed % 3] == 8) b.maxNodeSize8();
            if (nodeSizes[seed % 3] == 14) b.maxNodeSize14();
            Db db = b.start();
            db.setStartupDistance(10000);

            final List<long[]> keys = new ArrayList<long[]>();
            int n = 20 + r.nextInt(300);
            long time = 1000;
            for (int i = 0; i < n; i++) {
                String key = randomKey(r);
                long[] segs = Keys.toSegments(key);
                boolean dup = false;
                for (long[] k : keys) {
                    dup |= Keys.compareKeys(k, segs) == 0;
                }
                if (dup) {
                    continue;
                }
                keys.add(segs);
                time += 10;
                clock.setTime(time);
                db.execute(db.trans().put(key, new byte[5]).build());
            }
            Collections.sort(keys, new Comparator<long[]>() {
                public int compare(long[] a, long[] c) {
                    return Keys.compareKeys(a, c);
                }
            });

            for (int j = 0; j < 80; j++) {
                long[] start = r.nextBoolean() ? keys.get(r.nextInt(keys.size()))
                        : Keys.toSegments(randomKey(r));
                for (int mode = 0; mode < 4; mode++) {
                    boolean forward = mode < 2;
                    boolean inclusive = mode % 2 == 0;
                    GetMany g = db.newGetMany();
                    g.startKey = start;
                    g.inclusive = inclusive;
                    g.forward = forward;
                    g.stopCondition = new GetMany.StopCondition() {
                        private int count = 0;
                        public int handleKvt(Kvt kvt) {
                            return ++count >= 5 ? ADD_AND_STOP : ADD;
                        }
                        public void eod() {}
                    };
                    getMany(db, g);

                    List<long[]> expected = new ArrayList<long[]>();
                    for (int i = 0; i < keys.size(); i++) {
                        long[] k = keys.get(forward ? i : keys.size() - 1 - i);
                        int c = Keys.compareKeys(k, start);
                        boolean ok = forward ? (inclusive ? c >= 0 : c > 0)
                                : (inclusive ? c <= 0 : c < 0);
                        if (ok && expected.size() < 5) {
                            expected.add(k);
                        }
                    }

                    String what = "seed " + seed + ", start " + Keys.bkey2ikey(Keys.toBytes(start))
                            + ", forward " + forward + ", inclusive " + inclusive;
                    Assert.assertEquals(what + ": number of results", expected.size(),
                            g.result.size());
                    for (int i = 0; i < expected.size(); i++) {
                        Assert.assertEquals(what + ": result " + i, 0,
                                Keys.compareKeys(expected.get(i), g.result.get(i).key));
                    }
                }
            }
            db.stop();
        }
    }

    private static String randomKey(java.util.Random r) {
        // Short keys (one segment) and long ones (several), over a small alphabet so that
        // keys share prefixes and segments.
        String[] parts = {"a", "b", "ab", "abc", "k", "/k/", "/long/", "xyz", "q"};
        StringBuilder b = new StringBuilder();
        int count = 1 + r.nextInt(r.nextInt(4) == 0 ? 6 : 2);
        for (int i = 0; i < count; i++) {
            b.append(parts[r.nextInt(parts.length)]);
            if (r.nextBoolean()) {
                b.append(r.nextInt(100));
            }
        }
        return b.toString();
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
        getMany(db, g);

        if (forward) {
            Assert.assertEquals(2, g.result.size());
            Assert.assertEquals(keys[1], Keys.toString(g.result.get(0).key));
            Assert.assertEquals(keys[2], Keys.toString(g.result.get(1).key));
        } else {
            Assert.assertEquals(1, g.result.size());
            Assert.assertEquals(keys[0], Keys.toString(g.result.get(0).key));
        }
        db.close();
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
            bkeys[i] = StringUtil.hexStringToBytes(hexKeys[i]);
        };
        
        long[][] skeys = new long[bkeys.length][];
        for (int i = 0; i < bkeys.length; i++) {
            skeys[i] = Keys.toSegments(bkeys[i]);
        }
        
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put(skeys[0], new byte[]{0})
                .put(skeys[1], new byte[]{1}));
        
        long[] startSkey = Keys.toSegments(StringUtil.hexStringToBytes("00000000000002"));
        GetMany g = db.newGetMany();
        g.inclusive = true;
        g.forward = true;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        
        getMany(db, g);
        
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
            bkeys[i] = StringUtil.hexStringToBytes(hexKeys[i]);
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
                  StringUtil.hexStringToBytes("00000000000005"));
        GetMany g = db.newGetMany();
        g.inclusive = true;
        g.forward = true;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        
        getMany(db, g);
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
            bkeys[i] = StringUtil.hexStringToBytes(hexKeys[i]);
        };
        
        long[][] skeys = new long[bkeys.length][];
        for (int i = 0; i < bkeys.length; i++) {
            skeys[i] = Keys.toSegments(bkeys[i]);
        }
        
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put(skeys[0], new byte[]{0})
                .put(skeys[1], new byte[]{1}));
        
        long[] startSkey = Keys.toSegments(StringUtil.hexStringToBytes("00000000000004"));
        GetMany g = db.newGetMany();
        g.inclusive = true;
        g.forward = true;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        
        getMany(db, g);
        
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
            bkeys[i] = StringUtil.hexStringToBytes(hexKeys[i]);
        };
        
        long[][] skeys = new long[bkeys.length][];
        for (int i = 0; i < bkeys.length; i++) {
            skeys[i] = Keys.toSegments(bkeys[i]);
        }
        
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans()
                .put(skeys[0], new byte[]{0})
                .put(skeys[1], new byte[]{1}));
        
        long[] startSkey = Keys.toSegments(StringUtil.hexStringToBytes("00000000000002"));
        
        GetMany g = db.newGetMany();
        g.inclusive = true;
        g.forward = false;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        getMany(db, g);
        
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
        getMany(db, g);
        
        Assert.assertEquals(4 + DbTesterJavadoc.NEW_DB_KVS, g.getOpCount);
        db.close();
    }
    
    /**
     * GetMany.Prefix and PrefixN add the prefix's own key, as it starts with the prefix
     * (bergdb 021-18): they stopped at it, as Keys.isPrefix() is a strict prefix, so that a
     * scan from the prefix, inclusive, gave no KV at all when the prefix was a key, and a
     * backward scan left it out. Keys around a segment of 7 bytes, and the empty key.
     */
    @Nano
    public static void testPrefixHasThePrefixKey() {
        String[] keys = {"", "a", "ab", "abc", "abcdefg", "abcdefgh", "abcdefghi", "abd", "b"};
        String[] prefixes = {"", "a", "ab", "abc", "abcdefg", "abcdefgh", "abcdefghi", "abd",
                "b", "abcd", "abcdefgx", "c"};
        Db db = Db.builder().testSetup().start();
        try {
            Trans.Builder b = db.trans();
            for (String key : keys) {
                b.put(key.getBytes(StandardCharsets.US_ASCII), new byte[] {1});
            }
            db.execute(b.build());
            
            for (String prefix : prefixes) {
                List<String> expected = new ArrayList<String>();
                for (String key : keys) {
                    if (key.startsWith(prefix)) {
                        expected.add(key);
                    }
                }
                List<String> reversed = new ArrayList<String>(expected);
                Collections.reverse(reversed);
                List<String> afterPrefix = expected.isEmpty() || !expected.get(0).equals(prefix)
                        ? expected : expected.subList(1, expected.size());
                long[] p = Keys.toSegments(prefix.getBytes(StandardCharsets.US_ASCII));
                String about = "prefix \"" + prefix + "\"";
                
                Assert.assertEquals(about + ", Prefix", expected,
                        prefixScan(db, p, true, true, new GetMany.Prefix(p)));
                Assert.assertEquals(about + ", PrefixN", expected,
                        prefixScan(db, p, true, true, new GetMany.PrefixN(p, 100)));
                Assert.assertEquals(about + ", PrefixN 1", expected.subList(0,
                        Math.min(1, expected.size())),
                        prefixScan(db, p, true, true, new GetMany.PrefixN(p, 1)));
                Assert.assertEquals(about + ", exclusive", afterPrefix,
                        prefixScan(db, p, false, true, new GetMany.Prefix(p)));
                if (!expected.isEmpty()) {
                    long[] last = Keys.toSegments(expected.get(expected.size() - 1)
                            .getBytes(StandardCharsets.US_ASCII));
                    Assert.assertEquals(about + ", backward", reversed,
                            prefixScan(db, last, true, false, new GetMany.Prefix(p)));
                    Assert.assertEquals(about + ", backward PrefixN", reversed,
                            prefixScan(db, last, true, false, new GetMany.PrefixN(p, 100)));
                }
            }
        } finally {
            db.close();
        }
    }
    
    /** The keys, as ASCII strings, of a scan from 'start' with the stop condition. */
    private static List<String> prefixScan(Db db, long[] start, boolean inclusive,
            boolean forward, GetMany.StopCondition stop) {
        GetMany g = db.newGetMany();
        g.startKey = start;
        g.inclusive = inclusive;
        g.forward = forward;
        g.stopCondition = stop;
        getMany(db, g);
        List<String> keys = new ArrayList<String>();
        for (Kvt kvt : g.result) {
            keys.add(new String(Keys.toBytes(kvt.key), StandardCharsets.US_ASCII));
        }
        return keys;
    }
    
    // ======== The end key (bergdb 021-28) ========
    
    /**
     * GetMany.endKey gives what the Endpoint stop condition gives, inclusive or not, from any
     * start, at any lookup time, also where the keys after the end are deleted (bergdb
     * 021-28): random keys of 1 to 20 bytes of three letters, around the segments of 7
     * bytes, put in transactions of 50, then deleted, the run of keys that start with "b"
     * and every third of the others, in transactions of 50; scans at times before, between
     * and after the deletes. The scan ends as at the end of the database: eod() is called.
     */
    @Nano
    public static void testEndKeyAsEndpoint() {
        Random r = new Random(2128);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        try {
            TreeSet<String> keys = new TreeSet<String>();
            while (keys.size() < 2000) {
                keys.add(abcKey(r));
            }
            List<String> list = new ArrayList<String>(keys);
            Collections.shuffle(list, r);
            long time = 10;
            List<Long> times = new ArrayList<Long>();
            for (int i = 0; i < list.size(); i += 50) {
                clock.setTime(time);
                Trans.Builder b = db.trans();
                for (String key : list.subList(i, Math.min(list.size(), i + 50))) {
                    b.put(ascii(key), new byte[] {1});
                }
                db.execute(b.build());
                times.add(time);
                time += 10;
            }
            List<String> deleted = new ArrayList<String>();
            for (int i = 0; i < list.size(); i++) {
                if (list.get(i).startsWith("b") || i % 3 == 0) {
                    deleted.add(list.get(i));
                }
            }
            for (int i = 0; i < deleted.size(); i += 50) {
                clock.setTime(time);
                Trans.Builder b = db.trans();
                for (String key : deleted.subList(i, Math.min(deleted.size(), i + 50))) {
                    b.delete(ascii(key));
                }
                db.execute(b.build());
                times.add(time);
                time += 10;
            }
            
            for (int i = 0; i < 1500; i++) {
                long lookupTime = i % 3 == 0 ? Long.MAX_VALUE : times.get(r.nextInt(times.size()));
                long[] start = r.nextInt(10) == 0 ? null : Keys.toSegments(ascii(abcKey(r)));
                boolean inclusive = r.nextBoolean();
                long[] end = Keys.toSegments(ascii(abcKey(r)));
                boolean endInclusive = r.nextBoolean();
                
                GetMany g = db.newGetMany();
                g.lookupTime = lookupTime;
                g.startKey = start;
                g.inclusive = inclusive;
                g.stopCondition = new GetMany.Endpoint(end, endInclusive);
                getMany(db, g);
                
                final boolean[] eod = new boolean[1];
                GetMany h = db.newGetMany();
                h.lookupTime = lookupTime;
                h.startKey = start;
                h.inclusive = inclusive;
                h.endKey = end;
                h.endInclusive = endInclusive;
                h.stopCondition = new GetMany.StopCondition() {
                    public int handleKvt(Kvt kvt) {
                        return ADD;
                    }
                    
                    public void eod() {
                        eod[0] = true;
                    }
                };
                getMany(db, h);
                
                String about = "scan " + i + " from " + (start == null ? "null" 
                        : Keys.toString(start)) + " to " + Keys.toString(end) + " at " 
                        + lookupTime + ", " + inclusive + ", " + endInclusive;
                Assert.assertEquals(about, keysOf(g.result), keysOf(h.result));
                Assert.assertTrue(about + ": eod()", eod[0]);
            }
            
            GetMany backward = db.newGetMany();
            backward.setBackward();
            backward.endKey = Keys.toSegments(ascii("a"));
            boolean refused = false;
            try {
                getMany(db, backward);
            } catch (IllegalArgumentException e) {
                refused = true;
            }
            Assert.assertTrue("A backward scan with endKey refused", refused);
        } finally {
            db.close();
        }
    }
    
    /**
     * A scan that GetMany.endKey ends follows no key node of the deleted keys after its range
     * (bergdb 021-28; 020-24-17): 100 live keys "a0000" to "a0099", then 5,000 keys "b00000"
     * to "b04999" put and deleted, then "c". The scan of [a0050, a0100) follows the key
     * nodes on its path and no more. Before 023-09 the same scan ended by the stop condition
     * alone, which sees live KVs only, followed every key node of the deleted keys up to "c"
     * (398), and the test failed without the end key's check in GetMany.Chain.next(). Since
     * 023-09 a delete unlinks the nodes it empties (Dag.deleteUpward; bergdb 023-07, section
     * 5.1), so the stop condition alone follows few key nodes too (11); the results of both
     * are the same. So this tests K1 and SE together, and passes without SE's check;
     * testEndKeyAsEndpoint and testEndKeyChainEdges test SE's own (bergdb 023-11, B3).
     */
    @Nano
    public static void testEndKeyPassesNoDeletedKeys() {
        Db db = Db.builder().testSetup().start();
        try {
            Trans.Builder b = db.trans();
            for (int i = 0; i < 100; i++) {
                b.put(ascii(String.format("a%04d", i)), new byte[] {1});
            }
            b.put(ascii("c"), new byte[] {1});
            db.execute(b.build());
            for (int i = 0; i < 5000; i += 100) {
                b = db.trans();
                for (int j = i; j < i + 100; j++) {
                    b.put(ascii(String.format("b%05d", j)), new byte[] {1});
                }
                db.execute(b.build());
            }
            for (int i = 0; i < 5000; i += 100) {
                b = db.trans();
                for (int j = i; j < i + 100; j++) {
                    b.delete(ascii(String.format("b%05d", j)));
                }
                db.execute(b.build());
            }
            
            long[] from = Keys.toSegments(ascii("a0050"));
            long[] to = Keys.toSegments(ascii("a0100"));
            final int[] withEnd = new int[1];
            GetMany g = db.newGetMany();
            g.startKey = from;
            g.endKey = to;
            g.endInclusive = false;
            g.stopCondition = new GetMany.Endpoint(to, false);     // as the Pub API's scan
            g.gd.pointerListener = keyNodeCounter(withEnd);
            getMany(db, g);
            
            final int[] stopOnly = new int[1];
            GetMany h = db.newGetMany();
            h.startKey = from;
            h.stopCondition = new GetMany.Endpoint(to, false);
            h.gd.pointerListener = keyNodeCounter(stopOnly);
            getMany(db, h);
            
            Assert.assertEquals(50, g.result.size());
            Assert.assertEquals(keysOf(h.result), keysOf(g.result));
            Assert.assertTrue("key nodes followed with endKey: " + withEnd[0], withEnd[0] <= 20);
            Assert.assertTrue("key nodes followed by the stop condition alone: " + stopOnly[0],
                    stopOnly[0] <= 20);
        } finally {
            db.close();
        }
    }
    
    /**
     * As testEndKeyPassesNoDeletedKeys, with long keys, each in a segment tree of its own for
     * its last segment, as the Pub API's index entries (bergdb 021-28; 020-24-16): 100 live
     * keys "a000000xyzw" to "a000099xyzw", 2,000 keys "b000000xyzw" to "b001999xyzw" put
     * and deleted, then "c". The scan of the last five live keys, to the end "b" not
     * inclusive, follows few key nodes with endKey (9 on 2026-11-09). The stop condition
     * alone followed a node of each deleted key's segment tree (2,160) before 023-09, and
     * since then, as the deletes unlink them, few too (11): K1 and SE together, as above.
     * The 2,000 puts and the 2,000 deletes in transactions of 500, Db.MAX_OPERATIONS (L1;
     * each in one transaction until bergdb 024-24).
     */
    @Nano
    public static void testEndKeyPassesNoDeletedLongKeys() {
        Db db = Db.builder().testSetup().start();
        try {
            Trans.Builder b = db.trans();
            for (int i = 0; i < 100; i++) {
                b.put(ascii(String.format("a%06dxyzw", i)), new byte[] {1});
            }
            b.put(ascii("c"), new byte[] {1});
            db.execute(b.build());
            for (int i0 = 0; i0 < 2000; i0 += Db.MAX_OPERATIONS) {
                b = db.trans();
                for (int i = i0; i < i0 + Db.MAX_OPERATIONS; i++) {
                    b.put(ascii(String.format("b%06dxyzw", i)), new byte[] {1});
                }
                db.execute(b.build());
            }
            for (int i0 = 0; i0 < 2000; i0 += Db.MAX_OPERATIONS) {
                b = db.trans();
                for (int i = i0; i < i0 + Db.MAX_OPERATIONS; i++) {
                    b.delete(ascii(String.format("b%06dxyzw", i)));
                }
                db.execute(b.build());
            }
            
            long[] from = Keys.toSegments(ascii("a000095xyzw"));
            long[] to = Keys.toSegments(ascii("b"));
            final int[] withEnd = new int[1];
            GetMany g = db.newGetMany();
            g.startKey = from;
            g.endKey = to;
            g.endInclusive = false;
            g.stopCondition = new GetMany.Endpoint(to, false);
            g.gd.pointerListener = keyNodeCounter(withEnd);
            getMany(db, g);
            
            final int[] stopOnly = new int[1];
            GetMany h = db.newGetMany();
            h.startKey = from;
            h.stopCondition = new GetMany.Endpoint(to, false);
            h.gd.pointerListener = keyNodeCounter(stopOnly);
            getMany(db, h);
            
            Assert.assertEquals(5, g.result.size());
            Assert.assertEquals(keysOf(h.result), keysOf(g.result));
            Assert.assertTrue("key nodes followed with endKey: " + withEnd[0], withEnd[0] <= 30);
            Assert.assertTrue("key nodes followed by the stop condition alone: " + stopOnly[0],
                    stopOnly[0] <= 30);
        } finally {
            db.close();
        }
    }
    
    /**
     * A Chain driven directly, as Dag.getMany does, stays at its end once the end key has
     * ended it (bergdb 021-28, a review's point 1): with keys "pppppppa" and "pppppppb" and
     * the inclusive end "pppppppa", next() gives "pppppppa", then null, and null again. The
     * end set the local copy of the link count, not the field, and the third call gave a
     * truncated key "b". A backward scan with an end key is refused with
     * IllegalArgumentException by the Chain's constructor and by Dag.getMany, also at a lookup
     * time with no root (point 2: an assert, and nothing before the root).
     */
    @Nano
    public static void testEndKeyChainEdges() {
        Db db = Db.builder().testSetup().start();
        try {
            db.execute(db.trans().put(ascii("pppppppa"), new byte[] {1})
                    .put(ascii("pppppppb"), new byte[] {2}).build());
            Dag dag = db.internal().dag();
            GetMany g = db.newGetMany();
            g.actualLookupTime = db.lookupTime(Long.MAX_VALUE);
            g.endKey = Keys.toSegments(ascii("pppppppa"));
            g.startKey = Keys.toSegments(ascii("p"));     // after BergDB's keys (028-15)
            KeyNode root = dag.getTopDs().findRoot(g.actualLookupTime, g.gd);
            GetMany.Chain chain = g.new Chain();
            chain.setup(root);
            Kvt first = chain.next();
            Assert.assertEquals("pppppppa", keysOf(java.util.Collections.singletonList(first))
                    .get(0));
            Assert.assertTrue("second", chain.next() == null);
            Assert.assertTrue("third", chain.next() == null);
            
            for (long time : new long[] {-1, db.lookupTime(Long.MAX_VALUE)}) {
                GetMany h = db.newGetMany();
                h.forward = false;
                h.endKey = Keys.toSegments(ascii("a"));
                h.lookupTime = time;
                h.actualLookupTime = time;
                boolean refused = false;
                try {
                    dag.getMany(h);
                } catch (IllegalArgumentException e) {
                    refused = true;
                }
                Assert.assertTrue("Dag.getMany, backward, time " + time, refused);
            }
            
            GetMany k = db.newGetMany();
            k.forward = false;
            k.endKey = Keys.toSegments(ascii("a"));
            boolean refused = false;
            try {
                k.new Chain();
            } catch (IllegalArgumentException e) {
                refused = true;
            }
            Assert.assertTrue("Chain, backward", refused);
        } finally {
            db.close();
        }
    }
    
    /** A pointer listener that counts the key nodes followed. */
    private static Dag.PointerListener keyNodeCounter(final int[] count) {
        return new Dag.PointerListener() {
            public void pointerFollowed(Node predecessor, int pointerIndex, Node result,
                    int pointerType) {
                if (result instanceof KeyNode) {
                    count[0]++;
                }
            }
            
            public void superRootAccessed(TopNode superRoot) {}
        };
    }
    
    /**
     * GetMany.valuesBefore (bergdb 026-09, for reclaim's scan): 100 keys put, then 50 of them
     * and 100 new keys; with valuesBefore the position after the first transaction, a scan
     * gives the same keys, times and positions as without it, the values stored before the
     * position, and no value for the others. Also after a restart, when no value is in
     * memory and the position comes from the pointer's reference.
     */
    @Nano
    public static void testValuesBefore() {
        CoreTestClock clock = new CoreTestClock();
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup().clock(clock).mainStream(stream).start();
        clock.setTime(10);
        Trans.Builder b = db.trans();
        for (int i = 0; i < 100; i++) {
            b.put(ascii(String.format("a%03d", i)), new byte[] {1, (byte) i});
        }
        Trans t = b.build();
        db.execute(t);
        final long p = t.nextPos;
        clock.setTime(20);
        b = db.trans();
        for (int i = 0; i < 100; i++) {
            if (i % 2 == 0) b.put(ascii(String.format("a%03d", i)), new byte[] {2, (byte) i});
            b.put(ascii(String.format("b%03d", i)), new byte[] {3, (byte) i});
        }
        db.execute(b.build());
        
        for (int pass = 0; pass < 2; pass++) {
            if (pass == 1) {
                db.sync(0, SyncLevel.ORDINARY);
                db.close();
                db = Db.builder().testSetup().clock(clock).mainStream(stream.copy()).start();
            }
            GetMany all = db.newGetMany();
            getMany(db, all);
            GetMany some = db.newGetMany();
            some.valuesBefore = p;
            getMany(db, some);
            Assert.assertEquals(200, all.result.size());
            Assert.assertEquals(200, some.result.size());
            int with = 0;
            for (int i = 0; i < 200; i++) {
                Kvt x = all.result.get(i), y = some.result.get(i);
                Assert.assertArrayEquals(x.key, y.key);
                Assert.assertEquals(x.time, y.time);
                Assert.assertEquals(x.spos, y.spos);
                Assert.assertTrue(x.value != null);
                if (x.spos < p) {
                    Assert.assertArrayEquals(x.value, y.value);
                    Assert.assertEquals(1, x.value[0]);
                    with++;
                } else {
                    Assert.assertTrue(i + ": no value", y.value == null);
                }
            }
            Assert.assertEquals(50, with);
        }
        db.close();
    }
    
    /** A key of 1 to 20 of the bytes 'a', 'b' and 'c'. */
    private static String abcKey(Random r) {
        int length = 1 + r.nextInt(20);
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < length; i++) {
            sb.append((char) ('a' + r.nextInt(3)));
        }
        return sb.toString();
    }
    
    private static byte[] ascii(String s) {
        return s.getBytes(StandardCharsets.US_ASCII);
    }
    
    private static List<String> keysOf(List<Kvt> result) {
        List<String> keys = new ArrayList<String>();
        for (Kvt kvt : result) {
            keys.add(new String(Keys.toBytes(kvt.key), StandardCharsets.US_ASCII));
        }
        return keys;
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
    
    /**
     * db.getMany(g), and the KVs of BergDB's keys, under "/#", removed from g.result: the
     * startup distance's KV, which every database has since bergdb 028-15, as Db's Javadoc
     * tells a caller to skip them.
     */
    private static void getMany(Db db, GetMany g) {
        db.getMany(g);
        g.result.removeIf(kvt -> DbTesterJavadoc.bergDbKey(kvt.key));
    }
    
    private static void assertResultValues(List<Kvt> result, String... values) {
        int n = result.size();
        Assert.assertEquals(values.length, n);
        
        for (int i = 0; i < n; i++) {
            assertValueEquals(values[i], result.get(i).value);
        }
    }
    
    private static void assertValueEquals(String expected, byte[] value) {
        String stringValue = StringUtil.toString(value);
        Assert.assertEquals(expected, stringValue);
    }
}
