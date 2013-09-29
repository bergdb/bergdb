package bergdb.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;

import bergdb.common.Util;
import bergdb.coreds.GetMany;
import bergdb.coreds.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.stream.MemoryStream;


/**
 * Class for unit testing GetMany functionality of the DB.
 */
public class DbTesterGetMany {
    
    @T
    public static void test1() {
        //
        // Simple test with three short keys added in reverse order.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        //System.out.println("---- DBTesterGetMany.test1 ----");
        //for (KVT kvt : d.result) {
        //    System.out.println(Util.toString(Klong.segmentsToKeyBytes(kvt.key)) + ": " 
        //            + Util.toString(kvt.value) + " at " + kvt.time);
        //}
        
        Assert.assertEquals(3, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("1", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(2);
        Assert.assertEquals("3", Util.toString(kvt.value));
        
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("c", Keys.toString(kvt.key));
    }
    
    @T
    public static void test1Backward() {
        //
        // Like test1(), but backward iteration direction.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("a", "1"));
        clock.setTime(20);
        db.execute(Trans.builder().set("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("c", "3"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(3, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("3", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(2);
        Assert.assertEquals("1", Util.toString(kvt.value));
        
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("a", Keys.toString(kvt.key));
    }
    
    @T
    public static void test2() {
        //
        // Test keys with multiple segments. One single parent segment of all keys.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("segment/c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("segment/b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("segment/a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        
        db.getMany(d);
        
        //System.out.println("---- DBTesterGetMany.test2 ----");
        //for (KVT kvt : d.result) {
        //    System.out.println(Util.toString(Klong.segmentsToKeyBytes(kvt.key)) + ": " 
        //            + Util.toString(kvt.value) + " at " + kvt.time);
        //}
        
        Assert.assertEquals(3, d.result.size());
        
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("1", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(2);
        Assert.assertEquals("3", Util.toString(kvt.value));
        
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("segment/c", Keys.toString(kvt.key));
    }
    
    @T
    public static void test2Backward() {        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("segment/c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("segment/b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("segment/a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        
        db.getMany(d);
        
        Assert.assertEquals(3, d.result.size());
        
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("3", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(2);
        Assert.assertEquals("1", Util.toString(kvt.value));
        
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("segment/a", Keys.toString(kvt.key));
    }
    
    @T
    public static void test3() {
        //
        // Historic lookups.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 1;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(0, d.result.size());
        
        d = new GetMany();
        d.startKey = null;
        d.lookupTime = 25;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("3", Util.toString(kvt.value));
        
        d = new GetMany();
        d.startKey = null;
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(3, d.result.size());
        kvt = d.result.get(0);
        Assert.assertEquals("1", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(2);
        Assert.assertEquals("3", Util.toString(kvt.value));
    }
    
    @T
    public static void test3Backward() {
        //
        // Like test3(), but backward.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 1;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(0, d.result.size());
        
        d = new GetMany();
        d.startKey = null;
        d.lookupTime = 25;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("3", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        
        d = new GetMany();
        d.startKey = null;
        d.lookupTime = Long.MAX_VALUE;
        d.setBackward();
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(3, d.result.size());
        kvt = d.result.get(0);
        Assert.assertEquals("3", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(2);
        Assert.assertEquals("1", Util.toString(kvt.value));
    }
    
    @T
    public static void test4() {
        //
        // Lookup after a restart. Nodes will be read from stream.
        //
        
        KTestClock clock = new KTestClock();
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup().clock(clock).mainStream(stream).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("segment/c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("segment/b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("segment/a", "1"));
        db.sync();
        db = null;
        
        db = Db.builder().testSetup().clock(clock).mainStream(stream).start();
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(3, d.result.size());
        
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("1", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(2);
        Assert.assertEquals("3", Util.toString(kvt.value));
        
        Assert.assertTrue(kvt.time >= 30 || kvt.time < 35);
        Assert.assertEquals("segment/c", Keys.toString(kvt.key));
    }
    
    public static void testStopCondition1() {
        //
        // Tests a stop condition. Only 2 KVTs will be returned.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.StopCondition() {
            private int count = 0;
            public int handleKvt(Kvt kvt) {
                count++;
                return count > 2 ? STOP : ADD;
            }
            public void eod() {}
        };
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("1", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
    }
    
    @T
    public static void testEndpoint1() {
        //
        // Tests an endpoint stop condition.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("e", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("c", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("c"), true);
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("1", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        
        d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("c"), false);
        db.getMany(d);
        
        Assert.assertEquals(1, d.result.size());
        kvt = d.result.get(0);
        Assert.assertEquals("1", Util.toString(kvt.value));
    }
    
    @T
    public static void testEndpoint2() {
        //
        // Tests an endpoint stop condition. Longer keys.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("segment/e", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("segment/c", "2"));
        clock.setTime(30);
        db.execute(Trans.builder()
                .set("a", "1")
                .set("z", "4"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("z - should be the last"));
        db.getMany(d);
        
        Assert.assertEquals(4, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("1", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(2);
        Assert.assertEquals("3", Util.toString(kvt.value));
        kvt = d.result.get(3);
        Assert.assertEquals("4", Util.toString(kvt.value));
    }
    
    @T
    public static void testEndpoint3() {
        //
        // Tests an endpoint stop condition. Longer keys.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("segment/e", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("segment/c", "2"));
        clock.setTime(30);
        db.execute(Trans.builder()
                .set("a", "1")
                .set("z", "4"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("a"), false);
        db.getMany(d);
        
        Assert.assertEquals(0, d.result.size());
    }
    
    @T
    public static void testEndpointBackward() {
        //
        // Tests an endpoint stop condition.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("e", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("c", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("c"), true, true);
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("3", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("2", Util.toString(kvt.value));
        
        d = new GetMany();
        d.startKey = null;
        d.lookupTime = 100;
        d.setBackward();
        d.stopCondition = new GetMany.Endpoint(Keys.toSegments("c"), false, true);
        db.getMany(d);
        
        Assert.assertEquals(1, d.result.size());
        kvt = d.result.get(0);
        Assert.assertEquals("3", Util.toString(kvt.value));
    }
    
    @T
    public static void testCrazyKeys() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
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
        
        clock.setTime(100);
        Trans.Builder b = Trans.builder();
        for (int i = 0; i < size; i++) {
            b.set(KeyFactory.crazyKey(i), Util.toBytes("" + i));
        }
        db.execute(b);
        
        GetMany d = new GetMany();
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
    
    @T
    public static void testDeepSegment() {
        //
        // Tests with tree segments of depth > 1.
        // KVs added backwards.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        long time = 100;
        clock.setTime(time);
        int size = 100;
        
        for (int i = 0; i < size; i++) {
            db.execute(Trans.builder().set(KeyFactory.binaryIntKey(size - i), 
                    Util.toBytes("" + (size - i))));
            time += 10;
            clock.setTime(time);
        }
        
        GetMany d = new GetMany();
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
    
    @T
    public static void testStart1() {
        //
        // Tests setting d.key1 to non-null.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = Keys.toSegments("b");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("3", Util.toString(kvt.value));
    }
    
    @T
    public static void testStart1Backward() {
        //
        // Tests setting d.key1 to non-null.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        GetMany d = new GetMany();
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
    
    @T
    public static void testStart2() {
        //
        // Tests setting d.key1 to non-null.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        
        GetMany d = new GetMany();
        d.startKey = Keys.toSegments("bbb");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        Assert.assertEquals(1, d.result.size());
        Kvt kvt = d.result.get(0);
        Assert.assertEquals("3", Util.toString(kvt.value));
        
        
        d = new GetMany();
        d.startKey = Keys.toSegments("aa");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        Assert.assertEquals(2, d.result.size());
        kvt = d.result.get(0);
        Assert.assertEquals("2", Util.toString(kvt.value));
        kvt = d.result.get(1);
        Assert.assertEquals("3", Util.toString(kvt.value));
    }
    
    @T
    public static void testStart3() {
        //
        // A start key less than any existing key.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = Keys.toSegments("0");    // '0' < 'a'
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(3, d.result.size());
    }
    
    @T
    public static void testStart4() {
        //
        // A start key greater than any existing key.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder().set("c", "3"));
        clock.setTime(20);
        db.execute(Trans.builder().set("b", "2"));
        clock.setTime(30);
        db.execute(Trans.builder().set("a", "1"));
        
        GetMany d = new GetMany();
        d.startKey = Keys.toSegments("z");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(0, d.result.size());
    }
    
    
    @T
    public static void testStart5() {
        //
        // Two top nodes created.
        //
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        byte[] value = new byte[100];
        
        for (int i = 0; i < 16; i++) {
            clock.setTime(1000 + i*10);
            db.execute(Trans.builder().set("" + i, value));
        }
        
        GetMany g = new GetMany();
        g.startKey = null;
        g.inclusive = true;
        db.getMany(g);
        
        Assert.assertEquals(16, g.result.size());
        
        g = new GetMany();
        g.startKey = Keys.toSegments("0");
        g.inclusive = false;
        db.getMany(g);
        
        Assert.assertEquals(15, g.result.size());
    }
    
    @T
    public static void testStartWithLongerKeys() {
        //
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder()
                .set("directory/10", "10")
                .set("directory/20", "20")
                .set("directory/30", "30")
                .set("a40", "40"));
        
        GetMany d = new GetMany();
        d.startKey = Keys.toSegments("directory/19");
        d.lookupTime = 100;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        
        Assert.assertEquals(2, d.result.size());
        Assert.assertEquals(0, Keys.compareKeys(
                Keys.toSegments("directory/20"), d.result.get(0).key));
        Assert.assertEquals("20", Util.toString(d.result.get(0).value));
        Assert.assertEquals(0, Keys.compareKeys(
                Keys.toSegments("directory/30"), d.result.get(1).key));
        Assert.assertEquals("30", Util.toString(d.result.get(1).value));
    }
    
    @T
    public static void testStartWith7() {
        //
        // Test with key of size % 7 == 0.
        //
        
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        
        clock.setTime(10);
        db.execute(Trans.builder()
                .set("directory/10", "10")
                .set("directory/2000", "20")
                .set("directory/30", "30")
                .set("a40", "40"));
        
        GetMany d = new GetMany();
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
    
    @T
    public static void testStartWithCrazyKeys1() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        int size = 10;
        
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
        
        clock.setTime(100);
        Trans.Builder b = Trans.builder();
        for (int i = 0; i < size; i++) {
            b.set(KeyFactory.crazyKey(i), Util.toBytes("" + i));
        }
        db.execute(b);
        
        // Starting at Key 0. Gets all KVs.
        GetMany d = new GetMany();
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
    
    @T
    public static void testStartWithCrazyKeys2() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        int size = 10;
        
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
        
        clock.setTime(100);
        Trans.Builder b = Trans.builder();
        for (int i = 0; i < size; i++) {
            b.set(KeyFactory.crazyKey(i), Util.toBytes("" + i));
        }
        db.execute(b);
        
        GetMany d;
        
        // Starting at last key. 
        d = new GetMany();
        d.startKey = keys.get(size - 1);
        d.lookupTime = Long.MAX_VALUE;
        d.stopCondition = new GetMany.DontStop();
        db.getMany(d);
        Assert.assertEquals(1, d.result.size());
        Assert.assertEquals(0, Keys.compareKeys(keys.get(size - 1), d.result.get(0).key));
        
        
        // Starting at Key 5.
        d = new GetMany();
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
    
    @T
    public static void testGt1() {
        KTestClock clock = new KTestClock();
        Db db = Db.builder().testSetup().clock(clock).start();
        byte[] value = new byte[100];
        GetMany g;
        
        for (int i = 0; i < 10; i++) {
            clock.setTime(1000 + i*10);
            db.execute(Trans.builder().set("" + i, value));
        }
        
        /*g = new GetMany();
        g.startKey = null;
        g.inclusive = false;
        db.getMany(g);
        Assert.assertEquals(10, g.result.size());
        */
        
        g = new GetMany();
        g.startKey = Keys.toSegments("0");
        g.inclusive = true;
        db.getMany(g);
        
//        System.out.println("DbTesterGetMany.testGt1");
//        for (Kvt k : g.result) {
//            System.out.println("  key = " + Keys.toDisplayString(Keys.toBytes(k.key)));
//        }
        
        Assert.assertEquals(10, g.result.size());
        
        /*g = new GetMany();
        g.startKey = Keys.toSegments("0");
        g.inclusive = true;
        db.getMany(g);
        Assert.assertEquals(10, g.result.size());*/
    }
    
    @T
    public static void testFromIndexing1() {
        //
        // Replicates a bug that occurred when g.startKey is shorter than the actual keys.
        //
        
        String[] keys = new String[]{
                "001.object",
                "002.object",
                "003.object"
        };
        
        Db db = Db.builder().testSetup().start();
        Trans.Builder b = Trans.builder();
        
        for (int i = 0; i < keys.length; i++) {
            long[] segments = Keys.toSegments(keys[i]);
            Assert.assertEquals(2, segments.length);
            b.set(segments, new byte[0]);
        }
        
        db.execute(b.build());
        
        GetMany g = new GetMany();
        g.startKey = Keys.toSegments("002");
        Assert.assertEquals(1, g.startKey.length);
        db.getMany(g);
        
        /*System.out.println("---- DBTesterGetMany.testFromIndexing1 ----");
        for (KVT kvt : g.result) {
            System.out.println(KeySegments.toString(kvt.key));
        }*/
        
        Assert.assertEquals(2, g.result.size());
        Assert.assertEquals(keys[1], Keys.toString(g.result.get(0).key));
        Assert.assertEquals(keys[2], Keys.toString(g.result.get(1).key));
    }
    
    @T
    public static void testFromIndexing2() {
        //
        // Like testFromIndexing2(), but backwards.
        //
        
        String[] keys = new String[]{
                "001.object",
                "002.object",
                "003.object"
        };
        
        Db db = Db.builder().testSetup().start();
        Trans.Builder b = Trans.builder();
        
        for (int i = 0; i < keys.length; i++) {
            long[] segments = Keys.toSegments(keys[i]);
            Assert.assertEquals(2, segments.length);
            b.set(segments, new byte[0]);
        }
        
        db.execute(b.build());
        
        GetMany g = new GetMany();
        g.startKey = Keys.toSegments("002");
        g.forward = false;
        Assert.assertEquals(1, g.startKey.length);
        db.getMany(g);
        
        /*System.out.println("---- DBTesterGetMany.testFromIndexing2 ----");
        for (KVT kvt : g.result) {
            System.out.println(KeySegments.toString(kvt.key));
        }*/
        
        Assert.assertEquals(1, g.result.size());
        Assert.assertEquals(keys[0], Keys.toString(g.result.get(0).key));
    }

    /**
     * Bug I fixed 130606 - day of first release :-).
     * Simplified version of pub.PubTesterIndex.tStartAtLong2c().
     */
    @T
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
        db.execute(Trans.builder()
                .set(skeys[0], new byte[]{0})
                .set(skeys[1], new byte[]{1}));
        
        long[] startSkey = Keys.toSegments(Util.hexStringToBytes("00000000000002"));
        
//        System.out.println("startSkey: " + Util.toString(startSkey));
//        System.out.println("skeys[0]: " + Util.toString(skeys[0]));
//        System.out.println("skeys[1]: " + Util.toString(skeys[1]));
        
        GetMany g = new GetMany();
        g.inclusive = true;
        g.forward = true;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        
        db.getMany(g);
        
//        for (Kvt k : g.result) {
//            System.out.println("-- result key");
//            System.out.println(Keys.compareKeys(k.key, startSkey));
//            System.out.println("DbTester, key = " + Util.toHexString(Keys.toBytes(k.key)));
//        }
        
        Assert.assertEquals(1, g.result.size());
        Assert.assertArrayEquals(skeys[1], g.result.get(0).key);
        
        db.stop();
    }
    
    /**
     * Bug I fixed 130606 - day of first release :-).
     * Same index keys as for pub.PubTesterIndex.tStartAtLong2c().
     */
    @T
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
        db.execute(Trans.builder()
                .set(skeys[0], new byte[]{0})
                .set(skeys[1], new byte[]{1})
                .set(skeys[2], new byte[]{2}));
        
        long[] startSkey = Keys.toSegments(
                  Util.hexStringToBytes("00000000000005"));
        
//        System.out.println("startKey: " + Util.toString(startSkey));
//        System.out.println("skeys[0]: " + Util.toString(skeys[0]));
//        System.out.println("skeys[1]: " + Util.toString(skeys[1]));
//        System.out.println("skeys[2]: " + Util.toString(skeys[2]));
        
        GetMany g = new GetMany();
        g.inclusive = true;
        g.forward = true;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        
        db.getMany(g);
        
//        for (Kvt k : g.result) {
//            System.out.println("-- result key");
//            System.out.println("Compare: " + Keys.compareKeys(k.key, startSkey));
//            System.out.println("key:      " + Util.toString(k.key));
//        }
        
        Assert.assertEquals(1, g.result.size());
        Assert.assertArrayEquals(skeys[2], g.result.get(0).key);
        
        db.stop();
    }
    
    /**
     * Bug I fixed 130606 - day of first release :-).
     * Simplified version of pub.PubTesterIndex.tStartAtLong2c().
     */
    @T
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
        db.execute(Trans.builder()
                .set(skeys[0], new byte[]{0})
                .set(skeys[1], new byte[]{1}));
        
        long[] startSkey = Keys.toSegments(Util.hexStringToBytes("00000000000004"));
        
//        System.out.println("startSkey: " + Util.toString(startSkey));
//        System.out.println("skeys[0]: " + Util.toString(skeys[0]));
//        System.out.println("skeys[1]: " + Util.toString(skeys[1]));
        
        GetMany g = new GetMany();
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
    @T
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
        db.execute(Trans.builder()
                .set(skeys[0], new byte[]{0})
                .set(skeys[1], new byte[]{1}));
        
        long[] startSkey = Keys.toSegments(Util.hexStringToBytes("00000000000002"));
        
        GetMany g = new GetMany();
        g.inclusive = true;
        g.forward = false;
        g.startKey = startSkey;
        g.stopCondition = new GetMany.DontStop();
        db.getMany(g);
        
        Assert.assertEquals(1, g.result.size());
        Assert.assertArrayEquals(skeys[0], g.result.get(0).key);
        
        db.stop();
    }
    
    public static void main(String[] args) throws IOException {
        DbTesterGetMany.bug130606();
    }
}
