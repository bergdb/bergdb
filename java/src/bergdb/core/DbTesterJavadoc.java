package bergdb.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * The Javadoc of the Core API, Db and the types of its signatures, checked against what the
 * code does, a promise at a time (bergdb 020-27): the promises that no other test showed.
 * Each test names its class and promise. The Keys section of Db's Javadoc, which needs the
 * Pub API, is tested in bergdb.pubimp.PubTesterCoreKeys.
 */
public class DbTesterJavadoc {

    private static final long LATEST = Long.MAX_VALUE;

    /**
     * The KVs of BergDB's own in every database from its creation on: the startup distance's
     * (bergdb 028-15), which a scan of the whole database returns too.
     */
    static final int NEW_DB_KVS = 1;

    /**
     * Whether a key is BergDB's, under "/#": its bytes begin with 01 25 (Db, "Keys and the
     * layers above").
     */
    static boolean bergDbKey(long[] key) {
        byte[] k = Keys.toBytes(key);
        return k.length >= 2 && k[0] == 1 && k[1] == 0x25;
    }

    private static Db dbWithKeys(int n) {
        Db db = Db.builder().testSetup().start();
        for (int i = 0; i < n; i++) {
            db.execute(db.trans().put("k" + i, "v" + i).build());
        }
        return db;
    }

    private static byte[] get(Db db, String key) {
        return db.getOne(LATEST, Keys.toSegments(key), db.newGetData());
    }

    private interface Call {
        void run();
    }

    /** Runs the call and returns what it threw, or null. */
    private static Throwable thrown(Call call) {
        try {
            call.run();
            return null;
        } catch (Throwable e) {
            return e;
        }
    }

    private static void assertThrows(String about, Class<?> expected, Call call) {
        Throwable e = thrown(call);
        Assert.assertTrue(about + ": expected " + expected.getSimpleName() + ", got " + e,
                e != null && expected.isInstance(e));
    }

    /**
     * Db.getOne(): null for a key without a value at the lookup time; the array returned is
     * the database's own while the value is in memory (Trans.Builder: "A value's array is
     * not copied"); GetData.tpos is the position of the transaction that wrote the value,
     * which getTrans() reads (Trans.tpos, tt, lastPos); Trans.nextPos is the stream's length
     * after it.
     */
    @Nano
    public static void testGetOneAndTheTransaction() {
        Db db = Db.builder().testSetup().start();
        try {
            byte[] value = {1, 2, 3};
            Trans t = db.trans().put(Keys.toBytes("a"), value).build();
            db.execute(t);
            Assert.assertEquals("nextPos", t.lastPos + 1, t.nextPos);
            Assert.assertEquals("the stream's length", t.nextPos, db.getStreamLength());

            GetData gd = db.newGetData();
            Assert.assertNull(db.getOne(LATEST, Keys.toSegments("b"), gd));
            Assert.assertNull(db.getOne(t.tt - 1, Keys.toSegments("a"), gd));
            byte[] got = db.getOne(LATEST, Keys.toSegments("a"), gd);
            Assert.assertTrue("the database's own array, the one put", got == value);
            Assert.assertEquals("GetData.tpos", t.tpos, gd.tpos);

            StoredTrans stored = db.getTrans(gd.tpos);
            Assert.assertEquals("tt", t.tt, stored.tt);
            Assert.assertEquals("tpos", t.tpos, stored.tpos);
            Assert.assertEquals("lastPos", t.lastPos, stored.lastPos);
        } finally {
            db.close();
        }
    }

    /**
     * Trans.Builder.build(): one operation a key, the last call's, a put or a delete (bergdb
     * 024-10: the last operation wins). Until release 2026.4: the last put, or a delete if
     * there was no put, so that "a" held "1" and "f" held "2".
     */
    @Nano
    public static void testTransBuilderOneOperationPerKey() {
        Db db = dbWithKeys(0);
        try {
            db.execute(db.trans().put("e", "0").build());
            db.execute(db.trans().put("a", "1").delete("a").build());
            db.execute(db.trans().delete("b").put("b", "2").build());
            db.execute(db.trans().put("c", "1").put("c", "2").build());
            db.execute(db.trans().put("d", "1").delete("d").put("d", "3").build());
            db.execute(db.trans().delete("e").delete("e").build());
            Trans t = db.trans().put("f", "1").delete("f").put("f", "2").delete("f").build();
            Assert.assertEquals("one KV", 1, t.kvs.length);
            db.execute(t);
            String[][] expected = {{"a", null}, {"b", "2"}, {"c", "2"}, {"d", "3"}, {"e", null},
                    {"f", null}};
            for (String[] kv : expected) {
                byte[] value = get(db, kv[0]);
                Object got = value == null ? null : new String(value);
                Assert.assertEquals(kv[0], (Object) kv[1], got);
            }
        } finally {
            db.close();
        }
    }

    /**
     * Db.start(): a second call, also after stop(), throws IllegalDbStateException, and
     * nothing is closed: the database goes on.
     */
    @Nano
    public static void testSecondStartRefused() {
        Db db = dbWithKeys(1);
        try {
            assertThrows("start again", IllegalDbStateException.class, () -> db.start());
            Assert.assertEquals("v0", new String(get(db, "k0")));
            db.execute(db.trans().put("k1", "v1").build());
            Assert.assertEquals("v1", new String(get(db, "k1")));
            db.stop();
            assertThrows("start after stop", IllegalDbStateException.class, () -> db.start());
        } finally {
            db.close();
        }
    }

    /**
     * Before start(): reads, transactions and newGetData(), newGetMany() and printDag() throw
     * IllegalDbStateException. After stop(): reads, transactions and the settings kept in
     * the stream throw DbStoppingException, an IllegalDbStateException, and change nothing;
     * setCacheSizeIndicator() only sets the value. setCacheSizeIndicator() refuses a value
     * below 1, sync() a null sync level, with IllegalArgumentException; SyncLevel.NONE
     * returns at once.
     */
    @Nano
    public static void testCallsBeforeStartAndAfterStop() {
        final Db db = Db.builder().testSetup().build();
        final GetMany g = new GetMany();
        Call[] before = {
            () -> db.getOne(LATEST, Keys.toSegments("k"), new GetData()),
            () -> db.getMany(g),
            () -> db.execute(db.trans().put("k", "v").build()),
            () -> db.getTrans(128),
            () -> db.newGetData(),
            () -> db.newGetMany(),
            () -> db.printDag(System.out)};
        for (int i = 0; i < before.length; i++) {
            Throwable e = thrown(before[i]);
            Assert.assertTrue("before start, call " + i + ": " + e,
                    e instanceof IllegalDbStateException && !(e instanceof DbStoppingException));
        }
        db.close();

        final Db db2 = dbWithKeys(1);
        try {
            final Trans t = db2.trans().put("k1", "v1").build();
            db2.execute(t);
            assertThrows("below 1", IllegalArgumentException.class,
                    () -> db2.setCacheSizeIndicator(0));
            assertThrows("null", IllegalArgumentException.class, () -> db2.sync(null));
            assertThrows("null", IllegalArgumentException.class, () -> db2.sync(0, null));
            db2.sync(SyncLevel.NONE);
            long distance = db2.getStartupDistance();
            long retain = db2.getRetainDuration();
            double fraction = db2.getInternalFraction();

            db2.stop();
            final GetMany g2 = db2.newGetMany();
            Call[] after = {
                () -> db2.getOne(LATEST, Keys.toSegments("k0"), db2.newGetData()),
                () -> db2.getMany(g2),
                () -> db2.execute(db2.trans().put("k", "v").build()),
                () -> db2.getTrans(t.tpos),
                () -> db2.setStartupDistance(1000 * 1000),
                () -> db2.setRetainDuration(100 * Clock.UNITS_PER_SEC),
                () -> db2.setReclaimInternalFraction(0.5),
                () -> db2.printDag(System.out)};
            for (int i = 0; i < after.length; i++) {
                Throwable e = thrown(after[i]);
                Assert.assertTrue("after stop, call " + i + ": " + e,
                        e instanceof DbStoppingException);
            }
            Assert.assertEquals("distance", distance, db2.getStartupDistance());
            Assert.assertEquals("retain", retain, db2.getRetainDuration());
            Assert.assertTrue("fraction", fraction == db2.getInternalFraction());
            db2.setCacheSizeIndicator(12345);
            Assert.assertEquals("set after stop", 12345, db2.getCacheSizeIndicator());
        } finally {
            db2.close();
        }
    }

    /**
     * Db, "Db shutdown": a Db's own threads, the storage's writer and the eviction thread,
     * are daemon threads, so they do not keep the JVM alive; what a Db that is not stopped
     * has committed is written without stop() or sync().
     */
    @Nano
    public static void testOwnThreadsAreDaemons() {
        Set<Thread> before = new HashSet<>(Thread.getAllStackTraces().keySet());
        Db db = Db.builder().testSetup().cacheSizeIndicator(1000 * 1000).start();
        try {
            byte[] value = new byte[1000];
            for (int i = 0; i < 2000; i++) {
                db.execute(db.trans().put(Keys.toBytes("k" + i), value).build());
            }
            db.setCacheSizeIndicator(100 * 1000);     // Wakes the eviction thread.

            long end = System.nanoTime() + 30L * 1000 * 1000 * 1000;
            List<String> ours = new ArrayList<>();
            boolean written = false;
            while (System.nanoTime() < end) {
                ours.clear();
                for (Thread t : Thread.getAllStackTraces().keySet()) {
                    String name = t.getName();
                    if (!before.contains(t) && (name.startsWith("BufferedStream-consumer")
                            || name.equals("bergdb-evictor"))) {
                        Assert.assertTrue(name + " is a daemon", t.isDaemon());
                        ours.add(name.startsWith("Buffered") ? "writer" : "evictor");
                    }
                }
                written = db.getDurableLength() == db.getStreamLength();
                if (written && ours.contains("writer") && ours.contains("evictor")) {
                    break;
                }
                Thread.onSpinWait();
            }
            Assert.assertTrue("the threads: " + ours,
                    ours.contains("writer") && ours.contains("evictor"));
            Assert.assertTrue("written without stop() or sync()", written);
        } finally {
            db.close();
        }
    }

    /** GetMany.GetN and PrefixN: at most N KVs, N = 0 too; PrefixN keeps its own prefix. */
    @Nano
    public static void testGetManyAtMostN() {
        Db db = dbWithKeys(5);
        try {
            int[] counts = {0, 1, 3, 5, 7};
            for (int n : counts) {
                GetMany g = db.newGetMany();
                g.startKey = Keys.toSegments("k");      // after BergDB's keys (bergdb 028-15)
                g.stopCondition = new GetMany.GetN(n);
                db.getMany(g);
                Assert.assertEquals("GetN(" + n + ")", Math.min(n, 5), g.result.size());

                g = db.newGetMany();
                g.startKey = Keys.toSegments("k");
                g.stopCondition = new GetMany.PrefixN(Keys.toSegments("k"), n);
                db.getMany(g);
                Assert.assertEquals("PrefixN(k, " + n + ")", Math.min(n, 5), g.result.size());
            }
            GetMany g = db.newGetMany();
            g.startKey = Keys.toSegments("k");
            g.stopCondition = new GetMany.GetOne();
            db.getMany(g);
            Assert.assertEquals("GetOne", 1, g.result.size());

            long[] prefix = Keys.toSegments("k");
            g = db.newGetMany();
            g.startKey = Keys.toSegments("k");
            g.stopCondition = new GetMany.PrefixN(prefix, 10);
            prefix[0] = Keys.toSegments("x")[0];
            db.getMany(g);
            Assert.assertEquals("PrefixN, the caller's array changed", 5, g.result.size());
        } finally {
            db.close();
        }
    }

    /**
     * GetMany.StopCondition.eod(): called once when the end of the database is reached, and
     * handleKvt() never after it; not called when handleKvt() stops the scan; called also
     * for a lookup time before the first transaction, when the database has no state.
     */
    @Nano
    public static void testEodOnceAtTheEnd() {
        Db db = dbWithKeys(3);
        try {
            final int[] calls = new int[2];     // handleKvt, eod
            final boolean[] afterEod = {false};
            final int[] stopAt = {Integer.MAX_VALUE};
            GetMany.StopCondition condition = new GetMany.StopCondition() {
                public int handleKvt(Kvt kvt) {
                    afterEod[0] |= calls[1] > 0;
                    return ++calls[0] >= stopAt[0] ? STOP : ADD;
                }

                public void eod() {
                    calls[1]++;
                }
            };
            long[] times = {LATEST, 0};
            int[] sizes = {3 + NEW_DB_KVS, 0};
            for (int i = 0; i < times.length; i++) {
                calls[0] = calls[1] = 0;
                GetMany g = db.newGetMany();
                g.lookupTime = times[i];
                g.stopCondition = condition;
                db.getMany(g);
                Assert.assertEquals("time " + times[i], sizes[i], g.result.size());
                Assert.assertEquals("eod at time " + times[i], 1, calls[1]);
                Assert.assertFalse("handleKvt after eod", afterEod[0]);
            }

            calls[0] = calls[1] = 0;
            stopAt[0] = 2;
            GetMany g = db.newGetMany();
            g.stopCondition = condition;
            db.getMany(g);
            Assert.assertEquals("stopped", 1, g.result.size());
            Assert.assertEquals("no eod after STOP", 0, calls[1]);
        } finally {
            db.close();
        }
    }

    /**
     * DbBuilder's refusals: id(null), stream() with a null name
     * or stream or a negative buffer size or time, each with
     * IllegalArgumentException (and until bergdb 028-68 reclaimStepReserve() below 1), and a second stream's name with IllegalStateException;
     * mainStream() replaces a stream of any name, stream() one of the same name; a buffer
     * size or time of 0 taken; build() without a stream,
     * IllegalStateException, with a null clock IllegalArgumentException. Trans.Builder's: a
     * null value, also for a String key, and a negative lookup time, with
     * IllegalArgumentException.
     */
    @Nano
    public static void testBuilderRefusals() {
        final MemoryStream s = new MemoryStream();
        Call[] refused = {
            () -> Db.builder().id(null),
            () -> Db.builder().stream(null, s),
            () -> Db.builder().stream("main", null),
            () -> Db.builder().stream("main", s, -1, 10),
            () -> Db.builder().stream("main", s, 100, -1),
            () -> Db.builder().testSetup().clock(null).build(),
            () -> new Trans.Builder().put(new byte[] {5}, null),
            () -> new Trans.Builder().put(new long[] {5}, null),
            () -> new Trans.Builder().put("k", (String) null),
            () -> new Trans.Builder().put("k", (byte[]) null),
            () -> new Trans.Builder().lookupTime(-1)};
        for (int i = 0; i < refused.length; i++) {
            assertThrows("call " + i, IllegalArgumentException.class, refused[i]);
        }
        assertThrows("no stream", IllegalStateException.class, () -> Db.builder().build());
        assertThrows("a second name", IllegalStateException.class, 
                () -> Db.builder().stream("a", new MemoryStream()).stream("b", s));
        
        // mainStream() replaces a stream of any name; stream() one of the same name.
        Db other = Db.builder().stream("other", new MemoryStream()).mainStream(s).testId()
                .start();
        try {
            other.execute(other.trans().put("m", "1").build());
        } finally {
            other.close();
        }
        Assert.assertTrue("on the main stream", s.getLength() > 0);
        final MemoryStream s2 = s.copy();
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        Db db = b.stream("main", new MemoryStream()).stream("main", s2, 0, 0).start();
        try {
            db.execute(db.trans().put("k", "v").build());
            db.sync(SyncLevel.ORDINARY);
            Assert.assertEquals("v", new String(get(db, "k")));
            Assert.assertEquals("1", new String(get(db, "m")));
        } finally {
            db.close();
        }
    }

    /**
     * DbBuilder.cacheSizeIndicator(): a value below 1 is refused with
     * IllegalArgumentException, as Db.setCacheSizeIndicator() refuses one.
     */
    @Nano
    public static void testBuilderCacheSizeIndicatorBelowOneRefused() {
        long[] bad = {0, -1, Long.MIN_VALUE};
        for (final long size : bad) {
            assertThrows("cacheSizeIndicator(" + size + ")", IllegalArgumentException.class,
                    () -> Db.builder().cacheSizeIndicator(size));
        }
        Db db = Db.builder().testSetup().cacheSizeIndicator(1).start();
        try {
            Assert.assertEquals(1, db.getCacheSizeIndicator());
            db.execute(db.trans().put("k", "v").build());
            Assert.assertEquals("v", new String(get(db, "k")));
        } finally {
            db.close();
        }
    }

    /**
     * Db.setStartupDistance(), the only way to set the startup distance since bergdb 028-13
     * (DbBuilder.startupDistance() was removed): a new database has 50 MB; 10 to 10^9 taken
     * as given and returned; a value above 10^9 (10^9 + 1, Integer.MAX_VALUE) clamped to
     * 10^9, one from 1 to 9 to 10, and the clamped value returned and in force; a value
     * below 1 refused with IllegalArgumentException, the setting kept. Until 028-13 the
     * builder refused values outside 10 to 10^9 (028-12), and the setter clamped to 400,000
     * to 10^9.
     */
    @Nano
    public static void testSetStartupDistanceRange() {
        final int max = 1000 * 1000000;
        Assert.assertEquals(max, Db.MAX_STARTUP_DISTANCE);
        Assert.assertEquals(10, Db.MIN_STARTUP_DISTANCE);
        Db db = Db.builder().testSetup().start();
        try {
            Assert.assertEquals("the default", 50 * 1000000, db.getStartupDistance());
            Assert.assertEquals("10^9 taken", max, db.setStartupDistance(max));
            Assert.assertEquals("10^9 in force", max, db.getStartupDistance());
            db.execute(db.trans().put("k", "v").build());
            Assert.assertEquals("v", new String(get(db, "k")));
            Assert.assertEquals("10 taken", 10, db.setStartupDistance(10));
            Assert.assertEquals("2000 taken", 2000, db.setStartupDistance(2000));
            int[][] clamped = {{max + 1, max}, {Integer.MAX_VALUE, max}, {9, 10}, {1, 10}};
            for (int[] c : clamped) {
                Assert.assertEquals("setStartupDistance(" + c[0] + ")", c[1],
                        db.setStartupDistance(c[0]));
                Assert.assertEquals("in force after " + c[0], c[1], db.getStartupDistance());
            }
            for (final int sd : new int[] {0, -1, Integer.MIN_VALUE}) {
                final Db d = db;
                assertThrows("setStartupDistance(" + sd + ")", IllegalArgumentException.class,
                        () -> d.setStartupDistance(sd));
                Assert.assertEquals("kept after " + sd, 10, db.getStartupDistance());
            }
            db.execute(db.trans().put("k", "w").build());
            Assert.assertEquals("w", new String(get(db, "k")));
        } finally {
            db.close();
        }
    }

    /** Every KV of the latest state, with the stop condition 'c', or every one if null. */
    private static List<Kvt> scan(Db db, GetMany.StopCondition c) {
        GetMany g = db.newGetMany();
        if (c != null) {
            g.stopCondition = c;
        }
        db.getMany(g);
        return g.result;
    }

    /**
     * Db, "Keys and values" (bergdb 020-24-09, U9-5): any bytes make a key, the empty array
     * too; getMany() gives the keys in the unsigned order of their bytes, as
     * Arrays.compareUnsigned() orders them, forward and backward; a key of 111 bytes, the
     * most (Db, "Limits"; L2), works, and one of 112 is refused with IllegalArgumentException
     * (until bergdb 024-24 a key of 3,000 bytes worked); the empty array is a value, not a
     * delete; a put of a null value is refused with IllegalArgumentException.
     */
    @Nano
    public static void testKeysAndValues() {
        byte[][] keys = {{}, {0}, {0, 0}, {1}, {0x61}, {0x61, 0}, {0x61, 0, 0}, {0x61, 1},
                {0x61, 0x61}, {0x62}, {0x7f}, {(byte) 0x80}, {(byte) 0xfe, 0}, {(byte) 0xff},
                {(byte) 0xff, (byte) 0xff}, {1, 2, 3, 4, 5, 6, 7}, {1, 2, 3, 4, 5, 6, 7, 8},
                {1, 2, 3, 4, 5, 6, 7, (byte) 0x90}, new byte[Db.MAX_KEY_BYTES]};
        final byte[] longKey = keys[keys.length - 1];
        longKey[Db.MAX_KEY_BYTES - 1] = 5;
        final Db db = Db.builder().testSetup().start();
        try {
            Trans.Builder b = db.trans();
            for (int i = 0; i < keys.length; i++) {
                b.put(keys[i], i == 3 ? new byte[0] : new byte[] {(byte) i});
            }
            db.execute(b.build());

            byte[][] sorted = Arrays.copyOf(keys, keys.length + 1);
            sorted[keys.length] = Keys.toBytes(DbConstants.SD_KEY);    // bergdb 028-15
            Arrays.sort(sorted, Arrays::compareUnsigned);
            List<Kvt> forward = scan(db, null);
            GetMany g = db.newGetMany();
            g.forward = false;
            db.getMany(g);
            Assert.assertEquals("forward", sorted.length, forward.size());
            Assert.assertEquals("backward", sorted.length, g.result.size());
            for (int i = 0; i < sorted.length; i++) {
                Assert.assertTrue("forward, KV " + i,
                        Arrays.equals(sorted[i], Keys.toBytes(forward.get(i).key)));
                Assert.assertTrue("backward, KV " + i, Arrays.equals(
                        sorted[sorted.length - 1 - i], Keys.toBytes(g.result.get(i).key)));
            }

            byte[] v = db.getOne(LATEST, Keys.toSegments(new byte[0]), db.newGetData());
            Assert.assertTrue("the empty key", v != null && v.length == 1 && v[0] == 0);
            v = db.getOne(LATEST, Keys.toSegments(keys[3]), db.newGetData());
            Assert.assertTrue("the empty value is a value", v != null && v.length == 0);
            v = db.getOne(LATEST, Keys.toSegments(longKey), db.newGetData());
            Assert.assertTrue("the long key", v != null && v[0] == keys.length - 1);
            assertThrows("a key of 112 bytes", IllegalArgumentException.class,
                    () -> db.trans().put(new byte[Db.MAX_KEY_BYTES + 1], new byte[0]));
            assertThrows("a null value", IllegalArgumentException.class,
                    () -> db.trans().put(new byte[] {1}, null));
            assertThrows("a null value, a key of segments", IllegalArgumentException.class,
                    () -> db.trans().put(Keys.toSegments(new byte[] {1}), null));
        } finally {
            db.close();
        }
    }

    /**
     * Db, "Keys and the layers above" (bergdb 020-24-09, U9-4): the Core writes BergDB's keys
     * itself, with no Pub API: a new database has one, the startup distance, 4 bytes at
     * "/#i/-sd", which setStartupDistance() puts again (bergdb 028-15; a value
     * of 200 kB at "/#i/-dummy" until then), setRetainDuration() reclaim's settings at
     * "/#i/dreclaim/-settings.txt"; a scan returns them, getTransactionCount() counts their
     * transactions, and a StopCondition that returns CONTINUE for the keys that start with 01
     * 25 leaves the user's keys, those around 01 25 too.
     */
    @Nano
    public static void testCoreWritesBergDbsKeys() {
        Db db = Db.builder().testSetup().start();
        try {
            byte[][] mine = {{0}, {1, 0x24}, {1, 0x24, (byte) 0xff}, {1, 0x26}, {(byte) 0xff}};
            Trans.Builder b = db.trans();
            for (byte[] k : mine) {
                b.put(k, new byte[] {7});
            }
            db.execute(b.build());
            Assert.assertEquals("a new database", mine.length + 1, scan(db, null).size());

            db.setStartupDistance(500 * 1000);
            db.setRetainDuration(3600 * Clock.UNITS_PER_SEC);
            Assert.assertEquals("transactions", 3, db.getTransactionCount());
            byte[] sd = Keys.toBytes("/#i/-sd");
            byte[] settings = Keys.toBytes("/#i/dreclaim/-settings.txt");
            List<byte[]> bergdbs = new ArrayList<>();
            for (Kvt kvt : scan(db, null)) {
                byte[] k = Keys.toBytes(kvt.key);
                if (k.length >= 2 && k[0] == 1 && k[1] == 0x25) {
                    bergdbs.add(k);
                    if (Arrays.equals(k, sd)) {
                        Assert.assertArrayEquals("the startup distance's value",
                                new byte[] {0x20, (byte) 0xa1, 0x07, 0}, kvt.value);
                    }
                }
            }
            Assert.assertEquals("BergDB's keys", 2, bergdbs.size());
            Assert.assertTrue("/#i/-sd", Arrays.equals(sd, bergdbs.get(0)));
            Assert.assertTrue("the settings", Arrays.equals(settings, bergdbs.get(1)));

            List<Kvt> yours = scan(db, new GetMany.StopCondition() {
                public int handleKvt(Kvt kvt) {
                    byte[] k = Keys.toBytes(kvt.key);
                    return k.length >= 2 && k[0] == 1 && k[1] == 0x25 ? CONTINUE : ADD;
                }

                public void eod() {}
            });
            Assert.assertEquals("the user's keys", mine.length, yours.size());
            for (int i = 0; i < mine.length; i++) {
                Assert.assertTrue("key " + i,
                        Arrays.equals(mine[i], Keys.toBytes(yours.get(i).key)));
            }
        } finally {
            db.close();
        }
    }

    /**
     * Db.getTransactionCount() and getKvCount() count since the start: each transaction's
     * KVs, a delete of a key without a value too, and 0 after a start (bergdb 020-24-09,
     * U9-10). Db.getTrans(): a delete of a key that had no value is not listed, a delete of a
     * key with one is (U9-9).
     */
    @Nano
    public static void testCountersAndListedDeletes() {
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).start();
        try {
            db.execute(db.trans().put("a", "1").put("b", "2").build());
            Trans t = db.trans().delete("a").delete("never").put("c", "3").build();
            db.execute(t);
            Assert.assertEquals("transactions", 2, db.getTransactionCount());
            Assert.assertEquals("KVs", 5, db.getKvCount());
            Set<String> listed = new HashSet<>();
            for (StoredValueNode n : db.getTrans(t.tpos).getValueNodes()) {
                listed.add(Keys.toString(n.getKey()));
            }
            Assert.assertEquals("listed", new HashSet<>(Arrays.asList("a", "c")), listed);
        } finally {
            db.close();
        }
        db = Db.builder().testSetup(s.copy()).start();
        try {
            Assert.assertEquals("transactions after a start", 0, db.getTransactionCount());
            Assert.assertEquals("KVs after a start", 0, db.getKvCount());
            Assert.assertEquals("3", new String(get(db, "c")));
        } finally {
            db.close();
        }
    }

    /**
     * Db, "Optimistic transactions" (bergdb 020-24-09, U9-7): a transaction whose key read,
     * with a value or without, a later transaction wrote after its read time is refused with
     * RerunException, nothing changed, and runs again at a new read time; the default read
     * time checks nothing; a virtual write hash conflicts with a read of its hash.
     */
    @Nano
    public static void testOptimisticTransactions() {
        final Db db = dbWithKeys(0);
        try {
            final byte[] key = {9};
            final byte[] other = {8};
            final long t1 = db.currentTime();
            db.execute(db.trans().put(key, new byte[] {1}).build());
            assertThrows("the key read, written after t1", RerunException.class,
                    () -> db.execute(db.trans().lookupTime(t1).keyRead(Keys.toSegments(key))
                            .put(other, new byte[] {2}).build()));
            Assert.assertTrue("nothing changed",
                    db.getOne(LATEST, Keys.toSegments(other), db.newGetData()) == null);
            long t2 = db.currentTime();
            db.execute(db.trans().lookupTime(t2).keyRead(Keys.toSegments(key))
                    .put(other, new byte[] {2}).build());
            Assert.assertEquals("ran", 2,
                    db.getOne(LATEST, Keys.toSegments(other), db.newGetData())[0]);

            final byte[] absent = {7};
            final long t3 = db.currentTime();
            db.execute(db.trans().put(absent, new byte[] {3}).build());
            assertThrows("a key read without a value, then put", RerunException.class,
                    () -> db.execute(db.trans().lookupTime(t3).keyRead(Keys.toSegments(absent))
                            .put(other, new byte[] {4}).build()));
            db.execute(db.trans().keyRead(Keys.toSegments(absent)).put(other, new byte[] {5})
                    .build());

            final long t4 = db.currentTime();
            db.execute(db.trans().addVirtualWriteHash(12345).put(new byte[] {6}, new byte[] {6})
                    .build());
            assertThrows("a virtual write hash", RerunException.class,
                    () -> db.execute(db.trans().lookupTime(t4).addReadHash(12345)
                            .put(other, new byte[] {6}).build()));
            Assert.assertEquals("the last that ran", 5,
                    db.getOne(LATEST, Keys.toSegments(other), db.newGetData())[0]);
        } finally {
            db.close();
        }
    }

    /**
     * GetMany (bergdb 020-24-09, U9-8): Db.newGetMany()'s defaults, the latest state, from the
     * first key, inclusive, forward, a DontStop; a second getMany() with the same GetMany,
     * whose result has KVs, is refused with IllegalArgumentException (bergdb 020-27, Q2;
     * before, an AssertionError with -ea), and the database goes on.
     */
    @Nano
    public static void testGetManyDefaultsAndOneCall() {
        final Db db = dbWithKeys(3);
        try {
            final GetMany g = db.newGetMany();
            Assert.assertEquals("lookupTime", LATEST, g.lookupTime);
            Assert.assertTrue("startKey", g.startKey == null);
            Assert.assertTrue("inclusive, forward", g.inclusive && g.forward);
            Assert.assertTrue("stopCondition", g.stopCondition instanceof GetMany.DontStop);
            db.getMany(g);
            Assert.assertEquals("every KV", 3 + NEW_DB_KVS, g.result.size());
            assertThrows("a second call", IllegalArgumentException.class, () -> db.getMany(g));
            Assert.assertEquals("v0", new String(get(db, "k0")));
        } finally {
            db.close();
        }
    }

    /**
     * Kvt.time and GetData.kvTime: the time of the key node entry that points to the value,
     * not the time of the write (bergdb 021-19; 020-24-09, U9-3). T1 puts 25 keys, and T2 a
     * 26th, which makes PE cut their full key node's live list into new nodes, so T1's keys read T2's
     * time; at or after the write's time and at or before the lookup time; a read before T2
     * gives T1's; the write's time is getTrans(tpos).tt. If the time becomes the write's, the
     * last assertion fails, and the Javadoc of both is to change. 25 keys since bergdb 028-15:
     * the startup distance's KV, with its time klong, takes two places in the root.
     */
    @Nano
    public static void testKvTimeIsTheEntrysTime() {
        Db db = Db.builder().testSetup().start();
        final int n = 25;
        try {
            Trans.Builder b = db.trans();
            for (int i = 0; i < n; i++) {
                b.put(new byte[] {(byte) (2 * i)}, new byte[] {1});
            }
            Trans t1 = b.build();
            db.execute(t1);
            Trans t2 = db.trans().put(new byte[] {55}, new byte[] {2}).build();
            db.execute(t2);

            GetMany g = db.newGetMany();
            db.getMany(g);
            Assert.assertEquals("KVs", n + 1 + NEW_DB_KVS, g.result.size());
            GetData gd = db.newGetData();
            int later = 0;
            for (Kvt kvt : g.result) {
                if (bergDbKey(kvt.key)) continue;       // the startup distance (bergdb 028-15)
                boolean ofT2 = Keys.toBytes(kvt.key)[0] == 55;
                long written = ofT2 ? t2.tt : t1.tt;
                Assert.assertTrue("at or after the write's time", kvt.time >= written);
                Assert.assertTrue("at or before the lookup time",
                        kvt.time <= g.actualLookupTime);
                Assert.assertTrue("getOne", db.getOne(g.actualLookupTime, kvt.key, gd) != null);
                Assert.assertEquals("getOne's kvTime", kvt.time, gd.kvTime);
                Assert.assertEquals("the write's time", written, db.getTrans(gd.tpos).tt);
                if (!ofT2) {
                    Assert.assertTrue("before T2", db.getOne(t2.tt - 1, kvt.key, gd) != null);
                    Assert.assertEquals("kvTime before T2", t1.tt, gd.kvTime);
                }
                later += kvt.time != written ? 1 : 0;
            }
            Assert.assertEquals("T1's keys with T2's time", n, later);
        } finally {
            db.close();
        }
    }

    /**
     * Each of the 'count' builders had a call refused, and is spoiled (Trans.Builder; bergdb
     * 024-26, U26-5; 024-27): build() throws IllegalStateException, the refusal its cause.
     */
    private static void assertSpoiled(List<Trans.Builder> made, int count) {
        Assert.assertEquals("builders", count, made.size());
        for (Trans.Builder x : made) {
            Throwable e = thrown(() -> x.build());
            Assert.assertTrue("spoiled: " + e, e instanceof IllegalStateException
                    && e.getCause() instanceof IllegalArgumentException);
        }
    }

    private static void assertNullRefused(String[] params, Call[] calls) {
        Assert.assertEquals("cases", params.length, calls.length);
        for (int i = 0; i < calls.length; i++) {
            assertNullRefused("call " + i + ", " + params[i], params[i], calls[i]);
        }
    }

    /** Asserts that the call throws IllegalArgumentException with "PARAM == null" first. */
    private static void assertNullRefused(String about, String param, Call call) {
        Throwable e = thrown(call);
        Assert.assertTrue(about + ": expected IllegalArgumentException, got " + e,
                e instanceof IllegalArgumentException);
        Assert.assertTrue(about + ": the message names it, " + e.getMessage(),
                e.getMessage() != null && e.getMessage().startsWith(param + " == null"));
    }

    /**
     * Db refuses a null argument with IllegalArgumentException that names it, as every null
     * argument of the API (bergdb 020-27, Q2; Frans's decision for the Pub API, 020-21, 3),
     * before anything else: a refused read or transaction leaves the database active and
     * unchanged; getMany() refuses a null stop condition; after stop() the same. Until
     * 2026-11-14, start(null) too, before it closed anything: bergdb 028-10 removed start's
     * parameter.
     */
    @Nano
    public static void testDbNullArguments() {
        final Db db = Db.builder().testSetup().build();
        try {
            db.start();
            db.execute(db.trans().put("k", "v"));
            final GetData gd = db.newGetData();
            final GetMany noStop = db.newGetMany();
            noStop.stopCondition = null;
            String[] params = {"keySegments", "gd", "g", "g.stopCondition", "t", "b", "out",
                "syncLevel", "syncLevel"};
            Call[] calls = {
                () -> db.getOne(LATEST, null, gd),
                () -> db.getOne(LATEST, Keys.toSegments("k"), null),
                () -> db.getMany(null),
                () -> db.getMany(noStop),
                () -> db.execute((Trans) null),
                () -> db.execute((Trans.Builder) null),
                () -> db.printDag(null),
                () -> db.sync(null),
                () -> db.sync(0, null)};
            long length = db.getStreamLength();
            assertNullRefused(params, calls);
            Assert.assertEquals("nothing written", length, db.getStreamLength());
            Assert.assertEquals("v", new String(get(db, "k")));
            db.execute(db.trans().put("k", "v2"));
            Assert.assertEquals("v2", new String(get(db, "k")));

            db.stop();
            assertNullRefused(params, calls);
        } finally {
            db.close();
        }
    }

    /**
     * DbBuilder refuses a null argument with IllegalArgumentException that names it, at the
     * call (bergdb 020-27, Q2): clock(null) was taken and refused by build(), mainStream(null)
     * removed the stream before its refusal, evictionSchedule(null) and createdTxt(null)
     * were taken. Nothing is changed by a refusal: the builder starts its database after them
     * on its stream.
     */
    @Nano
    public static void testDbBuilderNullArguments() {
        final MemoryStream s = new MemoryStream();
        final DbBuilder b = Db.builder().testSetup(s);
        String[] params = {"clock", "id", "schedule", "stream", "stream", "name", "stream",
            "name", "stream", "dir"};
        Call[] calls = {
            () -> b.clock(null),
            () -> b.id(null),
            () -> b.evictionSchedule(null, 1),
            () -> b.mainStream(null),
            () -> b.stream("main", null),
            () -> b.stream(null, s),
            () -> b.stream("main", null, 100, 10),
            () -> b.stream(null, s, 100, 10),
            () -> b.testSetup(null),
            () -> b.createdTxt(null)};
        assertNullRefused(params, calls);
        Db db = b.start();
        try {
            db.execute(db.trans().put("k", "v"));
            db.sync(SyncLevel.ORDINARY);
            Assert.assertTrue("on the builder's stream", s.getLength() > 0);
        } finally {
            db.close();
        }
    }

    /**
     * Trans.Builder refuses a null key, value, read key or hash array with
     * IllegalArgumentException that names it (bergdb 020-27, Q2): a null key threw
     * NullPointerException, or AssertionError with -ea, and delete((long[]) null) was taken,
     * and build() threw. A refusal adds nothing and spoils its builder: build() then throws
     * IllegalStateException (bergdb 024-26, U26-5; 024-27), so each call has a builder of
     * its own. The transformations of put(long[], KeyTransformation, byte[],
     * ValueTransformation) may be null.
     */
    @Nano
    public static void testTransBuilderNullArguments() {
        final List<Trans.Builder> made = new ArrayList<>();
        final Supplier<Trans.Builder> nb = () -> {
            Trans.Builder x = new Trans.Builder().put("k", "v");
            made.add(x);
            return x;
        };
        final byte[] v = {1};
        final long[] k = Keys.toSegments("k2");
        String[] params = {"key", "key", "key", "key", "key", "key", "key", "key", "key",
            "key", "hashes", "value", "value", "value", "value", "value"};
        Call[] calls = {
            () -> nb.get().put((byte[]) null, v),
            () -> nb.get().put((long[]) null, v),
            () -> nb.get().put((long[]) null, null, v, null),
            () -> nb.get().put((String) null, "v"),
            () -> nb.get().put((String) null, v),
            () -> nb.get().delete((byte[]) null),
            () -> nb.get().delete((long[]) null),
            () -> nb.get().delete((String) null),
            () -> nb.get().keyRead((long[]) null),
            () -> nb.get().keyRead((String) null),
            () -> nb.get().addReadHashes(null, 0),
            () -> nb.get().put(Keys.toBytes("k2"), null),
            () -> nb.get().put(k, null),
            () -> nb.get().put(k, null, null, null),
            () -> nb.get().put("k2", (String) null),
            () -> nb.get().put("k2", (byte[]) null)};
        assertNullRefused(params, calls);
        assertSpoiled(made, calls.length);
        final Trans.Builder b = new Trans.Builder().put("k", "v");
        b.put(k, null, v, null);
        Trans t = b.build();
        Assert.assertEquals("kvs", 2, t.kvs.length);
        Assert.assertEquals("read hashes", 0, t.readKeyHashes.length);
    }

    /**
     * GetMany's stop conditions refuse a null key or prefix with IllegalArgumentException
     * that names it (bergdb 020-27, Q2): Endpoint and Prefix asserted it, PrefixN threw
     * NullPointerException.
     */
    @Nano
    public static void testGetManyNullArguments() {
        String[] params = {"key", "key", "key", "prefix", "prefix"};
        Call[] calls = {
            () -> new GetMany.Endpoint(null),
            () -> new GetMany.Endpoint(null, false),
            () -> new GetMany.Endpoint(null, true, true),
            () -> new GetMany.Prefix(null),
            () -> new GetMany.PrefixN(null, 3)};
        assertNullRefused(params, calls);
    }

    /**
     * The Core API refuses an argument out of its range with IllegalArgumentException, never
     * an assert that depends on -ea (bergdb 020-27, Q2, range checks): a key of no segments
     * in Trans.Builder's put(), delete() and keyRead() (with -ea a put or a delete of one
     * failed the database, without it was written) and in getOne() (it gave null); getMany()
     * with a startKey of no segments (with -ea it failed the database, without it gave no
     * KV), with a result that is not empty (without -ea it added to it), or with a stop
     * condition that answers none of the four (with -ea it failed the database, without it
     * was CONTINUE); GetN and PrefixN with a negative count (no KV); addReadHashes() with a
     * length outside 0 to hashes.length (without -ea an ArrayIndexOutOfBoundsException, some
     * hashes added). Each message names the argument; the database goes on, unchanged. Each
     * Trans.Builder call has a builder of its own, which the refusal spoils (bergdb 024-26,
     * U26-5; 024-27).
     */
    @Nano
    public static void testRangeArguments() {
        final Db db = dbWithKeys(2);
        try {
            final long[] none = new long[0];
            final byte[] v = {1};
            final GetMany emptyStart = db.newGetMany();
            emptyStart.startKey = none;
            final GetMany notEmpty = db.newGetMany();
            db.getMany(notEmpty);
            Assert.assertEquals("two KVs", 2 + NEW_DB_KVS, notEmpty.result.size());
            final GetMany badAnswer = db.newGetMany();
            badAnswer.stopCondition = new GetMany.StopCondition() {
                public int handleKvt(Kvt kvt) {
                    return 7;
                }
                public void eod() {}
            };
            final List<Trans.Builder> made = new ArrayList<>();     // one a call (024-27)
            final Supplier<Trans.Builder> b = () -> {
                Trans.Builder x = db.trans();
                made.add(x);
                return x;
            };
            String[] params = {"key", "key", "key", "key", "keySegments", "g.startKey",
                "g.result", "handleKvt", "maxCount", "maxCount", "length", "length"};
            Call[] calls = {
                () -> b.get().put(none, v),
                () -> b.get().put(none, null, v, null),
                () -> b.get().delete(none),
                () -> b.get().keyRead(none),
                () -> db.getOne(LATEST, none, db.newGetData()),
                () -> db.getMany(emptyStart),
                () -> db.getMany(notEmpty),
                () -> db.getMany(badAnswer),
                () -> new GetMany.GetN(-1),
                () -> new GetMany.PrefixN(Keys.toSegments("k"), -1),
                () -> b.get().addReadHashes(new long[] {1}, 2),
                () -> b.get().addReadHashes(new long[] {1}, -1)};
            long length = db.getStreamLength();
            for (int i = 0; i < calls.length; i++) {
                String about = "call " + i + ", " + params[i];
                Throwable e = thrown(calls[i]);
                Assert.assertTrue(about + ": expected IllegalArgumentException, got " + e,
                        e instanceof IllegalArgumentException);
                Assert.assertTrue(about + ": the message names it, " + e.getMessage(),
                        e.getMessage().contains(params[i]));
            }
            Assert.assertEquals("unchanged", 2 + NEW_DB_KVS, notEmpty.result.size());
            assertSpoiled(made, 6);
            Trans t = b.get().put("k2", "v2").build();
            Assert.assertEquals("nothing added", 1, t.kvs.length);
            Assert.assertEquals("no read hash", 0, t.readKeyHashes.length);
            db.execute(t);
            Assert.assertTrue("a commit", db.getStreamLength() > length);
            Assert.assertEquals("v0", new String(get(db, "k0")));
            Assert.assertEquals("v2", new String(get(db, "k2")));
        } finally {
            db.close();
        }
    }
}
