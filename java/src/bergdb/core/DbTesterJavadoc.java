package bergdb.core;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
     * Trans.Builder.build(): one operation a key: the last put, or a delete if there is no
     * put; a delete never replaces a put, whatever their order.
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
            String[][] expected = {{"a", "1"}, {"b", "2"}, {"c", "2"}, {"d", "3"}, {"e", null},
                    {"f", "2"}};
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

            long end = System.nanoTime() + 2000L * 1000 * 1000;
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
                g.stopCondition = new GetMany.GetN(n);
                db.getMany(g);
                Assert.assertEquals("GetN(" + n + ")", Math.min(n, 5), g.result.size());

                g = db.newGetMany();
                g.stopCondition = new GetMany.PrefixN(Keys.toSegments("k"), n);
                db.getMany(g);
                Assert.assertEquals("PrefixN(k, " + n + ")", Math.min(n, 5), g.result.size());
            }
            GetMany g = db.newGetMany();
            g.stopCondition = new GetMany.GetOne();
            db.getMany(g);
            Assert.assertEquals("GetOne", 1, g.result.size());

            long[] prefix = Keys.toSegments("k");
            g = db.newGetMany();
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
            int[] sizes = {3, 0};
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
     * DbBuilder's refusals: id(null), startupDistance() below 10, stream() with a null name
     * or stream or a negative buffer size or time, reclaimStepReserve() below 1, each with
     * IllegalArgumentException, and a second stream's name with IllegalStateException;
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
            () -> Db.builder().startupDistance(9),
            () -> Db.builder().stream(null, s),
            () -> Db.builder().stream("main", null),
            () -> Db.builder().stream("main", s, -1, 10),
            () -> Db.builder().stream("main", s, 100, -1),
            () -> Db.builder().reclaimStepReserve(0),
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
        Db.builder().startupDistance(10);
        
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
}
