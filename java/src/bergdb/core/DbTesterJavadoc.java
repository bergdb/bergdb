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
