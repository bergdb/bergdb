package bergdb.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * The capacity controller (bergdb item 001, WP J7; Eviction, schedule BUDGET; the plan's
 * Q9 and Q10): the resident bytes (Residents) stay near the budget with reads and no
 * writes, with scans, with large puts and with stalled readers; pinned state above the
 * budget is kept, reported, and changes no record; and the records and answers are those
 * of a database without eviction.
 */
public class CapacityTester {
    private static final long STEP = bergdb.pub.util.Clock.UNITS_PER_SEC / 100;

    private static DbBuilder builder(MemoryStream s, CoreTestClock clock, long budget) {
        DbBuilder b = Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8()
                .startupDistance(2000);
        if (budget > 0) b.cacheSizeIndicator(budget).evictionSchedule(Eviction.Schedule.BUDGET, 1);
        return b;
    }

    private static String value(int k, int version, int size) {
        StringBuilder sb = new StringBuilder("v" + k + "." + version + ":");
        while (sb.length() < size) sb.append((char) ('a' + (k + sb.length()) % 26));
        return sb.toString();
    }

    /** n keys, then 'updates' transactions of one put each; returns the last value of each. */
    private static String[] load(Db db, CoreTestClock clock, int n, int updates, int size) {
        String[] last = new String[n];
        long time = 100 * STEP;
        for (int i = 0; i < n; i += 50) {
            time += STEP;
            clock.setTime(time);
            Trans.Builder b = db.trans();
            for (int k = i; k < Math.min(n, i + 50); k++) {
                last[k] = value(k, 0, size);
                b.put("k" + k, last[k]);
            }
            db.execute(b.build());
        }
        Random r = new Random(1);
        for (int u = 0; u < updates; u++) {
            time += STEP;
            clock.setTime(time);
            int k = r.nextInt(n);
            last[k] = value(k, u + 1, size);
            db.execute(db.trans().put("k" + k, last[k]).build());
        }
        return last;
    }

    /**
     * The resident bytes, after the eviction thread has run the batches that readers asked
     * for (bergdb item 009, step 3b: a reader no longer runs them itself; 009-02, T5a).
     */
    private static long bytes(Db db) {
        db.internal().eviction().awaitBatch();
        return db.internal().cache().residents().bytes();
    }

    /** The index of each key "k" + i, by the key's segments (Keys.toSegments). */
    private static java.util.Map<String, Integer> keyIndex(int n) {
        java.util.Map<String, Integer> m = new java.util.HashMap<String, Integer>();
        for (int i = 0; i < n; i++) m.put(Arrays.toString(bergdb.dag.Keys.toSegments("k" + i)), i);
        return m;
    }

    /**
     * Reads with no writes: a database of about 1.4 MB of values, started cold with a budget
     * of 200 kB; every key read in random order, three times. After each read the resident
     * bytes are at most the budget plus one load's worth (the controller sweeps after the
     * load that passes the budget, under the write lock, with no writer about); the sweeps
     * are load-triggered; every value is right. The unit test is smaller: 1000 keys, a
     * budget of 50 kB.
     */
    @Nano
    public static void testReadsWithoutWrites() {
        readsWithoutWrites(1000, 500, 50 * 1000);
    }

    @Nano("f")
    public static void testReadsWithoutWritesF() {
        readsWithoutWrites(4000, 2000, 200 * 1000);
    }

    private static void readsWithoutWrites(int n, int updates, long budget) {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = builder(s, clock, 0).start();
        String[] last = load(db, clock, n, updates, 300);
        db.sync(SyncLevel.STRONG);
        db.stop();
        db = builder(s.copy(), clock, budget).start();
        Random r = new Random(2);
        long max = 0;
        for (int round = 0; round < 3; round++) {
            for (int j = 0; j < n; j++) {
                int k = r.nextInt(n);
                Assert.assertEquals(last[k], new String(DbUtil.get(db, "k" + k)));
                max = Math.max(max, bytes(db));
            }
        }
        long[] c = db.internal().eviction().sweepCounts();
        Assert.assertTrue("sweeps after loads: " + c[1], c[1] > 0);
        Assert.assertTrue("at most " + max + " bytes, budget " + budget, max <= budget + 20 * 1000);
        db.stop();
    }

    /** A database of n keys of 300 bytes, started cold with the budget, every key read. */
    private static Db readAll(int n, long budget) {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = builder(s, clock, 0).start();
        String[] last = load(db, clock, n, 0, 300);
        db.sync(SyncLevel.STRONG);
        db.stop();
        db = builder(s.copy(), clock, budget).start();
        for (int k = 0; k < n; k++) {
            Assert.assertEquals(last[k], new String(DbUtil.get(db, "k" + k)));
        }
        return db;
    }

    /**
     * The budget lowered and raised while the database runs (Db.setCacheSizeIndicator,
     * bergdb 005-52), with reads and no writes: 2000 keys of 300 bytes, started cold with a
     * budget of 10 MB and every key read, so that every value is resident; the budget
     * lowered to a quarter of the resident bytes; from the second round of random reads on,
     * the resident bytes are at most the new budget plus one load's worth; the budget raised
     * again, the reads grow them past the low budget.
     */
    @Nano
    public static void testBudgetLoweredAndRaisedUnderReads() {
        int n = 2000;
        Db db = readAll(n, 10 * 1000 * 1000);
        long full = bytes(db);
        long low = full / 4;
        db.setCacheSizeIndicator(low);
        Assert.assertEquals(low, db.getCacheSizeIndicator());
        Random r = new Random(3);
        long max = 0;
        for (int round = 0; round < 3; round++) {
            for (int j = 0; j < n; j++) {
                DbUtil.get(db, "k" + r.nextInt(n));
                if (round > 0) max = Math.max(max, bytes(db));
            }
        }
        Assert.assertTrue("at most " + max + " bytes, budget " + low + " of " + full,
                max <= low + 20 * 1000);
        
        db.setCacheSizeIndicator(10 * 1000 * 1000);
        for (int k = 0; k < n; k++) DbUtil.get(db, "k" + k);
        Assert.assertTrue("grown after the raise: " + bytes(db), bytes(db) > 2 * low);
        db.stop();
    }

    /**
     * A database that is not used gives the memory back after a lower budget (bergdb 005-52):
     * as testBudgetLoweredAndRaisedUnderReads, the budget lowered to a quarter of the resident
     * bytes, and no other call: the eviction thread, woken by the call, brings them to at most
     * the budget within 2 s. Until 005-52 nothing ran until the next commit or load (005-51).
     */
    @Nano
    public static void testBudgetLoweredWhileIdle() throws InterruptedException {
        Db db = readAll(2000, 10 * 1000 * 1000);
        long full = bytes(db);
        long low = full / 4;
        db.setCacheSizeIndicator(low);
        long end = System.nanoTime() + 2000L * 1000 * 1000;
        long bytes = full;
        while (System.nanoTime() < end) {
            bytes = db.internal().cache().residents().bytes();
            if (bytes <= low) break;
            Thread.sleep(1);
        }
        db.stop();
        Assert.assertTrue("at most " + bytes + " bytes, budget " + low + " of " + full,
                bytes <= low);
    }

    /**
     * A sweep stops near the low watermark: reads with no writes on a cold database whose
     * index alone is several times the budget, as at the end of the run of
     * bergdb 001-10: a scan of every key (one operation, so the slots it follows
     * get the same access time), then every key read in order, twice. A sweep counts the
     * objects that leave the resident set with those it takes (Eviction.drop: the snapshots
     * below a slot it unswizzles), so after the first sweep the resident bytes, sampled
     * after every read, stay near the low watermark or above it. Before 2026-10-18 a sweep
     * counted only the objects it released and here went down to the pinned state.
     */
    @Nano
    public static void testSweepsStopNearLow() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = builder(s, clock, 0).start();
        int n = 6000;
        String[] last = load(db, clock, n, 0, 100);
        db.sync(SyncLevel.STRONG);
        db.stop();
        long budget = 60 * 1000;
        db = builder(s.copy(), clock, budget).start();
        GetMany g = db.newGetMany();
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                return CONTINUE;
            }
            public void eod() {}
        };
        db.getMany(g);
        long min = Long.MAX_VALUE;
        for (int round = 0; round < 2; round++) {
            for (int k = 0; k < n; k++) {
                Assert.assertEquals(last[k], new String(DbUtil.get(db, "k" + k)));
                if (db.internal().eviction().sweepCounts()[1] > 0) {
                    min = Math.min(min, bytes(db));
                }
            }
        }
        long[] c = db.internal().eviction().sweepCounts();
        Assert.assertTrue("sweeps after loads: " + c[1], c[1] > 10);
        Assert.assertTrue("at least " + min + " bytes after the first sweep, budget " + budget,
                min >= budget / 2);
        db.stop();
    }

    /**
     * Scans: a scan over every key of a cold database with a budget much smaller than the
     * data; the resident bytes, sampled at every KV, stay near the budget (the sweeps run
     * after loads, between the scan's steps), and the scan's result is right.
     */
    @Nano
    public static void testScans() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = builder(s, clock, 0).start();
        int n = 4000;
        String[] last = load(db, clock, n, 0, 300);
        db.sync(SyncLevel.STRONG);
        db.stop();
        final long budget = 200 * 1000;
        final Db db2 = builder(s.copy(), clock, budget).start();
        final long[] max = new long[1];
        for (int round = 0; round < 2; round++) {
            GetMany g = db2.newGetMany();
            g.stopCondition = new GetMany.StopCondition() {
                public int handleKvt(Kvt kvt) {
                    max[0] = Math.max(max[0], bytes(db2));
                    return ADD;
                }
                public void eod() {}
            };
            db2.getMany(g);
            int found = 0;
            java.util.Map<String, Integer> index = keyIndex(n);
            for (Kvt kvt : g.result) {
                Integer k = index.get(Arrays.toString(kvt.key));
                if (k == null) continue;
                Assert.assertEquals(last[k], new String(kvt.value));
                found++;
            }
            Assert.assertEquals(n, found);
        }
        Assert.assertTrue("at most " + max[0] + " bytes, budget " + budget, max[0] <= budget + 20 * 1000);
        db2.stop();
    }

    /**
     * Large puts: values of 1.5 MiB, over the 1 MiB that a read does not cache, with a budget
     * of 4 MB: after every transaction the resident bytes are within the budget (the large
     * values go first), and the values read back are right. An f-test: about 1.4 s, most of
     * it waiting for the storage thread to take the values.
     */
    @Nano("f")
    public static void testLargePuts() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long budget = 4 * 1000 * 1000;
        Db db = builder(s, clock, budget).start();
        byte[][] values = new byte[12][];
        long time = 100 * STEP;
        for (int i = 0; i < 12; i++) {
            time += STEP;
            clock.setTime(time);
            values[i] = new byte[1536 * 1024];
            new Random(i).nextBytes(values[i]);
            db.execute(db.trans().put("big" + i, values[i]).put("small" + i, "s" + i).build());
            Assert.assertTrue("bytes " + bytes(db), bytes(db) <= budget);
        }
        for (int i = 0; i < 12; i++) {
            Assert.assertTrue(Arrays.equals(values[i], DbUtil.get(db, "big" + i)));
            Assert.assertEquals("s" + i, new String(DbUtil.get(db, "small" + i)));
        }
        db.stop();
    }

    /**
     * Stalled readers: two reader threads scan slowly (they pause at every KV), from a
     * snapshot each, while the writer runs 400 transactions with a budget much smaller than
     * the data, so that sweeps unswizzle and release what the readers hold. No deadlock;
     * every scan gives its snapshot; the resident bytes stay near the budget after every
     * transaction. An f-test: the readers' pauses alone take 0.4 s.
     */
    @Nano("f")
    public static void testStalledReaders() throws Exception {
        MemoryStream s = new MemoryStream();
        final CoreTestClock clock = new CoreTestClock();
        Db db0 = builder(s, clock, 0).start();
        final int n = 2000;
        final String[] base = load(db0, clock, n, 0, 300);
        db0.sync(SyncLevel.STRONG);
        db0.stop();
        final long budget = 150 * 1000;
        final Db db = builder(s.copy(), clock, budget).start();
        final long t0 = db.lookupTime(Long.MAX_VALUE);
        final ConcurrentLinkedQueue<String> problems = new ConcurrentLinkedQueue<String>();
        final AtomicLong scanned = new AtomicLong();
        final java.util.Map<String, Integer> index = keyIndex(n);
        List<Thread> readers = new ArrayList<Thread>();
        for (int r = 0; r < 2; r++) {
            Thread t = new Thread(new Runnable() {
                public void run() {
                    try {
                        GetMany g = db.newGetMany();
                        g.lookupTime = t0;
                        g.stopCondition = new GetMany.StopCondition() {
                            public int handleKvt(Kvt kvt) {
                                java.util.concurrent.locks.LockSupport.parkNanos(200 * 1000);
                                return ADD;
                            }
                            public void eod() {}
                        };
                        db.getMany(g);
                        for (Kvt kvt : g.result) {
                            Integer k = index.get(Arrays.toString(kvt.key));
                            if (k == null) continue;
                            if (!base[k].equals(new String(kvt.value))) {
                                problems.add("scan: k" + k);
                            }
                            scanned.incrementAndGet();
                        }
                    } catch (RuntimeException e) {
                        problems.add("scan failed: " + e);
                    }
                }
            });
            readers.add(t);
            t.start();
        }
        Random rnd = new Random(3);
        long time = clock.getTime();
        long max = 0;
        for (int i = 0; i < 400; i++) {
            time += STEP;
            clock.setTime(time);
            int k = rnd.nextInt(n);
            db.execute(db.trans().put("k" + k, value(k, 1000 + i, 300)).build());
            max = Math.max(max, bytes(db));
        }
        for (Thread t : readers) {
            t.join(60 * 1000);
            Assert.assertTrue("a reader is done", !t.isAlive());
        }
        Assert.assertTrue(problems.toString(), problems.isEmpty());
        Assert.assertEquals(2L * n, scanned.get());
        Assert.assertTrue("at most " + max + " bytes after a transaction, budget " + budget,
                max <= budget + 20 * 1000);
        db.stop();
    }

    /**
     * Pinned state above the budget: a budget of 20 kB, and a startup distance of 2 MB, so
     * that D holds far more than the budget. The pinned objects are kept, the sweeps report
     * the budget exceeded and do not run at every transaction, nothing fails or waits, and
     * the stream and the answers are those of a database without eviction. An f-test.
     */
    @Nano("f")
    public static void testPinnedAboveBudget() {
        MemoryStream s1 = new MemoryStream(), s2 = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db ref = Db.builder().testSetup(s1).clock(clock).testId().maxNodeSize8()
                .startupDistance(2000 * 1000).start();
        Db db = Db.builder().testSetup(s2).clock(clock).testId().maxNodeSize8()
                .startupDistance(2000 * 1000).cacheSizeIndicator(20 * 1000)
                .evictionSchedule(Eviction.Schedule.BUDGET, 1).audit(1).start();
        long auditFailures = Audit.failures();
        Random r = new Random(4);
        long time = 100 * STEP;
        for (int i = 0; i < 600; i++) {
            time += STEP;
            clock.setTime(time);
            int k = r.nextInt(1000);
            for (Db d : new Db[] {ref, db}) {
                d.execute(d.trans().put("k" + k, value(k, i, 100)).build());
            }
        }
        long[] c = db.internal().eviction().sweepCounts();
        Assert.assertTrue("sweeps above the budget: " + c[3], c[3] > 0);
        // Not a sweep at every transaction: the next waits for growth (Eviction.trigger).
        Assert.assertTrue("sweeps " + c[0] + " in 600 transactions", c[0] < 100);
        ref.sync(SyncLevel.STRONG);
        db.sync(SyncLevel.STRONG);
        Assert.assertEquals(s1.getLength(), s2.getLength());
        byte[] b1 = new byte[(int) s1.getLength()], b2 = new byte[(int) s2.getLength()];
        try {
            s1.read(0, b1, 0, b1.length);
            s2.read(0, b2, 0, b2.length);
        } catch (java.io.IOException e) {
            throw new RuntimeException(e);
        }
        Assert.assertTrue("same stream", Arrays.equals(b1, b2));
        for (int k = 0; k < 1000; k++) {
            Assert.assertTrue(Arrays.equals(DbUtil.get(ref, "k" + k), DbUtil.get(db, "k" + k)));
        }
        Assert.assertEquals(auditFailures, Audit.failures());
        ref.stop();
        db.stop();
    }

    /**
     * The budget through JMX (Jmx.DbMonitor: the cache size indicator is the budget, the
     * cache's total size the resident bytes): a database loaded with no budget to speak of,
     * then a budget of 100 kB set through the monitor; after the next transaction the resident
     * bytes are within it.
     */
    @Nano
    public static void testBudgetThroughJmx() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = builder(s, clock, 1000L * 1000 * 1000).start();
        load(db, clock, 2000, 0, 300);
        Jmx.DbMonitor monitor = new Jmx.DbMonitor(db);
        Assert.assertEquals(bytes(db), monitor.getCacheTotalSize());
        Assert.assertTrue("over 100 kB first", bytes(db) > 100 * 1000);
        monitor.setCacheSizeIndicator(100 * 1000);
        Assert.assertEquals(100L * 1000, monitor.getCacheSizeIndicator());
        clock.setTime(clock.getTime() + STEP);
        db.execute(db.trans().put("k0", "x").build());
        Assert.assertTrue("bytes " + bytes(db), bytes(db) <= 100 * 1000);
        db.stop();
    }

    /**
     * The same records and answers as without eviction, with the controller and a small
     * budget, reads at old times among the writes, and restarts; the audit after every
     * transaction. The unit test runs 300 transactions, the f-test 800.
     */
    @Nano
    public static void testSameRecordsAsWithoutEviction() {
        sameRecordsAsWithoutEviction(300);
    }

    @Nano("f")
    public static void testSameRecordsAsWithoutEvictionF() {
        sameRecordsAsWithoutEviction(800);
    }

    private static void sameRecordsAsWithoutEviction(int n) {
        MemoryStream s1 = new MemoryStream(), s2 = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db ref = builder(s1, clock, 0).start();
        Db db = builder(s2, clock, 60 * 1000).audit(1).start();
        long auditFailures = Audit.failures();
        Random r = new Random(5);
        List<Long> times = new ArrayList<Long>();
        long time = 100 * STEP;
        for (int i = 0; i < n; i++) {
            time += STEP;
            clock.setTime(time);
            int k = r.nextInt(500);
            for (Db d : new Db[] {ref, db}) {
                Trans.Builder b = d.trans().put("k" + k, value(k, i, 120));
                if (i % 7 == 3) b.delete("k" + ((k + 11) % 500));
                d.execute(b.build());
            }
            times.add(time);
            if (i % 20 == 19) {
                long t = times.get(r.nextInt(times.size()));
                for (int j = 0; j < 30; j++) {
                    String key = "k" + r.nextInt(500);
                    Assert.assertTrue(Arrays.equals(DbUtil.get(ref, t, key), DbUtil.get(db, t, key)));
                }
            }
            if (i % 250 == 249) {
                db.sync(SyncLevel.STRONG);
                db.stop();
                s2 = s2.copy();
                db = builder(s2, clock, 60 * 1000).audit(1).start();
            }
        }
        ref.sync(SyncLevel.STRONG);
        db.sync(SyncLevel.STRONG);
        Assert.assertEquals(s1.getLength(), s2.getLength());
        byte[] b1 = new byte[(int) s1.getLength()], b2 = new byte[(int) s2.getLength()];
        try {
            s1.read(0, b1, 0, b1.length);
            s2.read(0, b2, 0, b2.length);
        } catch (java.io.IOException e) {
            throw new RuntimeException(e);
        }
        Assert.assertTrue("same stream", Arrays.equals(b1, b2));
        Assert.assertTrue("sweeps", db.internal().eviction().sweepCounts()[0] > 0);
        Assert.assertEquals(auditFailures, Audit.failures());
        ref.stop();
        db.stop();
    }

    /**
     * A batch on a pinned leaf (bergdb 015-15; 016-06/R1, R1-F4, and its probe): with a
     * startup distance of 100 kB a leaf stays in D, dirty, while the writer puts 20 values of
     * 1,000 bytes into it, which are counted from its write, not before; a batch (a budget of
     * 1,000 bytes) takes them as stream pointers (Eviction.unswizzleValues). The leaf's count
     * goes down to its bytes without its values (its own and its entry in the node table,
     * bergdb 015-13), no further, and after its write it is its bytes again; its
     * eviction, written, takes the object counter down by one. Throughout,
     * every resident index object is counted (checkCounts). Before the fix the batch took the
     * leaf's count to 0, which meant "not counted", and it stayed 0 after the leaf's write.
     */
    @Nano
    public static void testBatchOnPinnedLeaf() {
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(new MemoryStream()).clock(clock).testId()
                .startupDistance(100 * 1000).start();
        try {
            Db.Internal in = db.internal();
            StringBuilder big = new StringBuilder();
            while (big.length() < 1000) big.append('x');
            long time = 100 * STEP;
            for (int t = 0; t < 20; t++) {
                clock.setTime(time += STEP);
                db.execute(db.trans().put("k" + (100 + t), big.toString() + t).build());
            }
            KeyNode leaf = null;
            for (Node o : in.cache().nodes()) {
                if (o instanceof KeyNode && ((KeyNode) o).isSegmentLeaf() && o.isDirty()
                        && Residents.bytesOf(o) > o.getMemSize() + 10 * 1000) {
                    leaf = (KeyNode) o;
                }
            }
            Assert.assertTrue("a dirty leaf with the values", leaf != null);
            Assert.assertTrue("its values not all counted: " + leaf.countedMemSize,
                    leaf.countedMemSize < Residents.bytesOf(leaf));
            checkCounts(db);

            // A batch ends after 2 ms (Eviction.BATCH_NANOS): under load one may not reach the
            // leaf's map, the next goes on from the hand.
            for (int i = 0; i < 1000
                    && Residents.bytesOf(leaf) > Residents.bytesWithoutValues(leaf); i++) {
                batch(db, 1000);
            }
            Assert.assertTrue("dirty", leaf.isDirty());
            Assert.assertEquals("its values taken", Residents.bytesWithoutValues(leaf),
                    Residents.bytesOf(leaf));
            Assert.assertEquals("its count after the batch", Residents.bytesOf(leaf),
                    leaf.countedMemSize);
            checkCounts(db);

            for (int t = 20; t < 420 && leaf.isDirty(); t++) {
                clock.setTime(time += STEP);
                db.execute(db.trans().put("k" + (100 + t), big.toString() + t).build());
            }
            Assert.assertFalse("the leaf written", leaf.isDirty());
            Assert.assertTrue("in its handle", in.cache().getNode(leaf.getId()) == leaf);
            Assert.assertEquals("its count after its write", Residents.bytesOf(leaf),
                    leaf.countedMemSize);
            checkCounts(db);

            long objects = in.cache().residents().objects();
            synchronized (in.getWriteLock()) {
                Assert.assertTrue("the leaf evicted", in.cache().evict(leaf.handle));
            }
            Assert.assertEquals("not counted", -1, leaf.countedMemSize);
            Assert.assertEquals("one object less", objects - 1, in.cache().residents().objects());
            checkCounts(db);
        } finally {
            db.stop();
        }
    }

    /**
     * The handles counted (bergdb 015-13; 009-02, 4.7; 016-06/R1, R1-F2): 2000 keys of 300
     * bytes, started cold with a budget of 10 MB, every key read; then every object that can
     * go evicted (a budget of 1 byte), the budget raised again and every key read, so that
     * each object is counted from a load after the start. Each resident index object that is
     * not dirty is then counted by 4.7's rule, computed here apart from Residents: its own
     * bytes, 79 for its live handle with its entry in the node table, 32 for each pointer that
     * holds a handle, live or dead, and the bytes of its values (checkRule); the resident bytes
     * are the sum of the counts (checkCounts). The reads put handles into pointers of objects
     * counted before (a loaded object's pointers hold none), which the follow's swizzle counts
     * (Residents.handleIn). Then the budget lowered to a third: eviction leaves dead handles in
     * the pointers of the objects that stay, counted still; every key read again, and the rule
     * holds again. (Right after the start, a few objects of the startup section, counted
     * before the startup's rerun of its transactions grew them, are counted below their bytes
     * until their next write, as Residents' comment says of the objects the writer changed
     * since their last count; the eviction takes them.) Before 015-13 no handle was counted:
     * R1's probe found 34 to 49 percent of the counted bytes held on top.
     */
    @Nano
    public static void testCountsWithHandles() throws InterruptedException {
        int n = 2000;
        long big = 10 * 1000 * 1000;
        Db db = readAll(n, big);
        try {
            db.setCacheSizeIndicator(1);
            bytes(db);
            db.setCacheSizeIndicator(big);
            for (int k = 0; k < n; k++) DbUtil.get(db, "k" + k);
            long[] c = checkRule(db);
            Assert.assertTrue("pointers that hold a handle: " + c[1] + " of " + c[0] + " objects",
                    c[1] > c[0] / 2);
            long full = bytes(db);
            long budget = full / 3;
            db.setCacheSizeIndicator(budget);
            long end = System.nanoTime() + 2000L * 1000 * 1000;
            while (db.internal().cache().residents().bytes() > budget && System.nanoTime() < end) {
                Thread.sleep(1);
            }
            bytes(db);
            c = checkRule(db);
            Assert.assertTrue("dead handles in pointers after the eviction: " + c[2], c[2] > 0);
            for (int k = 0; k < n; k++) DbUtil.get(db, "k" + k);
            bytes(db);
            checkRule(db);
        } finally {
            db.stop();
        }
    }

    /**
     * checkCounts, and each resident index object that is not dirty counted by 009-02, 4.7's
     * rule, computed apart from Residents (testCountsWithHandles). Returns the objects
     * checked, their pointers that hold a handle, and those of them that hold a dead one.
     */
    private static long[] checkRule(Db db) {
        checkCounts(db);
        Db.Internal in = db.internal();
        long objects = 0, handles = 0, dead = 0;
        synchronized (in.getWriteLock()) {
            final List<Node> d = new ArrayList<Node>();
            in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
                public void node(Node node, long tpos, long lastTpos) {
                    d.add(node);
                }
            });
            for (Node o : Residents.walk(in.superRoot(), in.cache().nodes(), d)) {
                if (!o.isIndexNode() || o.isDirty()) continue;
                long rule = o.getMemSize() + 79;
                for (int i = 0; i < o.getSize(); i++) {
                    bergdb.dag.Pointee p = o.getPointee(i);
                    if (p instanceof bergdb.dag.Handle) {
                        rule += 32;
                        handles++;
                        if (((bergdb.dag.Handle) p).isDead()) dead++;
                    } else if (p instanceof bergdb.dag.ValueNode) {
                        rule += ((bergdb.dag.ValueNode) p).getMemSize();
                    }
                }
                Assert.assertEquals("object " + o.getId() + " by 4.7's rule", rule,
                        (long) Residents.counted(o));
                objects++;
            }
        }
        return new long[] {objects, handles, dead};
    }

    /** One batch of the capacity controller with the budget 'budget', then the budget back. */
    private static void batch(Db db, long budget) {
        Db.Internal in = db.internal();
        long old = in.eviction().budget();
        in.eviction().setBudget(budget);
        synchronized (in.getWriteLock()) {
            in.eviction().sweep(db, false);
        }
        in.eviction().setBudget(old);
    }

    /**
     * The accounting against a walk of the resident objects, between transactions (bergdb
     * 015-15): each resident index object is counted, with at most its bytes
     * (Residents.bytesOf), and with its bytes unless the writer changed it since its last
     * count (dirty: D's objects, counted with their size at the last count until written,
     * docs/levels.md, section 7); the resident bytes are the sum of the counts and the
     * object counter their number.
     */
    private static void checkCounts(Db db) {
        Db.Internal in = db.internal();
        synchronized (in.getWriteLock()) {
            final List<Node> d = new ArrayList<Node>();
            in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
                public void node(Node node, long tpos, long lastTpos) {
                    d.add(node);
                }
            });
            long sum = 0, n = 0;
            for (Node o : Residents.walk(in.superRoot(), in.cache().nodes(), d)) {
                if (!o.isIndexNode()) continue;
                int c = Residents.counted(o);
                int b = Residents.bytesOf(o);
                String what = (o.isDirty() ? "dirty " : "") + "object " + o.getId()
                        + ": counted " + c + ", bytes " + b;
                Assert.assertTrue(what, c >= 0 && c <= b);
                if (!o.isDirty()) Assert.assertEquals(what, b, c);
                sum += c;
                n++;
            }
            Assert.assertEquals("the resident bytes", sum, in.cache().residents().bytes());
            Assert.assertEquals("the objects counted", n, in.cache().residents().objects());
        }
    }
}
