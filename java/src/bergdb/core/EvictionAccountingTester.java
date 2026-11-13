package bergdb.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReferenceArray;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import bergdb.dag.Dag;
import bergdb.dag.Handle;
import bergdb.dag.Node;
import bergdb.dag.Pointee;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.stream.MemoryStream;

/**
 * Harness 6.5 of bergdb 018-01, eviction's accounting (bergdb 018-05): random eviction
 * schedules and budget changes during reads and writes, with the audit after each batch of
 * transactions and the resident bytes compared with a recount. Its class of faults: 015-67 to
 * 015-71.
 *
 * <p>A run, from a seed, on a MemoryStream: the capacity controller (Eviction.Schedule.BUDGET)
 * with a random budget, nodes of at most 8 entries and a random startup distance; reader
 * threads that get random keys at random times of the history and compare each answer with
 * the test's own record of it, a quarter of them with a GetData that keeps nothing
 * (Dag.CACHE_NOTHING), whose reads remove the empty handles they leave (Cache3.dropIfEmpty,
 * the path of 015-71); a writer that runs batches of transactions (puts of small
 * values, now and then a value over 1 MiB, deletes), and between them, at random, a test
 * schedule's eviction (Db.Internal.evictNow: values, every, random; each ends with a resync
 * of the accounting while the readers load) or a new budget (Db.setCacheSizeIndicator,
 * higher or lower); now and then a restart (on a copy of the stream, with a new budget),
 * half of them right after a value over 1 MiB, so that the start's rerun makes it again
 * (015-68). After each batch:</p>
 * <ol>
 * <li><b>The audit</b> (Audit.check), under the write lock, while the readers go on: it
 * reports nothing (a reader's cleanup of an empty handle is right, 015-71).</li>
 * <li>With the readers paused, under the write lock, <b>the recount</b>: every object of a
 * live handle is counted (Residents.counted), the counts sum to the resident bytes and their
 * number is the resident objects (015-69: a resync dropped a reader's load); a clean object
 * that is not in D is counted with its bytes now (Residents.bytesOf; the writer's changes to
 * a dirty object are counted at its write, Residents' class comment); no object outside the
 * live handles is counted; and no resident pointer holds a value over 1 MiB, the admission
 * rule (015-68: a start kept those of its rerun).</li>
 * <li><b>The handle limit</b>: no batch of the controller examined more handles than its
 * limit (Eviction.batchesOverTheirHandles; 015-67).</li>
 * <li>At some batches' ends, with the readers paused and no write, <b>a budget
 * decrease</b>: the eviction thread is idle within 5 s, and if the bytes that cannot go (the
 * counts of the objects that are not detachable) fit the budget, the resident bytes are at
 * most the budget. Or, as R4's probe of 015-70, a decrease after the pins fell (pinsFell):
 * the budget lowered to 1 byte, so that the hand's rounds count the pins, raised, the
 * writer's transactions until a write of the dirty nodes lowers the pins, detachable objects
 * evicted down to the old pins, and the budget lowered to between the new pins and the old:
 * the resident bytes must reach it (015-70).</li>
 * </ol>
 * <p>The readers' answers are checked too: a wrong answer under eviction is a fault of the
 * class. Each run prints its seed and what it did; the property bergdb.accounting.seed runs
 * one seed, bergdb.accounting.debug recounts after every transaction, and main() runs seeds
 * from the command line (bergdb 018-05, section 3).</p>
 *
 * @author Frans Lundberg
 */
public final class EvictionAccountingTester {
    private static final long STEP = bergdb.pub.util.Clock.UNITS_PER_SEC / 100;

    /** A value over 1 MiB (Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES does not cache it). */
    private static final int LARGE = 1100 * 1024;

    private static final boolean DEBUG = Boolean.getBoolean("bergdb.accounting.debug");

    /** What a run is: its size. */
    static final class Shape {
        final int keys, batches, maxTrans, readers;
        final double largeP;

        Shape(int keys, int batches, int maxTrans, int readers, double largeP) {
            this.keys = keys;
            this.batches = batches;
            this.maxTrans = maxTrans;
            this.readers = readers;
            this.largeP = largeP;
        }
    }

    /** A version of a key: its time and value (null: deleted), and the older one. */
    private static final class Version {
        final long time;
        final byte[] value;
        final Version older;

        Version(long time, byte[] value, Version older) {
            this.time = time;
            this.value = value;
            this.older = older;
        }
    }

    /** One run's state and checks. */
    private static final class Run {
        final long seed;
        final Shape shape;
        final Random rnd;
        final CoreTestClock clock = new CoreTestClock();
        final AtomicReferenceArray<Version> history;
        final AtomicLong published = new AtomicLong(0);    // the last time readers may read
        final ReentrantReadWriteLock pause = new ReentrantReadWriteLock();
        final AtomicBoolean stop = new AtomicBoolean(false);
        final ConcurrentLinkedQueue<String> problems = new ConcurrentLinkedQueue<String>();
        final AtomicLong reads = new AtomicLong(0);
        final StringBuilder log = new StringBuilder();
        MemoryStream stream = new MemoryStream();
        volatile Db db;
        long time = 100 * STEP;
        int restarts = 0, decreases = 0, decreasesChecked = 0, evictNows = 0, budgetSets = 0;
        int pinsFell = 0, pinsFellChecked = 0;
        boolean started = false;        // a restart since the last check
        int audits = 0, recounts = 0, larges = 0;
        String failure = null;

        Run(long seed, Shape shape) {
            this.seed = seed;
            this.shape = shape;
            this.rnd = new Random(seed);
            this.history = new AtomicReferenceArray<Version>(shape.keys);
        }

        Db start(long budget) {
            int sd = 200 + rnd.nextInt(20000);
            log("start: budget " + budget + ", startup distance " + sd);
            return Db.builder().testSetup(stream).clock(clock).testId().maxNodeSize8()
                    .startupDistance(sd).cacheSizeIndicator(budget)
                    .evictionSchedule(Eviction.Schedule.BUDGET, seed).audit(1 << 30).start();
        }

        void log(String s) {
            if (log.length() < 4000) log.append(s).append('\n');
        }

        /** A random budget: from a few bytes to about twice the resident bytes, or none. */
        long budget(Db d) {
            long bytes = d == null ? 100000 : d.internal().cache().residents().bytes();
            switch (rnd.nextInt(6)) {
                case 0: return 1 + rnd.nextInt(1000);
                case 1: return Long.MAX_VALUE;
                default: return Math.max(1, (long) (bytes * (0.05 + 1.5 * rnd.nextDouble())));
            }
        }

        void fail(String s) {
            if (failure == null) failure = "seed " + seed + ": " + s;
        }
    }

    /** The reader threads' loop: random keys at random published times, each answer checked. */
    private static void read(Run run, int id) {
        Random rr = new Random(run.seed * 31 + id);
        while (!run.stop.get()) {
            run.pause.readLock().lock();
            try {
                long last = run.published.get();
                if (last == 0) continue;
                long t = 100 * STEP + 1 + (long) (rr.nextDouble() * (last - 100 * STEP));
                if (rr.nextInt(3) == 0) t = last;
                int k = rr.nextInt(run.shape.keys);
                Version v = run.history.get(k);
                while (v != null && v.time > t) v = v.older;
                byte[] exp = v == null ? null : v.value;
                byte[] got;
                try {
                    // A quarter of the gets keep nothing (Dag.CACHE_NOTHING): their reads
                    // leave empty handles, which they remove (Cache3.dropIfEmpty; 015-71).
                    Db db = run.db;
                    bergdb.dag.GetData gd = db.newGetData();
                    if (rr.nextInt(4) == 0) gd.cachePolicy = Dag.CACHE_NOTHING;
                    got = db.getOne(t, bergdb.dag.Keys.toSegments("k" + k), gd);
                } catch (RuntimeException e) {
                    run.problems.add("get(k" + k + ", " + t + ") threw " + e);
                    continue;
                }
                if (!Arrays.equals(exp, got)) {
                    run.problems.add("get(k" + k + ", " + t + "): " + describe(got) + ", expected "
                            + describe(exp));
                }
                run.reads.incrementAndGet();
            } finally {
                run.pause.readLock().unlock();
            }
        }
    }

    private static String describe(byte[] v) {
        if (v == null) return "null";
        if (v.length > 100) return "a value of " + v.length + " bytes";
        return "'" + new String(v) + "'";
    }

    /** Runs one seed; returns null, or the first failure with the run's log. */
    static String run(long seed, Shape shape, java.io.PrintStream out) throws InterruptedException {
        Run run = new Run(seed, shape);
        long t0 = System.nanoTime();
        run.db = run.start(run.budget(null));
        List<Thread> readers = new ArrayList<Thread>();
        for (int r = 0; r < shape.readers; r++) {
            final int id = r;
            final Run fr = run;
            Thread th = new Thread(new Runnable() {
                public void run() {
                    read(fr, id);
                }
            }, "EvictionAccountingTester-reader-" + r);
            readers.add(th);
            th.start();
        }
        try {
            for (int b = 0; b < shape.batches && run.failure == null && run.problems.isEmpty();
                    b++) {
                batch(run, b);
                check(run, b);
            }
        } finally {
            run.stop.set(true);
            for (Thread th : readers) {
                th.join(60_000);
                Assert.assertFalse("a reader thread did not end within 60 s", th.isAlive());
            }
            run.db.close();
        }
        if (run.failure == null && !run.problems.isEmpty()) {
            run.fail(run.problems.size() + " wrong answers, first: " + run.problems.peek());
        }
        long ms = (System.nanoTime() - t0) / 1000000;
        if (out != null) {
            out.println("EvictionAccountingTester seed " + seed + ": " + shape.batches
                    + " batches, "
                    + run.reads.get() + " reads, " + run.audits + " audits, " + run.recounts
                    + " recounts, " + run.evictNows + " test-schedule evictions, " + run.budgetSets
                    + " budget changes, " + run.decreasesChecked + " of " + run.decreases
                    + " decreases checked (pins fit), " + run.pinsFellChecked + " of "
                    + run.pinsFell
                    + " checked after the pins fell, " + run.restarts + " restarts, " + run.larges
                    + " large values; " + ms + " ms" + (run.failure == null ? ", OK" : ", FAILED"));
        }
        return run.failure == null ? null : run.failure + "\nthe run:\n" + run.log;
    }

    /** One batch of transactions, with test-schedule evictions and budget changes between. */
    private static void batch(Run run, int b) throws InterruptedException {
        Random rnd = run.rnd;
        int n = 1 + rnd.nextInt(run.shape.maxTrans);
        for (int i = 0; i < n; i++) {
            Db db = run.db;
            run.time += STEP;
            run.clock.setTime(run.time);
            Trans.Builder tb = db.trans();
            int c = 1 + rnd.nextInt(5);
            int[] ks = new int[c];
            byte[][] vs = new byte[c][];
            java.util.HashSet<Integer> seen = new java.util.HashSet<Integer>();
            int m = 0;
            for (int j = 0; j < c; j++) {
                int k = rnd.nextInt(run.shape.keys);
                if (!seen.add(k)) continue;
                byte[] v;
                if (rnd.nextInt(20) == 0) {
                    v = null;
                    tb.delete("k" + k);
                } else {
                    if (rnd.nextDouble() < run.shape.largeP) {
                        v = new byte[LARGE];
                        rnd.nextBytes(v);
                        run.larges++;
                    } else {
                        v = ("v" + b + "-" + i + "-" + j + "-" + "x".repeat(rnd.nextInt(200)))
                                .getBytes();
                    }
                    tb.put("k" + k, v);
                }
                ks[m] = k;
                vs[m++] = v;
            }
            db.execute(tb.build());
            for (int j = 0; j < m; j++) {
                run.history.set(ks[j], new Version(run.time, vs[j], run.history.get(ks[j])));
            }
            run.published.set(run.time);
            if (DEBUG) {
                run.pause.writeLock().lock();
                try {
                    synchronized (db.internal().getWriteLock()) {
                        String r = recount(db);
                        if (r != null) {
                            run.fail("batch " + b + ", after transaction " + i
                                    + ": the recount: " + r);
                            return;
                        }
                    }
                } finally {
                    run.pause.writeLock().unlock();
                }
            }
            // Between transactions, at random: a test schedule's eviction, a new budget.
            int x = rnd.nextInt(40);
            if (x == 0) {
                Eviction.Schedule[] ss = {Eviction.Schedule.VALUES, Eviction.Schedule.EVERY,
                    Eviction.Schedule.RANDOM};
                Eviction.Schedule sc = ss[rnd.nextInt(3)];
                db.internal().evictNow(sc, rnd.nextLong());
                run.evictNows++;
                run.log("batch " + b + " trans " + i + ": evictNow " + sc);
            } else if (x == 1) {
                long budget = run.budget(db);
                if (budget < db.internal().eviction().budget()) run.decreases++;
                db.setCacheSizeIndicator(budget);
                run.budgetSets++;
                run.log("batch " + b + " trans " + i + ": budget " + budget);
            }
        }
        if (rnd.nextInt(25) == 0) restart(run);
    }

    /** A restart, with the readers paused, on a copy of the stream, with a new budget. */
    private static void restart(Run run) {
        run.pause.writeLock().lock();
        try {
            if (run.rnd.nextBoolean()) {
                // A large value just before the restart, so that the start's rerun makes it
                // again (015-68).
                Db db = run.db;
                int k = run.rnd.nextInt(run.shape.keys);
                byte[] v = new byte[LARGE];
                run.rnd.nextBytes(v);
                run.time += STEP;
                run.clock.setTime(run.time);
                db.execute(db.trans().put("k" + k, v).build());
                run.history.set(k, new Version(run.time, v, run.history.get(k)));
                run.published.set(run.time);
                run.larges++;
            }
            run.db.close();
            run.stream = run.stream.copy();
            run.db = run.start(run.budget(run.db));
            run.restarts++;
            run.started = true;
        } finally {
            run.pause.writeLock().unlock();
        }
    }

    /** The checks after a batch. */
    private static void check(Run run, int b) throws InterruptedException {
        Db db = run.db;
        Db.Internal in = db.internal();
        Eviction e = in.eviction();
        long auditFailures = Audit.failures();
        // 1. The audit, while the readers go on.
        List<String> fs;
        synchronized (in.getWriteLock()) {
            fs = Audit.check(db);
        }
        run.audits++;
        if (!fs.isEmpty()) {
            run.fail("batch " + b + ": the audit: " + fs);
            return;
        }
        run.pause.writeLock().lock();
        try {
            // 2. The recount, and 3. the handle limit.
            synchronized (in.getWriteLock()) {
                String r = recount(db, run.started);
                run.started = false;
                run.recounts++;
                if (r != null) {
                    run.fail("batch " + b + ": the recount: " + r);
                    return;
                }
                long over = e.batchesOverTheirHandles();
                if (over > 0) {
                    run.fail("batch " + b + ": " + over + " batches examined more handles than "
                            + "their limit (" + Eviction.BATCH + ", "
                            + Eviction.BATCH_UNDER_PRESSURE + ")");
                    return;
                }
            }
            if (Audit.failures() != auditFailures) {
                run.fail("batch " + b + ": the audit at a start failed (see System.err)");
                return;
            }
            // 4. A budget decrease, with no write and the readers paused; or after the pins
            //    fell (015-70).
            if (run.rnd.nextInt(6) == 0) {
                pinsFell(run, b);
            } else if (run.rnd.nextInt(4) == 0) {
                long bytes = in.cache().residents().bytes();
                long budget = Math.max(1, (long) (bytes * (0.1 + 0.85 * run.rnd.nextDouble())));
                // A decrease of the budget in force: the resident bytes may be above it, with
                // pins above it, and a higher budget is an increase, after which the
                // controller stops at the trigger, which may be above the budget.
                budget = Math.min(budget, e.budget() - 1);
                if (budget < 1) return;
                run.decreases++;
                run.budgetSets++;
                db.setCacheSizeIndicator(budget);
                long end = System.nanoTime() + 5000L * 1000 * 1000;
                while (!e.idle() && System.nanoTime() < end) Thread.sleep(1);
                synchronized (in.getWriteLock()) {
                    if (!e.idle()) {
                        run.fail("batch " + b + ": the eviction thread not idle 5 s after a "
                                + "decrease "
                                + "of the budget to " + budget + ", from " + bytes + " bytes: "
                                + e.summary());
                        return;
                    }
                    long pins = pins(db);
                    long after = in.cache().residents().bytes();
                    if (pins <= budget) {
                        run.decreasesChecked++;
                        if (after > budget) {
                            run.fail("batch " + b + ": a decrease of the budget to " + budget
                                    + " settled at " + after + " bytes (from " + bytes
                                    + "), the pins " + pins + " fit: " + e.summary());
                            return;
                        }
                    }
                    run.log("batch " + b + ": decrease to " + budget + ", from " + bytes + " to "
                            + after + ", pins " + pins);
                }
            }
        } finally {
            run.pause.writeLock().unlock();
        }
    }

    /** Waits until the eviction thread is idle, at most 5 s; false if it is not. */
    private static boolean settle(Eviction e) throws InterruptedException {
        long end = System.nanoTime() + 5000L * 1000 * 1000;
        while (!e.idle() && System.nanoTime() < end) Thread.sleep(1);
        return e.idle();
    }

    /**
     * A decrease after the pins fell (015-70; 016-06, R4-F5), as R4's probe and
     * Eviction.testLoweredBudgetAfterPinsFell: with the readers paused, the budget lowered to
     * 1 byte, so that the hand's rounds count the pins (P0); the budget raised again, and the
     * writer's transactions until a write of the dirty nodes lowers the pins (P1); detachable
     * objects evicted until the resident bytes are at most P0, where a batch that counts with
     * P0 stops; then the budget lowered to between P1 and P0: the pins fit, and the resident
     * bytes must reach the budget. The caller holds the pause's write lock.
     */
    private static void pinsFell(Run run, int b) throws InterruptedException {
        Db db = run.db;
        Db.Internal in = db.internal();
        Eviction e = in.eviction();
        long before = e.budget();
        run.pinsFell++;
        run.budgetSets += 3;
        db.setCacheSizeIndicator(1);
        if (!settle(e)) {
            run.fail("batch " + b + ": the eviction thread not idle 5 s after a budget of 1 byte: "
                    + e.summary());
            return;
        }
        long p0, p1;
        synchronized (in.getWriteLock()) {
            p0 = pins(db);
        }
        db.setCacheSizeIndicator(Long.MAX_VALUE);
        p1 = p0;
        for (int i = 0; i < 500 && p1 > p0 * 3 / 4; i++) {
            run.time += STEP;
            run.clock.setTime(run.time);
            int k = run.rnd.nextInt(run.shape.keys);
            byte[] v = ("p" + b + "-" + i).getBytes();
            db.execute(db.trans().put("k" + k, v).build());
            run.history.set(k, new Version(run.time, v, run.history.get(k)));
            run.published.set(run.time);
            synchronized (in.getWriteLock()) {
                p1 = pins(db);
            }
        }
        long bytes;
        synchronized (in.getWriteLock()) {
            TopNode superRoot = in.superRoot(), newest = in.newestWrittenTop();
            for (Handle h : in.cache().handles()) {
                if (in.cache().residents().bytes() <= p0) break;
                Node o = h.obj;
                if (o != null && Eviction.detachable(o, superRoot, newest)) in.cache().evict(h);
            }
            bytes = in.cache().residents().bytes();
        }
        long budget = (p0 + p1) / 2;
        String state = "P0 " + p0 + ", P1 " + p1 + ", " + bytes + " bytes, budget " + budget;
        if (!(p1 < budget && budget < bytes)) {
            run.log("batch " + b + ": pins fell, not checked: " + state);
            db.setCacheSizeIndicator(before);
            return;
        }
        db.setCacheSizeIndicator(budget);
        if (!settle(e)) {
            run.fail("batch " + b + ": the eviction thread not idle 5 s after a decrease, the pins "
                    + "fell: " + state + ": " + e.summary());
            return;
        }
        synchronized (in.getWriteLock()) {
            long pins = pins(db), after = in.cache().residents().bytes();
            run.pinsFellChecked++;
            run.log("batch " + b + ": pins fell: " + state + "; after " + after + ", pins " + pins);
            if (pins <= budget && after > budget) {
                run.fail("batch " + b + ": a decrease after the pins fell settled at " + after
                        + " bytes: " + state + ", pins now " + pins + ": " + e.summary());
                return;
            }
        }
        db.setCacheSizeIndicator(before);
    }

    /**
     * The recount: null if the resident bytes and objects equal the counts of the objects of
     * the live handles, every clean object outside D is counted with its bytes now, no object
     * outside the live handles is counted, and no resident pointer holds a value over 1 MiB;
     * else what differs. The caller holds the write lock, with no reader in a get.
     */
    static String recount(Db db) {
        return recount(db, false);
    }

    /**
     * As recount(db), and with 'all', every object of a live handle counted with its bytes
     * now, dirty ones too: after a start, which counts D's objects with their bytes (019-21;
     * R5's F4 of night 006-12, the handles that linkD puts into their pointers).
     */
    static String recount(Db db, boolean all) {
        Db.Internal in = db.internal();
        Cache3 table = in.cache();
        Residents res = table.residents();
        final List<Node> dObjects = new ArrayList<Node>();
        final Set<Node> dSet = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                dObjects.add(node);
                dSet.add(node);
            }
        });
        Set<Node> live = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        long sum = 0, n = 0;
        StringBuilder bad = new StringBuilder();
        int bads = 0;
        for (Handle h : table.handles()) {
            Node o = h.obj;
            if (o == null || !live.add(o)) continue;
            int c = Residents.counted(o);
            if (c < 0) {
                if (bads++ < 5) {
                    bad.append("; the object of node " + o.getId() + "'s live handle is not "
                            + "counted");
                }
                continue;
            }
            sum += c;
            n++;
            if (all || (!o.isDirty() && !dSet.contains(o))) {
                int now = Residents.bytesOf(o);
                if (now != c && bads++ < 5) {
                    bad.append("; the " + (o.isDirty() ? "dirty" : "clean") + " object of node "
                            + o.getId() + " is counted with " + c
                            + " bytes, its bytes now " + now + " (" + o.getClass().getSimpleName()
                            + ", canonical " + o.isCanonical() + ", size " + o.getSize() + ", mem "
                            + o.getMemSize() + ", handles " + (Residents.bytesWithoutValues(o)
                            - o.getMemSize() - Residents.ENTRY_BYTES) / Residents.HANDLE_BYTES
                            + ", spos " + o.getSpos() + ")");
                }
            }
            int size = o.getSize();
            for (int i = 0; i < size; i++) {
                Pointee p = o.getPointee(i);
                if (p instanceof ValueNode
                        && !Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES.shouldCache((ValueNode) p)
                        && bads++ < 5) {
                    bad.append("; pointer " + i + " of node " + o.getId() + " holds a value of "
                            + ((ValueNode) p).getMemSize() + " bytes (over 1 MiB: not kept)");
                }
            }
        }
        if (sum != res.bytes()) {
            bad.append("; the resident bytes are " + res.bytes()
                    + ", the counts of the live handles' "
                    + n + " objects sum to " + sum);
        }
        if (n != res.objects()) {
            bad.append("; the resident objects are " + res.objects()
                    + ", the live handles' counted "
                    + "objects " + n);
        }
        for (Node x : Residents.walk(in.superRoot(), table.nodes(), dObjects)) {
            if (x.isIndexNode() && !live.contains(x) && Residents.counted(x) >= 0 && bads++ < 5) {
                bad.append("; node " + x.getId() + "'s object is counted, not a live handle's");
            }
        }
        return bad.length() == 0 ? null : bad.substring(2);
    }

    /**
     * The bytes that a batch cannot take: the counts of the objects of the live handles that
     * are not detachable (Eviction.detachable). The caller holds the write lock.
     */
    static long pins(Db db) {
        Db.Internal in = db.internal();
        TopNode superRoot = in.superRoot(), newest = in.newestWrittenTop();
        long pins = 0;
        for (Node o : in.cache().nodes()) {
            if (!Eviction.detachable(o, superRoot, newest)) pins += Residents.countedBytes(o);
        }
        return pins;
    }

    private static void runSeeds(TestEnvironment c, long from, int count, Shape shape)
            throws InterruptedException {
        Long only = Long.getLong("bergdb.accounting.seed");
        List<String> failures = new ArrayList<String>();
        if (only != null) {
            from = only;
            count = 1;
        }
        for (long s = from; s < from + count; s++) {
            String f = run(s, shape, c.out());
            if (f != null) failures.add(f);
        }
        Assert.assertTrue(failures.size() + " runs failed, the first: "
                + (failures.isEmpty() ? "" : failures.get(0)), failures.isEmpty());
    }

    /** The unit tests' shape. */
    static final Shape UNIT = new Shape(300, 25, 30, 2, 0.002);

    /** The night test's shape: more than 4,096 handles resident. */
    static final Shape NIGHT = new Shape(30000, 60, 400, 3, 0.0005);

    /**
     * Runs seeds and prints a line for each, and the first failure:
     * EvictionAccountingTester unit|night FROM [COUNT]. Exits with 1 if a run failed.
     */
    public static void main(String[] args) throws InterruptedException {
        Shape shape = args[0].equals("night") ? NIGHT : UNIT;
        long from = Long.parseLong(args[1]);
        int count = args.length > 2 ? Integer.parseInt(args[2]) : 1;
        String first = null;
        int failed = 0;
        for (long s = from; s < from + count; s++) {
            String f = run(s, shape, System.out);
            if (f != null) {
                failed++;
                if (first == null) first = f;
            }
        }
        System.out.println(failed == 0 ? "EVICTION ACCOUNTING OK, " + count + " seeds"
                : "EVICTION ACCOUNTING FAILED, " + failed + " of " + count + " seeds; the first:\n"
                + first);
        if (failed > 0) System.exit(1);
    }

    /** Three seeds, small: about a second together. */
    @Nano
    public static void testAccounting(TestEnvironment c) throws InterruptedException {
        runSeeds(c, 1, 3, UNIT);
    }

    /**
     * bergdb 019-46: the unit shape's seeds with a pause of 0.2 ms in every Cache3.dropIfEmpty
     * between its test that the handle is empty and its compareAndSet (Cache3.dropIfEmptyHook),
     * a window that load opens now and then: a gate on a loaded machine failed on it once.
     * Before the fix, 31 of 300 seeds failed (INV-SLOT, an object of D not canonical, INV-CAN,
     * readers' old values); about 15 s.
     */
    @Nano("night")
    public static void testAccountingWideDropWindow(TestEnvironment c) throws InterruptedException {
        Cache3.dropIfEmptyHook = new Runnable() {
            public void run() {
                java.util.concurrent.locks.LockSupport.parkNanos(200 * 1000);
            }
        };
        try {
            runSeeds(c, 1000, 40, UNIT);
        } finally {
            Cache3.dropIfEmptyHook = null;
        }
    }
    
    /**
     * bergdb 019-47: a longer run of small batches, with six readers, whose restarts come
     * one after another, so that a start's section can begin with the transaction of a large
     * value. Seed 1075 restarted with no budget after such a section, and the start kept the
     * large value in its leaf (the recount: "holds a value of 1126456 bytes"), as did 1133,
     * 1249, 1267 and 1276 (at batch 37 to 247); about 30 s.
     */
    @Nano("night")
    public static void testAccountingManyRestarts(TestEnvironment c) throws InterruptedException {
        runSeeds(c, 1070, 10, new Shape(300, 300, 4, 6, 0.002));
    }
    
    /**
     * Ten seeds, larger: more than 4,096 handles resident, so that a batch can reach its
     * handle limit; about 10 s a seed.
     */
    @Nano("night")
    public static void testAccountingLong(TestEnvironment c) throws InterruptedException {
        runSeeds(c, 100, 10, NIGHT);
    }
}
