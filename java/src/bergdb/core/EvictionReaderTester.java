package bergdb.core;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import bergdb.dag.Pointee;
import bergdb.dag.Handle;
import bergdb.dag.AccessData;
import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.MemoryStream;

/**
 * Readers under eviction (bergdb item 001, WP J5; bergdb 001-08, 7.4; the plan's
 * Q8), with handles since bergdb item 009 (items/009-handles/02-implementation-plan.md, 3.4
 * and 4.4): the protocol of Eviction's class comment, tested. A reader follows a pointer
 * without a lock when the pointer's handle holds an object that may serve it; else it
 * resolves the pointer to its node's live handle and loads under the handle's monitor.
 * Eviction runs under the write lock, which readers never take, and kills a handle under its
 * map's lock without waiting for a loader. A reader that holds an object may finish with it
 * after its eviction: it is the version at its position.
 *
 * <p>The tests: eviction changes no record; a reader that took a canonical object from a live
 * handle puts the handle into a pointer after an eviction killed it (the steps made one after
 * the other); pointers that hold dead handles are resolved again; a reader paused
 * (deterministically) inside a load while an eviction runs; a scan in chunks with eviction
 * and writes between the chunks; and reader threads while the writer alternates the pointers
 * between memory and stream, with a forced schedule or the capacity controller.</p>
 */
public class EvictionReaderTester {
    private static final long STEP = bergdb.pub.util.Clock.UNITS_PER_SEC / 100;

    private static Db start(MemoryStream s, CoreTestClock clock, Eviction.Schedule schedule,
            int audit) {
        return Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8().startupDistance(200)
                .evictionSchedule(schedule, 1).audit(audit).start();
    }

    private static String value(int i, int j) {
        return "v" + i + "-" + j;
    }

    /** n transactions on both databases: puts of keys k0..k(keys-1); returns the times. */
    private static List<Long> load(Db ref, Db db, CoreTestClock clock, int n, int keys, long seed) {
        Random rnd = new Random(seed);
        List<Long> times = new ArrayList<Long>();
        long time = 100 * STEP;
        for (int i = 0; i < n; i++) {
            time += STEP;
            clock.setTime(time);
            java.util.TreeSet<Integer> ks = new java.util.TreeSet<Integer>();
            int c = 1 + rnd.nextInt(4);
            for (int j = 0; j < c; j++) ks.add(i < keys ? (i + j * 13) % keys : rnd.nextInt(keys));
            for (Db d : new Db[] {ref, db}) {
                Trans.Builder b = d.trans();
                int j = 0;
                for (int k : ks) b.put("k" + k, value(i, j++));
                d.execute(b.build());
            }
            times.add(time);
        }
        return times;
    }

    private static boolean sameBytes(MemoryStream s1, MemoryStream s2) {
        if (s1.getLength() != s2.getLength()) return false;
        byte[] b1 = new byte[(int) s1.getLength()], b2 = new byte[(int) s2.getLength()];
        try {
            s1.read(0, b1, 0, b1.length);
            s2.read(0, b2, 0, b2.length);
        } catch (java.io.IOException e) {
            throw new RuntimeException(e);
        }
        return Arrays.equals(b1, b2);
    }

    private static void assertSameReads(Db ref, Db db, int keys, List<Long> times) {
        for (int k = 0; k < keys; k++) {
            Assert.assertTrue("k" + k + " latest", Arrays.equals(DbUtil.get(ref, "k" + k),
                    DbUtil.get(db, "k" + k)));
            for (int t = 0; t < times.size(); t += 7) {
                Assert.assertTrue("k" + k + " at " + times.get(t), Arrays.equals(
                        DbUtil.get(ref, times.get(t), "k" + k), DbUtil.get(db, times.get(t), "k" + k)));
            }
        }
    }

    /**
     * Evicting a handle changes no record (bergdb item 009, step 3a; 009-02, 4.6): for a key
     * node's pointers, a top node's root pointer and its skip pointers, the reference a
     * record would get is the same before and after the pointee's handle dies, its object's
     * position, and the reads are those of the database without eviction. (Until step 3a
     * this test was of the access data that a reader wrote after an unswizzle; with handles
     * a follow writes into the pointee's handle, never into the pointer.)
     */
    @Nano
    public static void testEvictionKeepsTheRecords() {
        MemoryStream s1 = new MemoryStream(), s2 = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db ref = start(s1, clock, Eviction.Schedule.NONE, 0);
        Db db = start(s2, clock, Eviction.Schedule.NONE, 0);
        load(ref, db, clock, 60, 30, 1);
        db.sync(SyncLevel.STRONG);
        Db.Internal in = db.internal();
        TopNode top = in.superRoot();
        int checked = 0;
        List<Object[]> slots = new ArrayList<Object[]>();
        slots.add(new Object[] {top, 0});
        for (int i = 1; i < top.getSize(); i++) slots.add(new Object[] {top, i});
        KeyNode root = (KeyNode) top.getPointerNode(0);
        for (int i = 0; i < root.size; i++) slots.add(new Object[] {root, i});
        for (Object[] s : slots) {
            Node x = (Node) s[0];
            int i = (Integer) s[1];
            Node c = x.getPointerNode(i);
            if (c == null || !c.isIndexNode() || c.isDirty() || bergdb.dag.Spos.isVpos(c.getSpos())) continue;
            if (!(x.getPointee(i) instanceof Handle)) continue;
            Handle h = (Handle) x.getPointee(i);
            long before = x.getSerializedRef(i);
            Assert.assertEquals(c.getSpos(), before);
            synchronized (in.getWriteLock()) {
                if (!Eviction.detachable(c, in.superRoot(), in.newestWrittenTop())) continue;
                Assert.assertTrue("evicted", in.cache().evict(h));
            }
            Assert.assertTrue(h.isDead() && h.obj == null && !c.isCanonical());
            Assert.assertEquals(before, x.getSerializedRef(i));
            Assert.assertTrue(x.getPointerNode(i) == null);
            checked++;
        }
        Assert.assertTrue("pointers checked", checked >= 3);
        assertSameReads(ref, db, 30, new ArrayList<Long>());
    }

    /**
     * Key node objects of the current tree that the node table names, canonical, clean and
     * not pinned, each with its parent key node's memory slot (from the super root's root
     * slot down, so that a lookup at the latest time passes the slot); parents that are
     * pinned first (objects of D), so that the paused reader's slot stays resident.
     */
    private static List<Object[]> candidates(Db db) {
        Db.Internal in = db.internal();
        Cache3 table = in.cache();
        TopNode superRoot = in.superRoot();
        List<Object[]> pinnedParent = new ArrayList<Object[]>(), other = new ArrayList<Object[]>();
        ArrayDeque<Node> todo = new ArrayDeque<Node>();
        Set<Node> seen = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        todo.add(superRoot);
        while (!todo.isEmpty()) {
            Node p = todo.poll();
            if (!seen.add(p)) continue;
            int size = p == superRoot ? 1 : p.getSize();
            for (int i = 0; i < size; i++) {
                Node c = p.getPointerNode(i);
                if (!(c instanceof KeyNode)) continue;
                todo.add(c);
                if (p instanceof KeyNode && p.isCanonical() && c.isCanonical() && !c.isDirty()
                        && table.getNode(c.getId()) == c && !Residents.isPinned(c, superRoot)) {
                    (Residents.isPinned(p, superRoot) ? pinnedParent : other).add(new Object[] {p, i, c});
                }
            }
        }
        pinnedParent.addAll(other);
        return pinnedParent;
    }

    /** A database with 80 transactions, and its twin without eviction; see load(). */
    private static final class Pair {
        final MemoryStream s1 = new MemoryStream(), s2 = new MemoryStream();
        final CoreTestClock clock = new CoreTestClock();
        final Db ref = start(s1, clock, Eviction.Schedule.NONE, 0);
        final Db db = start(s2, clock, Eviction.Schedule.NONE, 1);
        final int keys = 40;
        final List<Long> times;

        Pair(long seed) {
            times = load(ref, db, clock, 80, keys, seed);
        }

        /** The writer goes on: ten transactions, then the same stream and reads as without
         *  eviction, and no audit failed. */
        void goOn() {
            long auditFailures = Audit.failures();
            for (int j = 0; j < 10; j++) {
                clock.setTime(times.get(times.size() - 1) + (j + 1) * STEP);
                for (Db d : new Db[] {ref, db}) {
                    d.execute(d.trans().put("k" + (j * 7 % keys), "w" + j).build());
                }
            }
            ref.sync(SyncLevel.STRONG);
            db.sync(SyncLevel.STRONG);
            Assert.assertTrue("same stream", sameBytes(s1, s2));
            assertSameReads(ref, db, keys, times);
            Assert.assertEquals(auditFailures, Audit.failures());
        }
    }

    /**
     * A reader and an eviction (Q8, with handles; bergdb item 009, step 3a): a reader takes
     * a canonical object from its node's live handle for a pointer that holds nothing
     * (NodeCollection.followStreamPointer, step 4); before it puts the handle into the pointer
     * (step 5), eviction kills the handle; then the reader puts the dead handle into the
     * pointer. The steps are made here one after the other. The object is the version at
     * its position, its node's latest, so the reader's answers are right; the pointer holds
     * a dead handle, which the next follow resolves to a new live one by the node id; the
     * audit passes; and the writer goes on with the records it writes without eviction.
     */
    @Nano
    public static void testDeadHandleInAPointer() {
        int done = 0;
        for (int attempt = 0; attempt < 4; attempt++) {
            Pair w = new Pair(attempt);
            List<Object[]> cs = candidates(w.db);
            Assert.assertTrue("candidates", !cs.isEmpty());
            Object[] cand = cs.get(attempt % cs.size());
            Node p = (Node) cand[0];
            int i = (Integer) cand[1];
            Node c = (Node) cand[2];
            Db.Internal in = w.db.internal();
            long ref = p.getSerializedRef(i);

            p.setPointer(i, null, c.getSpos());             // the pointer holds nothing
            Handle h = in.cache().liveHandle(c.getId());     // the reader's step 3 and 4
            Assert.assertTrue(h != null && h.obj == c && c.isCanonical());
            in.evictNow(Eviction.Schedule.EVERY, 1);         // the eviction
            Assert.assertTrue("evicted", h.isDead() && !c.isCanonical()
                    && in.cache().liveHandle(c.getId()) == null);
            boolean pResident = Residents.isPinned(p, in.superRoot());
            synchronized (p) {                               // the reader's step 5
                if (p.getPointee(i) == null) p.setPointee(i, h);
            }
            Assert.assertEquals(ref, p.getSerializedRef(i));
            List<String> audit = Audit.check(w.db);
            Assert.assertTrue(audit.toString(), audit.isEmpty());
            assertSameReads(w.ref, w.db, w.keys, w.times);
            w.goOn();
            if (pResident) done++;
        }
        Assert.assertTrue("a pinned parent's pointer (" + done + ")", done > 0);
    }

    /**
     * A pointer that holds a dead handle is resolved again by its node's id (bergdb item
     * 009, step 3a; 009-02, 4.4, the slow path's step 1): every pointer of the current tree
     * holds a dead handle after an eviction of every detachable object; reads through them
     * load the nodes again into new live handles, which the pointers then hold, and the
     * references a record would get stay the same. (Until step 3a this test was of the race
     * of a reader's node table entry and a release, which handles do not have: the table is
     * not entered on a follow.)
     */
    @Nano
    public static void testDeadHandlesResolvedAgain() {
        Pair w = new Pair(5);
        Db.Internal in = w.db.internal();
        List<Object[]> cs = candidates(w.db);
        Assert.assertTrue("candidates", !cs.isEmpty());
        long[] refs = new long[cs.size()];
        Handle[] olds = new Handle[cs.size()];
        for (int j = 0; j < cs.size(); j++) {
            Node p = (Node) cs.get(j)[0];
            int i = (Integer) cs.get(j)[1];
            refs[j] = p.getSerializedRef(i);
            olds[j] = (Handle) p.getPointee(i);
        }
        in.evictNow(Eviction.Schedule.EVERY, 1);
        int dead = 0;
        for (Handle h : olds) if (h != null && h.isDead()) dead++;
        Assert.assertTrue("dead handles", dead > 0);
        assertSameReads(w.ref, w.db, w.keys, w.times);
        int resolved = 0;
        for (int j = 0; j < cs.size(); j++) {
            Node p = (Node) cs.get(j)[0];
            int i = (Integer) cs.get(j)[1];
            if (olds[j] == null || !olds[j].isDead()) continue;
            Pointee now = p.getPointee(i);
            if (now != olds[j]) {
                Assert.assertTrue("a live handle", now instanceof Handle && !((Handle) now).isDead());
                resolved++;
            }
            Assert.assertEquals("reference of " + j, refs[j], p.getSerializedRef(i));
        }
        Assert.assertTrue("resolved again", resolved > 0);
        List<String> audit = Audit.check(w.db);
        Assert.assertTrue(audit.toString(), audit.isEmpty());
        w.goOn();
    }

    /**
     * A reader paused inside a follow's slow path, holding the handle's monitor, after it
     * took a canonical object from the node's live handle: an eviction of every detachable
     * object runs meanwhile. Eviction takes no handle's monitor (it kills a handle by a
     * compareAndSet of its state, under its map's lock), and a load never asks for the write
     * lock (Q8), so there is no deadlock; whichever order results, the reader's answers are
     * right, the audit passes, and the writer goes on with the records it writes without
     * eviction. The unit test makes one try and gives the eviction 50 ms to run; the f-test
     * three tries and 500 ms. (Until bergdb item 009, step 3c, the reader held the pointer's
     * lock, which a sweep could wait for.)
     */
    @Nano
    public static void testReaderPausedInsideAFollow() throws Exception {
        readerPausedInsideAFollow(1, 50);
    }

    @Nano("f")
    public static void testReaderPausedInsideAFollowF() throws Exception {
        readerPausedInsideAFollow(3, 500);
    }

    private static void readerPausedInsideAFollow(int maxTries, long sweepMillis) throws Exception {
        int tries = 0;
        for (int attempt = 0; attempt < 8 && tries < maxTries; attempt++) {
            final Pair w = new Pair(attempt);
            List<Object[]> cs = candidates(w.db);
            if (cs.isEmpty()) continue;
            Object[] cand = cs.get(attempt % cs.size());
            final Node p = (Node) cand[0];
            final int i = (Integer) cand[1];
            final Node c = (Node) cand[2];
            p.setPointer(i, null, c.getSpos());

            final CountDownLatch paused = new CountDownLatch(1);
            final CountDownLatch resume = new CountDownLatch(1);
            final AtomicBoolean once = new AtomicBoolean(false);
            final ConcurrentLinkedQueue<String> problems = new ConcurrentLinkedQueue<String>();
            NodeCollection.firstTouchListener = new NodeCollection.FirstTouchListener() {
                public void firstTouch(long id, long ref, Node result, boolean read, boolean cutBack) {
                    if (result == c && !read && once.compareAndSet(false, true)) {
                        paused.countDown();
                        try {
                            if (!resume.await(20, TimeUnit.SECONDS)) problems.add("not resumed");
                        } catch (InterruptedException e) {
                            problems.add("interrupted");
                        }
                    }
                }
            };
            Thread reader = new Thread(new Runnable() {
                public void run() {
                    for (int k = 0; k < w.keys; k++) {
                        if (!Arrays.equals(DbUtil.get(w.ref, "k" + k), DbUtil.get(w.db, "k" + k))) {
                            problems.add("get(k" + k + ") differs");
                        }
                    }
                }
            });
            try {
                reader.start();
                // The lookups pass the slot unless it is an old entry's; then the next object.
                if (paused.await(5, TimeUnit.SECONDS)) {
                    tries++;
                    Thread evictor = new Thread(new Runnable() {
                        public void run() {
                            w.db.internal().evictNow(Eviction.Schedule.EVERY, 1);
                        }
                    });
                    evictor.start();
                    evictor.join(sweepMillis);
                    resume.countDown();
                    evictor.join(20000);
                    Assert.assertTrue("the sweep ended", !evictor.isAlive());
                }
                reader.join(20000);
                Assert.assertTrue("the reader ended", !reader.isAlive());
            } finally {
                NodeCollection.firstTouchListener = null;
                resume.countDown();
            }
            Assert.assertTrue(problems.toString(), problems.isEmpty());
            List<String> audit = Audit.check(w.db);
            Assert.assertTrue(audit.toString(), audit.isEmpty());
            w.goOn();
        }
        Assert.assertTrue("tried", tries > 0);
    }

    /**
     * A scan in chunks keeps its actual snapshot: between the chunks, every detachable object
     * is evicted, the writer runs, and a random sweep follows; the chunks together give what
     * one scan at the first chunk's actual time gives on a database without eviction.
     */
    @Nano
    public static void testChunkedScanAcrossEviction() {
        MemoryStream s1 = new MemoryStream(), s2 = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db ref = start(s1, clock, Eviction.Schedule.NONE, 0);
        Db db = start(s2, clock, Eviction.Schedule.RANDOM, 1);
        int keys = 60;
        List<Long> times = load(ref, db, clock, 90, keys, 3);
        long t = times.get(50);

        GetMany all = ref.newGetMany();
        all.lookupTime = t;
        ref.getMany(all);

        List<Kvt> chunks = new ArrayList<Kvt>();
        long actual = -1;
        long[] from = null;
        int round = 0;
        while (true) {
            GetMany g = db.newGetMany();
            g.lookupTime = actual < 0 ? t : actual;
            g.startKey = from;
            g.inclusive = from == null;
            final int[] n = new int[1];
            g.stopCondition = new GetMany.StopCondition() {
                public int handleKvt(Kvt kvt) {
                    return ++n[0] >= 7 ? ADD_AND_STOP : ADD;
                }
                public void eod() {}
            };
            db.getMany(g);
            if (actual < 0) actual = g.actualLookupTime;
            Assert.assertEquals(actual, g.actualLookupTime);
            chunks.addAll(g.result);
            if (g.result.size() < 7) break;
            from = g.result.get(g.result.size() - 1).key;
            db.internal().evictNow(Eviction.Schedule.EVERY, round);
            round++;
            clock.setTime(times.get(times.size() - 1) + round * STEP);
            for (Db d : new Db[] {ref, db}) {
                d.execute(d.trans().put("k" + (round * 11 % keys), "s" + round).build());
            }
            db.internal().evictNow(Eviction.Schedule.RANDOM, round);
        }
        Assert.assertEquals(all.actualLookupTime, actual);
        Assert.assertEquals(all.result.size(), chunks.size());
        for (int j = 0; j < chunks.size(); j++) {
            Assert.assertTrue("key " + j, Arrays.equals(all.result.get(j).key, chunks.get(j).key));
            Assert.assertTrue("value " + j, Arrays.equals(all.result.get(j).value, chunks.get(j).value));
        }
        Assert.assertTrue("rounds", round >= 5);
    }

    /**
     * Reader threads, gets at random times, while the writer alternates the pointers
     * between memory and stream: every transaction evicts (random schedule), and every third
     * one is followed by an eviction of every detachable object. Every answer is checked
     * against the history; no read may fail. The unit test: 3 readers and 300 transactions.
     * The f-tests (bergdb item 009, step 3d; 009-02, 3.5): 8 readers and 3,000 transactions;
     * and the same with the capacity controller and a budget far below the database instead
     * of the random schedule, so that readers' loads wake the eviction thread (T5a), whose
     * batches run while the readers follow pointers without a lock.
     */
    @Nano
    public static void testReadersWhileSlotsAlternate() throws Exception {
        readersWhileSlotsAlternate(3, 300, false);
    }

    @Nano("f")
    public static void testReadersWhileSlotsAlternateF() throws Exception {
        readersWhileSlotsAlternate(8, 3000, false);
    }

    @Nano("f")
    public static void testReadersUnderTheCapacityControllerF() throws Exception {
        readersWhileSlotsAlternate(8, 3000, true);
    }

    private static void readersWhileSlotsAlternate(int readerCount, final int n, boolean budget)
            throws Exception {
        MemoryStream s1 = new MemoryStream();
        final CoreTestClock clock = new CoreTestClock();
        final Db db = budget
                ? Db.builder().testSetup(s1).clock(clock).testId().maxNodeSize8()
                        .startupDistance(200).cacheSizeIndicator(4 * 1000)
                        .evictionSchedule(Eviction.Schedule.BUDGET, 1).audit(0).start()
                : start(s1, clock, Eviction.Schedule.RANDOM, 0);
        final int keys = 50;
        final String[][] history = new String[n][];     // per transaction, its values by key
        final long[] times = new long[n];
        final AtomicInteger done = new AtomicInteger(0);    // transactions published
        final ConcurrentLinkedQueue<String> problems = new ConcurrentLinkedQueue<String>();
        final AtomicBoolean stop = new AtomicBoolean(false);
        final AtomicInteger reads = new AtomicInteger(0);

        List<Thread> readers = new ArrayList<Thread>();
        for (int r = 0; r < readerCount; r++) {
            final int rid = r;
            Thread th = new Thread(new Runnable() {
                public void run() {
                    Random rr = new Random(rid);
                    while (!stop.get()) {
                        int m = done.get();
                        if (m == 0) continue;
                        int ti = rr.nextInt(m);
                        int k = rr.nextInt(keys);
                        String exp = null;
                        for (int x = 0; x <= ti; x++) {
                            if (history[x][k] != null) exp = history[x][k];
                        }
                        byte[] got;
                        try {
                            got = DbUtil.get(db, times[ti], "k" + k);
                        } catch (RuntimeException e) {
                            problems.add("get(k" + k + ", " + times[ti] + ") failed: " + e);
                            continue;
                        }
                        String gs = got == null ? null : new String(got);
                        if (exp == null ? gs != null : !exp.equals(gs)) {
                            problems.add("get(k" + k + ", " + times[ti] + "): " + gs + ", expected " + exp);
                        }
                        reads.incrementAndGet();
                    }
                }
            });
            readers.add(th);
            th.start();
        }
        try {
            Random rnd = new Random(7);
            for (int i = 0; i < n; i++) {
                long time = 100 * STEP + (i + 1) * STEP;
                clock.setTime(time);
                String[] h = new String[keys];
                Trans.Builder b = db.trans();
                int c = 1 + rnd.nextInt(5);
                for (int j = 0; j < c; j++) {
                    int k = rnd.nextInt(keys);
                    if (h[k] != null) continue;
                    h[k] = value(i, j);
                    b.put("k" + k, h[k]);
                }
                db.execute(b.build());
                history[i] = h;
                times[i] = time;
                done.set(i + 1);
                if (i % 3 == 2) db.internal().evictNow(Eviction.Schedule.EVERY, i);
            }
        } finally {
            stop.set(true);
            for (Thread th : readers) th.join();
        }
        Assert.assertTrue(problems.size() + " problems, first: " + problems.peek(), problems.isEmpty());
        Assert.assertTrue("reads", reads.get() > 1000);
        if (budget) {
            Assert.assertTrue("batches after loads", db.internal().eviction().sweepCounts()[1] > 0);
        }
    }
}
