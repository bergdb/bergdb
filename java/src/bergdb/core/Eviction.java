package bergdb.core;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.Pointee;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.MemoryStream;

/**
 * Eviction at transaction boundaries (bergdb item 001, WP J2: values; J3: index nodes;
 * docs/level4-alignment.md, 5.2 and 6.2, rows 8 and 9; the Lean model's `Mem.unswizzle`,
 * `Mem.release` and `Mem.detachable`, lean/SIS/Evict.lean). With handles since bergdb item
 * 009, step 3a (items/009-handles/02-implementation-plan.md, 4.7).
 *
 * <p>An object is <b>detachable</b> when it is not pinned (Residents.isPinned: the super
 * root, and the canonical objects of D and of the record being written; also the newest
 * written top node, which Db keeps for the next record) and written (its position is a
 * stream position, not a vpos). Values are never dirty; a new value is detachable once its
 * record is appended. An index object is a version read, or the canonical object of a clean
 * node, which holds exactly the node's latest version (INV-CAN). <b>Evict</b> an index
 * object: its handle dies (Cache3.evict): the object leaves the handle and the handle the
 * node table, a canonical object's flag is cleared (M31: a reader may still hold it), and
 * the handle keeps the position a canonical object was at (Handle.writtenPos), so that a
 * pointer that holds the dead handle is written, and followed, as the unswizzled pointer of
 * before was (the record rule, Handle.serializedRef): no record changes. Nothing asks which
 * pointers hold the handle. A later follow resolves the pointer to the node's live handle by
 * the id, and loads the version again; the writer's follower makes it canonical (the model's
 * `Mem.promote`). <b>Unswizzle</b> a value: a leaf's pointer that holds a detachable value
 * becomes a stream pointer naming its position, under the pointer's lock. Values have no
 * handles and are not in the node table (009-02, 4.8).</p>
 *
 * <p>Admission: a large value (over 1 MiB, as `Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES` does not
 * cache on a read) is not kept: when eviction is on, it is taken once its record is written,
 * whatever the schedule selects.</p>
 *
 * <p>Which detachable objects eviction takes is a schedule. <b>budget</b>, the default (WP
 * J7; the plan's Q9 and Q10): the capacity controller, with the budget of
 * DbBuilder.cacheSizeIndicator (the public API's cacheSizeInMb) for the resident bytes
 * (Residents) as its high watermark and LOW of it as its low one: when the resident bytes
 * pass the budget, at a transaction boundary or after a reader's load (afterLoad), a sweep
 * (sweep()) takes the oldest detachable objects, values first, down to the low watermark
 * (counting the values that leave the resident set with the objects it takes), and takes
 * every detachable object if that is not enough; pinned state is never taken.
 * The schedules for tests (the plan's 8.4): none; values (every detachable value after every
 * transaction, WP J2's eviction); every (every detachable object after every transaction);
 * random (each detachable value pointer and each handle of a detachable object, with
 * probability 0.3, seeded). The system property evict (none, values, every, random or
 * budget; evictseed, default 1; evictbudget, a budget in bytes) sets the default, so that
 * existing stress programs and the gates can run with any schedule.</p>
 *
 * <p>The caller holds Db.writeLock, between transactions: after the record is appended and
 * the record's nodes are out of TransNodes, before the next transaction begins. Not during
 * startup.</p>
 *
 * <p><b>Readers</b> (the plan's Q8; bergdb item 001, WP J5; EvictionReaderTester). Eviction
 * runs only under the write lock, which readers take only for a load-triggered sweep
 * (afterLoad), and kills a handle under its map's lock, with a compareAndSet of its state
 * that fails while a loader holds the handle (LOADING; 009-02, T7a), so eviction never waits
 * for a load. Until step 3c a reader holds the pointer's lock (PointerLocks) for the whole
 * of a follow. A reader that holds an object (it took it from a handle before the
 * eviction) may finish with it: it is the version at its position, so its answers are
 * right; if the reader then puts the dead handle into a pointer, the next follow resolves
 * it again (EvictionReaderTester.testDeadHandleInAPointer).</p>
 */
public final class Eviction {
    /** The schedule; see the class comment. BUDGET is the capacity controller (WP J7). */
    public enum Schedule { NONE, VALUES, EVERY, RANDOM, BUDGET }

    /**
     * The default schedule: the system property evict (none, values, every, random or
     * budget), else budget, the capacity controller: eviction is on by default (WP J7; the
     * plan's Q10, Frans's decision of 2026-10-16), with the budget
     * DbBuilder.cacheSizeIndicator (the public API's cacheSizeInMb). DbBuilder.noEvict()
     * and the test setups make the budget Long.MAX_VALUE, so that nothing is evicted.
     */
    public static Schedule defaultSchedule() {
        String s = System.getProperty("evict");
        if ("none".equals(s)) return Schedule.NONE;
        if ("values".equals(s)) return Schedule.VALUES;
        if ("every".equals(s)) return Schedule.EVERY;
        if ("random".equals(s)) return Schedule.RANDOM;
        return Schedule.BUDGET;
    }

    /** The low watermark, as a fraction of the budget (the high one): see sweep(). */
    static final double LOW = 0.75;

    /** The default seed of the random schedule: the system property evictseed, else 1. */
    public static long defaultSeed() {
        return Long.getLong("evictseed", 1);
    }

    private final Schedule schedule;
    private final Random random;

    /** The capacity controller's watermarks (BUDGET): the budget, and LOW of it. */
    private volatile long high, low;

    /**
     * The resident bytes above which the controller sweeps: the budget; after a sweep that
     * ended above it (pinned state above the budget), that sweep's result plus the gap
     * between the watermarks, so that the controller does not sweep again and again for
     * nothing; back to the budget after a sweep that ends below it.
     */
    private volatile long trigger;

    private long unswizzled = 0;
    private long released = 0;

    // The controller's metrics (BUDGET); see stats().
    private long sweeps = 0, loadSweeps = 0, completeSweeps = 0, overTarget = 0;
    private long sweepNanos = 0, maxSweepNanos = 0;
    private long lastBefore = 0, lastAfter = 0, lastPinned = 0, maxPinned = 0;

    /** Slots unswizzled and objects released by every Db of this process; see totals(). */
    private static long allUnswizzled = 0, allReleased = 0;

    public Eviction(Schedule schedule, long seed) {
        this(schedule, seed, Long.MAX_VALUE);
    }

    /**
     * @param budget  The capacity controller's target for the resident bytes (Residents),
     *                its high watermark (BUDGET; DbBuilder.cacheSizeIndicator).
     */
    public Eviction(Schedule schedule, long seed, long budget) {
        this.schedule = schedule;
        this.random = new Random(seed);
        this.high = budget;
        this.low = budget == Long.MAX_VALUE ? Long.MAX_VALUE : (long) (budget * LOW);
        this.trigger = budget;
    }

    /** The budget, the high watermark. */
    public long budget() {
        return high;
    }

    /**
     * Sets the budget (the cache size indicator, also through JMX: Jmx.DbMonitor); the low
     * watermark follows. Used from the next transaction boundary or load.
     */
    public void setBudget(long budget) {
        if (budget < 1) throw new IllegalArgumentException("Illegal budget, " + budget);
        synchronized (this) {
            this.high = budget;
            this.low = budget == Long.MAX_VALUE ? Long.MAX_VALUE : (long) (budget * LOW);
            this.trigger = budget;
        }
    }

    /** Slots unswizzled and objects released so far; and the controller's metrics. */
    public synchronized String summary() {
        String s = "eviction " + schedule + ": " + unswizzled + " slots unswizzled, " + released
                + " objects released";
        if (schedule == Schedule.BUDGET) s += "; " + stats();
        return s;
    }

    /**
     * The capacity controller's metrics (BUDGET): the budget and the low watermark; the
     * sweeps, those that a load started, the complete ones (needed when the oldest slots did
     * not free enough), and those after which the resident bytes stayed above the budget
     * (pinned state above it); the resident bytes before and after the last sweep, the
     * pinned bytes then and at most; the time of the sweeps.
     */
    public synchronized String stats() {
        return "budget " + high + " bytes, low " + low + "; " + sweeps + " sweeps (" + loadSweeps
                + " after loads, " + completeSweeps + " complete, " + overTarget
                + " above the budget after); last sweep " + lastBefore + " -> " + lastAfter
                + " bytes, pinned " + lastPinned + " (at most " + maxPinned + "); sweep time "
                + sweepNanos / 1000000 + " ms in total, " + maxSweepNanos / 1000000 + " ms at most";
    }

    /**
     * The figures of CacheStats (bergdb item 009, step 1a): the sweeps, the objects
     * released, the time of the sweeps in all and the longest, in nanoseconds.
     */
    public synchronized long[] figures() {
        return new long[] {sweeps, released, sweepNanos, maxSweepNanos};
    }

    /** Sweeps, and sweeps after which the resident bytes stayed above the budget. */
    public synchronized long[] sweepCounts() {
        return new long[] {sweeps, loadSweeps, completeSweeps, overTarget};
    }

    /** Slots unswizzled and objects released by every Db of this process, as a pair. */
    public static synchronized long[] totals() {
        return new long[] {allUnswizzled, allReleased};
    }

    /**
     * Object 'node' may be detached: not pinned, and written. The caller holds Db.writeLock,
     * between transactions.
     */
    static boolean detachable(Node node, TopNode superRoot, TopNode newestWrittenTop) {
        if (node.isInTransNodes()) return false;
        if (node.isIndexNode()) {
            if (node == superRoot || node == newestWrittenTop) return false;
            if (Residents.isPinned(node, superRoot)) return false;
        }
        long spos = node.getSpos();
        return Spos.isValid(spos) && !Spos.isVpos(spos);
    }

    /** The schedule takes detachable object c; a large value always. */
    private boolean selected(Node c) {
        if (!c.isIndexNode() && !Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES.shouldCache(c)) return true;
        switch (schedule) {
            case VALUES: return !c.isIndexNode();
            case EVERY: return true;
            case RANDOM: return random.nextInt(10) < 3;
            default: return false;
        }
    }

    /**
     * After a transaction: unswizzles the slots of resident objects to detachable objects
     * that the schedule selects (large values always), then releases the objects that no
     * resident memory slot names any more. The caller holds Db.writeLock, between
     * transactions.
     */
    public void afterTransaction(Db db) {
        if (schedule == Schedule.NONE) return;
        if (schedule == Schedule.BUDGET) {
            if (db.internal().cache().residents().bytes() > trigger) sweep(db, false);
            return;
        }
        final Db.Internal in = db.internal();
        final Cache3 table = in.cache();
        final TopNode superRoot = in.superRoot();
        final TopNode newestWritten = in.newestWrittenTop();

        final java.util.ArrayList<Node> dObjects = new java.util.ArrayList<Node>();
        in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                dObjects.add(node);
            }
        });
        List<Node> resident = Residents.walk(superRoot, table.nodes(), dObjects);

        // 1. Values: the pointers of resident objects to detachable values that the schedule
        //    selects become stream pointers (bergdb item 009, step 3a: a value has no
        //    handle; its leaf's pointer holds it). A value so leaves memory, unless another
        //    resident pointer holds it: counted as released.
        long n = 0, r = 0;
        for (Node x : resident) {
            if (!(x instanceof KeyNode)) continue;
            int size = x.getSize();
            for (int i = 0; i < size; i++) {
                Pointee p = x.getPointee(i);
                if (!(p instanceof ValueNode)) continue;
                ValueNode v = (ValueNode) p;
                if (detachable(v, superRoot, newestWritten) && selected(v)) {
                    if (unswizzleValue(in, x, i, v)) {
                        n++;
                        r++;
                    }
                }
            }
        }

        // 2. Index nodes: the handles of detachable objects that the schedule selects are
        //    evicted (Cache3.evict): local, whoever points to them (009-02, 4.7).
        for (Handle h : table.handles()) {
            Node c = h.obj;
            if (c == null) continue;
            if (detachable(c, superRoot, newestWritten) && selected(c)) {
                if (table.evict(h)) r++;
            }
        }
        synchronized (this) {
            unswizzled += n;
            released += r;
        }
        synchronized (Eviction.class) {
            allUnswizzled += n;
            allReleased += r;
        }

        // 3. The accounting, exact again: the objects that are still resident.
        table.residents().resync(Residents.walk(superRoot, table.nodes(), dObjects));
    }

    /**
     * Pointer i of x to value v becomes a stream pointer naming v's position, under the
     * pointer's lock, if it still holds v. True if it did.
     */
    private static boolean unswizzleValue(Db.Internal in, Node x, int i, ValueNode v) {
        synchronized (in.getPointerLock(x, i)) {
            if (x.getPointee(i) != v) return false;
            x.setPointer(i, null, v.getSpos());
            return true;
        }
    }

    // ======== The capacity controller (BUDGET; bergdb item 001, WP J7) ========

    /**
     * After a reader's load (NodeCollection.followPointer, a stream slot followed; the
     * reader holds no pointer lock then): when the resident bytes are above the budget, a
     * sweep under the write lock, a load-triggered batch (Q8, Q9), so that reads without
     * writes stay within the budget. Not inside a transaction (the thread holds the write
     * lock: the user's own read in a value transformation; the transaction's end sweeps) and
     * not before the database is active (startup).
     */
    public void afterLoad(Db db) {
        if (schedule != Schedule.BUDGET) return;
        Db.Internal in = db.internal();
        if (in.cache().residents().bytes() <= trigger) return;
        Object writeLock = in.getWriteLock();
        if (Thread.holdsLock(writeLock) || !in.isActive()) return;
        synchronized (writeLock) {
            if (in.cache().residents().bytes() > trigger) sweep(db, true);
        }
    }

    /**
     * A candidate of a sweep: a value pointer of a resident object (x, i, the value c), or
     * a handle h with its object c; its age (the access time of the last follow, of the
     * value's leaf or of the handle; Handle.stamp) and its place in the walk's breadth-first
     * order (seq).
     */
    private static final class Slot {
        final Node x;
        final int i;
        final Handle h;
        final Node c;
        final long time;
        final int seq;

        Slot(Node x, int i, Handle h, Node c, long time, int seq) {
            this.x = x;
            this.i = i;
            this.h = h;
            this.c = c;
            this.time = time;
            this.seq = seq;
        }
    }

    /**
     * The oldest first; of slots of the same age, the later in the walk's breadth-first order
     * first, so the deeper: an operation gives every node it follows the same access data, so
     * a node and the nodes below it are often of the same age, and the sweep takes the leaves
     * before the inner nodes above them.
     */
    private static final Comparator<Slot> OLDEST_FIRST = new Comparator<Slot>() {
        public int compare(Slot a, Slot b) {
            if (a.time != b.time) return a.time < b.time ? -1 : 1;
            return a.seq > b.seq ? -1 : a.seq < b.seq ? 1 : 0;
        }
    };

    /** Large values first (admission: a value over 1 MiB is not kept), then the oldest. */
    private static final Comparator<Slot> LARGE_THEN_OLDEST = new Comparator<Slot>() {
        public int compare(Slot a, Slot b) {
            boolean la = !Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES.shouldCache(a.c);
            boolean lb = !Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES.shouldCache(b.c);
            if (la != lb) return la ? -1 : 1;
            return OLDEST_FIRST.compare(a, b);
        }
    };

    /** The age of a handle's last follow, or 0. */
    private static long ageOf(Handle h) {
        long acc = h == null ? Spos.NULL : h.stamp;
        return AccessData.isValid(acc) ? AccessData.getAccessTime(acc) : 0;
    }

    /**
     * One sweep of the capacity controller, down to the low watermark (Q9): first values
     * (those over 1 MiB first, as a read does not cache them either: admission), each
     * pointer to one made a stream pointer under its pointer lock; then index nodes, the
     * oldest first by their access time (the access clock when a reader or the writer last
     * followed a pointer to the node: Handle.stamp), each evicted (Cache3.evict; bergdb item
     * 009, step 3a: with handles, nothing asks who points to an object); then the accounting
     * is made exact (Residents.resync). What the sweep frees is counted as it goes: an
     * object it evicts, with the values that only it holds, or a value no other resident
     * pointer holds; so a sweep stops near the low watermark. If the resident bytes are
     * still above the budget, a complete sweep follows: every detachable object, whatever
     * its age, so that a working set larger than the budget cannot stop progress. Pinned
     * state is never taken; if it alone is above the budget, the sweep is counted as above
     * the budget (stats()), and the next sweep waits until the resident bytes have grown by
     * the gap between the watermarks (trigger), so that pinned state above the budget does
     * not make every transaction and every load sweep. In this step (3a) the sweep still
     * walks every resident object (Residents.walk), for its choice and its byte count; step
     * 3b removes the walks. The caller holds Db.writeLock, between transactions.
     */
    void sweep(Db db, boolean afterLoad) {
        final long t0 = System.nanoTime();
        final Db.Internal in = db.internal();
        final Cache3 table = in.cache();
        final Residents res = table.residents();
        final TopNode superRoot = in.superRoot();
        final TopNode newestWritten = in.newestWrittenTop();
        final ArrayList<Node> dObjects = new ArrayList<Node>();
        in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                dObjects.add(node);
            }
        });
        List<Node> resident = Residents.walk(superRoot, table.nodes(), dObjects);

        long before = 0, pinned = 0;
        int seq = 0;
        IdentityHashMap<Node, int[]> named = new IdentityHashMap<Node, int[]>();
        IdentityHashMap<Node, Integer> order = new IdentityHashMap<Node, Integer>();
        ArrayList<Slot> values = new ArrayList<Slot>(), index = new ArrayList<Slot>();
        for (Node x : resident) {
            int size = x.getMemSize();
            before += size;
            order.put(x, seq++);
            if (x.isIndexNode() && !detachable(x, superRoot, newestWritten)) pinned += size;
            if (!(x instanceof KeyNode)) continue;
            int n = x.getSize();
            for (int i = 0; i < n; i++) {
                Pointee p = x.getPointee(i);
                if (!(p instanceof ValueNode)) continue;
                ValueNode v = (ValueNode) p;
                int[] count = named.get(v);
                if (count == null) named.put(v, count = new int[1]);
                count[0]++;
                if (!detachable(v, superRoot, newestWritten)) continue;
                values.add(new Slot(x, i, null, v, ageOf(Cache3.handleOf(x)), seq));
            }
        }
        for (Handle h : table.handles()) {
            Node c = h.obj;
            if (c == null || !detachable(c, superRoot, newestWritten)) continue;
            Integer s = order.get(c);
            index.add(new Slot(null, -1, h, c, ageOf(h), s == null ? 0 : s));
        }

        long need = before - low;
        long freed = 0, n = 0, r = 0;
        // 1. Values, then index nodes, the oldest first. Large values always.
        for (int pass = 0; pass < 2 && freed < need; pass++) {
            ArrayList<Slot> list = pass == 0 ? values : index;
            Collections.sort(list, pass == 0 ? LARGE_THEN_OLDEST : OLDEST_FIRST);
            for (Slot sl : list) {
                if (freed >= need) break;
                if (pass == 0) {
                    if (!unswizzleValue(in, sl.x, sl.i, (ValueNode) sl.c)) continue;
                    n++;
                    int[] count = named.get(sl.c);
                    if (--count[0] == 0) {
                        freed += sl.c.getMemSize();
                        r++;
                    }
                } else {
                    if (sl.h.obj != sl.c || !table.evict(sl.h)) continue;
                    r++;
                    freed += sl.c.getMemSize() + valuesOnlyIn(sl.c, named);
                }
            }
        }
        res.resync(Residents.walk(superRoot, table.nodes(), dObjects));

        boolean complete = false;
        if (res.bytes() > high) {
            // 2. Under pressure: every detachable object (a complete sweep).
            complete = true;
            long[] nr = takeAll(in, table, superRoot, newestWritten, dObjects);
            n += nr[0];
            r += nr[1];
            res.resync(Residents.walk(superRoot, table.nodes(), dObjects));
        }
        long after = res.bytes();
        trigger = after > high ? after + (high - low) : high;
        long dt = System.nanoTime() - t0;
        synchronized (this) {
            unswizzled += n;
            released += r;
            sweeps++;
            if (afterLoad) loadSweeps++;
            if (complete) completeSweeps++;
            if (after > high) overTarget++;
            lastBefore = before;
            lastAfter = after;
            lastPinned = pinned;
            maxPinned = Math.max(maxPinned, pinned);
            sweepNanos += dt;
            maxSweepNanos = Math.max(maxSweepNanos, dt);
        }
        synchronized (Eviction.class) {
            allUnswizzled += n;
            allReleased += r;
        }
    }

    /**
     * The bytes of the values that only object c holds among the resident objects (their
     * counts of resident pointers, 'named', reach 0 as c leaves).
     */
    private static long valuesOnlyIn(Node c, IdentityHashMap<Node, int[]> named) {
        if (!(c instanceof KeyNode)) return 0;
        long bytes = 0;
        int size = c.getSize();
        for (int i = 0; i < size; i++) {
            Pointee p = c.getPointee(i);
            if (!(p instanceof ValueNode)) continue;
            int[] count = named.get(p);
            if (count != null && --count[0] == 0) bytes += ((ValueNode) p).getMemSize();
        }
        return bytes;
    }

    /**
     * Makes every pointer of a resident object to a detachable value a stream pointer, and
     * evicts every handle of a detachable object. Returns the pointers and the objects.
     */
    private static long[] takeAll(Db.Internal in, Cache3 table, TopNode superRoot,
            TopNode newestWritten, List<Node> dObjects) {
        List<Node> resident = Residents.walk(superRoot, table.nodes(), dObjects);
        long n = 0, r = 0;
        for (Node x : resident) {
            if (!(x instanceof KeyNode)) continue;
            int size = x.getSize();
            for (int i = 0; i < size; i++) {
                Pointee p = x.getPointee(i);
                if (!(p instanceof ValueNode)) continue;
                ValueNode v = (ValueNode) p;
                if (detachable(v, superRoot, newestWritten) && unswizzleValue(in, x, i, v)) n++;
            }
        }
        for (Handle h : table.handles()) {
            Node c = h.obj;
            if (c != null && detachable(c, superRoot, newestWritten) && table.evict(h)) r++;
        }
        return new long[] {n, r};
    }

    // ======== Tests ========
    //
    // The cases of docs/level4-plan.md, section 9 (bergdb item 001, WPs J2 and J3), each run
    // as a twin: the same transactions on a database without eviction and on one with a
    // schedule, the audit after every transaction (INV-CAN, the pins, INV-SLOT), the streams
    // byte for byte the same and every lookup the same.

    /** The schedules each case runs with: values, every, and random with three seeds. */
    private static final Schedule[] SCHEDULES = {Schedule.VALUES, Schedule.EVERY,
            Schedule.RANDOM, Schedule.RANDOM, Schedule.RANDOM};

    /**
     * The indexes of SCHEDULES. A case runs as a unit test with one schedule and the
     * checks of every time only (quick), and as an f-test, its name ending in F, with every
     * schedule and every check.
     */
    private static final int[] ALL = {0, 1, 2, 3, 4};

    /** One time step of the twins' clock, 10 ms; 50 ms with reclaim. */
    private static final long STEP = bergdb.pub.util.Clock.UNITS_PER_SEC / 100;

    /**
     * Two databases with the same transactions and clock: 'ref' without eviction, 'sub' with
     * a schedule and the audit after every transaction. check() compares their streams byte
     * for byte, from the later first position of the two (a cut decided is made when the
     * stream is durable, which depends on the storage threads' timing), and their answers to
     * lookups of every key at every time so far, from the first available time on, and that
     * no audit failed. The streams are CutStreams, so a read below a cut fails; with reclaim,
     * retain is in seconds. Quick: check(false) does nothing, as each check waits for the
     * storage threads.
     */
    private static final class Twin {
        final Schedule schedule;
        final long seed;
        final int retain;
        final boolean quick;
        final long step;
        final CoreTestClock clock = new CoreTestClock();
        final java.util.ArrayList<Long> times = new java.util.ArrayList<Long>();
        final java.util.TreeSet<String> keys = new java.util.TreeSet<String>();
        final long auditFailures = Audit.failures();
        bergdb.stream.CutStream s1 = new bergdb.stream.CutStream();
        bergdb.stream.CutStream s2 = new bergdb.stream.CutStream();
        Db ref, sub;
        long time = 100 * STEP;
        int sharedIndex = 0, sharedValues = 0;

        Twin(Schedule schedule, long seed, int retain, boolean quick) {
            this.schedule = schedule;
            this.seed = seed;
            this.retain = retain;
            this.quick = quick;
            this.step = retain > 0 ? 5 * STEP : STEP;
            ref = start(s1, Schedule.NONE);
            sub = start(s2, schedule);
        }

        private Db start(bergdb.stream.CutStream s, Schedule sch) {
            // A small startup distance, so that index nodes are written soon and leave D,
            // and eviction takes them too.
            DbBuilder b = Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8()
                    .startupDistance(300).evictionSchedule(sch, seed)
                    .audit(sch == Schedule.NONE ? 0 : 1);
            Db db = b.start();
            if (retain > 0) db.setRetainDuration(retain * bergdb.pub.util.Clock.UNITS_PER_SEC);
            return db;
        }

        /** A transaction on both: "k=v" puts, "-k" deletes; none, an empty one. */
        void trans(String... ops) {
            time += step;
            clock.setTime(time);
            for (Db db : new Db[] {ref, sub}) {
                Trans.Builder b = db.trans();
                for (String op : ops) {
                    if (op.startsWith("-")) {
                        b.delete(op.substring(1));
                    } else {
                        int e = op.indexOf('=');
                        b.put(op.substring(0, e), op.substring(e + 1));
                    }
                }
                db.execute(b.build());
            }
            for (String op : ops) keys.add(op.startsWith("-") ? op.substring(1) : op.substring(0, op.indexOf('=')));
            times.add(time);
            countShared();
            if (schedule == Schedule.EVERY) assertOnlyPinned();
        }

        /** After a transaction with the schedule every: only pinned objects are resident. */
        private void assertOnlyPinned() {
            Db.Internal in = sub.internal();
            final java.util.ArrayList<Node> d = new java.util.ArrayList<Node>();
            in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
                public void node(Node node, long tpos, long lastTpos) {
                    d.add(node);
                }
            });
            for (Node x : Residents.walk(in.superRoot(), in.cache().nodes(), d)) {
                Assert.assertTrue("resident and detachable: " + x,
                        !detachable(x, in.superRoot(), in.newestWrittenTop()));
            }
        }

        /** Restarts 'sub' (only) from its stream. */
        void restart() {
            sub.sync(SyncLevel.STRONG);
            sub.stop();
            s2 = s2.copy();
            sub = start(s2, schedule);
        }

        /** Reads every key at time t in 'sub' (loads of historical nodes), as in 'ref'. */
        void read(long t) {
            for (String k : keys) {
                Assert.assertTrue("get(" + k + ", " + t + ")", java.util.Arrays.equals(
                        DbUtil.get(ref, t, k), DbUtil.get(sub, t, k)));
            }
            countShared();
        }

        /** The comparison, at every time so far (all) or the latest only. */
        void check(boolean all) {
            if (quick && !all) return;
            ref.sync(SyncLevel.STRONG);
            sub.sync(SyncLevel.STRONG);
            Assert.assertEquals(s1.getLength(), s2.getLength());
            Assert.assertTrue("same bytes", sameBytes(s1, s2));
            Assert.assertEquals(ref.getFirstAvailableLookupTime(), sub.getFirstAvailableLookupTime());
            read(Long.MAX_VALUE);
            if (all) {
                long first = sub.getFirstAvailableLookupTime();
                for (long t : times) {
                    if (t >= first) read(t);
                    if (t - 1 >= first) read(t - 1);
                }
            }
            Assert.assertEquals("audit failures", auditFailures, Audit.failures());
        }

        /** Counts objects that two or more memory slots of resident objects name. */
        private void countShared() {
            Db.Internal in = sub.internal();
            final java.util.ArrayList<Node> d = new java.util.ArrayList<Node>();
            in.transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
                public void node(Node node, long tpos, long lastTpos) {
                    d.add(node);
                }
            });
            IdentityHashMap<Node, Integer> named = new IdentityHashMap<Node, Integer>();
            for (Node x : Residents.walk(in.superRoot(), in.cache().nodes(), d)) {
                if (!x.isIndexNode()) continue;
                for (int i = 0; i < x.getSize(); i++) {
                    Node c = x.getPointerNode(i);
                    if (c == null) continue;
                    Integer n = named.get(c);
                    named.put(c, n == null ? 1 : n + 1);
                }
            }
            for (Map.Entry<Node, Integer> e : named.entrySet()) {
                if (e.getValue() < 2) continue;
                if (e.getKey().isIndexNode()) sharedIndex++;
                else sharedValues++;
            }
        }

        long released() {
            return sub.internal().eviction().released;
        }
    }

    private static boolean sameBytes(bergdb.stream.CutStream s1, bergdb.stream.CutStream s2) {
        long first = Math.max(s1.getFirstPos(), s2.getFirstPos());
        int n = (int) (s1.getLength() - first);
        byte[] b1 = new byte[n], b2 = new byte[n];
        try {
            s1.read(first, b1, 0, n);
            s2.read(first, b2, 0, n);
        } catch (java.io.IOException e) {
            throw new RuntimeException(e);
        }
        return java.util.Arrays.equals(b1, b2);
    }

    private static Twin twin(int s, boolean quick) {
        return new Twin(SCHEDULES[s], 1 + s, 0, quick);
    }

    /**
     * One child, several parents: an old version of a parent, read from the stream at an old
     * time, names in its slot the canonical object of a child that a current parent names
     * too. An object stays while a slot names it (the random schedule unswizzles some slots
     * of a shared object) and is loaded again after release. With empty transactions.
     */
    @Nano
    public static void testSharedChild() {
        sharedChild(true, 2);
    }

    @Nano("f")
    public static void testSharedChildF() {
        sharedChild(false, ALL);
    }

    private static void sharedChild(boolean quick, int... schedules) {
        int shared = 0;
        for (int s : schedules) {
            Twin w = twin(s, quick);
            for (int i = 0; i < 40; i++) {
                if (i % 3 == 0) w.trans();
                else w.trans("a" + (i % 17) + "=" + i, "b=" + i);
            }
            w.restart();
            for (int i = 0; i < 20; i++) {
                w.trans("a" + (i % 5) + "=x" + i);
                w.read(w.times.get(i * 2));
                if (i % 3 == 0) w.trans();
                w.check(i % 5 == 4);
            }
            w.check(true);
            Assert.assertTrue("released", w.released() > 0);
            shared += w.sharedIndex;
        }
        Assert.assertTrue("an index object named by two slots", shared > 0);
    }

    /**
     * An old snapshot and a newer canonical object: reads at old times load old versions
     * (as snapshots, after the canonical objects were released), the writer then loads the
     * latest versions and makes them canonical; the records and later reads are right.
     */
    @Nano
    public static void testOldSnapshotAndNewerCanonical() {
        oldSnapshotAndNewerCanonical(true, 1);
    }

    @Nano("f")
    public static void testOldSnapshotAndNewerCanonicalF() {
        oldSnapshotAndNewerCanonical(false, ALL);
    }

    private static void oldSnapshotAndNewerCanonical(boolean quick, int... schedules) {
        for (int s : schedules) {
            Twin w = twin(s, quick);
            for (int i = 0; i < 30; i++) w.trans("k" + (i * 7 % 30) + "=" + i);
            for (int i = 0; i < 20; i++) {
                w.read(w.times.get(i * 3 % 30));
                w.trans("k5=u" + i, "k" + (i * 11 % 30) + "=w" + i);
                w.check(i % 5 == 4);
            }
            w.check(true);
        }
    }

    /** Startup, later updates, writeout, eviction; and again after a restart. */
    @Nano
    public static void testStartupUpdatesWriteoutEviction() {
        startupUpdatesWriteoutEviction(true, 3);
    }

    @Nano("f")
    public static void testStartupUpdatesWriteoutEvictionF() {
        startupUpdatesWriteoutEviction(false, ALL);
    }

    private static void startupUpdatesWriteoutEviction(boolean quick, int... schedules) {
        for (int s : schedules) {
            Twin w = twin(s, quick);
            for (int i = 0; i < 25; i++) w.trans("k" + i + "=" + i);
            w.restart();
            w.check(true);
            for (int i = 0; i < 25; i++) {
                w.trans("k" + (i * 3 % 25) + "=v" + i);
                if (i % 8 == 7) w.restart();
                w.check(i % 6 == 5);
            }
            w.restart();
            w.check(true);
        }
    }

    /**
     * Splits, replacement and root changes: keys in order and in reverse (the root splits
     * several times), deletes, several changes of the root in one transaction.
     */
    @Nano
    public static void testSplitsAndRootChanges() {
        splitsAndRootChanges(true, 1);
    }

    @Nano("f")
    public static void testSplitsAndRootChangesF() {
        splitsAndRootChanges(false, ALL);
    }

    private static void splitsAndRootChanges(boolean quick, int... schedules) {
        int n = quick ? 30 : 60;
        for (int s : schedules) {
            Twin w = twin(s, quick);
            for (int i = 0; i < n; i++) {
                w.trans("k" + (1000 + i) + "=" + i, "j" + (2000 - i) + "=" + i);
                w.check(i % 20 == 19);
            }
            String[] many = new String[40];
            for (int i = 0; i < many.length; i++) many[i] = "m" + (3000 + i) + "=" + i;
            w.trans(many);
            w.check(true);
            for (int i = 0; i < n; i += 2) {
                w.trans("-k" + (1000 + i), "-j" + (2000 - i), "-m" + (3000 + i % 40));
                w.check(i % 20 == 18);
            }
            w.check(true);
        }
    }

    /**
     * Cold historical parents and shared, updated children (the Lean model's example 5): an
     * old version of a parent, read at an old time after eviction, names old versions of
     * children that the writer updates since; with long keys, whose delete leaves a subtree
     * cold.
     */
    @Nano
    public static void testHistoricalParentsAndLongKeys() {
        historicalParentsAndLongKeys(true, 4);
    }

    @Nano("f")
    public static void testHistoricalParentsAndLongKeysF() {
        historicalParentsAndLongKeys(false, ALL);
    }

    private static void historicalParentsAndLongKeys(boolean quick, int... schedules) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < 300; i++) sb.append((char) ('a' + i % 26));
        String pad = sb.toString();
        for (int s : schedules) {
            Twin w = twin(s, quick);
            for (int i = 0; i < 40; i++) w.trans("p" + i + "=" + i, "L" + (i % 6) + pad + "=" + i);
            long old = w.times.get(10);
            for (int i = 0; i < (quick ? 15 : 30); i++) {
                w.read(old);
                w.read(w.times.get(25 + i % 10));
                if (i % 5 == 2) w.trans("-L" + (i % 6) + pad);
                else w.trans("p" + (i % 40) + "=x" + i, "L" + (i % 6) + pad + "=y" + i);
                w.check(i % 10 == 9);
            }
            w.restart();
            w.read(old);
            w.trans("p1=z");
            w.check(true);
        }
    }

    /**
     * Reclaim with misses: cuts on a CutStream, which refuses reads below the cut; slots
     * unswizzled to versions above the cut are loaded again, and restarts from the cut
     * stream.
     */
    @Nano
    public static void testReclaimWithMisses() {
        reclaimWithMisses(true, 2);
    }

    @Nano("f")
    public static void testReclaimWithMissesF() {
        reclaimWithMisses(false, ALL);
    }

    private static void reclaimWithMisses(boolean quick, int... schedules) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < 1000; i++) sb.append((char) ('a' + i % 26));
        String big = sb.toString();
        long cuts = 0;
        for (int s : schedules) {
            Twin w = new Twin(SCHEDULES[s], 1 + s, 1, quick);
            for (int i = 0; i < (quick ? 100 : 200); i++) {
                w.trans("k" + (i * 7 % 40) + "=" + i + big, i % 9 == 0 ? "-k" + (i % 40) : "c=" + i);
                if (i % 50 == 49) w.restart();
                w.check(i % 25 == 24);
            }
            w.check(true);
            if (w.s2.getCut() > 0) cuts++;
        }
        Assert.assertEquals("a cut in every run", (long) schedules.length, cuts);
    }

    /** A key node object that a memory slot of a resident parent names, and a value in a
     *  memory slot of it that the node table names: {parent, slot, key node, value}. */
    private static Object[] valueHeldBelow(Db db) {
        Cache3 table = db.internal().cache();
        java.util.ArrayDeque<Node> todo = new java.util.ArrayDeque<Node>();
        todo.add(db.internal().superRoot());
        Set<Node> seen = java.util.Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        while (!todo.isEmpty()) {
            Node p = todo.poll();
            if (!seen.add(p)) continue;
            for (int i = 0; i < p.getSize(); i++) {
                Node k = p.getPointerNode(i);
                if (k == null || !k.isIndexNode()) continue;
                todo.add(k);
                if (!(k instanceof KeyNode)) continue;
                for (int j = 0; j < k.getSize(); j++) {
                    Node v = k.getPointerNode(j);
                    if (v instanceof ValueNode && !((ValueNode) v).isDelete()) {
                        return new Object[] {p, i, k, v, j};
                    }
                }
            }
        }
        return null;
    }

    /**
     * Values are not in the node table (bergdb item 009, step 3a; 009-02, 4.8): a value a
     * reader loads goes into its leaf's pointer only, and a sweep of every detachable object
     * makes those pointers stream pointers again. (From 2026-10-18 to step 3a this test was
     * of a value that only the node table held, after the key node version that had loaded
     * it left memory; with handles no value is in the table.)
     */
    @Nano
    public static void testValuesNotInTheTable() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8()
                .startupDistance(200).evictionSchedule(Schedule.EVERY, 1).start();
        long time = 100 * STEP;
        for (int i = 0; i < 30; i++) {
            time += STEP;
            clock.setTime(time);
            db.execute(db.trans().put("k" + i, "v" + i).build());
        }
        for (int i = 0; i < 30; i++) DbUtil.get(db, "k" + i);       // loads, values too
        Object[] found = valueHeldBelow(db);
        Assert.assertTrue("a value in a leaf's pointer", found != null);
        Node v = (Node) found[3];
        Assert.assertTrue("not in the node table", db.internal().cache().getNode(v.getId()) == null);
        time += STEP;
        clock.setTime(time);
        db.execute(db.trans().build());             // an empty transaction, and its sweep
        Node p = (Node) found[2];
        int i = (Integer) found[4];
        Assert.assertTrue("the value's pointer is a stream pointer", p.getPointee(i) != v);
        Assert.assertEquals("v" + 0, new String(DbUtil.get(db, "k0")));
        db.stop();
    }

    /**
     * Values (WP J2): a value is released after its record is written and read again from
     * the stream; values under a dirty parent too; and a value named by two slots.
     */
    @Nano
    public static void testValues() {
        values(true, 0);
    }

    @Nano("f")
    public static void testValuesF() {
        values(false, ALL);
    }

    private static void values(boolean quick, int... schedules) {
        Twin w = new Twin(Schedule.VALUES, 1, 0, quick);
        w.trans("a=1", "b=2");
        w.trans("c=3");
        Assert.assertTrue("released", w.released() > 0);
        w.check(true);
        for (int i = 0; i < 40; i++) {
            w.trans("k" + (i * 7 % 23) + "=v" + i, i % 5 == 4 ? "-k" + (i % 23) : "x=" + i);
            if (i == 20) w.restart();
            w.check(i % 10 == 9);
        }
        int shared = 0;
        for (int s : schedules) {
            Twin r = twin(s, quick);
            for (int i = 0; i < 30; i++) {
                r.trans("k" + (i % 10) + "=v" + i);
                r.read(r.times.get(i / 2));
            }
            r.check(true);
            shared += r.sharedValues;
        }
        // Until bergdb item 009, step 3a: a value named by two slots (shared > 0). Values
        // are no longer in the node table, so two leaves that load a value get a copy each;
        // a value is shared only where a split copies a pointer that holds it.
    }
}
