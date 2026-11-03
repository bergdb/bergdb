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
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * Eviction at transaction boundaries (bergdb item 001, WP J2: values; J3: index nodes;
 * bergdb 001-08, 5.2 and 6.2, rows 8 and 9; the Lean model's `Mem.unswizzle`,
 * `Mem.release` and `Mem.detachable`, lean/SIS/Evict.lean until bergdb 005-62). With handles
 * since bergdb item 009, step 3a (items/009-handles/02-implementation-plan.md, 4.7).
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
 * becomes a stream pointer naming its position, under the leaf's monitor. Values have no
 * handles and are not in the node table (009-02, 4.8).</p>
 *
 * <p>Admission: a large value (over 1 MiB, as `Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES` does not
 * cache on a read) is not kept: when eviction is on, it is taken once its record is written,
 * whatever the schedule selects.</p>
 *
 * <p>Which detachable objects eviction takes is a schedule. <b>budget</b>, the default (WP
 * J7; the plan's Q9 and Q10): the capacity controller, with the budget of
 * DbBuilder.cacheSizeIndicator (the public API's cacheSizeInMb) for the resident bytes
 * (Residents) as its high watermark and 3/4 of it (lowOf) as its low one: when the resident bytes
 * pass the budget, at a transaction boundary or, through the eviction thread, after a
 * reader's load (afterLoad), a batch (sweep()) of CLOCK steps over the node table, one map
 * at a time, takes detachable objects whose CLOCK bit is clear, with the values they hold,
 * down to the low watermark or until the batch has examined its handles (bergdb item 009,
 * step 3b); pinned state is never taken. No walk of the resident objects: the work of a
 * batch is bounded, whatever the size of the database.
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
 * runs only under the write lock, which readers never take (since bergdb item 009, step 3b:
 * a reader's load over the budget wakes the eviction thread), and kills a handle under its
 * map's lock, with a compareAndSet of its state that fails while a loader holds the handle
 * (LOADING; 009-02, T7a), so eviction never waits for a load. A reader follows a pointer
 * without a lock when the pointer's handle holds an object that may serve it (since step
 * 3c; 009-02, 3.4); every change of a pointer's pair, by a reader, the writer or eviction,
 * is made under the node's monitor. A reader that holds an object (it took it from a handle
 * before the eviction) may finish with it: it is the version at its position, so its
 * answers are right; if the reader then puts the dead handle into a pointer, the next
 * follow resolves it again (EvictionReaderTester.testDeadHandleInAPointer).</p>
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

    /**
     * The low watermark of a budget (the high one; see sweep()): floor(3 budget / 4), in
     * integers without overflow (bergdb 005-79), as budget / 4 * 3 is at most 3 2^61 and
     * budget % 4 * 3 / 4 at most 2. Long.MAX_VALUE, no budget, stays Long.MAX_VALUE. It was
     * (long) (budget * 0.75), the same for every budget below 2^53 / 3, about 3 10^15 bytes,
     * where budget and 3 budget / 4 are exact doubles. Between 2^53 / 3 and 2^53 the double
     * product can round up past the next integer.
     */
    static long lowOf(long budget) {
        return budget == Long.MAX_VALUE ? Long.MAX_VALUE : budget / 4 * 3 + budget % 4 * 3 / 4;
    }

    /** The default seed of the random schedule: the system property evictseed, else 1. */
    public static long defaultSeed() {
        return Long.getLong("evictseed", 1);
    }

    private final Schedule schedule;
    private final Random random;

    /** The capacity controller's watermarks (BUDGET): the budget, and lowOf(budget). */
    private volatile long high, low;

    /**
     * The resident bytes above which the controller runs a batch: the budget, or the pinned
     * bytes that the hand's last round found plus the gap between the watermarks if that is
     * more (bergdb item 009, step 3d; sweep()), so that pinned state above the budget does
     * not keep the controller running for nothing.
     */
    private volatile long trigger;

    /**
     * A test's hook in sweep(), under the monitor, between the computation of the trigger and
     * its write (bergdb 005-80, testSetBudgetAtBatchEnd); null but in that test.
     */
    Runnable testBeforeTrigger = null;

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
        this.low = lowOf(budget);
        this.trigger = budget;
    }

    /** The budget, the high watermark. */
    public long budget() {
        return high;
    }

    /**
     * Sets the budget (the cache size indicator: Db.setCacheSizeIndicator, also through JMX);
     * the low watermark follows. Used from the next transaction boundary or load.
     */
    public void setBudget(long budget) {
        if (budget < 1) throw new IllegalArgumentException("Illegal budget, " + budget);
        synchronized (this) {
            this.high = budget;
            this.low = lowOf(budget);
            this.trigger = budget;
        }
    }

    /**
     * Sets the budget as setBudget(long) does, for Db.setCacheSizeIndicator (bergdb 005-52),
     * and wakes the eviction thread if the resident bytes are over the new trigger, so that
     * a decrease is reached also when no transaction or load follows: work that the call
     * starts (010-P3). Not when the database is not active: its thread has ended or ends.
     */
    public void setBudget(Db db, long budget) {
        setBudget(budget);
        if (schedule != Schedule.BUDGET) return;
        Db.Internal in = db.internal();
        if (in.isActive() && in.cache().residents().bytes() > trigger) wake(db);
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
            Db.Internal bin = db.internal();
            if (bin.cache().residents().bytes() > trigger) {
                sweep(db, false);
                // A batch is bounded (BATCH_NANOS): if the resident bytes are still over the
                // trigger, the eviction thread goes on, between transactions (step 3d).
                if (bin.cache().residents().bytes() > trigger && bin.isActive()) wake(db);
            }
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
     * Pointer i of x to value v becomes a stream pointer naming v's position, under x's
     * monitor, if it still holds v. True if it did.
     */
    private static boolean unswizzleValue(Db.Internal in, Node x, int i, ValueNode v) {
        synchronized (x) {          // C2 (bergdb item 009, step 3c; before, the pointer lock)
            if (x.getPointee(i) != v) return false;
            x.setPointer(i, null, v.getSpos());
            in.cache().residents().valueOut(x, v);      // bergdb item 009, step 3b
            return true;
        }
    }

    // ======== The capacity controller (BUDGET; bergdb item 001, WP J7) ========

    /**
     * After a reader's load (the capacity controller, BUDGET): if the resident bytes are over
     * the trigger, the database's eviction thread runs batches, so that reads without writes
     * stay within the budget (Q8, Q9). The reader does not take the write lock: it wakes the
     * thread, which takes it between transactions (bergdb item 009, step 3b; 009-02, T5a).
     * If the resident bytes are over the trigger by more than the gap between the
     * watermarks, the thread is behind the loads, and the reader waits for its next batch, at
     * most LOAD_WAIT_NANOS (step 3d): loads, which grow the resident bytes, go at the pace
     * of eviction. Until step 3b the reader took the write lock itself, and waited for any
     * transaction in progress and for a sweep of the resident objects. Not inside a
     * transaction (the thread holds the write lock: the user's own read in a value
     * transformation; the transaction's end runs a batch) and not before the database is
     * active (startup).
     */
    public void afterLoad(Db db) {
        if (schedule != Schedule.BUDGET) return;
        Db.Internal in = db.internal();
        long bytes = in.cache().residents().bytes();
        if (bytes <= trigger) return;
        if (Thread.holdsLock(in.getWriteLock()) || !in.isActive()) return;
        long batch = batches;
        wake(db);
        if (bytes > trigger + (high - low)) {
            long end = System.nanoTime() + LOAD_WAIT_NANOS;
            while (batches == batch && in.isActive() && System.nanoTime() < end) {
                java.util.concurrent.locks.LockSupport.parkNanos(50 * 1000);
            }
        }
    }

    /** The longest a reader's load waits for the eviction thread (afterLoad): 2 ms. */
    static final long LOAD_WAIT_NANOS = 2L * 1000 * 1000;

    /** The batches the eviction thread has run, for afterLoad's wait. */
    private volatile long batches = 0;

    /**
     * Asks the eviction thread for batches (a request), and starts it if there is none. If a
     * request is pending (wanted), it returns without entering evictorLock: one pending
     * request serves every load until the thread takes it (bergdb 005-65; before, with 8
     * readers, 78,000 loads a second entered the monitor, and its queue made after-load calls
     * of over 10 ms). The protocol, by which no request is lost although the thread waits with
     * no timeout (005-51):
     * <ol>
     * <li>wanted is written only under evictorLock: set here, with notifyAll, and cleared by
     * the thread when it takes the request, before its batches. The thread reads it under the
     * lock before each wait(), which lets the lock go atomically: a request made as the thread
     * is about to wait comes before that read, or after the wait began, and wakes it.</li>
     * <li>A caller that finds wanted set made its change before it read the flag (a load added
     * to the resident bytes, setBudget lowered the trigger), and the thread clears the flag
     * after that read, then reads the bytes and the trigger for its batches (volatile accesses
     * are in one total order): its batches see the change. A caller that finds the flag clear,
     * as the thread has just taken a request, makes a new one, which the thread takes after
     * its batches.</li>
     * <li>The thread ends only with no request pending: when the database is no longer active
     * (the close sets the state, then endThread notifies), or on an interrupt while it waits
     * with none. So a pending request always has a thread that will take it, unless an error
     * ended the thread (a batch that throws), which, as before 005-65, stops the loads'
     * eviction. A load that found the database active just before the close may start a
     * thread after endThread; it ends at once.</li>
     * <li>A reader under pressure (afterLoad) reads batches before wake and parks until a batch
     * has ended, at most LOAD_WAIT_NANOS, whether its request is new or was pending.</li>
     * </ol>
     */
    private void wake(Db db) {
        if (wanted) return;
        synchronized (evictorLock) {
            wanted = true;
            if (evictor == null) {
                evictor = new Thread(new EvictorRun(db), "bergdb-evictor");
                evictor.setDaemon(true);
                evictor.start();
            }
            evictorLock.notifyAll();
        }
    }

    private final Object evictorLock = new Object();
    private Thread evictor = null;      // under evictorLock
    private volatile boolean wanted = false;    // written under evictorLock; see wake()
    private boolean running = false;    // under evictorLock: a batch in progress

    /**
     * Waits until the eviction thread has run the batches readers asked for (at most a
     * second); for tests, which sample the resident bytes after the controller has run.
     */
    public void awaitBatch() {
        long end = System.nanoTime() + 1000L * 1000 * 1000;
        synchronized (evictorLock) {
            while ((wanted || running) && System.nanoTime() < end) {
                try {
                    evictorLock.wait(10);
                } catch (InterruptedException e) {
                    return;
                }
            }
        }
    }

    /**
     * Ends the eviction thread, for the close of a database that is no longer active (bergdb
     * 005-51): wakes it, so that it sees that and ends at once, and with wait, waits until it
     * has ended, through an interrupt, whose flag it keeps, as close() does. Not with wait
     * while the write lock is held: a batch takes it.
     */
    public void endThread(boolean wait) {
        Thread t;
        synchronized (evictorLock) {
            evictorLock.notifyAll();
            t = evictor;
        }
        if (!wait || t == null || t == Thread.currentThread()) return;
        boolean interrupted = false;
        while (true) {
            try {
                t.join();
                break;
            } catch (InterruptedException e) {
                interrupted = true;
            }
        }
        if (interrupted) Thread.currentThread().interrupt();
    }

    /**
     * The eviction thread: when a reader or the writer asks, batches until the resident bytes
     * are at most the trigger, or until the hand has gone over the maps twice without freeing
     * anything (bergdb 015-10), each under the write lock. It ends when the database is no
     * longer active. Between requests it waits with no timeout, so that the thread of a
     * database that is not used does not wake (010-P3, bergdb 005-51); the database's close
     * wakes it (endThread). Until 005-51 it woke once a second, to see whether the database
     * had stopped.
     */
    private final class EvictorRun implements Runnable {
        private final Db db;

        EvictorRun(Db db) {
            this.db = db;
        }

        public void run() {
            Db.Internal in = db.internal();
            while (true) {
                synchronized (evictorLock) {
                    while (!wanted) {
                        if (!in.isActive()) {
                            evictor = null;
                            return;
                        }
                        try {
                            evictorLock.wait();
                        } catch (InterruptedException e) {
                            if (!wanted) {      // not with a request pending (wake, 3)
                                evictor = null;
                                return;
                            }
                        }
                    }
                    wanted = false;
                    running = true;
                }
                try {
                    // Batches until the resident bytes are at most the trigger (bergdb item
                    // 009, step 3d: a batch ends after BATCH_NANOS). Before each, a writer
                    // that waits for the write lock goes first: a monitor is not fair, and a
                    // busy eviction thread would keep the writer out for as long as readers
                    // load; the end of the writer's transaction runs a batch anyway.
                    // They end too when the hand has gone over the maps twice (2 maps() of
                    // them) since the request or since the last batch that freed something
                    // (bergdb 015-10): then nothing can go (every object in use, held by a
                    // loader, or pinned), as the first round may only clear the CLOCK bits and
                    // the second takes what is still clear; the next request, a load or a
                    // transaction's end, starts them again. A batch that took no map (a writer
                    // waited, or its time ran out first) counts none: the next goes on. Until
                    // 015-10 a batch that freed nothing ended them; a batch cut short by its
                    // time or its handles in the first round frees nothing, and when every
                    // object is resident no load comes to start them again.
                    long idleMaps = 0;      // the maps taken without freeing
                    while (in.isActive() && in.cache().residents().bytes() > trigger) {
                        while (in.writersWaiting() > 0 && in.isActive()) {
                            java.util.concurrent.locks.LockSupport.parkNanos(100 * 1000);
                        }
                        long[] fm = null;
                        synchronized (in.getWriteLock()) {
                            if (in.isActive() && in.cache().residents().bytes() > trigger) {
                                fm = sweep(db, true);
                            }
                        }
                        batches++;      // this thread's only (afterLoad reads it)
                        if (fm == null) break;
                        idleMaps = fm[0] > 0 ? 0 : idleMaps + fm[1];
                        if (idleMaps >= 2 * Cache3.maps()) break;
                    }
                } finally {
                    synchronized (evictorLock) {
                        running = false;
                        evictorLock.notifyAll();
                    }
                }
            }
        }
    }

    /** The CLOCK hand: the next map of the node table (Cache3.clockStep). */
    private int hand = 0;

    /**
     * The counted bytes of the objects that were not detachable (pinned) in the hand's
     * current round, and in its last complete round (sweep(); the trigger). Under the write
     * lock.
     */
    private long roundPinned = 0, pinnedOfLastRound = 0;

    /**
     * The handles a batch examines at most (bergdb item 009, step 3b; 009-02, 4.7, K):
     * BATCH, or BATCH_UNDER_PRESSURE when the resident bytes are over the trigger by more
     * than the gap between the watermarks; at most two rounds of the hand over the maps (the
     * first may only clear the CLOCK bits); and at most BATCH_NANOS, 2 ms, of time (step 3d:
     * on s1, a batch of 65,536 handles took up to 100 ms, and a writer waits for the batch
     * in progress). The work of a batch is bounded by these, whatever the size of the
     * database. A batch of the eviction thread also ends when a writer waits for the write
     * lock.
     */
    static final int BATCH = 4096, BATCH_UNDER_PRESSURE = 65536;
    static final long BATCH_NANOS = 2L * 1000 * 1000;

    /**
     * One batch of the capacity controller (bergdb item 009, step 3b; 009-02, 4.7): CLOCK
     * steps over the node table, one map at a time (Cache3.clockStep), from where the last
     * batch stopped, until the resident bytes are below the low watermark or the batch has
     * taken its maps. An object whose handle's CLOCK bit is set (a follow since the hand last
     * passed) gets a second chance; one with the bit clear goes if it is detachable, with the
     * values its pointers hold. No walk of the resident objects, and no count of who points
     * to what: the work is bounded by the maps a batch takes, whatever the size of the
     * database and of the budget. The accounting is without walks, exact but for the objects
     * the writer changed since their last count (Residents; bergdb 015-15). If the
     * resident bytes stay above the budget, the next trigger goes on from the hand; pinned
     * state is never taken: its bytes, which the hand's rounds count, raise the trigger if
     * they are above the budget (trigger). Until step
     * 3b a sweep walked every resident object, twice. Returns the bytes freed and the maps
     * taken (the eviction thread's stop rule, EvictorRun). The caller holds Db.writeLock,
     * between transactions.
     */
    long[] sweep(Db db, boolean afterLoad) {
        final long t0 = System.nanoTime();
        final Db.Internal in = db.internal();
        final Cache3 table = in.cache();
        final Residents res = table.residents();
        final TopNode superRoot = in.superRoot();
        final TopNode newestWritten = in.newestWrittenTop();
        final Cache3.Detachable d = new Cache3.Detachable() {
            public boolean detachable(Node o) {
                return Eviction.detachable(o, superRoot, newestWritten);
            }
        };

        long before = res.bytes();
        // Down to the low watermark, or to the pinned bytes of the hand's last round if they
        // are above it: the rest cannot go.
        long need = before - Math.max(low, pinnedOfLastRound);
        boolean pressure = before > trigger + (high - low);
        long maxHandles = pressure ? BATCH_UNDER_PRESSURE : BATCH;
        final int all = Cache3.maps();
        int maxMaps = 2 * all;
        long freed = 0, r = 0, examined = 0, values = 0;
        int maps = 0;
        boolean complete = false;
        final java.util.ArrayList<Node> pinned = new java.util.ArrayList<Node>();
        // The eviction thread's batch also ends at the next map when a writer waits for the
        // write lock (bergdb item 009, step 3d): on s1, two busy readers on two CPUs kept the
        // thread off a CPU in the middle of a batch, and a commit waited 45 ms for it.
        while (freed < need && examined < maxHandles && maps < maxMaps
                && System.nanoTime() - t0 < BATCH_NANOS
                && !(afterLoad && in.writersWaiting() > 0)) {
            long[] fr = table.clockStep(hand, d, pinned);
            freed += fr[0];
            r += fr[1];
            examined += fr[2];
            // The objects that are not detachable (pinned; bergdb item 009, step 3d): the
            // written values of the key nodes among them become stream pointers (009-02,
            // 4.8), as a pinned object is never evicted and the values that reads load into
            // it would stay, where the sweep took them; and their bytes are the round's
            // pinned bytes.
            for (int j = 0; j < pinned.size(); j++) {
                Node x = pinned.get(j);
                if (x instanceof KeyNode) {
                    long[] fv = unswizzleValues(in, x);
                    freed += fv[0];
                    values += fv[1];
                }
                roundPinned += Residents.countedBytes(x);
            }
            pinned.clear();
            maps++;
            if (++hand == all) {
                hand = 0;
                complete = true;
                pinnedOfLastRound = roundPinned;
                roundPinned = 0;
            }
        }

        long after = res.bytes();
        // The trigger (bergdb item 009, step 3d): the budget, or the pinned bytes of the
        // hand's last round plus the gap between the watermarks if that is more: then the
        // controller runs once the detachable objects have grown by the gap. (In step 3b the
        // trigger was raised only after a round that met no detachable object, so readers
        // that kept loading kept the batches going with pinned state above the budget.)
        // Under this monitor, as setBudget writes the watermarks and the trigger: else a batch
        // that ended as it ran could put back the trigger of the old budget (bergdb 005-65).
        // The hook, a test's, stops the batch between the two (testSetBudgetAtBatchEnd).
        long dt = System.nanoTime() - t0;
        synchronized (this) {
            final long next = Math.max(high, pinnedOfLastRound + (high - low));
            final Runnable hook = testBeforeTrigger;
            if (hook != null) hook.run();
            trigger = next;
            released += r + values;
            unswizzled += values;
            sweeps++;
            if (afterLoad) loadSweeps++;
            if (complete) completeSweeps++;
            if (after > high) overTarget++;
            lastBefore = before;
            lastAfter = after;
            lastPinned = pinnedOfLastRound;
            maxPinned = Math.max(maxPinned, pinnedOfLastRound);
            sweepNanos += dt;
            maxSweepNanos = Math.max(maxSweepNanos, dt);
        }
        synchronized (Eviction.class) {
            allReleased += r + values;
            allUnswizzled += values;
        }
        return new long[] {freed, maps};
    }

    /**
     * The written values that pinned key node x holds become stream pointers (unswizzleValue);
     * returns their bytes and their number. The caller holds Db.writeLock, between
     * transactions (sweep()).
     */
    private static long[] unswizzleValues(Db.Internal in, Node x) {
        long bytes = 0, n = 0;
        int size = x.getSize();
        for (int i = 0; i < size; i++) {
            Pointee p = x.getPointee(i);
            if (!(p instanceof ValueNode)) continue;
            ValueNode v = (ValueNode) p;
            long spos = v.getSpos();
            if (v.isInTransNodes() || !Spos.isValid(spos) || Spos.isVpos(spos)) continue;
            if (unswizzleValue(in, x, i, v)) {
                bytes += v.getMemSize();
                n++;
            }
        }
        return new long[] {bytes, n};
    }

    /** The large values the writer made in this transaction: {holder, index, value}. */
    private final java.util.ArrayList<Object[]> largeValues = new java.util.ArrayList<Object[]>();

    /**
     * The writer made pointer i of x to value v (Db's pointer listener): a value over 1 MiB
     * is remembered, to be unswizzled when its record is written (recordWritten). The caller
     * holds Db.writeLock.
     */
    public void largeValueCreated(Node x, int i, ValueNode v) {
        if (schedule != Schedule.NONE && !Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES.shouldCache(v)) {
            largeValues.add(new Object[] {x, i, v});
        }
    }

    /**
     * Admission (bergdb item 009, step 3b): after a record is written, a pointer of a written
     * key node to a value over 1 MiB becomes a stream pointer, as a read does not cache such
     * a value either (Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES). With eviction on (any schedule
     * but none). Until step 3b a sweep took them, first. The work is the record's: its key
     * nodes' pointers. The caller holds Db.writeLock (Db.store).
     */
    public void recordWritten(Db db, java.util.Iterator<Node> written) {
        if (schedule == Schedule.NONE) {
            largeValues.clear();
            return;
        }
        Db.Internal in = db.internal();
        long n = 0;
        // The large values the transaction made: their pointers, as the writer made them
        // (largeValueCreated). A value is written with its transaction's record, which this is.
        for (Object[] lv : largeValues) {
            Node x = (Node) lv[0];
            int i = (Integer) lv[1];
            ValueNode v = (ValueNode) lv[2];
            if (!Spos.isValid(v.getSpos()) || Spos.isVpos(v.getSpos())) continue;
            int size = x.getSize();
            if (i >= size || x.getPointee(i) != v) {
                i = -1;
                for (int j = 0; j < size; j++) if (x.getPointee(j) == v) i = j;
            }
            if (i >= 0 && unswizzleValue(in, x, i, v)) n++;
        }
        largeValues.clear();
        while (written.hasNext()) {
            Node x = written.next();
            if (!(x instanceof KeyNode)) continue;
            int size = x.getSize();
            for (int i = 0; i < size; i++) {
                Pointee p = x.getPointee(i);
                if (!(p instanceof ValueNode)) continue;
                ValueNode v = (ValueNode) p;
                if (!Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES.shouldCache(v)
                        && Spos.isValid(v.getSpos()) && !Spos.isVpos(v.getSpos())
                        && unswizzleValue(in, x, i, v)) {
                    n++;
                }
            }
        }
        if (n > 0) {
            synchronized (this) {
                unswizzled += n;
                released += n;
            }
            synchronized (Eviction.class) {
                allUnswizzled += n;
                allReleased += n;
            }
        }
    }

    // ======== Tests ========
    //
    // The cases of bergdb 011-05, section 9 (bergdb item 001, WPs J2 and J3), each run
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

        /** Closes both databases. */
        void close() {
            ref.close();
            sub.close();
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
     * lowOf(budget) is floor(3 budget / 4), as BigInteger computes it, for every budget from
     * 1 to Long.MAX_VALUE - 1, on the edges and on random values spread over the bit lengths;
     * Long.MAX_VALUE stays (bergdb 005-79).
     */
    @Nano
    public static void testLowOfExact() {
        Assert.assertEquals(Long.MAX_VALUE, lowOf(Long.MAX_VALUE));
        long[] edges = {1, 2, 3, 4, 5, 0xFFFF, 1L << 47, (1L << 53) / 3, (1L << 53) / 3 + 1,
                1L << 53, Long.MAX_VALUE - 2, Long.MAX_VALUE - 1};
        for (long b : edges) {
            checkLowOf(b);
        }
        Random r = new Random(79);
        for (int i = 0; i < 100000; i++) {
            long b = (r.nextLong() >>> 1) >>> r.nextInt(63);
            if (b >= 1 && b < Long.MAX_VALUE) {
                checkLowOf(b);
            }
        }
    }

    private static void checkLowOf(long budget) {
        long expected = java.math.BigInteger.valueOf(budget).multiply(java.math.BigInteger.valueOf(3))
                .shiftRight(2).longValueExact();
        long actual = lowOf(budget);
        if (actual != expected) {
            Assert.assertEquals("lowOf(" + budget + ")", expected, actual);
        }
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
            w.close();
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
            w.close();
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
            w.close();
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
            w.close();
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
            w.close();
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
            w.close();
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
        w.close();
        int shared = 0;
        for (int s : schedules) {
            Twin r = twin(s, quick);
            for (int i = 0; i < 30; i++) {
                r.trans("k" + (i % 10) + "=v" + i);
                r.read(r.times.get(i / 2));
            }
            r.check(true);
            shared += r.sharedValues;
            r.close();
        }
        // Until bergdb item 009, step 3a: a value named by two slots (shared > 0). Values
        // are no longer in the node table, so two leaves that load a value get a copy each;
        // a value is shared only where a split copies a pointer that holds it.
    }

    /**
     * Eviction only in response to the calls (bergdb 005-51, 010-P3): the eviction thread,
     * started by the loads of reads, waits for the next request with no timeout, so that the
     * thread of a database that is not used does not wake; the close ends it, and close()
     * returns after it has ended, also after stop(). Until 005-51 it woke once a second, to
     * see whether the database had stopped.
     */
    @Nano
    public static void testEvictionThreadIdleUntilClose() throws InterruptedException {
        for (int stopFirst = 0; stopFirst < 2; stopFirst++) {
            MemoryStream s = new MemoryStream();
            CoreTestClock clock = new CoreTestClock();
            Db db = Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8()
                    .startupDistance(200).cacheSizeIndicator(4 * 1000)
                    .evictionSchedule(Schedule.BUDGET, 1).audit(0).start();
            long time = 100 * STEP;
            for (int i = 0; i < 300; i++) {
                time += STEP;
                clock.setTime(time);
                db.execute(db.trans().put("k" + i, "value " + i).build());
            }
            Eviction e = db.internal().eviction();
            Thread t = null;
            for (int round = 0; round < 10 && t == null; round++) {
                for (int i = 0; i < 300; i++) DbUtil.get(db, "k" + i);     // loads
                synchronized (e.evictorLock) {
                    t = e.evictor;
                }
            }
            Assert.assertTrue("the loads started the eviction thread", t != null);
            e.awaitBatch();
            long end = System.nanoTime() + 2000L * 1000 * 1000;
            while (!idle(e, t) && System.nanoTime() < end) {
                Thread.sleep(1);
            }
            Assert.assertTrue("idle, the thread waits with no timeout: " + t.getState(), idle(e, t));
            if (stopFirst == 1) db.stop();
            db.close();
            Assert.assertTrue("the thread ended with the close", !t.isAlive());
        }
    }

    /** Whether the eviction thread t waits for a request with no timeout (005-51's test). */
    private static boolean idle(Eviction e, Thread t) {
        synchronized (e.evictorLock) {
            return !e.wanted && !e.running && t.getState() == Thread.State.WAITING;
        }
    }

    /**
     * No request lost (bergdb 005-65): a load skips evictorLock when a request is pending
     * (wake), which is safe only if the eviction thread takes every pending request. Eight
     * reader threads read in bursts under a small budget, so that the thread sleeps and wakes
     * again and again; after each burst, within 2 s, the thread waits with no request pending
     * (it is never asleep with one) and the resident bytes are at most the trigger, or its
     * last batch freed nothing (then, after two rounds of the hand without freeing, it stops
     * until the next request, by design: 005-51, 015-10).
     * Without the thread's check of the flag before it waits, on which the skip relies, the
     * first burst fails.
     */
    @Nano
    public static void testNoLostRequest() throws Exception {
        noLostRequest(15);
    }

    @Nano("f")
    public static void testNoLostRequestF() throws Exception {
        noLostRequest(300);
    }

    private static void noLostRequest(final int bursts) throws Exception {
        final int n = 2000, readers = 8, gets = 100;
        StringBuilder sb = new StringBuilder(":");
        while (sb.length() < 280) sb.append((char) ('a' + sb.length() % 26));
        final String pad = sb.toString();
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db0 = Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8()
                .startupDistance(2000).start();
        long time = 100 * STEP;
        for (int i = 0; i < n; i += 50) {
            time += STEP;
            clock.setTime(time);
            Trans.Builder b = db0.trans();
            for (int k = i; k < i + 50; k++) b.put("k" + k, k + pad);
            db0.execute(b.build());
        }
        db0.sync(SyncLevel.STRONG);
        db0.stop();
        final Db db = Db.builder().testSetup(s.copy()).clock(clock).testId().maxNodeSize8()
                .startupDistance(2000).cacheSizeIndicator(50 * 1000)
                .evictionSchedule(Schedule.BUDGET, 1).audit(0).start();
        final java.util.concurrent.CyclicBarrier go = new java.util.concurrent.CyclicBarrier(readers + 1);
        final java.util.concurrent.CyclicBarrier done = new java.util.concurrent.CyclicBarrier(readers + 1);
        final java.util.concurrent.ConcurrentLinkedQueue<String> wrong =
                new java.util.concurrent.ConcurrentLinkedQueue<String>();
        Thread[] ts = new Thread[readers];
        for (int r = 0; r < readers; r++) {
            final Random rnd = new Random(r);
            ts[r] = new Thread(new Runnable() {
                public void run() {
                    try {
                        for (int b = 0; b < bursts; b++) {
                            go.await(10, java.util.concurrent.TimeUnit.SECONDS);
                            for (int j = 0; j < gets; j++) {
                                int k = rnd.nextInt(n);
                                try {
                                    String v = new String(DbUtil.get(db, "k" + k));
                                    if (!v.equals(k + pad)) wrong.add("k" + k + " = " + v);
                                } catch (RuntimeException x) {
                                    wrong.add("k" + k + ": " + x);
                                }
                            }
                            done.await(10, java.util.concurrent.TimeUnit.SECONDS);
                        }
                    } catch (Exception x) {
                        // A barrier broken or timed out: the bursts stopped, after a failure.
                    }
                }
            });
            ts[r].setDaemon(true);
            ts[r].start();
        }
        Eviction e = db.internal().eviction();
        String failed = null;
        try {
            for (int b = 0; b < bursts && failed == null; b++) {
                go.await(10, java.util.concurrent.TimeUnit.SECONDS);
                done.await(10, java.util.concurrent.TimeUnit.SECONDS);
                failed = settled(e, db, 2000);
                if (failed != null) failed = "after burst " + b + ": " + failed;
            }
        } finally {
            go.reset();     // the readers end, if the bursts stopped early
            done.reset();
            for (Thread t : ts) t.join(12 * 1000);
            db.close();
        }
        Assert.assertTrue("wrong values: " + wrong, wrong.isEmpty());
        Assert.assertTrue(failed, failed == null);
    }

    /**
     * Waits at most 'millis', after loads, until the eviction thread waits for a request with
     * none pending and the resident bytes are at most the trigger, or its last batch freed
     * nothing; null then, else what it found (005-65's tests).
     */
    private static String settled(Eviction e, Db db, long millis) throws InterruptedException {
        long end = System.nanoTime() + millis * 1000 * 1000;
        while (true) {
            Thread t;
            boolean wanted, running;
            synchronized (e.evictorLock) {
                t = e.evictor;
                wanted = e.wanted;
                running = e.running;
            }
            long before, after;
            synchronized (e) {
                before = e.lastBefore;
                after = e.lastAfter;
            }
            long bytes = db.internal().cache().residents().bytes(), trigger = e.trigger;
            Thread.State st = t == null ? null : t.getState();
            if (!wanted && !running && st == Thread.State.WAITING
                    && (bytes <= trigger || (before == after && after == bytes))) {
                return null;
            }
            if (System.nanoTime() > end) {
                return "request pending " + wanted + ", batches running " + running + ", the thread "
                        + st + "; resident bytes " + bytes + ", trigger " + trigger
                        + ", the last batch " + before + " -> " + after;
            }
            Thread.sleep(1);
        }
    }

    /**
     * setBudget as a batch ends (bergdb 005-80): a batch computes the trigger from the
     * watermarks it reads, and a setBudget that lowers the budget before the batch writes the
     * trigger must not have its own trigger put back by the batch's. Since 988fe1a (005-65)
     * the batch computes and writes the trigger under the monitor that setBudget holds, so
     * setBudget waits for it and writes its trigger last. The hook testBeforeTrigger stops
     * the batch between the computation and the write, and a thread calls setBudget there;
     * the batch goes on when that thread waits for the monitor. Before 988fe1a the line was
     * outside the monitor: setBudget ended within the hook, and the batch then wrote the old
     * budget's trigger, B0 instead of B0 / 4.
     */
    @Nano
    public static void testSetBudgetAtBatchEnd() throws InterruptedException {
        final long b0 = 1000 * 1000;
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).testId().cacheSizeIndicator(b0)
                .evictionSchedule(Schedule.BUDGET, 1).audit(0).start();
        long time = 100 * STEP;
        for (int i = 0; i < 300; i++) {
            time += STEP;
            clock.setTime(time);
            db.execute(db.trans().put("k" + i, "value " + i).build());
        }
        final Eviction e = db.internal().eviction();
        final Thread setter = new Thread(new Runnable() {
            public void run() {
                e.setBudget(b0 / 4);
            }
        });
        setter.setDaemon(true);
        final Thread.State[] inHook = new Thread.State[1];
        e.testBeforeTrigger = new Runnable() {
            public void run() {
                if (setter.getState() != Thread.State.NEW) return;     // the test's batch only
                setter.start();
                // Until setBudget waits for the monitor, or has ended; at most 2 s.
                final long end = System.nanoTime() + 2000L * 1000 * 1000;
                Thread.State st = setter.getState();
                while (st != Thread.State.BLOCKED && st != Thread.State.TERMINATED
                        && System.nanoTime() < end) {
                    Thread.yield();
                    st = setter.getState();
                }
                inHook[0] = st;
            }
        };
        try {
            synchronized (db.internal().getWriteLock()) {     // as a batch's caller
                e.sweep(db, false);
            }
            setter.join(2000);
        } finally {
            e.testBeforeTrigger = null;
            db.close();
        }
        Assert.assertTrue("setBudget has ended", !setter.isAlive());
        Assert.assertEquals("the budget", b0 / 4, e.budget());
        Assert.assertEquals("the trigger, setBudget's (setBudget in the hook: " + inHook[0]
                + ")", b0 / 4, e.trigger);
        Assert.assertEquals("setBudget in the hook", Thread.State.BLOCKED, inHook[0]);
    }

    /**
     * An interrupt ends the eviction thread only with no request pending (bergdb 005-65): a
     * load that finds a request pending does not enter evictorLock (wake), so a request left
     * by a thread that ended would leave the loads without eviction. The thread waits idle;
     * under evictorLock the test makes a request without notifyAll, as a wake whose notifyAll
     * an interrupt overtakes, and interrupts the thread: it takes the request and waits
     * again. Idle, an interrupt ends it, and the next loads start a new thread.
     */
    @Nano
    public static void testInterruptWithRequestPending() throws InterruptedException {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8()
                .startupDistance(200).cacheSizeIndicator(4 * 1000)
                .evictionSchedule(Schedule.BUDGET, 1).audit(0).start();
        long time = 100 * STEP;
        for (int i = 0; i < 300; i++) {
            time += STEP;
            clock.setTime(time);
            db.execute(db.trans().put("k" + i, "value " + i).build());
        }
        Eviction e = db.internal().eviction();
        Thread t = loadsStartThread(db, e);
        String state = settled(e, db, 2000);
        Assert.assertTrue("idle first: " + state, state == null);
        synchronized (e.evictorLock) {
            e.wanted = true;
            t.interrupt();
        }
        state = settled(e, db, 2000);
        Assert.assertTrue("the request taken: " + state, state == null && t.isAlive());
        t.interrupt();
        t.join(2000);
        Assert.assertTrue("idle, an interrupt ends the thread", !t.isAlive());
        Thread t2 = loadsStartThread(db, e);
        Assert.assertTrue("the loads start a new thread", t2 != t);
        db.close();
        Assert.assertTrue("the close ends it", !t2.isAlive());
    }

    /** Reads keys k0 to k299 until the eviction thread runs, and returns it (005-65's test). */
    private static Thread loadsStartThread(Db db, Eviction e) {
        for (int round = 0; round < 10; round++) {
            for (int i = 0; i < 300; i++) DbUtil.get(db, "k" + i);     // loads
            synchronized (e.evictorLock) {
                if (e.evictor != null) return e.evictor;
            }
        }
        throw new AssertionError("the loads started no eviction thread");
    }

    /**
     * A database of n keys with short values, started cold with a budget of 100 MB and every
     * key read twice, so that every index node is resident (bergdb 015-10's tests); the
     * eviction thread has not run. Then nothing that the hand's first round over the maps meets
     * can go: every live handle's CLOCK bit is set (the reads set nearly all; the few they
     * leave clear, 2 of about 5,000 here, the test sets, as a follow does),
     * and no pinned key node holds a resident value (the reads load some into the leaves of D,
     * and a batch would take them whatever their bits: the test takes them first, as
     * unswizzleValues does). Checks that a batch cannot take a round of the hand (more
     * detachable objects than BATCH).
     */
    private static Db everyKeyReadTwice(int n) {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db0 = Db.builder().testSetup(s).clock(clock).testId().maxNodeSize8()
                .startupDistance(2000).start();
        long time = 100 * STEP;
        for (int i = 0; i < n; i += 50) {
            time += STEP;
            clock.setTime(time);
            Trans.Builder b = db0.trans();
            for (int k = i; k < i + 50; k++) b.put("k" + k, "value " + k);
            db0.execute(b.build());
        }
        db0.sync(SyncLevel.STRONG);
        db0.stop();
        Db db = Db.builder().testSetup(s.copy()).clock(clock).testId().maxNodeSize8()
                .startupDistance(2000).cacheSizeIndicator(100L * 1000 * 1000)
                .evictionSchedule(Schedule.BUDGET, 1).audit(0).start();
        boolean ok = false;
        try {
            for (int round = 0; round < 2; round++) {
                for (int k = 0; k < n; k++) DbUtil.get(db, "k" + k);
            }
            Db.Internal in = db.internal();
            int detachable = 0;
            synchronized (in.getWriteLock()) {
                for (Handle h : in.cache().handles()) {
                    Node o = h.obj;
                    if (o == null) continue;
                    h.ref = 1;
                    if (detachable(o, in.superRoot(), in.newestWrittenTop())) {
                        detachable++;
                    } else if (o instanceof KeyNode) {
                        unswizzleValues(in, o);
                    }
                }
            }
            Assert.assertTrue("more detachable objects than a batch examines: " + detachable,
                    detachable > BATCH);
            synchronized (in.eviction().evictorLock) {
                Assert.assertTrue("no eviction thread yet", in.eviction().evictor == null);
            }
            ok = true;
            return db;
        } finally {
            if (!ok) db.close();
        }
    }

    /**
     * A lowered budget is reached when every resident object was just read (bergdb 015-10,
     * 005-52): 10,000 keys (about 5,000 index nodes, more than BATCH), every key read twice
     * (everyKeyReadTwice); the budget lowered to 9/10 of the resident bytes, so that they are
     * not under pressure and a batch examines at most BATCH handles; no other call. The first
     * batch is in the hand's first round over the maps, which only clears the CLOCK bits, and
     * it frees nothing; the eviction thread goes on from the hand, and within 2 s the resident
     * bytes are at most the budget and the thread waits for a request with none pending. Until
     * 015-10 a batch that freed nothing ended the thread's batches, here the first, and
     * nothing started them again (a read that finds its objects resident loads nothing), so
     * the resident bytes stayed above the budget; on s1 under load, a batch cut short by its
     * 2 ms in the first round did so in CapacityTester.testBudgetLoweredAndRaisedUnderReads.
     */
    @Nano
    public static void testLoweredBudgetAfterReads() throws InterruptedException {
        Db db = everyKeyReadTwice(10000);
        try {
            Db.Internal in = db.internal();
            Eviction e = in.eviction();
            long full = in.cache().residents().bytes();
            long budget = full / 10 * 9;
            Assert.assertTrue("not under pressure", full <= budget + (budget - lowOf(budget)));
            db.setCacheSizeIndicator(budget);
            long end = System.nanoTime() + 2000L * 1000 * 1000;
            long bytes = full;
            while (System.nanoTime() < end) {
                bytes = in.cache().residents().bytes();
                if (bytes <= budget) break;
                Thread.sleep(1);
            }
            String state = settled(e, db, 2000);
            Assert.assertTrue("at most " + bytes + " bytes, budget " + budget + " of " + full
                    + ", after " + e.sweepCounts()[0] + " batches", bytes <= budget);
            Assert.assertTrue("idle after: " + state, state == null);
        } finally {
            db.close();
        }
    }

    /**
     * Nothing can go, and the eviction thread stops (bergdb 015-10; 005-51, 010-P3): as
     * testLoweredBudgetAfterReads, with every handle that holds an object held as by a loader
     * (LOADING), so that no batch frees anything and no object is pinned for it (the trigger
     * stays the budget). The thread goes over the maps twice without freeing, then waits for
     * the next request with none pending, within 2 s, and stays so: no batch in the next 20
     * ms; the resident bytes are as they were. Without a stop rule it would run batches for
     * as long as the database is active; with the rule of before 015-10 it stopped after the
     * first batch, before the hand had gone over the maps once.
     */
    @Nano
    public static void testNothingToFree() throws InterruptedException {
        Db db = everyKeyReadTwice(10000);
        List<Handle> held = new ArrayList<Handle>();
        try {
            Db.Internal in = db.internal();
            Eviction e = in.eviction();
            for (Handle h : in.cache().handles()) {
                if (h.obj != null && h.casState(Handle.LIVE, Handle.LOADING)) held.add(h);
            }
            long full = in.cache().residents().bytes();
            long budget = full / 10 * 9;
            db.setCacheSizeIndicator(budget);
            String state = settled(e, db, 2000);
            Assert.assertTrue("idle: " + state, state == null);
            long batches = e.batches;
            long[] c = e.sweepCounts();
            Thread.sleep(20);
            Assert.assertEquals("no batch since", batches, e.batches);
            Assert.assertEquals("nothing freed", full, in.cache().residents().bytes());
            // A batch takes less than a round (everyKeyReadTwice), so each round ends in its own.
            Assert.assertTrue("the hand went over the maps twice: " + c[2] + " of " + c[0]
                    + " batches ended a round", c[2] >= 2);
        } finally {
            for (Handle h : held) h.casState(Handle.LOADING, Handle.LIVE);
            db.close();
        }
    }
}
