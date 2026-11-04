package bergdb.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import bergdb.common.Bug;
import bergdb.common.StringMap;
import bergdb.common.StringUtil;
import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.PointerFollower;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.MemoryStream;

/**
 * This class handles stream space reclaim.
 * 
 * <p>2026-10-13 (bergdb 011-04, level 3): reworked after tests with restarts
 * and an exact cut (java/stress/ReclaimStress.java). How it works now:</p>
 * 
 * <ul>
 * <li>An iteration starts at an external transaction when the stream has grown by twice
 * the startup distance since the last iteration started, and a quarter of the retain
 * duration has passed (ITERATION_DIVISOR): pStart is the stream length then, tStart the
 * time. The startup distance is Db's live value: the stream's after start(), and the new
 * one after setStartupDistance() (bergdb 005-61; it was the builder's before). Its cut point pCut is the pStart of the iteration before (the first iteration:
 * its own pStart).</li>
 * <li>Each external transaction allows a step when the bytes rewritten so far are below
 * internalFraction times the stream growth since pStart (fractionOf). A step scans the KVs at time
 * tStart after lastKey, rewrites each live value stored before pCut, and "touches"
 * the same key range at the current time (Trans.touch): every index node on the way
 * gets dirty and is written again, also nodes that hold deleted keys only. The row of the
 * iteration, with the new lastKey, is stored in the same transaction (CURRENT_KEY_NAME);
 * the table is stored when an iteration starts, ends, gets safe or is cut.</li>
 * <li>When the scan reaches the end, the iteration is done; tEnd and pEnd are the time and
 * position of the last step. Every node and value reachable at times from tEnd on is then
 * stored at pCut or later (index nodes at pStart or later), or is dirty and will be
 * written there.</li>
 * <li>The cut waits until the startup pos has passed pEnd (every touched node written
 * once), and then passed pSafe, the stream length at that moment (nodes written before
 * their children and kept dirty by the still-dirty test written once more, now naming the
 * children's new positions). Then, when tEnd is older than the retention duration, the
 * stream is cut at pCut, the row is marked cut and the first available lookup time is
 * tEnd.</li>
 * <li>All state that decides what reclaim writes is in the table or follows from stream
 * positions, so a restart changes nothing (INV-RESTART).</li>
 * <li>The retain duration may change at any time, also by a restart, since it is not stored.
 * Every cut keeps the guarantee of the duration in force when it is decided (the first
 * available lookup time is then before the decision time minus the duration); the first
 * available lookup time never moves back, and a larger duration does not bring back what was
 * cut (ReclaimRetentionTester, java/stress/ReclaimStress.java; bergdb 011-04, W2).</li>
 * <li>A read admitted before a cut may reach bytes the cut removes. It expires with a
 * LookupTimeNotAvailableException; the stream and the database are not affected (see
 * cutIfDurable(); ReclaimReaderTester, java/stress/ReclaimReaders.java; W1).</li>
 * </ul>
 * 
 * @author Frans Lundberg
 */
public class Reclaim implements Db.TransactionListener {
    //
    // 1301 Frans: Considered running aos.pretruncate() delayed (in later call to transactionCompleted).
    // This got complicated and difficult to test. Some code left in comments. Fix later.
    //
    // 1301 Frans: The call to transactionCompleted() moved to within writeLock block. That
    // should take care of synchronization for the space reclaim.
    //
    // 1301 Frans: See end of file for comments on retainTime.
    //
    
    private final Db db;
        // Note, we could reduce access by ClassForMe pattern to reduce 
        // knowledge of DB.
    private final AppendOnlyStream aos;
    private final IterationTable table;
    private final long[] tableKey;
    private static final String TABLE_KEY_NAME = DbConstants.INTERNAL_PREFIX + "dreclaim/-table.txt";
    
    /**
     * The prefix of reclaim's keys, the table's and the row's: a record with a KV under it
     * is one of reclaim's transactions, a step or the table (bergdb 005-42).
     */
    public static final long[] KEY_PREFIX_SKEY = 
            Keys.toSegments(DbConstants.INTERNAL_PREFIX + "dreclaim/");
    
    /**
     * The row of the iteration in progress, as stored by its last step (2026-10-13,
     * bergdb 011-04, "Level 3 cost"). Steps stored the whole table, which grows by a
     * row per iteration until a cut; with a long retention about 30 rows, stored at every
     * step. Newer than the table's row with the same pStart while that row is not done.
     */
    private final long[] currentKey;
    private static final String CURRENT_KEY_NAME = 
            DbConstants.INTERNAL_PREFIX + "dreclaim/-current.txt";
    
    /**
     * An iteration starts when the retain duration over this divisor has passed since the
     * last one started (2026-10-13, bergdb 011-04, "Level 3 cost"). Before,
     * iterations ran back to back whatever the retention; with a long retention, many
     * per retention duration, each rewriting most KVs. A cut point every quarter of the
     * retention keeps the stream within about 1.25 times what the retention needs.
     * 
     * <p>In integers since bergdb 005-79: retainDuration / 4 (retainDuration is at least
     * one second and not Long.MAX_VALUE there). It was (long) (0.25 * retainDuration), the
     * same for every duration below 2^53 time units, 28.5 years: there the conversion to
     * double and the product by 0.25 are exact.</p>
     */
    static final long ITERATION_DIVISOR = 4;
    
    /** A step is made when it may rewrite more than this many bytes. */
    private static final long MIN_STEP_SIZE = 10 * 1000L;
    
    /**
     * A step scans at most this many bytes of KVs (2026-10-13, bergdb 011-04,
     * "Level 3 cost"). The allowance is a budget for the whole iteration, and the stream
     * grows in bursts (the writes of nodes made dirty a startup distance earlier), so it
     * reached a megabyte at times; one step then made 800 index nodes dirty, and since
     * the writer takes the dirty nodes of a transaction together (TransSeq.take), a user
     * commit later wrote up to 1100 index nodes.
     */
    private static final long MAX_STEP_SIZE = 16 * 1000L;
    
    /** Bytes of a value node besides its key and value (StoredValueNode). */
    private static final int VALUE_NODE_BYTES = 28;
    
    // internalFraction: the bytes rewritten by an iteration, compared to the growth of the
    // stream while it runs. A small internalFraction will reduce the stream writes but 
    // increase the total stream size.
    // In units of 2^-16, an int, since bergdb 005-79 (a double before): FRACTION_ONE is 1.
    
    /** The unit of the internal fraction: FRACTION_ONE units are 1 (bergdb 005-79). */
    static final int FRACTION_ONE = 1 << 16;
    
    /** The default internal fraction, 0.25: 16,384 units of 2^-16, exactly. */
    static final int DEFAULT_INTERNAL_FRACTION = 16384;
    
    /**
     * The smallest and the largest internal fraction, in units of 2^-16: 0.001 and 0.90
     * (Db.setReclaimInternalFraction's range) rounded to the nearest unit, 65.536 to 66 and
     * 58,982.4 to 58,982.
     */
    static final int MIN_INTERNAL_FRACTION = 66, MAX_INTERNAL_FRACTION = 58982;
    
    private volatile int internalFraction;
    
    private volatile long retainDuration;
    
    private final Object readSynch;         // From DB.
    private final Object writeLock;         // From DB.
    
    // Volatile since bergdb item 009, step 1c: reads read them without synchronizing on
    // readSync. Written by the writer, as before.
    private volatile long firstAvailableLookupTime;
    private volatile long firstAvailablePos;
    
    private volatile long iterationCount;   // Iterations completed by this object (statistics).
    
    private long pendingCut = -1;           // A cut decided but not yet made, or -1.
    private long pendingCutDurableAt;       // The cut is made when this is durable.
    
    private Stats stats;                    // null unless enableStats() was called.
    
    /** The default reserve for a step's pinned bytes, 4 MiB; see setStepReserve(). */
    public static final long DEFAULT_STEP_RESERVE = 4L << 20;
    
    private volatile long stepReserve = DEFAULT_STEP_RESERVE;
    
    
    public Reclaim(Db db, AppendOnlyStream aos) {
        table = new IterationTable();
        tableKey = Keys.toSegments(TABLE_KEY_NAME);
        currentKey = Keys.toSegments(CURRENT_KEY_NAME);
        if (db == null) {
            throw new IllegalArgumentException("db == null not allowed");
        }
        
        if (aos == null) {
            throw new IllegalArgumentException("aos == null not allowed");
        }
        this.db = db;
        this.aos = aos;
        
        this.retainDuration = Long.MAX_VALUE;
        this.internalFraction = DEFAULT_INTERNAL_FRACTION;
        this.iterationCount = 0;
        
        this.readSynch = db.internal().getReadSynch();
        this.writeLock = db.internal().getWriteLock();
        
        synchronized (readSynch) {}
            // 1301: Currently not needed; same synchronized block is executed by caller.
    }
    
    /**
     * Called to set the currently wanted retain duration.
     * The caller has no synch requirements ("thread-safe" method).
     */
    public void setRetainDuration(long retainDuration) {
        final long SMALLEST = 1 * Clock.UNITS_PER_SEC;
        
        if (retainDuration < SMALLEST) {
            throw new IllegalArgumentException("retainDuration = " + retainDuration + " is too small.");
        }
        
        this.retainDuration = retainDuration;
    }
    
    /**
     * This is the wanted retain time. The duration of time for which the database user wants
     * to keep all (historic) states available for lookup operations.
     * Since this value can be changed while the database is running (by the database user). 
     * The currently available lookup period may be shorter than retain time if retain time
     * has been increased.
     * The caller has no synch requirements ("thread-safe" method).
     */
    public long getRetainDuration() {
        return retainDuration;
    }
    
    /**
     * Returns the first (smallest value) time that can currently be used as a lookup time
     * for get operations on the database. Note, this time is increased asynchronously.
     * A volatile read (bergdb item 009, step 1c; before, the caller synchronized on readSynch
     * to see the last value).
     */
    public final long getFirstAvailableLookupTime() {
        return this.firstAvailableLookupTime;
    }
    
    public final long getFirstAvailablePos() {
        // Synch note: a volatile read (bergdb item 009, step 1c; before, published by
        // DB.readSynch's unlock, and the caller locked DB.readSynch to see the last value).
        return this.firstAvailablePos;
    }
    
    /**
     * Sets the internal fraction, in units of 2^-16 (FRACTION_ONE), used from the next step.
     * Must be between MIN_INTERNAL_FRACTION and MAX_INTERNAL_FRACTION inclusive, 66 and
     * 58,982 (0.001 and 0.90); otherwise IllegalArgumentException, and the setting stays as
     * it was. Db.setReclaimInternalFraction converts the API's double to this unit.
     */
    public void setInternalFractionUnits(int internalFraction) {
        if (internalFraction < MIN_INTERNAL_FRACTION || internalFraction > MAX_INTERNAL_FRACTION) {
            throw new IllegalArgumentException("Illegal internalFraction value, " + internalFraction);
        }
        
        this.internalFraction = internalFraction;
    }
    
    /**
     * Sets the reserve for the pinned bytes of a reclaim step (bergdb item 001, WP J6): the
     * index nodes that its touch and its rewrites make dirty, which stay pinned until they
     * are written. A step's scan stops at the KV where the index nodes it has followed
     * (NodeCollection.MaintenanceFollower, by id) would need more than the reserve, counted
     * stepNodeBytes() each; so a step that would exceed it is split into smaller ones, and
     * it exceeds the reserve by at most the nodes of one path. With the default, 4 MiB,
     * steps are not split in practice (a step scans about 16 kB of KVs). Thread-safe; used
     * from the next step.
     */
    public void setStepReserve(long bytes) {
        if (bytes < 1) {
            throw new IllegalArgumentException("Illegal step reserve, " + bytes);
        }
        this.stepReserve = bytes;
    }
    
    /** The reserve for a step's pinned bytes; see setStepReserve(). */
    public long getStepReserve() {
        return stepReserve;
    }
    
    /**
     * The bytes counted for an index node in a step's reserve: a key node of the maximum
     * node size with arrays twice that long (KeyNode.getMemSize). From the node size only,
     * so that the steps, and so the records, do not depend on what is resident.
     */
    long stepNodeBytes() {
        return 80 + 48L * db.internal().maxNodeSize();
    }
    
    /**
     * Gets the internal fraction to be used for the next step, in units of 2^-16
     * (FRACTION_ONE).
     */
    public int getInternalFractionUnits() {
        return this.internalFraction;
    }
    
    /**
     * floor(g * f / 2^16): the part f, in units of 2^-16, of g bytes (bergdb 005-79). Exact
     * for every long g and every f from 0 to 2^16 - 1, without overflow: with g = a 2^16 + b,
     * a = g >> 16 and 0 <= b = g & 0xFFFF < 2^16, it is a f + floor(b f / 2^16), and |a f| is
     * below 2^47 2^16 = 2^63, b f below 2^32. For the default fraction, 16,384, it is
     * floor(g / 4), which (long) (0.25 * g) gave for 0 <= g < 2^53.
     */
    static long fractionOf(long g, int f) {
        return (g >> 16) * f + (((g & 0xFFFF) * f) >>> 16);
    }
    
    public long getIterationCount() {
        return this.iterationCount;
    }
    
    /** The last completed iteration in the table, or null. For tests. */
    IterationInfo lastDoneRow() {
        IterationInfo result = null;
        for (IterationInfo row : table.rows) {
            if (row.done) {
                result = row;
            }
        }
        return result;
    }
    
    /**
     * The newest row of the table marked cut, or null. For tests (bergdb item 001, WP R2:
     * java/stress/TraceExport.java reads the cuts from it).
     */
    IterationInfo lastCutRow() {
        IterationInfo result = null;
        for (IterationInfo row : table.rows) {
            if (row.cut) {
                result = row;
            }
        }
        return result;
    }
    
    /**
     * Called by Db after each transaction completed, while it holds the write lock.
     * Internal transactions are ignored.
     * 
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws InternalDataException  If DB data "table.txt" is badly formatted.
     */
    public void transactionCompleted(Trans t) {
        if (t.isInternal()) {
            return;
        }
        
        final long streamSize = t.nextPos;
            // This is correct since meta blocks are written eagerly by RecoverableStream.
        IterationInfo current = currentIteration();
        
        if (current == null && retainDuration != Long.MAX_VALUE
                && streamSize > lastPStart() + 2L * db.getStartupDistance()
                && t.tt - lastTStart() >= retainDuration / ITERATION_DIVISOR) {
            current = new IterationInfo();
            current.pStart = streamSize;
            current.tStart = t.tt;
            current.pCut = table.rows.isEmpty() ? streamSize : lastPStart();
            table.rows.add(current);
            storeTable();
        }
        
        if (current != null) {
            long allowed = fractionOf(streamSize - current.pStart, internalFraction) 
                    - current.rewritten;
            if (allowed > MIN_STEP_SIZE) {
                step(current, Math.min(allowed, MAX_STEP_SIZE));
            }
        }
        
        markSafePositions(streamSize);
        pretruncateIfPossible(t.tt);
        cutIfDurable();
    }
    
    /**
     * Makes the pending cut when the stream is durable up to pendingCutDurableAt: past the
     * table that marks the cut and the meta block that recovery starts from. Otherwise a
     * crash could lose them after the front of the stream is gone (2026-10-13).
     *
     * <p>The wait does not protect readers. A read admitted before the first available
     * lookup time moved can still be running, with a lookup time before the new first
     * available lookup time, and reach bytes this cut removes. Such a read expires: the
     * stream throws ReadBelowFirstPosException, the stream stays usable, and Db turns the
     * exception into a LookupTimeNotAvailableException (bergdb 011-04, W1,
     * decision D1 = A; ReclaimReaderTester, java/stress/ReclaimReaders.java). Protected reads
     * (registration of readers, a wait for them before the cut) are decision D1 = B,
     * not done.</p>
     */
    private void cutIfDurable() {
        if (pendingCut != -1 && db.getDurableLength() >= pendingCutDurableAt) {
            pretruncate(pendingCut);
            pendingCut = -1;
        }
    }
    
    /** The iteration in progress, the last row of the table if it is not done, or null. */
    IterationInfo currentIteration() {
        int size = table.rows.size();
        if (size == 0) {
            return null;
        }
        IterationInfo last = table.rows.get(size - 1);
        return last.done ? null : last;
    }
    
    /** pStart of the last iteration started, or 0. */
    private long lastPStart() {
        int size = table.rows.size();
        return size == 0 ? 0 : table.rows.get(size - 1).pStart;
    }
    
    /** tStart of the last iteration started, or Long.MIN_VALUE / 2. */
    private long lastTStart() {
        int size = table.rows.size();
        return size == 0 ? Long.MIN_VALUE / 2 : table.rows.get(size - 1).tStart;
    }
    
    /**
     * One step of iteration 'it': scans KVs at time tStart after lastKey, about writeSize
     * bytes of them, rewrites each live value stored before pCut, touches the key range,
     * and stores the table row as it is after the step; all in one internal transaction.
     * After the last step (the scan reached the end), the iteration is done, and tEnd and
     * pEnd are stored.
     */
    private void step(final IterationInfo it, final long writeSize) {
        final long[][] lastKeyOfStep = new long[][] {it.lastKey};
        final boolean[] eod = new boolean[] {false};
        
        // 2026-10-17 (bergdb item 001, WP R8, change 5: M28): the scan and the reads of each
        // KV are maintenance reads. They swizzled and entered in the node table all they
        // read, the values too, which then stayed in memory; with eviction they would push
        // out the application's nodes. The step's follower reads a version once.
        final NodeCollection.MaintenanceFollower maintenance =
                db.internal().nodeCollection().maintenance();
        
        // 2026-10-18 (bergdb item 001, WP J6): the step's reserve, in index nodes followed.
        final long maxNodes = Math.max(1, stepReserve / stepNodeBytes());
        final boolean[] split = new boolean[] {false};
        
        GetMany g = db.newGetMany();
        g.gd.pointerFollower = maintenance;
        g.startKey = it.lastKey;
        assert g.startKey == null || g.startKey.length > 0;
        g.inclusive = false;
        g.lookupTime = it.tStart;
        g.stopCondition = new GetMany.StopCondition() {
            private long size = 0;
                // An approximation of the stream space the KVs of the step.
            
            public int handleKvt(Kvt kvt) {
                size += kvt.key.length * 8 + kvt.value.length + 100;
                lastKeyOfStep[0] = kvt.key;
                if (maintenance.indexNodes() > maxNodes) {
                    split[0] = true;
                    return ADD_AND_STOP;
                }
                return size > writeSize ? ADD_AND_STOP : ADD;
            }
            
            public void eod() {
                eod[0] = true;
            }
        };
        db.getMany(g);
        final int scanNodes = maintenance.indexNodes();
        
        Trans.Builder b = db.trans();
        long stepLookupTime = -1;
        long rewritten = 0;
        long values = 0, valueBytes = 0;    // For stats.
        
        for (Kvt kvt : g.result) {
            GetData gd = db.newGetData();
            gd.pointerFollower = maintenance;
            byte[] value;
            
            if (stepLookupTime == -1) {         // BUG Fixed 130131, was "1" instead of "-1".
                value = db.getOne(Long.MAX_VALUE, kvt.key, gd);
                stepLookupTime = gd.actualLookupTime;
            } else {
                value = db.getOne(stepLookupTime, kvt.key, gd);
            }
            
            // If the KV still exists and its value is stored before pStart, it is 
            // rewritten to the stream.
            // 2026-10-13 (Reclaim.Tester.testIterationRewritesAllOldValues):
            // was "gd.kvTime <= tStart". After a time split of the key node, kvTime is
            // the time of the split, not of the write, so old values were skipped and
            // then cut away. The position of the value decides what the cut removes.
            
            // A value not yet written (tpos Spos.NULL, bergdb 005-34) is after the cut, as
            // its vpos was.
            if (value != null && gd.tpos != Spos.NULL && gd.tpos < it.pCut) {
                b.keyRead(kvt.key);
                b.put(kvt.key, value);      // Note, no mem copy of key and value.
                rewritten += kvt.key.length * 8 + value.length + VALUE_NODE_BYTES;
                values++;
                valueBytes += kvt.key.length * 8 + value.length;
            }
        }
        
        final IterationInfo next = it.copy();
        next.lastKey = lastKeyOfStep[0];
        next.kvCount += g.result.size();
        next.rewritten += rewritten;
        final Trans[] stepTrans = new Trans[1];
        final byte[][] tableBytes = new byte[1][];
        final long[] dirtiedStored = new long[1];
        
        // 2026-10-13 (bergdb 011-04, "Level 3 cost"): the allowance counted the
        // values only, about 100 bytes each for the index; the index nodes the step makes
        // dirty, by its puts and its touch, were not counted, so reclaim wrote more than
        // internalFraction. Their size is known during the step only (Trans.dirtiedBytes),
        // so the row is stored by a value transformation.
        
        b.put(currentKey, null, new byte[0], new ValueTransformation() {
            public byte[] transform(long transTime, byte[] inputValue, byte[] previous) {
                dirtiedStored[0] = stepTrans[0].dirtiedBytes;
                next.rewritten += dirtiedStored[0];
                tableBytes[0] = StringUtil.toBytes(next.serialize());
                return tableBytes[0];
            }
        });
            // Not done yet: done is stored with tEnd and pEnd, below.
        
        Trans t = b.build();
        stepTrans[0] = t;
        if (stepLookupTime != -1) {
            t.readTime = stepLookupTime;
        }
        t.isInternal = true;
        
        // 2026-10-13 (Q7 in bergdb 011-01, 
        // Reclaim.Tester.testDeletedKeysAfterCut): only live values were rewritten. Nodes
        // that hold deleted keys only, and the segment subtrees of deleted long keys, kept 
        // their versions before pStart, and lookups still pass through them.
        t.touch = true;
        t.touchFrom = it.lastKey;
        t.touchTo = eod[0] ? null : lastKeyOfStep[0];
        
        Stats.Iteration st = stats == null ? null : statsOf(it);
        if (st != null && stats.countTouch) {
            t.touchCount = st.touch;
            t.touchOldBefore = it.pCut;
        }
        
        try {
            db.execute(t);
        } catch (RerunException e) {
            return;     // The same step is tried at a later transaction.
        }
        
        if (st != null) {
            st.steps++;
            st.kvs += g.result.size();
            st.values += values;
            st.valueBytes += valueBytes;
            st.recordBytes += t.nextPos - t.tpos;
            st.tableBytes += tableBytes[0].length;
            st.dirtiedNodes += t.dirtiedNodes;
            st.dirtiedStored += dirtiedStored[0];
            st.dirtiedBytes += t.dirtiedBytes;
            st.maxStepDirtied = Math.max(st.maxStepDirtied, t.dirtiedNodes);
            st.loads += maintenance.loads();
            st.loadBytes += maintenance.loadBytes();
            st.maxStepNodes = Math.max(st.maxStepNodes, scanNodes);
            if (split[0]) st.splitSteps++;
            if (eod[0]) {
                st.tEnd = t.tt;
                st.pEnd = t.tpos;
            }
        }
        
        it.set(next);
        
        if (eod[0]) {
            // 2026-10-13: eod() set done at once, so when the rewrite got a
            // RerunException, the iteration ended without rewriting the last step. And 
            // tEnd was the time of the external transaction, before the last rewrite.
            // The row is stored as done together with tEnd and pEnd; before, the step
            // stored done, and a crash before the next transaction left a done row with
            // tEnd 0 (Reclaim.Tester.testCrashBeforeIterationEnd). After such a crash, 
            // the iteration resumes and its next step finds the end at once.
            it.done = true;
            it.tEnd = t.tt;
            it.pEnd = t.tpos;
            iterationCount++;
            storeTable();
        }
    }
    
    /**
     * Sets pSafe of done iterations whose last step the startup pos has passed: the stream
     * length now. See the class comment.
     */
    private void markSafePositions(long streamSize) {
        final long startupPos = db.internal().getStartupPosForEvict();
        boolean changed = false;
        
        for (IterationInfo row : table.rows) {
            if (row.done && row.pSafe == -1 && startupPos >= row.pEnd) {
                row.pSafe = streamSize;
                changed = true;
            }
        }
        
        if (changed) {
            storeTable();
        }
    }

    /**
     * Initializes the iteration table, 'table' from what is stored in the database.
     * Db must be in state ACTIVE when this method is called.
     * 
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws InternalDataException  If DB data "table.txt" is badly formatted.
     */
    public void initFromDb() {
        GetData g = db.newGetData();
        byte[] value = db.getOne(Long.MAX_VALUE, tableKey, g);
        
        if (value != null) {
            String s = StringUtil.toString(value);
            table.parse(s);  // throws InternalDataException
            
            // The progress of the iteration in progress, stored by its last step.
            byte[] current = db.getOne(Long.MAX_VALUE, currentKey, g);
            if (current != null) {
                IterationInfo c = new IterationInfo();
                c.deserialize(StringUtil.toString(current));
                for (IterationInfo row : table.rows) {
                    if (row.pStart == c.pStart && !row.done && !c.done) {
                        row.set(c);
                    }
                }
            }
        }
        
        // 2026-10-13 (Reclaim.Tester.testFirstAvailableTimeAfterRestart): the first
        // available lookup time came from the last completed iteration, also when the
        // stream had not been cut there yet; lookups in the retention window then failed.
        // Now the table marks the iteration where the stream was cut.
        
        IterationInfo cutRow = null;
        for (IterationInfo row : table.rows) {
            if (row.cut && (cutRow == null || row.pStart > cutRow.pStart)) {
                cutRow = row;
            }
        }
        
        long firstPos = 0;
        long firstTime = 0;
        if (cutRow != null) {
            firstPos = cutRow.pCut;
            firstTime = cutRow.tEnd;
            if (aos.getFirstPos() < firstPos) {
                pretruncate(firstPos);      // A crash came between the table write and the cut.
            }
        }
        
        synchronized (readSynch) {
            this.firstAvailableLookupTime = firstTime;
            this.firstAvailablePos = firstPos;
        }
    }
    
    /**
     * Cuts the stream at the pStart of the latest iteration that is done, safe (see the
     * class comment), ended before the retention window, and starts at or before the
     * transaction named by the last valid meta block. The table marks that iteration
     * (cut = true) and is written before the cut, so that a restart knows where the
     * stream was cut. The cut itself is made by cutIfDurable().
     * 
     * @throws StreamIoException
     */
    private void pretruncateIfPossible(long timeNow) {
        assert Thread.holdsLock(this.writeLock);
        
        final long tRetain = db.getRetainDuration();
        final long metaTransPos = db.getLastTransPosOfLastValidMetaBlock();
        final long startupPos = db.internal().getStartupPosForEvict();
        IterationInfo cutRow = null;
        
        for (IterationInfo row : table.rows) {
            // 2026-10-13: the cut must not pass the startup pos, which startup
            // reads from, and must wait until the nodes are rewritten (pSafe). Neither
            // was checked.
            if (row.done && timeNow - tRetain > row.tEnd 
                    && row.pSafe != -1 && startupPos >= row.pSafe
                    // 2026-10-13 (testCutKeepsMetaBlockTransaction): recovery
                    // starts at the transaction the last valid meta block names; the
                    // cut checked only the position of the meta block itself.
                    && metaTransPos >= row.pCut
                    // The first iteration after the first cut has its pCut there.
                    && row.pCut > firstAvailablePos
                    && (cutRow == null || row.pStart > cutRow.pStart)) {
                cutRow = row;
            }
        }
        
        if (cutRow == null || cutRow.cut) {
            return;     // Nothing to cut, or already cut there.
        }
        
        // Removes rows no longer needed, marks the cut and stores the table.
        
        for (int i = 0; i < table.rows.size(); i++) {
            if (table.rows.get(i).pStart < cutRow.pStart) {
                table.rows.remove(i);
                i--;      // we need to run same index again since we removed one
            }
        }
        cutRow.cut = true;
        storeTable();
        
        // 2026-10-13 (Q6 in bergdb 011-01, 
        // Reclaim.Tester.testLookupsFromFirstAvailableTime): the first available lookup 
        // time was cutRow.tStart. A value not changed since tStart is rewritten later in
        // the iteration; until then, lookups find the old version, below the cut. The 
        // states from tEnd on are complete after the cut.
        
        synchronized (readSynch) {
            this.firstAvailableLookupTime = cutRow.tEnd;
            this.firstAvailablePos = cutRow.pCut;
        }
        
        pendingCut = cutRow.pCut;
        pendingCutDurableAt = db.getStreamLength();
        
        if (stats != null) {
            Stats.Cut c = new Stats.Cut();
            c.pos = cutRow.pCut;
            c.tEnd = cutRow.tEnd;
            c.decidedAt = pendingCutDurableAt;
            c.decidedTime = timeNow;
            c.retain = tRetain;
            stats.cuts.add(c);
        }
    }
    
    private void pretruncate(long pos) {
        try {
            aos.pretruncate(pos);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
    }
    
    /** Stores the iteration table in an internal transaction. */
    private void storeTable() {
        byte[] tableBytes = StringUtil.toBytes(table.serialize());
        if (stats != null) {
            stats.tableBytes += tableBytes.length;
        }
        Trans t = db.trans().put(tableKey, tableBytes).build();
        t.isInternal = true;
        try {
            db.execute(t);
        } catch (RerunException e) {
            throw new Bug("RerunException for write-only trans unexpected, " + e.getMessage());
        }
    }

    /**
     * Counts what a record in the stream consists of, if statistics are on. Called by Db
     * after it has written the record of 't'.
     */
    void recordWritten(Trans t, TransNodes n) {
        final Stats st = this.stats;
        if (st == null) {
            return;
        }
        Stats.Record rec = !t.isInternal ? st.user : (t.touch ? st.step : st.table);
        rec.records++;
        rec.bytes += t.nextPos - t.tpos;
        for (int i = 0; i < n.valueCount; i++) {
            rec.valueBytes += StoredValueNode.getByteSize(n.valueNodes[i], n.keys[i]);
        }
        for (int i = 0; i < n.keyCount; i++) {
            rec.indexBytes += StoredKeyNode.getByteSize(n.keyNodes[i]);
        }
        for (int i = 0; i < n.topCount; i++) {
            rec.indexBytes += StoredTopNode.getByteSize(n.topNodes[i]);
        }
        rec.indexNodes += n.keyCount + n.topCount;
    }

    /**
     * Turns on statistics (Stats) and returns them. For measurements; call while holding
     * the write lock, or from the writer thread.
     */
    Stats enableStats() {
        if (stats == null) {
            stats = new Stats();
        }
        return stats;
    }

    /** The statistics record of iteration 'it', created at its first step. */
    private Stats.Iteration statsOf(IterationInfo it) {
        List<Stats.Iteration> list = stats.iterations;
        Stats.Iteration last = list.isEmpty() ? null : list.get(list.size() - 1);
        if (last == null || last.pStart != it.pStart) {
            last = new Stats.Iteration();
            last.pStart = it.pStart;
            last.tStart = it.tStart;
            list.add(last);
        }
        return last;
    }

    /**
     * Statistics of reclaim, in memory only, for measurements of its cost (2026-10-13,
     * java/stress/ReclaimCost.java): per iteration, what it read and wrote; per cut,
     * where and when. Not stored, so after a restart they cover the new session only.
     */
    static final class Stats {
        final List<Iteration> iterations = new ArrayList<Iteration>();
        final List<Cut> cuts = new ArrayList<Cut>();
        boolean countTouch = true;      // Counting the touch costs time in the writer.
        long tableBytes;                // Bytes of the table stored outside steps.

        /** Records written, by who wrote them (2026-10-13, W4.1; see Record). */
        final Record user = new Record();       // External (user) transactions.
        final Record step = new Record();       // Internal transactions of reclaim steps.
        final Record table = new Record();      // Internal transactions storing the table.

        /**
         * What the transaction records in the stream consist of. The index nodes in a record
         * are those the writer took when it wrote the record, not necessarily those that
         * this transaction made dirty: index nodes that reclaim made dirty are written in
         * user records too (bergdb 011-04, "Level 3 cost"). "Other" is the rest of the record:
         * headers, the key/value overhead of the value nodes is in valueBytes.
         */
        static final class Record {
            long records;
            long bytes;                 // Stream bytes of the records (nextPos - tpos).
            long valueBytes;            // Value nodes: key, value and node overhead.
            long indexBytes;            // Key nodes and top nodes.
            long indexNodes;

            long otherBytes() {
                return bytes - valueBytes - indexBytes;
            }

            Record copy() {
                Record r = new Record();
                r.records = records;
                r.bytes = bytes;
                r.valueBytes = valueBytes;
                r.indexBytes = indexBytes;
                r.indexNodes = indexNodes;
                return r;
            }

            /** This minus 'o', for the records between two moments. */
            Record minus(Record o) {
                Record r = new Record();
                r.records = records - o.records;
                r.bytes = bytes - o.bytes;
                r.valueBytes = valueBytes - o.valueBytes;
                r.indexBytes = indexBytes - o.indexBytes;
                r.indexNodes = indexNodes - o.indexNodes;
                return r;
            }
        }

        static final class Iteration {
            long pStart, tStart;
            long pEnd = -1, tEnd = -1;  // -1 until done.
            long steps;
            long kvs;                   // KVs scanned at tStart.
            long values;                // Values rewritten (stored before pCut).
            long valueBytes;            // Their key and value bytes.
            long recordBytes;           // Bytes of the step transactions in the stream.
            long tableBytes;            // Bytes of the table stored by the steps.
            long dirtiedNodes;          // Index nodes the steps made dirty (2026-10-13).
            long dirtiedBytes;          // Their size in the stream then.
            long maxStepDirtied;        // Most index nodes one step made dirty.
            long dirtiedStored;         // Bytes of them counted in the allowance.
            long loads;                 // Versions the steps loaded from the stream (WP J6).
            long loadBytes;             // Their memory size.
            long maxStepNodes;          // Most index nodes one step's scan followed.
            long splitSteps;            // Steps that the reserve stopped (setStepReserve).
            final TouchCount touch = new TouchCount();
        }

        static final class Cut {
            long pos;                   // pCut of the iteration cut at.
            long tEnd;                  // The new first available lookup time.
            long decidedAt;             // Stream length when the cut was decided.
            long decidedTime;           // Time then.
            long retain;                // The retain duration in force then (2026-10-13, W2).
        }
    }

    /** What the touches of reclaim did (Trans.touchCount). */
    static final class TouchCount {
        long visited;       // Index nodes visited.
        long dirtied;       // Index nodes made dirty, that is, not dirty before.
        long old;           // Of those, the ones stored before pCut (touchOldBefore).
        long minimal;       // Of those made dirty, the old ones and their ancestors: what
                            // a touch of the old nodes only would make dirty.
    }

    /**
     * Counts what a touch does (TouchCount). Wraps the pointer listener that makes the
     * visited nodes dirty, and looks at each node before it.
     */
    static final class TouchCounter implements Dag.PointerListener {
        private final TouchCount count;
        private final long oldBefore;
        private final Dag.PointerListener dirtying;
        private final IdentityHashMap<Node, Node> parent = new IdentityHashMap<Node, Node>();
        private final Set<Node> madeDirty =
                Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        private final List<Node> oldNodes = new ArrayList<Node>();

        TouchCounter(TouchCount count, long oldBefore, Dag.PointerListener dirtying) {
            this.count = count;
            this.oldBefore = oldBefore;
            this.dirtying = dirtying;
        }

        public void superRootAccessed(TopNode superRoot) {
            visit(superRoot, null);
            dirtying.superRootAccessed(superRoot);
        }

        public void pointerFollowed(Node predecessor, int pointerIndex, Node result,
                int pointerType) {
            if (result != null && result.isIndexNode()) {
                visit(result, predecessor);
            }
            dirtying.pointerFollowed(predecessor, pointerIndex, result, pointerType);
        }

        private void visit(Node node, Node predecessor) {
            if (parent.containsKey(node)) {
                return;
            }
            parent.put(node, predecessor);
            count.visited++;
            if (!node.isDirty()) {
                madeDirty.add(node);
                count.dirtied++;
                long spos = node.getSpos();
                if (Spos.isValid(spos) && !Spos.isVpos(spos) && spos < oldBefore) {
                    oldNodes.add(node);
                    count.old++;
                }
            }
        }

        /** Counts the old nodes and their ancestors; call after the touch. */
        void finish() {
            Set<Node> needed = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
            for (Node n : oldNodes) {
                for (Node a = n; a != null && needed.add(a); a = parent.get(a)) {}
            }
            for (Node n : needed) {
                if (madeDirty.contains(n)) {
                    count.minimal++;
                }
            }
        }
    }

    /**
     * Information about an iteration, completed (done=true) or ongoing (done=false).
     * The information can be serialized to a string and parse back from such a string.
     */
    public static final class IterationInfo {
        long pStart;
        long tStart;
        long tEnd;
        long kvCount;       // total number of KVs in the database for the iteration lookup time
        long[] lastKey;     // Last key that was iterated, or null if none was iterated.
        boolean done;
        boolean cut;        // The stream was cut at pCut (2026-10-13).
        long rewritten;     // Approximate bytes rewritten so far (2026-10-13).
        long pEnd = -1;     // Position of the last step, when done (2026-10-13).
        long pSafe = -1;    // See the class comment; -1 until known (2026-10-13).
        
        /**
         * The cut point (2026-10-13, bergdb 011-04, "Level 3 cost"): values
         * stored before it are rewritten, and the stream is cut there. It was pStart; now
         * the pStart of the iteration before, so that the values the users update between
         * the two need no rewrite. Rows stored before have pCut = pStart.
         */
        long pCut;
        
        IterationInfo copy() {
            IterationInfo c = new IterationInfo();
            c.set(this);
            return c;
        }
        
        void set(IterationInfo o) {
            pStart = o.pStart;
            tStart = o.tStart;
            tEnd = o.tEnd;
            kvCount = o.kvCount;
            lastKey = o.lastKey;
            done = o.done;
            cut = o.cut;
            rewritten = o.rewritten;
            pEnd = o.pEnd;
            pSafe = o.pSafe;
            pCut = o.pCut;
        }
        
        /**
         * Serializes data to a string.
         */
        public String serialize() {
            // Note, lastKey = null is serialized in a special way.
            
            StringMap m = new StringMap();
            m.put("pStart", "" + pStart);
            m.put("pCut", "" + pCut);
            m.put("tStart", "" + tStart);
            m.put("tEnd", "" + tEnd);
            m.put("kvCount", "" + kvCount);
            
            if (lastKey == null) {
                m.put("lastKey", "null");
            } else {
                StringBuilder b = new StringBuilder();
                for (long l : lastKey) {
                    b.append(l + " ");
                }
                m.put("lastKey", b.toString().trim());
            }
            
            m.put("done", done ? "true" : "false");
            m.put("cut", cut ? "true" : "false");
            m.put("rewritten", "" + rewritten);
            m.put("pEnd", "" + pEnd);
            m.put("pSafe", "" + pSafe);
            
            return m.serialize();
        }
        
        /**
         * Sets the fields of this class based on values in the string 's'.
         * 
         * @param s  A serialized StringMap.
         * @throws InternalDataException
         */
        public void deserialize(String s) {
            StringMap m = new StringMap(s);
            pStart = getLong(m, "pStart");
            tStart = getLong(m, "tStart"); 
            tEnd = getLong(m, "tEnd");
            kvCount = getLong(m, "kvCount");
            String last = m.get("lastKey");
            if (last == null) {
                throw new InternalDataException("Missing lastKey in " + TABLE_KEY_NAME 
                        + ". m=" + m.serialize());
            }
            
            if (last.equals("null")) {
                this.lastKey = null;
            } else {
                String[] parts = last.split(" ");
                if (parts.length < 1) {
                    throw new InternalDataException("Bad value of lastKey in " + TABLE_KEY_NAME + ", " 
                            + last + ", m=" + m.serialize());
                }
                
                ArrayList<Long> segments = new ArrayList<Long>();
                for (String part : parts) {
                    part = part.trim();
                    if (part.length() > 0) {
                        long segment;
                        try {
                            segment = Long.parseLong(part);
                        } catch (NumberFormatException e) {
                            throw new InternalDataException("Bad value of lastKey in " + TABLE_KEY_NAME 
                                    + ", " + last);
                        }
                        segments.add(segment);
                    }
                }
                
                lastKey = new long[segments.size()];
                for (int i = 0; i < lastKey.length; i++) {
                    lastKey[i] = segments.get(i);
                }
            }
            
            done = false;
            
            String doneString = m.get("done");
            if (doneString == null) {
                throw new InternalDataException("Missing 'done' in " + TABLE_KEY_NAME);
            }
            
            if (!(  ("true".equals(doneString)) || "false".equals(doneString)  )) {
                throw new InternalDataException("Bad value of 'done' in " + TABLE_KEY_NAME 
                        + ", '" + doneString + "'.");
            }
            
            if (doneString.equals("true")) {
                done = true;
            }
            
            // Missing before 2026-10-13:
            cut = "true".equals(m.get("cut"));
            rewritten = m.hasLong("rewritten") ? m.getLong("rewritten") : 0;
            pEnd = m.hasLong("pEnd") ? m.getLong("pEnd") : pStart;
            pSafe = m.hasLong("pSafe") ? m.getLong("pSafe") : -1;
            pCut = m.hasLong("pCut") ? m.getLong("pCut") : pStart;     // Since 2026-10-13.
        }
        
        private long getLong(StringMap m, String key) {
            if (!m.hasLong(key)) {
                throw new InternalDataException("Missing or non-long key '" + key + "' from " 
                        + TABLE_KEY_NAME + ". Table string map: " + m.serialize());
            }
            return m.getLong(key);
        }
        
        @Nano
        private static void testSerialize1() {
            IterationInfo i1 = new IterationInfo();
            i1.done = true;
            i1.kvCount = 10;
            i1.lastKey = new long[]{123};
            i1.pStart = 1000;
            i1.tEnd = 20*1000;
            i1.tStart = 10*1000;
            
            String s = i1.serialize();            
            IterationInfo i2 = new IterationInfo();
            i2.deserialize(s);
            
            Assert.assertEquals(i1.done, i2.done);
            Assert.assertEquals(i1.kvCount, i2.kvCount);
            Assert.assertArrayEquals(i1.lastKey, i2.lastKey);
            Assert.assertEquals(i1.pStart, i2.pStart);
            Assert.assertEquals(i1.tEnd, i2.tEnd);
            Assert.assertEquals(i1.tStart, i2.tStart);
        }
        
        @Nano
        private static void testSerialize2() {
            IterationInfo i1 = new IterationInfo();
            i1.done = false;
            i1.kvCount = 10;
            i1.lastKey = new long[]{123};
            i1.pStart = 1000;
            i1.tEnd = 20*1000;
            i1.tStart = 10*1000;
            
            String s = i1.serialize();            
            IterationInfo i2 = new IterationInfo();
            i2.deserialize(s);
            
            Assert.assertEquals(i1.done, i2.done);
            Assert.assertEquals(i1.kvCount, i2.kvCount);
            Assert.assertArrayEquals(i1.lastKey, i2.lastKey);
            Assert.assertEquals(i1.pStart, i2.pStart);
            Assert.assertEquals(i1.tEnd, i2.tEnd);
            Assert.assertEquals(i1.tStart, i2.tStart);
        }
        
        @Nano
        private static void testDeserializeWithBadString() {
            IterationInfo i1 = new IterationInfo();
            i1.done = false;
            i1.kvCount = 10;
            i1.lastKey = new long[]{123};
            i1.pStart = 1000;
            i1.tEnd = 20*1000;
            i1.tStart = 10*1000;
            
            String s = i1.serialize();            
            s = s.replace("false", "fALse");
            
            IterationInfo i2 = new IterationInfo();
            
            InternalDataException ex = null;
            try {
                i2.deserialize(s);
            } catch (InternalDataException e) {
                ex = e;
            }
            
            Assert.assertTrue("ex should be non-null", ex != null);
        }
    }
    
    /**
     * Multiple iterations stored as a number of IterationInfo:s.
     */
    final class IterationTable {
        List<IterationInfo> rows;
        
        public IterationTable() {
            rows = new ArrayList<IterationInfo>();
        }
        
        public String serialize() {
            return serializeWith(null, null);
        }
        
        /** Serializes the table with row 'replacement' instead of row 'row'. */
        public String serializeWith(IterationInfo row, IterationInfo replacement) {
            StringBuilder b = new StringBuilder();
            
            for (IterationInfo info : rows) {
                IterationInfo r = info == row ? replacement : info;
                b.append(r.serialize() + "----next----\n");
            }
            
            return b.toString();
        }
        
        /**
         * @throws InternalDataException If format of 's' is bad.
         */
        public void parse(String s) {
            String[] parts = s.split("----next----");
            for (String part : parts) {
                part = part.trim();
                
                if (part.length() > 0) {
                    IterationInfo info = new IterationInfo();
                    info.deserialize(part);
                    rows.add(info);
                }
            }
            
            if (rows.size() == 0) {
                throw new InternalDataException("Error in bergdb data, key: " + TABLE_KEY_NAME);
            }
        }
    }
    
    /**
     * Class for testing.
     */
    public static class Tester {

        private Tester() {}
        
        @Nano
        public static void test1() {
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(10);
            MemoryStream stream = new MemoryStream();
            byte[] value = new byte[100*1000];
            int size = 40;
            
            Db db = Db.builder().testSetup().mainStream(stream).clock(clock)
                    .startupDistance(100*1000).start();
            
            for (int i = 0; i < size; i++) {
                long time = 1000 + i * 10;
                clock.setTime(time);
                Trans t = db.trans().put("" + i, value).build();
                db.execute(t);
            }
            
            GetMany g = db.newGetMany();
            g.lookupTime = Long.MAX_VALUE;
            g.startKey = null;
            db.getMany(g);
            Assert.assertTrue(g.result.size() == size || g.result.size() == size + 1);
            db.close();
        }
        
        @Nano
        public static void testPretruncate() {
            //
            // Same key set again and again.
            //
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(10);
            final long[] ints = new long[] {-1, -1};
            
            MemoryStream stream = new MemoryStream() {
                public void pretruncate(long spos) {
                    super.pretruncate(spos);
                    ints[0] = getFirstArrayIndex();
                    ints[1] = spos;
                }
            };
            
            byte[] value = new byte[100000];
            int size = 40;      // Was 20; the cut now waits until the nodes are rewritten.
            
            Db db = Db.builder().testSetup().mainStream(stream).clock(clock)
                    .startupDistance(100*1000).start();
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            
            for (int i = 0; i < size; i++) {
                long time = (i + 1) * Clock.UNITS_PER_SEC;
                clock.setTime(time);
                Trans t = db.trans().put("k", value).build();
                db.execute(t);
            }
            
            db.sync(SyncLevel.ORDINARY);    // The cut waits until the table is durable,
            clock.setTime(size * Clock.UNITS_PER_SEC + 1);
            db.execute(db.trans().put("k2", value).build());    // and is made at a transaction.
            db.sync(SyncLevel.ORDINARY);    // A cut in bytes not yet flushed waits for the flush.
            Assert.assertTrue("" + ints[0], ints[0] > 0);
            Assert.assertTrue("" + ints[1], ints[1] > value.length);
            db.close();
        }
        
        @Nano
        public static void testIterationInfo() {
            
        }
        
        /**
         * Regression test for a fault found 2026-10-27 (bergdb 005-53, question 3; fixed in
         * 005-61): Reclaim kept the builder's startup distance, copied when Db was made,
         * not the stream's that Db.start() reads, nor a later setStartupDistance(). A
         * database made at 2000 bytes and restarted with the builder's default (50 MB)
         * then nearly stopped reclaiming. Restarted with the default or with 2000, it must
         * reclaim the same, as at its own distance.
         */
        @Nano
        public static void testIterationsFollowTheStreamsStartupDistance() {
            long[] time = {Clock.UNITS_PER_SEC};
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(time[0]);
            MemoryStream stream = new MemoryStream();
            Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(2000).start();
            distancePuts(db, clock, time, 2000);
            db.sync(SyncLevel.ORDINARY);
            db.close();
            
            long t0 = time[0];
            long[] iterations = new long[2];
            long[] length = new long[2];
            for (int run = 0; run < 2; run++) {
                time[0] = t0;
                CoreTestClock c = new CoreTestClock();
                c.setTime(time[0]);
                DbBuilder b = Db.builder().testSetup(stream.copy()).clock(c);
                if (run == 0) {
                    b.startupDistance(2000);
                }
                Db d = b.start();
                Assert.assertEquals(2000, d.getStartupDistance());
                iterations[run] = distancePuts(d, c, time, 2000);
                length[run] = d.getStreamLength() - d.getFirstAvailablePos();
                d.close();
            }
            
            Assert.assertTrue("iterations: " + iterations[0], iterations[0] >= 10);
            Assert.assertEquals(iterations[0], iterations[1]);
            Assert.assertEquals(length[0], length[1]);
        }
        
        /**
         * A larger startup distance set while the database runs (Db.setStartupDistance) also
         * spaces reclaim's iterations (bergdb 005-61): none starts before the stream has
         * grown by twice the new distance.
         */
        @Nano
        public static void testIterationsFollowSetStartupDistance() {
            long[] time = {Clock.UNITS_PER_SEC};
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(time[0]);
            Db db = Db.builder().testSetup().clock(clock).startupDistance(2000).start();
            Assert.assertTrue(distancePuts(db, clock, time, 1000) >= 5);
            
            db.setStartupDistance(bergdb.storage.RecoverableStream.META_BLOCK_DISTANCE * 2);
            long pStart = db.internal().reclaim().lastPStart();
            long length = db.getStreamLength();
            distancePuts(db, clock, time, 2000);
            Assert.assertEquals(pStart, db.internal().reclaim().lastPStart());
            Assert.assertTrue("grew " + (db.getStreamLength() - length), 
                    db.getStreamLength() - length > 50 * 1000);
            db.close();
        }
        
        /**
         * The probe's workload for 005-61 (005-53's ReclaimDistanceProbe): a retention of 1 s,
         * small puts 50 ms apart. Asserts that each iteration that starts does so when the
         * stream has grown by more than twice the database's startup distance since the
         * last one started. Returns the iterations completed.
         */
        private static long distancePuts(Db db, CoreTestClock clock, long[] time, int count) {
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            java.util.Random r = new java.util.Random(1);
            Reclaim reclaim = db.internal().reclaim();
            long before = reclaim.getIterationCount();
            for (int i = 0; i < count; i++) {
                time[0] += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time[0]);
                long pStart = reclaim.lastPStart();
                byte[] v = new byte[1 + r.nextInt(60)];
                db.execute(db.trans().put("/k/" + r.nextInt(50), v).build());
                long next = reclaim.lastPStart();
                if (next != pStart) {
                    Assert.assertTrue("started at " + next + ", last " + pStart + ", distance "
                            + db.getStartupDistance(),
                            next - pStart > 2L * db.getStartupDistance());
                }
            }
            return reclaim.getIterationCount() - before;
        }
        
        /**
         * Regression test for a bug found 2026-10-13 (java/stress/ReclaimStress.java):
         * when an iteration is done, every live value must be stored at or after its
         * pStart, or the cut at pStart removes it. The iteration chose the values to
         * rewrite by their time, gd.kvTime, but after a time split of the key node that
         * time is the split time, so old values were skipped.
         */
        @Nano
        public static void testIterationRewritesAllOldValues() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            Db db = Db.builder().testSetup().clock(clock).maxNodeSize8()
                    .startupDistance(2000).start();
            db.setRetainDuration(1000 * Clock.UNITS_PER_SEC);    // Iterations, but no cut.
            
            java.util.Random r = new java.util.Random(1);
            java.util.TreeMap<String, byte[]> live = new java.util.TreeMap<String, byte[]>();
            long checked = 0;
            
            for (int i = 0; i < 1000 && checked < 2; i++) {
                time += Clock.UNITS_PER_SEC;    // Was 0.1 ms; iterations are now a quarter
                clock.setTime(time);            // of the retain duration apart (2026-10-13).
                String k = "/k/" + r.nextInt(100);
                byte[] v = new byte[1 + r.nextInt(30)];
                r.nextBytes(v);
                db.execute(db.trans().put(k, v).build());
                live.put(k, v);
                
                if (db.getReclaimIterationCount() > checked) {
                    checked = db.getReclaimIterationCount();
                    long pCut = db.internal().reclaim().lastDoneRow().pCut;
                    for (String key : live.keySet()) {
                        GetData gd = db.newGetData();
                        db.getOne(Long.MAX_VALUE, Keys.toSegments(key), gd);
                        Assert.assertTrue(key + " at " + gd.tpos + ", pCut " + pCut, 
                                gd.tpos >= pCut);
                    }
                }
            }
            
            Assert.assertTrue("iterations: " + checked, checked >= 2);
            db.stop();
        }
        
        /**
         * Regression test for a bug found 2026-10-13 (java/stress/ReclaimStress.java):
         * startup after a cut failed when the meta block before the last transaction's
         * position was cut away; the search for a meta block went down to position 0.
         */
        @Nano
        public static void testRestartAfterCut() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = startForCutTest(stream, clock);
            java.util.Map<String, byte[]> live = new java.util.HashMap<String, byte[]>();
            java.util.Random r = new java.util.Random(2);
            
            for (int i = 0; i < 3000 && stream.getCut() == 0; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                String k = "/k/" + r.nextInt(50);
                byte[] v = new byte[1 + r.nextInt(30)];
                r.nextBytes(v);
                db.execute(db.trans().put(k, v).build());
                live.put(k, v);
            }
            
            Assert.assertTrue("no cut", stream.getCut() > 0);
            db.sync(SyncLevel.ORDINARY);
            db.stop();
            clock = new CoreTestClock();
            clock.setTime(time);
            db = startForCutTest(stream.copy(), clock);
            for (String k : live.keySet()) {
                Assert.assertArrayEquals(live.get(k), DbUtil.get(db, Long.MAX_VALUE, k));
            }
            db.stop();
        }
        
        /**
         * Regression test for bergdb 005-39: after a cut, NodeStream.createTransIterator()
         * and print() threw NullPointerException for a start pos before the first meta block
         * after the cut (RecoverableStream.getPosOfTransCompletedBefore()). Now they start
         * at the first transaction after the cut that a meta block names.
         */
        @Nano
        public static void testTransIteratorAfterCut() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = startForCutTest(stream, clock);
            java.util.Random r = new java.util.Random(2);
            Trans t = null;
            
            for (int i = 0; i < 3000 && stream.getCut() == 0; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                byte[] v = new byte[1 + r.nextInt(30)];
                r.nextBytes(v);
                t = db.trans().put("/k/" + r.nextInt(50), v).build();
                db.execute(t);
            }
            
            Assert.assertTrue("no cut", stream.getCut() > 0);
            synchronized (db.internal().getWriteLock()) {
                NodeStream ns = db.internal().nodeStream();
                long first = -1;
                for (long startPos : new long[] {0, stream.getCut(), stream.getCut() + 1}) {
                    NodeStream.TransIterator ti = ns.createTransIterator(startPos);
                    Assert.assertTrue(ti.next());
                    Assert.assertTrue(ti.tpos + ", cut " + stream.getCut(),
                            ti.tpos >= stream.getCut());
                    if (first == -1) {
                        first = ti.tpos;
                    }
                    Assert.assertEquals(first, ti.tpos);
                    boolean seen = false;
                    long end;
                    do {
                        seen |= ti.tpos == t.tpos;
                        end = ti.nextTransPos;
                    } while (ti.next());
                    Assert.assertTrue("the last transaction", seen);
                    Assert.assertEquals(ns.getNextPos(), end);
                }
                
                java.io.ByteArrayOutputStream out = new java.io.ByteArrayOutputStream();
                ns.print(new java.io.PrintStream(out), 0);
                Assert.assertTrue(out.toString().startsWith("==== Trans @" + first + " ===="));
            }
            db.stop();
        }
        
        /**
         * Regression test for a bug found 2026-10-13 (java/stress/ReclaimStress.java):
         * after a restart, the first available lookup time was taken from the last
         * completed iteration, also when the stream had not been cut there yet. Then
         * lookups in the retention window failed.
         */
        @Nano
        public static void testFirstAvailableTimeAfterRestart() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = startForCutTest(stream, clock);
            java.util.Random r = new java.util.Random(3);
            int restarts = 0;
            
            for (int i = 1; i < 3000 && restarts < 5; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                byte[] v = new byte[1 + r.nextInt(30)];
                db.execute(db.trans().put("/k/" + r.nextInt(50), v).build());
                
                // A restart right after an iteration is done: it is not yet cut there.
                if (db.getReclaimIterationCount() > 0 && stream.getCut() > 0) {
                    long first = db.getFirstAvailableLookupTime();
                    db.sync(SyncLevel.ORDINARY);
                    db.stop();
                    stream = stream.copy();
                    clock = new CoreTestClock();
                    clock.setTime(time);
                    db = startForCutTest(stream, clock);
                    restarts++;
                    Assert.assertEquals(first, db.getFirstAvailableLookupTime());
                }
            }
            
            Assert.assertTrue("restarts: " + restarts, restarts >= 5);
            db.stop();
        }
        
        /**
         * Regression test for a bug found 2026-10-13 (java/stress/ReclaimStress.java):
         * after a cut and a restart, writing an index node failed. Its history has dead
         * pointers to versions below the cut, and NodeCollection.resolvePointers() read
         * their headers.
         */
        @Nano
        public static void testWritesAfterCut() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = startForCutTest(stream, clock);
            java.util.Random r = new java.util.Random(4);
            boolean restarted = false;
            
            for (int i = 0; i < 3000; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                byte[] v = new byte[1 + r.nextInt(30)];
                db.execute(db.trans().put("/k/" + r.nextInt(50), v).build());
                
                if (!restarted && stream.getCut() > 0) {
                    db.sync(SyncLevel.ORDINARY);
                    db.stop();
                    stream = stream.copy();
                    clock = new CoreTestClock();
                    clock.setTime(time);
                    db = startForCutTest(stream, clock);
                    restarted = true;
                    i = 2500;       // 500 more transactions
                }
            }
            
            Assert.assertTrue("no cut", restarted);
            db.stop();
        }
        
        /**
         * Regression test for a bug found 2026-10-13 (java/stress/ReclaimStress.java),
         * Q7 in bergdb 011-01: an iteration rewrote live values only. Nodes that hold
         * only deleted keys, and the segment subtrees of deleted long keys, kept their 
         * versions below the cut, and lookups and scans still pass through them.
         */
        @Nano
        public static void testDeletedKeysAfterCut() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = startForCutTest(stream, clock);
            
            for (int i = 0; i < 100; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                db.execute(db.trans().put("/k/" + i, "v").put("/long/" + i, "v").build());
            }
            for (int i = 0; i < 60; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                db.execute(db.trans().delete("/k/" + i).delete("/long/" + i).build());
            }
            
            java.util.Random r = new java.util.Random(5);
            long cut = 0;
            int cuts = 0;
            for (int i = 0; i < 4000 && cuts < 3; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                int k = 60 + r.nextInt(40);
                db.execute(db.trans().put("/k/" + k, "w" + i).build());
                if (stream.getCut() > cut) {
                    cut = stream.getCut();
                    cuts++;
                }
            }
            
            Assert.assertTrue("cuts: " + cuts, cuts >= 3);
            db.sync(SyncLevel.ORDINARY);
            db.stop();
            clock = new CoreTestClock();
            clock.setTime(time);
            db = startForCutTest(stream.copy(), clock);
            DbUtil.checksum(db);
            for (int i = 0; i < 60; i++) {
                Assert.assertTrue(DbUtil.get(db, Long.MAX_VALUE, "/k/" + i) == null);
                Assert.assertTrue(DbUtil.get(db, Long.MAX_VALUE, "/long/" + i) == null);
            }
            db.stop();
        }
        
        /**
         * Regression test for a bug found 2026-10-13 (java/stress/ReclaimStress.java):
         * startup after a cut failed when the last valid meta block named a transaction
         * before the cut; recovery starts at that transaction. The cut checked only that
         * the meta block itself came after the cut position.
         */
        @Nano("f")
        public static void testCutKeepsMetaBlockTransaction() {
            for (int seed = 0; seed < 20; seed++) {
                CoreTestClock clock = new CoreTestClock();
                long time = Clock.UNITS_PER_SEC;
                clock.setTime(time);
                CutStream stream = new CutStream();
                Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(10000).start();
                db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
                java.util.Random r = new java.util.Random(seed);
                long cut = 0;
                
                for (int i = 0; i < 3000; i++) {
                    time += Clock.UNITS_PER_SEC / 20;
                    clock.setTime(time);
                    byte[] v = new byte[1 + r.nextInt(60)];
                    db.execute(db.trans().put("/k/" + r.nextInt(5), v).build());
                    if (stream.getCut() > cut) {
                        cut = stream.getCut();
                        db.sync(SyncLevel.ORDINARY);
                        db.stop();
                        stream = stream.copy();
                        clock = new CoreTestClock();
                        clock.setTime(time);
                        db = Db.builder().testSetup(stream).clock(clock).startupDistance(10000)
                                .start();
                        db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
                    }
                }
                db.stop();
            }
        }
        
        /**
         * Regression test for a bug found 2026-10-13 (java/stress/CrashTest.java with
         * reclaim): the last step of an iteration stored the row as done, and tEnd and pEnd
         * followed in the next transaction. After a crash between the two, the row was 
         * done with tEnd = 0, and the cut there made 0 the first available lookup time.
         * 
         * <p>Durability follows the transactions, not the clock (2026-11-03, bergdb 015-09):
         * the main stream's buffer flushes only when the test syncs, after each transaction
         * (startForCrashTest). With the tests' 10 ms buffer time, a flush could reach the
         * stream between the iteration's last records and a physical cut in the same
         * transaction, under load (a before-commit.sh beside other gates): the cut then
         * recorded a length past the crash position, which no crash can lose, and
         * CutStream.truncate refused the crash ("truncate to 241352, before the length at
         * the last cut, 246952"). Now a cut in the transaction of the iteration's end comes
         * before the transaction's records reach the stream.</p>
         */
        @Nano
        public static void testCrashBeforeIterationEnd() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = startForCrashTest(stream, clock);
            java.util.Random r = new java.util.Random(6);
            java.util.Map<String, java.util.TreeMap<Long, byte[]>> model = 
                    new java.util.HashMap<String, java.util.TreeMap<Long, byte[]>>();
            boolean crashed = false;
            long cutAtCrash = 0;
            
            for (int i = 0; i < 2500; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                String k = "/k/" + r.nextInt(50);
                byte[] v = new byte[1 + r.nextInt(30)];
                Trans t = db.trans().put(k, v).build();
                long count = db.getReclaimIterationCount();
                db.execute(t);
                if (!model.containsKey(k)) {
                    model.put(k, new java.util.TreeMap<Long, byte[]>());
                }
                model.get(k).put(t.tt, v);
                
                if (!crashed && db.getReclaimIterationCount() > count && stream.getCut() > 0) {
                    // After t come the last step and the table with tEnd; a crash cuts 
                    // the stream between the two.
                    NodeStream.TransIterator iter = 
                            db.internal().nodeStream().createTransIteratorFromExactStartupPos(t.nextPos);
                    Assert.assertTrue(iter.next());
                    Assert.assertTrue(iter.next());
                    long crashPos = iter.getStoredTrans().tpos;
                    db.sync(SyncLevel.ORDINARY);
                    db.stop();
                    stream = stream.copy();
                    stream.truncate(crashPos);
                    clock = new CoreTestClock();
                    clock.setTime(time);
                    db = startForCrashTest(stream, clock);
                    crashed = true;
                    cutAtCrash = stream.getCut();
                    
                    // The table after the restart: a done row has its tEnd and pEnd.
                    for (IterationInfo row : db.internal().reclaim().table.rows) {
                        Assert.assertTrue("done row without tEnd: " + row.serialize(), 
                                !row.done || (row.tEnd >= row.tStart && row.pEnd >= row.pStart));
                    }
                }
                
                // A cut always comes with a first available lookup time after it.
                if (db.getFirstAvailablePos() > 0) {
                    Assert.assertTrue("first available lookup time 0, after a cut at " 
                            + db.getFirstAvailablePos(), db.getFirstAvailableLookupTime() > 0);
                }
                db.sync(SyncLevel.ORDINARY);    // the only flush (startForCrashTest)
            }
            
            Assert.assertTrue("no crash", crashed);
            Assert.assertTrue("no cut after the crash", stream.getCut() > cutAtCrash);
            long first = db.getFirstAvailableLookupTime();
            Assert.assertTrue("first available: " + first, first > 0);
            for (long lt = first; lt <= time; lt += Clock.UNITS_PER_SEC / 4) {
                for (String key : model.keySet()) {
                    java.util.Map.Entry<Long, byte[]> e = model.get(key).floorEntry(lt);
                    Assert.assertArrayEquals(e == null ? null : e.getValue(), 
                            DbUtil.get(db, lt, key));
                }
            }
            db.stop();
        }
        
        /**
         * As startForCutTest, with a buffer time of 60 s, so that the main stream's buffer
         * is flushed only by a sync (or when full), not by the clock (bergdb 015-09).
         */
        private static Db startForCrashTest(CutStream stream, CoreTestClock clock) {
            DbBuilder b = Db.builder();
            b.testSetupExceptStream();
            Db db = b.stream("main", stream, 100 * 1000, 60 * 1000).clock(clock)
                    .maxNodeSize8().startupDistance(2000).start();
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            return db;
        }
        
        private static Db startForCutTest(CutStream stream, CoreTestClock clock) {
            Db db = Db.builder().testSetup(stream).clock(clock).maxNodeSize8()
                    .startupDistance(2000).start();
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            return db;
        }

        /**
         * The allowance counts the index nodes a step makes dirty (2026-10-13,
         * bergdb 011-04, "Level 3 cost"): before, 100 bytes per value rewritten, and
         * reclaim wrote more than internalFraction of the stream.
         */
        @Nano
        public static void testAllowanceCountsIndexNodes() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            Db db = Db.builder().testSetup().clock(clock).maxNodeSize8()
                    .startupDistance(2000).start();
            Reclaim reclaim = db.internal().reclaim();
            Stats stats = reclaim.enableStats();
            for (int i = 0; i < 3000; i += 100) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                Trans.Builder b = db.trans();
                for (int j = i; j < i + 100; j++) {
                    b.put("/k/" + j, new byte[10]);
                }
                db.execute(b.build());
            }
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            java.util.Random r = new java.util.Random(6);
            
            for (int i = 0; i < 5000 && reclaim.getIterationCount() == 0; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                db.execute(db.trans().put("/k/" + r.nextInt(3000), new byte[10]).build());
            }
            
            Assert.assertTrue("no iteration done", reclaim.getIterationCount() > 0);
            IterationInfo row = reclaim.lastDoneRow();
            Stats.Iteration st = stats.iterations.get(0);
            Assert.assertEquals(row.pStart, st.pStart);
            Assert.assertTrue("steps " + st.steps, st.steps >= 2);
            Assert.assertTrue("index bytes " + st.dirtiedStored, st.dirtiedStored > 0);
            Assert.assertEquals(st.valueBytes + VALUE_NODE_BYTES * st.values + st.dirtiedStored,
                    row.rewritten);
            db.stop();
        }
        
        /**
         * The cut point of an iteration is the pStart of the one before (pCut, 2026-10-13,
         * bergdb 011-04, "Level 3 cost"): values stored between the two are not
         * rewritten, and every live value is stored at pCut or later when it is done.
         */
        @Nano
        public static void testCutPointBeforeScan() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            Db db = Db.builder().testSetup().clock(clock).maxNodeSize8()
                    .startupDistance(2000).start();
            db.setRetainDuration(1000 * Clock.UNITS_PER_SEC);    // Iterations, but no cut.
            Reclaim reclaim = db.internal().reclaim();
            java.util.Random r = new java.util.Random(5);
            java.util.TreeMap<String, byte[]> live = new java.util.TreeMap<String, byte[]>();
            long checked = 0;
            int spared = 0;
            
            for (int i = 0; i < 2000 && checked < 4; i++) {
                time += Clock.UNITS_PER_SEC;
                clock.setTime(time);
                String k = "/k/" + r.nextInt(100);
                byte[] v = new byte[1 + r.nextInt(30)];
                r.nextBytes(v);
                db.execute(db.trans().put(k, v).build());
                live.put(k, v);
                
                if (db.getReclaimIterationCount() > checked) {
                    checked = db.getReclaimIterationCount();
                    List<IterationInfo> rows = reclaim.table.rows;
                    IterationInfo done = reclaim.lastDoneRow();
                    int index = rows.indexOf(done);
                    Assert.assertEquals(index == 0 ? done.pStart : rows.get(index - 1).pStart,
                            done.pCut);
                    for (String key : live.keySet()) {
                        GetData gd = db.newGetData();
                        db.getOne(Long.MAX_VALUE, Keys.toSegments(key), gd);
                        Assert.assertTrue(key + " at " + gd.tpos + ", pCut " + done.pCut, 
                                gd.tpos >= done.pCut);
                        if (gd.tpos < done.pStart) {
                            spared++;
                        }
                    }
                }
            }
            
            Assert.assertTrue("iterations: " + checked, checked >= 4);
            Assert.assertTrue("no value was spared", spared > 0);
            db.stop();
        }
        
        /**
         * Iterations start a quarter of the retain duration apart (ITERATION_DIVISOR,
         * 2026-10-13, bergdb 011-04, "Level 3 cost"); before, they ran back
         * to back whatever the retention.
         */
        @Nano
        public static void testIterationsSpacedByRetention() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = Db.builder().testSetup(stream).clock(clock).maxNodeSize8()
                    .startupDistance(2000).start();
            final long retain = 20 * Clock.UNITS_PER_SEC;
            db.setRetainDuration(retain);
            Reclaim reclaim = db.internal().reclaim();
            java.util.Random r = new java.util.Random(3);
            List<Long> starts = new ArrayList<Long>();

            for (int i = 0; i < 2000; i++) {
                time += Clock.UNITS_PER_SEC / 10;
                clock.setTime(time);
                byte[] v = new byte[1 + r.nextInt(30)];
                r.nextBytes(v);
                db.execute(db.trans().put("/k/" + r.nextInt(50), v).build());
                List<IterationInfo> rows = reclaim.table.rows;
                long tStart = rows.isEmpty() ? -1 : rows.get(rows.size() - 1).tStart;
                if (tStart != -1 && (starts.isEmpty() || starts.get(starts.size() - 1) != tStart)) {
                    starts.add(tStart);
                }
            }

            Assert.assertTrue("iterations started: " + starts.size(), starts.size() >= 4);
            Assert.assertTrue("no cut", db.getFirstAvailablePos() > 0);
            for (int i = 1; i < starts.size(); i++) {
                Assert.assertTrue("iteration " + i + " started " + (starts.get(i) - starts.get(i - 1))
                        + " after the one before", starts.get(i) - starts.get(i - 1) >= retain / 4);
            }
            db.stop();
        }

        /**
         * fractionOf(g, f) is floor(g f / 2^16), as BigInteger computes it, on the edges and
         * on random values spread over the bit lengths (bergdb 005-79).
         */
        @Nano
        public static void testFractionOfExact() {
            long[] gs = {0, 1, 3, 4, 0xFFFF, 0x10000, 1L << 47, (1L << 53) / 3, 1L << 53,
                    Long.MAX_VALUE - 1, Long.MAX_VALUE, -1, -0x10001, Long.MIN_VALUE};
            int[] fs = {0, 1, MIN_INTERNAL_FRACTION, DEFAULT_INTERNAL_FRACTION,
                    MAX_INTERNAL_FRACTION, FRACTION_ONE - 1};
            for (long g : gs) {
                for (int f : fs) {
                    checkFractionOf(g, f);
                }
            }
            java.util.Random r = new java.util.Random(79);
            for (int i = 0; i < 100000; i++) {
                checkFractionOf(r.nextLong() >> r.nextInt(64), r.nextInt(FRACTION_ONE));
            }
        }
        
        private static void checkFractionOf(long g, int f) {
            long expected = java.math.BigInteger.valueOf(g).multiply(java.math.BigInteger.valueOf(f))
                    .shiftRight(16).longValueExact();
            long actual = fractionOf(g, f);
            if (actual != expected) {
                Assert.assertEquals("fractionOf(" + g + ", " + f + ")", expected, actual);
            }
        }

        /**
         * Steps store only the row of the iteration (CURRENT_KEY_NAME), not the whole table,
         * and a restart resumes the iteration from that row (2026-10-13).
         */
        @Nano
        public static void testRestartResumesIteration() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = startForCutTest(stream, clock);
            db.setRetainDuration(Long.MAX_VALUE);       // Loads 3000 keys first, so that
            java.util.Random r = new java.util.Random(4);   // the first iteration has steps.
            for (int i = 0; i < 3000; i += 100) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                Trans.Builder b = db.trans();
                for (int j = i; j < i + 100; j++) {
                    b.put("/k/" + j, new byte[10]);
                }
                db.execute(b.build());
            }
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            long tableTpos = -1;
            int steps = 0;
            IterationInfo before = null;

            for (int i = 0; i < 5000 && steps < 3; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                byte[] v = new byte[1 + r.nextInt(30)];
                r.nextBytes(v);
                db.execute(db.trans().put("/k/" + r.nextInt(3000), v).build());
                IterationInfo current = db.internal().reclaim().currentIteration();
                if (current == null) {
                    // The first iteration only: no other iteration gets safe or cut (and
                    // stores the table) while it runs.
                    Assert.assertTrue("the first iteration ended", tableTpos == -1);
                    continue;
                }
                GetData gd = db.newGetData();
                db.getOne(Long.MAX_VALUE, Keys.toSegments(TABLE_KEY_NAME), gd);
                if (tableTpos == -1) {
                    tableTpos = gd.tpos;
                } else {
                    Assert.assertEquals("the table was stored by a step", tableTpos, gd.tpos);
                }
                if (current.lastKey != null && (before == null
                        || !java.util.Arrays.equals(before.lastKey, current.lastKey))) {
                    steps++;
                }
                before = current.copy();
            }

            Assert.assertTrue("steps: " + steps, steps >= 3);
            db.sync(SyncLevel.ORDINARY);
            db.stop();
            clock = new CoreTestClock();
            clock.setTime(time);
            db = startForCutTest(stream.copy(), clock);
            IterationInfo after = db.internal().reclaim().currentIteration();
            Assert.assertTrue("no iteration after the restart", after != null);
            Assert.assertEquals(before.serialize(), after.serialize());
            db.stop();
        }

        /**
         * Regression test for a bug found 2026-10-13 (java/stress/ReclaimStress.java),
         * Q6 in bergdb 011-01: after a cut at the pStart of an iteration, the first
         * available lookup time was the iteration's start time, tStart. But a value not
         * changed since tStart is rewritten later in the iteration, so between tStart and
         * the rewrite, lookups find the old version, which was cut away. Only the states
         * from the end of the iteration, tEnd, are complete after the cut.
         */
        @Nano
        public static void testLookupsFromFirstAvailableTime() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = startForCutTest(stream, clock);
            
            java.util.Random r = new java.util.Random(1);
            java.util.Map<String, java.util.TreeMap<Long, byte[]>> model = 
                    new java.util.HashMap<String, java.util.TreeMap<Long, byte[]>>();
            int cuts = 0;
            long lastCut = 0;
            
            for (int i = 0; i < 3000 && cuts < 2; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                String k = "/k/" + r.nextInt(50);
                byte[] v = new byte[1 + r.nextInt(30)];
                r.nextBytes(v);
                Trans t = db.trans().put(k, v).build();
                db.execute(t);
                if (!model.containsKey(k)) {
                    model.put(k, new java.util.TreeMap<Long, byte[]>());
                }
                model.get(k).put(t.tt, v);
                
                if (stream.getCut() > lastCut) {
                    // A restart, so that values are read from the stream; the running
                    // database has most of them in memory.
                    cuts++;
                    lastCut = stream.getCut();
                    db.sync(SyncLevel.ORDINARY);
                    db.stop();
                    stream = stream.copy();
                    clock = new CoreTestClock();
                    clock.setTime(time);
                    db = startForCutTest(stream, clock);
                    long first = db.getFirstAvailableLookupTime();
                    for (long lt = first; lt <= time; lt += Clock.UNITS_PER_SEC / 40) {
                        for (String key : model.keySet()) {
                            java.util.Map.Entry<Long, byte[]> e = model.get(key).floorEntry(lt);
                            byte[] expected = e == null ? null : e.getValue();
                            Assert.assertArrayEquals(expected, DbUtil.get(db, lt, key));
                        }
                    }
                }
            }
            
            Assert.assertTrue("cuts: " + cuts, cuts >= 2);
            db.stop();
        }

        /**
         * The reserve for a step's pinned bytes (bergdb item 001, WP J6), with every object
         * evicted after every transaction: with a reserve of four nodes, each step's scan
         * stops when the index nodes it followed would need more, so steps are split (more
         * of them, each following a few nodes, about a path's worth above the reserve); the
         * iterations still end and cut, the same KVs are kept, and the lookups from the first
         * available time on are right, also after a restart from the cut stream. With the
         * default reserve no step is split. Reclaim's loads are counted: after eviction the
         * steps read from the stream.
         */
        @Nano
        public static void testStepReserveSplitsSteps() {
            long[] steps = new long[2];
            long[] maxNodes = new long[2];
            for (int pass = 0; pass < 2; pass++) {
                boolean small = pass == 1;
                CoreTestClock clock = new CoreTestClock();
                long time = Clock.UNITS_PER_SEC;
                clock.setTime(time);
                CutStream stream = new CutStream();
                DbBuilder builder = Db.builder().testSetup(stream).clock(clock).maxNodeSize8()
                        .startupDistance(2000).evictionSchedule(Eviction.Schedule.EVERY, 1);
                if (small) builder.reclaimStepReserve(4 * (80 + 48 * 8));
                Db db = builder.start();
                db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
                Reclaim reclaim = db.internal().reclaim();
                Stats stats = reclaim.enableStats();
                
                java.util.Random r = new java.util.Random(1);
                java.util.Map<String, java.util.TreeMap<Long, byte[]>> model = 
                        new java.util.HashMap<String, java.util.TreeMap<Long, byte[]>>();
                for (int i = 0; i < 3000 && stream.getCut() == 0; i++) {
                    time += Clock.UNITS_PER_SEC / 20;
                    clock.setTime(time);
                    String k = "/k/" + r.nextInt(200);
                    byte[] v = new byte[1 + r.nextInt(30)];
                    r.nextBytes(v);
                    Trans t = db.trans().put(k, v).build();
                    db.execute(t);
                    if (!model.containsKey(k)) {
                        model.put(k, new java.util.TreeMap<Long, byte[]>());
                    }
                    model.get(k).put(t.tt, v);
                }
                Assert.assertTrue("a cut", stream.getCut() > 0);
                Stats.Iteration st = stats.iterations.get(0);
                Assert.assertTrue("loads " + st.loads, st.loads > 0 && st.loadBytes > 0);
                long reserveNodes = reclaim.getStepReserve() / reclaim.stepNodeBytes();
                if (small) {
                    Assert.assertEquals(4L, reserveNodes);
                    Assert.assertTrue("split steps " + st.splitSteps, st.splitSteps > 0);
                    Assert.assertTrue("nodes " + st.maxStepNodes, st.maxStepNodes <= reserveNodes + 12);
                } else {
                    Assert.assertEquals(0L, st.splitSteps);
                }
                steps[pass] = st.steps;
                maxNodes[pass] = st.maxStepNodes;
                
                db.sync(SyncLevel.ORDINARY);
                db.stop();
                stream = stream.copy();
                clock = new CoreTestClock();
                clock.setTime(time);
                db = Db.builder().testSetup(stream).clock(clock).maxNodeSize8()
                        .startupDistance(2000).evictionSchedule(Eviction.Schedule.EVERY, 1).start();
                long first = db.getFirstAvailableLookupTime();
                for (long lt = first; lt <= time; lt += Clock.UNITS_PER_SEC / 4) {
                    for (String key : model.keySet()) {
                        java.util.Map.Entry<Long, byte[]> e = model.get(key).floorEntry(lt);
                        byte[] expected = e == null ? null : e.getValue();
                        Assert.assertArrayEquals(expected, DbUtil.get(db, lt, key));
                    }
                }
                db.stop();
            }
            Assert.assertTrue("steps " + steps[0] + ", " + steps[1], steps[1] > steps[0]);
            Assert.assertTrue("nodes " + maxNodes[0] + ", " + maxNodes[1], maxNodes[1] < maxNodes[0]);
        }

        /**
         * bergdb 011-04, W5c. The cut is made only when the stream is durable up to the
         * decision (the table that marks the cut, the meta block that recovery starts from):
         * when the front is cut, the underlying stream is at least as long as it was at the
         * decision. CutStream.getLengthAtCut() is the length then, and CrashTest never cuts
         * the stream shorter than that: what a crash may lose is only what came after.
         * "Durable" is what StorageManager confirms: FileStream forces appended bytes
         * and backing-file names before completion (see bergdb 011-07). The unit
         * test waits for two cuts and does not sync; the f-test waits for three and syncs
         * after every seventh transaction, which waits for the storage thread.
         */
        @Nano
        public static void testCutIsMadeAfterDecisionIsDurable() {
            cutIsMadeAfterDecisionIsDurable(2, false);
        }

        @Nano("f")
        public static void testCutIsMadeAfterDecisionIsDurableF() {
            cutIsMadeAfterDecisionIsDurable(3, true);
        }

        private static void cutIsMadeAfterDecisionIsDurable(int wanted, boolean sync) {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = startForCutTest(stream, clock);
            Stats stats = db.internal().reclaim().enableStats();
            java.util.Random r = new java.util.Random(8);
            long lastCut = 0;
            int cuts = 0;

            for (int i = 0; i < 30000 && cuts < wanted; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                db.execute(db.trans().put("/k/" + r.nextInt(50), new byte[1 + r.nextInt(30)])
                        .build());
                if (sync && i % 7 == 0) {
                    db.sync(SyncLevel.ORDINARY);
                }
                if (stream.getCut() > lastCut) {
                    lastCut = stream.getCut();
                    Stats.Cut decided = null;
                    for (Stats.Cut c : stats.cuts) {
                        if (c.pos == lastCut) {
                            decided = c;
                        }
                    }
                    Assert.assertTrue("no decision for the cut at " + lastCut, decided != null);
                    Assert.assertTrue("the cut at " + lastCut + " was made when the stream was "
                            + stream.getLengthAtCut() + " bytes, before the decision's "
                            + decided.decidedAt, stream.getLengthAtCut() >= decided.decidedAt);
                    cuts++;
                }
            }

            Assert.assertTrue("cuts: " + cuts, cuts >= wanted);
            db.stop();
        }
    }
}

/*

SpaceReclaim implementation
---------------------------

130129 Frans. SpaceReclaim is setup to listen to DB.TransactionListener.transactionCompleted() 
events from DB. 
SpaceReclaim uses these calls to run its methods. Current implement does not start new threads,
but runs piggyback in the thread that executes an ordinary external transaction.

This functionality is quite independent from the rest of the code. It will be possible to easily
try different reclaim algorithms :-). However, interfaces are not used now. Also consider that fact
that we need be compatible with what is stored in the database. Is user allowed to switch 
reclaim algorithms in same database? That requires every type of reclaim implementation to 
understand the data stored in TABLE_KEY_NAME even when it was produced by another implementation.
Scary. Instead we keep one algorithm only. We only need the possibility for the advanced user 
to be able to choose to either use the ordinary reclaim algorithm or disable reclaim all together.
Disabling it is suitable for testing only.

The method setInternalFraction() is available to the user. A large internal fraction will result in
a smaller stream size, while a small internal fraction will reduce the amount of data written to
the stream. The suitable setting for this depends on cost of storage space vs cost of writing data
(slower transactions, replication, network usage).

*/
