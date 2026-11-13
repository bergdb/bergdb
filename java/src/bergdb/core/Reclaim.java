package bergdb.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
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
import bergdb.storage.RecoverableStream;
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
 * tStart after lastKey and rewrites each live value stored before pCut: a put of the same
 * key and value, which makes the index nodes on the key's path dirty, as every put does, so
 * that they are written again. The row of the
 * iteration, with the new lastKey, is stored in the same transaction (CURRENT_KEY_NAME);
 * the table is stored when an iteration starts, ends, gets safe or is cut.</li>
 * <li>When the scan reaches the end, the iteration is done; tEnd and pEnd are the time and
 * position of the last step. Every node and value reachable at times from tEnd on is then
 * stored at pCut or later, or is dirty and will be written there. A value: by its put, or
 * by the step that rewrote it. An index node: a delete unlinks the nodes it empties
 * (Dag.deleteUpward, format 6), so the node has a live key below it; if nothing below the
 * node changed since pCut, that key's value is stored before pCut, and the step that rewrote
 * it made the node dirty; otherwise the transaction that changed something below it did
 * (bergdb 024-07, section 4). The space root, the only node that can be empty, is on the path
 * of every step's row.</li>
 * <li>A step makes dirty the index nodes on the paths of its own puts only (Trans.touch,
 * Db.touchPaths), so what it pins and what a later record writes for it follow the 16 kB
 * of its scan, not the size of the database (024-07). From 2026-10-13 until 024-07 a step
 * also visited every index node of its scan's key range at the step's time, and the last
 * step every node from the scan's last key to the end of the key space, to write again the
 * nodes that held deleted keys only; with keys put in time order that was every node made
 * since the iteration began, in one transaction (024-03, section 7).</li>
 * <li>The cut waits until the startup pos has passed pEnd (every touched node written
 * once), and then passed pSafe, the stream length at that moment (nodes written before
 * their children and kept dirty by the still-dirty test written once more, now naming the
 * children's new positions). That moment is after the internal records that the external
 * transaction's call appends before the marking (an iteration's table, a step, the table
 * of the iteration done): their takes may move the startup pos past pEnd and keep such
 * nodes dirty, so pSafe is the length after them (bergdb 015-54; it was the end of the
 * external transaction's record). Then, when tEnd is older than the retention duration, the
 * stream is cut at pCut, the row is marked cut and the first available lookup time is
 * tEnd.</li>
 * <li>All state that decides what reclaim writes is in the table or follows from stream
 * positions, so a restart changes nothing (INV-RESTART).</li>
 * <li>The retain duration and the internal fraction, reclaim's settings, are kept in the
 * stream, in the internal KV SETTINGS_KEY_NAME (bergdb 015-87): Db.setRetainDuration and
 * Db.setReclaimInternalFraction commit it (setSettings), and a start reads it with the
 * table (initFromDb), so a restart keeps them (010-P2). Before 015-87 a start took the
 * builder's retain duration and the default fraction, and a restart that did not set them
 * again stopped reclaim, or changed what it wrote.</li>
 * <li>The retain duration may change at any time, by Db.setRetainDuration.
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
     * Reclaim's settings, kept in the stream (bergdb 015-87, Frans's decision F1 = B): the
     * retain duration and the internal fraction, as text in the style of the table's rows,
     * two lines in this order, each a decimal long:
     * 
     * <pre>
     * retain=&lt;the retain duration in time units&gt;
     * fraction=&lt;the internal fraction in units of 2^-16&gt;
     * </pre>
     * 
     * Forever is Long.MAX_VALUE, 9223372036854775807, as getRetainDuration() gives it; the
     * default fraction is 16384, 0.25. Each line ends with a newline, and the numbers have
     * no sign and no leading zeros (serializeSettings).
     * 
     * Written by setSettings, in an internal transaction of its own, as the table is, and
     * only when a setting changes: a database whose settings were never changed has no
     * such KV, and runs with the defaults (forever, 16384). Read by initFromDb at every
     * start, which refuses a value in any other form (parseSettings). Reclaim's steps
     * rewrite it as any live value, so a cut never removes it.
     */
    static final String SETTINGS_KEY_NAME = DbConstants.INTERNAL_PREFIX + "dreclaim/-settings.txt";
    private final long[] settingsKey;
    
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
    
    /**
     * Bytes of a value node besides its key and value: StoredValueNode's, so that a change of
     * the node's layout changes it too (2026-11-12, bergdb 024-25: it was 28, the size before
     * the checksum's 4 bytes, here and in testAllowanceCountsIndexNodes).
     */
    static final int VALUE_NODE_BYTES = StoredValueNode.VALUE_OVERHEAD;
    
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
        settingsKey = Keys.toSegments(SETTINGS_KEY_NAME);
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
     * Sets reclaim's settings, the retain duration (in time units, Long.MAX_VALUE is
     * forever) and the internal fraction (in units of 2^-16), and keeps them in the stream
     * (bergdb 015-87): if they differ from those in force, an internal transaction puts
     * SETTINGS_KEY_NAME with both, and the fields are set after it is committed, so the next
     * transaction uses them; if they are those in force, nothing is written. A value out of
     * range is refused with an IllegalArgumentException before anything is written, and a
     * change once the top node ordinals are used up as a user transaction is
     * (Db.refuseIfTopOrdinalsUsed). If the commit throws, the settings in force stay as
     * they were: refused before its go point, it wrote nothing; failed after it, it failed
     * the database, and a restart takes what the stream holds. The caller holds Db's write
     * lock and has checked that the database is active (Db.setRetainDuration,
     * Db.setReclaimInternalFraction).
     */
    void setSettings(long retainDuration, int internalFraction) {
        assert Thread.holdsLock(this.writeLock);
        checkRetainDuration(retainDuration);
        checkInternalFraction(internalFraction);
        if (retainDuration == this.retainDuration && internalFraction == this.internalFraction) {
            return;     // In force: nothing is written.
        }
        db.refuseIfTopOrdinalsUsed();   // As a user transaction is refused.
        
        Trans t = db.trans()
                .putCore(settingsKey, serializeSettings(retainDuration, internalFraction)).build();
        t.isInternal = true;
        try {
            db.execute(t);
        } catch (RerunException e) {
            throw new Bug("RerunException for write-only trans unexpected, " + e.getMessage());
        }
        
        this.retainDuration = retainDuration;
        this.internalFraction = internalFraction;
    }
    
    /** Refuses a retain duration below one second with an IllegalArgumentException. */
    static void checkRetainDuration(long retainDuration) {
        if (retainDuration < 1 * Clock.UNITS_PER_SEC) {
            throw new IllegalArgumentException("retainDuration = " + retainDuration
                    + " is too small, must be at least one second (" + Clock.UNITS_PER_SEC
                    + " time units).");
        }
    }
    
    /**
     * Refuses an internal fraction outside MIN_INTERNAL_FRACTION to MAX_INTERNAL_FRACTION,
     * units of 2^-16, with an IllegalArgumentException.
     */
    static void checkInternalFraction(int internalFraction) {
        if (internalFraction < MIN_INTERNAL_FRACTION || internalFraction > MAX_INTERNAL_FRACTION) {
            throw new IllegalArgumentException("Illegal internalFraction value, " + internalFraction);
        }
    }
    
    /** The value of SETTINGS_KEY_NAME for the given settings. */
    static byte[] serializeSettings(long retainDuration, int internalFraction) {
        return StringUtil.toBytes("retain=" + retainDuration + "\nfraction=" + internalFraction
                + "\n");
    }
    
    /**
     * Sets the fields from a value of SETTINGS_KEY_NAME. The value must be in the one form
     * that serializeSettings writes, byte for byte: the two lines in their order, the
     * numbers in range. Only setSettings writes the KV, so any other value is refused, one
     * with a line of its own too: it is damage, or the settings of a later version, which
     * this one must neither run without nor drop at its next setSettings (bergdb 015-87).
     * 
     * @throws InternalDataException  If the value is not in that form.
     */
    private void parseSettings(byte[] value) {
        String s = StringUtil.toString(value);
        StringMap m = new StringMap(s);
        long retain = m.hasLong("retain") ? m.getLong("retain") : -1;
        long fraction = m.hasLong("fraction") ? m.getLong("fraction") : -1;
        if (retain < Clock.UNITS_PER_SEC || fraction < MIN_INTERNAL_FRACTION
                || fraction > MAX_INTERNAL_FRACTION
                || !Arrays.equals(value, serializeSettings(retain, (int) fraction))) {
            throw new InternalDataException("Bad value of " + SETTINGS_KEY_NAME + ", reclaim's "
                    + "settings: not the two lines retain=<time units> and fraction=<units of "
                    + "2^-16>, in range, that this version writes (bergdb 015-87): '"
                    + (s.length() <= 200 ? s : s.substring(0, 200) + "...") + "'.");
        }
        this.retainDuration = retain;
        this.internalFraction = (int) fraction;
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
     * Sets the reserve for the pinned bytes of a reclaim step (bergdb item 001, WP J6): the
     * index nodes that its touch and its rewrites make dirty, which stay pinned until they
     * are written. A step's scan stops at the KV where the index nodes it has followed
     * (NodeCollection.MaintenanceFollower, by id) would need more than the reserve, counted
     * stepNodeBytes() each; so a step that would exceed it is split into smaller ones, and
     * it exceeds the reserve by at most the nodes of one path. With the default, 4 MiB,
     * steps are not split in practice (a step scans about 16 kB of KVs). Thread-safe; used
     * from the next step.
     * 
     * <p>A setting for tests (bergdb 015-87, F7): below the default it splits steps, and so
     * changes the stream's bytes, but it is not kept in the stream; a start takes the
     * builder's (DbBuilder.reclaimStepReserve). At the default no step is split in the
     * stress workloads (bergdb 005-78, probe P4).</p>
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
        
        markSafePositions();    // The length after the records above (bergdb 015-54).
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
    
    /**
     * The least that the cut of an iteration that maintain() begins must release, in stream
     * bytes (bergdb 024-32, section 2.2, M1): two meta block distances. With no cut
     * pending, what a new one releases is the stretch between the last two pStarts;
     * once a database has converged, that holds an iteration's records and at most one
     * filler (MAINTAIN_FILL_KEY_NAME, below one meta block distance), so no iteration
     * begins and the calls return false. And a filler is at most half of what its cut
     * releases.
     */
    static final long MAINTAIN_MIN_RELEASE = 2L * RecoverableStream.META_BLOCK_DISTANCE;
    
    /**
     * The most bytes of index nodes that the take of one maintain() call writes beyond its
     * share, after its first transaction (TransSeq.takeTo; bergdb 024-32, section 2.2, M4).
     */
    static final long MAINTAIN_TAKE_BYTES = 256 * 1024L;
    
    /**
     * maintain()'s filler (bergdb 024-32, section 2.2, M5): put with a value of zeros that
     * reaches the next meta block, and deleted at once in a transaction of its own, so that
     * a meta block names a transaction at or after an iteration's pCut and the cut can be
     * made without the application's writes. Never live after a call.
     */
    static final String MAINTAIN_FILL_KEY_NAME = 
            DbConstants.INTERNAL_PREFIX + "dreclaim/-fill.txt";
    private static final long[] MAINTAIN_FILL_KEY = Keys.toSegments(MAINTAIN_FILL_KEY_NAME);
    
    /**
     * One call of Db.maintain() (bergdb 024-32, section 2): a bounded part of what reclaim
     * does after the application's commits, without them, in reclaim's internal
     * transactions, at most one of each, in this order:
     * 
     * <ol>
     * <li>M1: if no iteration runs, the retain duration is finite, a quarter of it has
     * passed since the last iteration began, no done iteration waits for its cut
     * (cutPending),
     * and the cut that a new iteration leads to releases at least MAINTAIN_MIN_RELEASE, an
     * iteration begins, as at a commit, with tStart = lastTransTime, the time of the state
     * at pStart. The commit's condition on the stream's growth is not asked.</li>
     * <li>M2: a step of the iteration that runs, of MAX_STEP_SIZE, without the commit's
     * allowance (the internal fraction of the growth).</li>
     * <li>M3: the safe positions (markSafePositions).</li>
     * <li>M4: if a done iteration waits for the startup pos, an empty internal transaction
     * whose take goes on to that position (Trans.maintainTakeTo, TransSeq.takeTo); M3
     * again.</li>
     * <li>M5: if an iteration's cut waits for a meta block only, the filler
     * (MAINTAIN_FILL_KEY_NAME).</li>
     * <li>M6: the cut, if it is due (pretruncateIfPossible, cutIfDurable).</li>
     * </ol>
     * 
     * The caller holds the write lock and has checked that the database is active.
     * 
     * @param now  The time of the call, DbClock.currentTime().
     * @param lastTransTime  The time of the last transaction.
     * @return Whether more is due now: maintainDue().
     */
    boolean maintain(long now, long lastTransTime) {
        assert Thread.holdsLock(this.writeLock);
        
        if (maintainBeginDue(now)) {                                // M1
            final long streamSize = db.getStreamLength();
            IterationInfo it = new IterationInfo();
            it.pStart = streamSize;
            it.tStart = lastTransTime;
            it.pCut = table.rows.isEmpty() ? streamSize : lastPStart();
            table.rows.add(it);
            storeTable();
        }
        
        IterationInfo current = currentIteration();                 // M2
        if (current != null) {
            step(current, MAX_STEP_SIZE);
        }
        
        markSafePositions();                                        // M3
        
        final long target = maintainTakeTarget();                   // M4
        if (target != -1) {
            Trans t = db.trans().build();
            t.isInternal = true;
            t.maintainTakeTo = target;
            try {
                db.execute(t);
            } catch (RerunException e) {
                throw new Bug("RerunException for an empty trans unexpected, " + e.getMessage());
            }
            markSafePositions();
        }
        
        if (cutWaitsForMetaBlock(now)) {                            // M5
            final long length = db.getStreamLength();
            final int distance = RecoverableStream.META_BLOCK_DISTANCE;
            final int fill = Math.max(1, (int) (distance - length % distance));
            executeInternal(db.trans().putCore(MAINTAIN_FILL_KEY, new byte[fill]).build());
            executeInternal(db.trans().deleteCore(MAINTAIN_FILL_KEY).build());
        }
        
        pretruncateIfPossible(now);                                 // M6
        cutIfDurable();
        return maintainDue(now);
    }
    
    /** Executes an internal write-only transaction (maintain()'s filler). */
    private void executeInternal(Trans t) {
        t.isInternal = true;
        try {
            db.execute(t);
        } catch (RerunException e) {
            throw new Bug("RerunException for write-only trans unexpected, " + e.getMessage());
        }
    }
    
    /**
     * Whether a call of maintain() now has work (bergdb 024-32, section 2.3): an iteration
     * runs, a take or a filler is due, a cut waits to be durable, or an iteration may begin.
     * False when nothing is due until time passes or the application writes.
     */
    boolean maintainDue(long now) {
        return currentIteration() != null || maintainTakeTarget() != -1 
                || cutWaitsForMetaBlock(now) || pendingCut != -1 || maintainBeginDue(now);
    }
    
    /**
     * The stream length that must be durable before the pending cut is made, or -1 if no
     * cut is pending; see cutIfDurable().
     */
    long pendingCutDurableAt() {
        return pendingCut == -1 ? -1 : pendingCutDurableAt;
    }
    
    /** Makes the pending cut if its table is durable; maintain() calls it after a sync. */
    void cutIfDurableNow() {
        cutIfDurable();
    }
    
    /** maintain()'s M1 condition; see maintain(). */
    private boolean maintainBeginDue(long now) {
        if (retainDuration == Long.MAX_VALUE || currentIteration() != null
                || now - lastTStart() < retainDuration / ITERATION_DIVISOR) {
            return false;
        }
        for (IterationInfo row : table.rows) {
            if (cutPending(row)) {
                return false;
            }
        }
        final long cutAt = table.rows.isEmpty() ? db.getStreamLength() : lastPStart();
        return cutAt - firstAvailablePos >= MAINTAIN_MIN_RELEASE;
    }
    
    /**
     * True if 'row' is a done iteration whose cut is still to come: not cut, and its pCut
     * is after the first available position (an iteration whose pCut is not, such as one
     * that began when the last one had the same pStart as its pCut, has nothing to cut).
     */
    private boolean cutPending(IterationInfo row) {
        return row.done && !row.cut && row.pCut > firstAvailablePos;
    }
    
    /**
     * The least position that a done iteration whose cut is pending waits for the startup pos to
     * reach (pEnd until it is safe, then pSafe), or -1 if none waits (maintain()'s M4).
     */
    private long maintainTakeTarget() {
        final long sp = db.internal().getStartupPosForEvict();
        long target = -1;
        for (IterationInfo row : table.rows) {
            if (!cutPending(row)) {
                continue;
            }
            final long p = row.pSafe == -1 ? row.pEnd : row.pSafe;
            if (sp < p && (target == -1 || p < target)) {
                target = p;
            }
        }
        return target;
    }
    
    /**
     * True if an iteration has all that its cut needs (see pretruncateIfPossible) but a
     * meta block that names a transaction at or after its pCut (maintain()'s M5).
     */
    private boolean cutWaitsForMetaBlock(long now) {
        final long metaTransPos = db.getLastTransPosOfLastValidMetaBlock();
        final long startupPos = db.internal().getStartupPosForEvict();
        for (IterationInfo row : table.rows) {
            if (row.done && !row.cut && now - retainDuration > row.tEnd
                    && row.pSafe != -1 && startupPos >= row.pSafe
                    && row.pCut > firstAvailablePos && metaTransPos < row.pCut) {
                return true;
            }
        }
        return false;
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
     * bytes of them, rewrites each live value stored before pCut,
     * and stores the table row as it is after the step; all in one internal transaction.
     * Only a KV whose value the scan found before pCut is read again, at the step's time
     * (bergdb 024-34).
     * After the last step (the scan reached the end), the iteration is done, and tEnd and
     * pEnd are stored.
     * 
     * <p>A value that a step rewrites, its copy, is the value of its key at one unit before
     * the step's time: the step reads it at the latest state and puts it with the key as read
     * (keyRead, readTime), so a write of the key between them makes the step run again
     * (RerunException). ConnectionImp.transactionInfo() follows a copy back to the
     * transaction that wrote the value by it (bergdb 021-17).</p>
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
        final long[] atCut = new long[2];   // Value loads seen, those at pCut or later (stats).
        
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
                final long vl = maintenance.valueLoads();
                if (vl > atCut[0]) {
                    atCut[0] = vl;
                    if (Spos.isVpos(kvt.spos) || kvt.spos >= it.pCut) atCut[1]++;
                }
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
        
        // bergdb 015-50 (016-06's R7-F1): the step's value nodes stay within
        // StoredTrans.valueLimit(), as a user transaction's do (Db.checkSize). The scan adds
        // KVs until their size passes writeSize, so its last one can be a value of any size;
        // the step's internal transaction, refused for its size inside the go point of the
        // user transaction that allowed it, failed the database, and again after every
        // restart. A value that would take the step's value nodes past the limit ends the
        // step before it, unless it is the step's first: then it is the first of the next
        // step. Alone, it is within the limit, as its user transaction was (or the transaction
        // of a step before); the step's row comes on top of it, so Db.checkSize does not apply
        // to internal transactions. A step that did not pass the limit is the same as before.
        final long valueLimit = StoredTrans.valueLimit();
        long valueNodeBytes = 0;
        int kvs = 0;                        // The KVs of the scan that the step covers.
        long gets = 0;                      // For stats.
        
        for (Kvt kvt : g.result) {
            // bergdb 024-34 (024-05, OP8): a KV whose value the scan found at pCut or later,
            // or not yet written (a vpos), is not rewritten, so it is not read again. Its value
            // at the step's time is that one, a later one (stored after tStart, so after
            // pStart), or none, and a record lies wholly before or after pCut, a record
            // boundary: so the test below would fail for it. Before, every KV of the scan was
            // read again; the step's puts, its row and so its bytes are the same.
            if (Spos.isVpos(kvt.spos) || kvt.spos >= it.pCut) {
                kvs++;
                continue;
            }
            GetData gd = db.newGetData();
            gd.pointerFollower = maintenance;
            byte[] value;
            gets++;
            
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
                final long nodeBytes = StoredValueNode.getByteSizeLong(value, kvt.key);
                if (values > 0 && valueNodeBytes + nodeBytes > valueLimit) {
                    lastKeyOfStep[0] = g.result.get(kvs - 1).key;
                    eod[0] = false;
                    break;
                }
                valueNodeBytes += nodeBytes;
                b.keyRead(kvt.key);
                // Note, no mem copy of key and value. The internal call: a live key may be
                // BergDB's own, longer than Db.MAX_KEY_BYTES (an index entry), and a check
                // that threw here, inside a user transaction's go point, would fail the
                // database (bergdb 024-24).
                b.putLongKey(kvt.key, null, value, null);
                rewritten += kvt.key.length * 8 + value.length + VALUE_NODE_BYTES;
                values++;
                valueBytes += kvt.key.length * 8 + value.length;
            }
            kvs++;
        }
        
        final IterationInfo next = it.copy();
        next.lastKey = lastKeyOfStep[0];
        next.kvCount += kvs;
        next.rewritten += rewritten;
        final Trans[] stepTrans = new Trans[1];
        final byte[][] tableBytes = new byte[1][];
        final long[] dirtiedStored = new long[1];
        
        // 2026-10-13 (bergdb 011-04, "Level 3 cost"): the allowance counted the
        // values only, about 100 bytes each for the index; the index nodes the step makes
        // dirty, by its puts and its touch, were not counted, so reclaim wrote more than
        // internalFraction. Their size is known during the step only (Trans.dirtiedBytes),
        // so the row is stored by a value transformation.
        
        b.putCore(currentKey, null, new byte[0], new ValueTransformation() {
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
        
        // The touch (Trans.touch): the index nodes on the paths of the step's puts get dirty
        // before the puts, so that the row stores what the step made dirty. From 2026-10-13
        // (Q7 in bergdb 011-01, Reclaim.Tester.testDeletedKeysAfterCut) until bergdb 024-07
        // the touch visited the key range of the step's scan at the step's time, to the end
        // of the key space in the last step: only live values were rewritten, and nodes that
        // held deleted keys only, and the segment subtrees of deleted long keys, kept their
        // versions before pStart, while lookups still passed through them. Since format 6 a
        // delete unlinks the nodes it empties, so no such node is left (024-07, section 4).
        t.touch = true;
        
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
            st.kvs += kvs;
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
            st.valueLoads += maintenance.valueLoads();
            st.scanValueLoadsAtCut += atCut[1];
            st.gets += gets;
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
     * length now, after the internal records that the call of transactionCompleted appended
     * before it (bergdb 015-54). See the class comment.
     */
    private void markSafePositions() {
        final long startupPos = db.internal().getStartupPosForEvict();
        final long streamLength = db.getStreamLength();     // The write lock is held.
        boolean changed = false;
        
        for (IterationInfo row : table.rows) {
            if (row.done && row.pSafe == -1 && startupPos >= row.pEnd) {
                row.pSafe = streamLength;
                changed = true;
            }
        }
        
        if (changed) {
            storeTable();
        }
    }

    /**
     * Initializes reclaim's settings (SETTINGS_KEY_NAME; the defaults if the stream has
     * none, bergdb 015-87) and the iteration table, 'table', from what is stored in the
     * database. Db must be in state ACTIVE when this method is called; the start calls it
     * last, before any transaction, so the settings are in force from the first one.
     * 
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws InternalDataException  If DB data "table.txt" or the settings are badly
     *      formatted.
     */
    public void initFromDb() {
        GetData g = db.newGetData();
        
        // The settings kept in the stream (bergdb 015-87).
        byte[] settings = db.getOne(Long.MAX_VALUE, settingsKey, g);
        if (settings != null) {
            parseSettings(settings);    // throws InternalDataException
        }
        
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
        
        // bergdb 026-05: a pending cut whose table is durable is made before the newer one
        // replaces it. It was dropped: a cut decided at every transaction (iterations of one
        // step, as 026-05 makes them when the keys are overwritten) left the stream uncut
        // (Reclaim.Tester.testPretruncate; 023-08, check V8, Q2). The older cut is the one
        // that cutIfDurable() would have made at the end of the call before; it cuts at or
        // before the newer one.
        cutIfDurable();
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
        Trans t = db.trans().putCore(tableKey, tableBytes).build();
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
            long valueLoads;            // Of the loads, values (bergdb 024-34).
            long scanValueLoadsAtCut;   // Values the scans loaded stored at pCut or later.
            long gets;                  // Second reads: a key read again at the step's time.
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
         * Regression test for bergdb 015-55 (016-06's R7-F6): a user transaction at the last
         * database time, Klong.MAX_TIME, was taken; the reclaim step it allowed then found no
         * time left, inside the transaction's go point, and the database failed. Now a user
         * transaction after DbClock.LAST_USER_TIME is refused and the database goes on; one
         * at LAST_USER_TIME is taken, and its step runs in the times kept for it.
         */
        @Nano
        public static void testUserTransactionLeavesTimesForReclaim() {
            final long[] now = {Clock.UNITS_PER_SEC};
            Clock clock = new Clock() {         // Can go back, as CoreTestClock cannot.
                public long getTime() {
                    return now[0];
                }
            };
            Db db = Db.builder().testSetup().clock(clock).startupDistance(2000).start();
            try {
                db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
                Reclaim rc = db.internal().reclaim();
                java.util.Random r = new java.util.Random(1);
                boolean armed = false;
                for (int i = 0; i < 4000 && !armed; i++) {
                    now[0] += Clock.UNITS_PER_SEC / 20;
                    IterationInfo cur = rc.currentIteration();
                    armed = cur != null && fractionOf(db.getStreamLength() + 150 - cur.pStart,
                            DEFAULT_INTERNAL_FRACTION) - cur.rewritten > 10000;
                    if (!armed) {
                        db.execute(db.trans().put("/k/" + r.nextInt(50), 
                                new byte[1 + r.nextInt(60)]).build());
                    }
                }
                Assert.assertTrue("no step was armed", armed);
                
                // The next put makes a step. At Klong.MAX_TIME it is refused before its go
                // point, and the database goes on.
                now[0] = bergdb.dag.Klong.MAX_TIME;
                try {
                    db.execute(db.trans().put("/last", "a").build());
                    throw new AssertionError("a user transaction at Klong.MAX_TIME was taken");
                } catch (bergdb.pub.util.DbFailedException e) {
                    throw new AssertionError("the database failed", e);
                } catch (bergdb.pub.util.DbException e) {
                    Assert.assertTrue(e.getMessage(), 
                            e.getMessage().contains("for a user transaction"));
                }
                Assert.assertEquals(null, db.getOne(Long.MAX_VALUE, Keys.toSegments("/last"), 
                        db.newGetData()));
                
                // At the last user time it is taken, and its step has times after it.
                now[0] = DbClock.LAST_USER_TIME;
                long count = db.getTransactionCount();
                db.execute(db.trans().put("/last", "b").build());
                Assert.assertTrue("the put made a step", db.getTransactionCount() > count + 1);
                Assert.assertEquals("b", StringUtil.toString(db.getOne(Long.MAX_VALUE, 
                        Keys.toSegments("/last"), db.newGetData())));
            } finally {
                db.close();
            }
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
         * Regression test for 015-50 (016-06's R7-F1): a step rewrote the old values of its
         * scan in one internal transaction, which Db.checkSize (bergdb 005-17) refused when
         * they passed StoredTrans.valueLimit() together, each committed within it; the
         * refusal came inside a user transaction's go point and failed the database, and
         * again at the first commit after every restart. The record limit lowered to 100 kB,
         * as StoredTrans's own test does: ten old values of 4 kB, then /b, whose node takes
         * valueLimit() - 1000 bytes (a step's scan takes the last of the ten and /b), and in
         * a second run valueLimit() (alone with the step's row it passes the limit).
         * Before the fix: "The transaction is too large: its values and keys take 90596
         * bytes in the stream, more than 87500", at about the 400th put.
         */
        @Nano("f")
        public static void testStepWithinValueLimit() {
            final long saved = StoredTrans.recordLimit;
            StoredTrans.recordLimit = 100 * 1000;
            try {
                stepWithinValueLimit(1000);
                stepWithinValueLimit(0);
            } finally {
                StoredTrans.recordLimit = saved;
            }
        }
        
        private static void stepWithinValueLimit(long slack) {
            final long limit = StoredTrans.valueLimit();
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(2000).start();
            try {
                stepWithinValueLimit(db, stream, clock, time, limit, slack);
            } finally {
                db.stop();
            }
        }
        
        private static void stepWithinValueLimit(Db db, CutStream stream, CoreTestClock clock,
                long time, long limit, long slack) {
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            for (int i = 0; i < 10; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                db.execute(db.trans().put("/a/" + i, new byte[4000]).build());
            }
            final long[] key = Keys.toSegments("/b");
            int n = (int) (limit - slack);
            while (StoredValueNode.getByteSizeLong(new byte[n], key) > limit - slack) {
                n--;
            }
            time += Clock.UNITS_PER_SEC / 20;
            clock.setTime(time);
            db.execute(db.trans().put("/b", new byte[n]).build());
            final long bEnd = db.getStreamLength();
            
            java.util.Random r = new java.util.Random(1);
            long cut = 0;
            int cuts = 0;
            for (int i = 0; i < 4000 && cuts < 3; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                db.execute(db.trans().put("/k/" + r.nextInt(50), new byte[1 + r.nextInt(60)])
                        .build());
                if (stream.getCut() > cut) {
                    cut = stream.getCut();
                    cuts++;
                }
            }
            Assert.assertTrue("slack " + slack + ", cuts: " + cuts, cuts >= 3);
            Assert.assertTrue("slack " + slack + ", cut " + cut + " not past /b's record, "
                    + bEnd, cut > bEnd);
            
            db.sync(SyncLevel.ORDINARY);
            clock = new CoreTestClock();
            clock.setTime(time);
            Db db2 = Db.builder().testSetup(stream.copy()).clock(clock).start();
            try {
                for (int j = 0; j < 20; j++) {
                    time += Clock.UNITS_PER_SEC / 20;
                    clock.setTime(time);
                    db2.execute(db2.trans().put("/k/" + j, new byte[10]).build());
                }
                Assert.assertEquals(n, DbUtil.get(db2, Long.MAX_VALUE, "/b").length);
                for (int i = 0; i < 10; i++) {
                    Assert.assertEquals(4000, DbUtil.get(db2, Long.MAX_VALUE, "/a/" + i).length);
                }
            } finally {
                db2.stop();
            }
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

        /**
         * bergdb 015-54 (016-06, R7-F5): pSafe is the stream length when it is set, after
         * the internal records that the same call appended before it: the table of an
         * iteration started, a step, the table of the iteration done (step() stores it).
         * It was the user record's end, read before them, so the cut did not wait for the
         * nodes that those records wrote before their children. The workload is R7-F5's
         * probe's; in its first 4000 puts, each of the 57 markings comes in a call that
         * made a step before it. Five are checked.
         */
        @Nano
        public static void testSafePosAfterTheCallsRecords() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            Db db = Db.builder().testSetup().clock(clock).startupDistance(2000).start();
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            Reclaim reclaim = db.internal().reclaim();
            Stats stats = reclaim.enableStats();
            java.util.Random r = new java.util.Random(1);
            Set<IterationInfo> marked =
                    Collections.newSetFromMap(new IdentityHashMap<IterationInfo, Boolean>());
            int markings = 0;
            int afterRecords = 0;

            for (int i = 0; i < 4000 && afterRecords < 5; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                long stepBytes = stats.step.bytes;
                Trans t = db.trans().put("/k/" + r.nextInt(50), new byte[1 + r.nextInt(60)])
                        .build();
                db.execute(t);

                // The call's records before the marking: at least its steps', and the
                // table of an iteration it started.
                long steps = stats.step.bytes - stepBytes;
                boolean started = false;
                for (IterationInfo row : reclaim.table.rows) {
                    started |= row.pStart == t.nextPos;
                }
                long atLeast = t.nextPos + steps + (started ? 1 : 0);
                for (IterationInfo row : reclaim.table.rows) {
                    if (row.pSafe != -1 && marked.add(row)) {
                        markings++;
                        if (atLeast > t.nextPos) {
                            afterRecords++;
                        }
                        Assert.assertTrue("put " + i + ": pSafe " + row.pSafe + ", the user record"
                                + " ends at " + t.nextPos + ", the call's steps wrote " + steps
                                + " bytes, an iteration started: " + started,
                                row.pSafe >= atLeast);
                        Assert.assertTrue("put " + i + ": pSafe " + row.pSafe + " after the stream's"
                                + " length " + db.getStreamLength(),
                                row.pSafe <= db.getStreamLength());
                    }
                }
            }

            Assert.assertTrue("markings " + markings + ", after the call's records "
                    + afterRecords, afterRecords >= 5);
            db.close();
        }
        
        /**
         * Regression test for bergdb 015-53 (016-06's R7-F4): stop() comes while a user
         * transaction runs, after its record is appended and before reclaim's work for it
         * (Db.testHooks' transExecuted calls stop() as another thread would at that moment).
         * The step's read and internal transaction are refused, as the database is stopping;
         * execute() threw that DbStoppingException, which says the call was refused, but the
         * transaction was committed and was there after a restart. Now the call returns, and
         * the put is there after the restart.
         */
        @Nano
        public static void testStopDuringStepCommits() {
            long time = Clock.UNITS_PER_SEC;
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(time);
            MemoryStream ms = new MemoryStream();
            final Db db = Db.builder().testSetup(ms).clock(clock).startupDistance(2000).start();
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            final Reclaim rc = db.internal().reclaim();
            final boolean[] armed = {false};
            Db.testHooks = new Db.TestHooks() {
                public void transExecuted(Db.ExecuteData x) {
                    if (armed[0] && !x.trans.isInternal()) {
                        armed[0] = false;
                        db.stop();
                    }
                }
                public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}
                public void nodeTouched(Node node) {}
                public void nodeReplaced(Node node) {}
            };
            String key = null;
            byte[] v = null;
            try {
                java.util.Random r = new java.util.Random(1);
                for (int i = 0; i < 4000 && key == null; i++) {
                    time += Clock.UNITS_PER_SEC / 20;
                    clock.setTime(time);
                    IterationInfo cur = rc.currentIteration();
                    boolean step = cur != null && fractionOf(db.getStreamLength() + 150 
                            - cur.pStart, DEFAULT_INTERNAL_FRACTION) - cur.rewritten > 10000;
                    String k = "/k/" + r.nextInt(50);
                    byte[] value = new byte[1 + r.nextInt(60)];
                    value[0] = 42;
                    armed[0] = step;    // This put's transactionCompleted makes a step.
                    db.execute(db.trans().put(k, value).build());
                    if (step) {
                        Assert.assertTrue("the hook stopped the database", !armed[0]);
                        key = k;
                        v = value;
                    }
                }
            } finally {
                Db.testHooks = null;
                db.close();
            }
            Assert.assertTrue("no step was armed", key != null);
            
            Db d2 = Db.builder().testSetup(ms.copy()).start();
            try {
                byte[] got = d2.getOne(Long.MAX_VALUE, Keys.toSegments(key), d2.newGetData());
                Assert.assertTrue("the put's value after the restart", Arrays.equals(v, got));
            } finally {
                d2.close();
            }
        }
        
        /**
         * Reclaim's liveness with a queue before a key (bergdb 023-08, review C, 5.3, item 2,
         * testProbeQueueBeforeEndKey; its check, section 3): a queue of 1,000 keys, then "/z"
         * after it; then 200 puts at the tail and 200 deletes at the head a transaction. Each
         * step scans the keys live at the iteration's start, so the iteration ends within 2 x
         * (the data at tStart) / (the step's 16 kB) + 10 transactions: 1,000 KVs of 216 bytes
         * by the scan's measure, 37. On 2026-11-10 it ended in 22 on main, 15 with the upward
         * unlink; P8, which scanned at the step's time, never ended it (fault 13).
         */
        @Nano
        public static void testQueueBeforeAKeyEnds() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            Db db = Db.builder().testSetup().clock(clock).startupDistance(2000).start();
            Reclaim reclaim = db.internal().reclaim();
            byte[] v = new byte[100];
            int head = 100000, next = 100000;
            for (int i = 0; i < 5; i++) {
                Trans.Builder b = db.trans();
                for (int j = 0; j < 200; j++) {
                    b.put("/q/" + next++, v);
                }
                db.execute(b.build());
            }
            db.execute(db.trans().put("/z", "z").build());     // One key after the queue.
            
            db.setRetainDuration(1000 * Clock.UNITS_PER_SEC);    // Iterations, but no cut.
            time += Clock.UNITS_PER_SEC;
            clock.setTime(time);
            db.execute(db.trans().put("/a", "a").build());
            
            for (int i = 0; reclaim.lastDoneRow() == null; i++) {
                Assert.assertTrue("the iteration ends: " + i, i < 37);
                Trans.Builder b = db.trans();
                for (int j = 0; j < 200; j++) {
                    b.put("/q/" + next++, v);
                    b.delete("/q/" + head++);
                }
                db.execute(b.build());
            }
            db.stop();
        }
        
        /**
         * Random puts ahead of the scan do not stop an iteration (bergdb 023-08, review B, 2.6;
         * its check, sections 3 and 4.1, from 023-v8-fix's 0f4571fc, without P8's end key):
         * 500 keys, then 400 new keys a transaction between them. Each step scans the keys live
         * at the iteration's start, so the iteration ends within 30 transactions (7 on main
         * and with the fix on 2026-11-10; P8 took 449).
         */
        @Nano
        public static void testRandomPutsAheadDoNotSlowTheScan() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            Db db = Db.builder().testSetup().clock(clock).startupDistance(2000).start();
            Reclaim reclaim = db.internal().reclaim();
            byte[] v = new byte[100];
            for (int i = 0; i < 500; i += 20) {
                Trans.Builder b = db.trans();
                for (int j = i; j < i + 20; j++) {
                    b.put("/k/" + (10000 + j), v);
                }
                db.execute(b.build());
            }
            
            db.setRetainDuration(1000 * Clock.UNITS_PER_SEC);    // Iterations, but no cut.
            time += Clock.UNITS_PER_SEC;
            clock.setTime(time);
            db.execute(db.trans().put("/a", "a").build());
            
            java.util.Random r = new java.util.Random(1);
            int next = 0;
            for (int i = 0; reclaim.lastDoneRow() == null; i++) {
                Assert.assertTrue("the iteration ends: " + i, i < 30);
                Trans.Builder b = db.trans();
                for (int j = 0; j < 400; j++) {
                    b.put("/k/" + (10000 + r.nextInt(499)) + "-" + next++, v);
                }
                db.execute(b.build());
            }
            db.stop();
        }
        
        /** A key of the queue of the tests of bergdb 024-07: in key order by i. */
        private static String queueKey(int i) {
            return "/q/" + (100000000 + i);
        }
        
        /**
         * bergdb 024-07, the bound of a reclaim step: a step makes dirty the index nodes on
         * the paths of its own puts only, the values it rewrites and its row, however many
         * keys the database holds: here at most 63 index nodes for each of its puts, three
         * for each node of a path, taken as at most 20 nodes long, and three more, as
         * Db.checkDirtyNodes counts a put. The same bound with 2,000
         * and with 8,000 keys. A queue, keys in time order: each transaction puts 100 new keys
         * at the tail and deletes the 100 oldest, until three iterations are done; from the
         * second on an iteration has no user value to rewrite.
         * 
         * <p>Until 024-07 the last step of an iteration visited every index node from its
         * scan's last key to the end of the key space, every key put since the iteration began:
         * here one step with 1 put made 991 index nodes dirty with 2,000 keys and 4,180 with
         * 8,000 (2026-11-11); at 10M keys 772,454, a record of 206 MB (024-07, section 2).</p>
         */
        @Nano
        public static void testStepDirtiesItsPathsOnly() {
            final int nodesAPut = 3 * 20 + 3;
            for (final int n : new int[] {2000, 8000}) {
                CoreTestClock clock = new CoreTestClock();
                long time = Clock.UNITS_PER_SEC;
                clock.setTime(time);
                Db db = Db.builder().testSetup().clock(clock).maxNodeSize8()
                        .startupDistance(2000).start();
                Reclaim reclaim = db.internal().reclaim();
                byte[] v = new byte[100];
                int head = 0, next = 0;
                while (next < n) {
                    Trans.Builder b = db.trans();
                    for (int j = 0; j < 100; j++) {
                        b.put(queueKey(next++), v);
                    }
                    db.execute(b.build());
                }
                db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
                
                // Of the steps, the one with most dirty nodes above the bound: the excess, its
                // dirty nodes and its puts; and the steps.
                final long[] worst = new long[] {Long.MIN_VALUE, 0, 0, 0};
                Db.testHooks = new Db.TestHooks() {
                    public void transExecuted(Db.ExecuteData x) {
                        final Trans t = x.trans;
                        if (t.touch) {
                            final long excess = t.dirtiedNodes - (long) nodesAPut * t.kvs.length;
                            if (excess > worst[0]) {
                                worst[0] = excess;
                                worst[1] = t.dirtiedNodes;
                                worst[2] = t.kvs.length;
                            }
                            worst[3]++;
                        }
                    }
                    public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}
                    public void nodeTouched(Node node) {}
                    public void nodeReplaced(Node node) {}
                };
                try {
                    for (int i = 0; reclaim.getIterationCount() < 3; i++) {
                        Assert.assertTrue("three iterations, n=" + n + ": " + i, i < 20000);
                        time += Clock.UNITS_PER_SEC / 20;
                        clock.setTime(time);
                        Trans.Builder b = db.trans();
                        for (int j = 0; j < 100; j++) {
                            b.put(queueKey(next++), v);
                            b.delete(queueKey(head++));
                        }
                        db.execute(b.build());
                    }
                } finally {
                    Db.testHooks = null;
                    db.stop();
                }
                Assert.assertTrue("steps, n=" + n + ": " + worst[3], worst[3] >= 3 * n / 150);
                Assert.assertTrue("n=" + n + ": a step with " + worst[2] + " puts made "
                        + worst[1] + " index nodes dirty, more than " + nodesAPut + " a put",
                        worst[0] <= 0);
            }
        }
        
        /**
         * bergdb 024-07, the last step and the record limit. TransSeq.take takes a
         * transaction's dirty index nodes whole, in one record, and never a transaction whose
         * nodes do not fit in a record; Db.checkDirtyNodes refuses such a user transaction
         * before it changes anything, and leaves reclaim's steps to their own bound. Until
         * 024-07 an iteration's last step had none: its touch made dirty every index node
         * after its scan's last key. Here, with the record limit lowered to 200 kB, and a queue
         * of 6,000 keys in time order, the index nodes of the first iteration's last step did
         * not fit in a record (at 100 kB, as StoredTrans's own test lowers it): no record took
         * them, the startup pos stayed before the step for good (2.3 MB behind after 1,000
         * transactions more, with a startup distance of 2 kB, four iterations done), and
         * the stream was never cut, with no exception: the fault of a queue of about 100M
         * keys at the real limit, 2 GB (024-07, section 3). Now the startup pos passes the
         * last step within 100 transactions. 200 kB since the merges at the delete (bergdb
         * 024-21): Dag.dirtyNodeBound counts up to 922 index nodes, 179 kB, for the user's
         * transactions of 8 puts and 8 deletes at node size 8, and a limit of 100 kB refused
         * them. At 200 kB the test still has its fault: with the touch of a key range back
         * (Db.touchRange before 024-07) it fails, the startup pos 252,408 bytes behind after
         * 100 transactions (024-21's review, R5).
         */
        @Nano
        public static void testLastStepWithinRecordLimit() {
            final long saved = StoredTrans.recordLimit;
            StoredTrans.recordLimit = 200 * 1000;
            Db db = null;
            try {
                CoreTestClock clock = new CoreTestClock();
                long time = Clock.UNITS_PER_SEC;
                clock.setTime(time);
                db = Db.builder().testSetup().clock(clock).maxNodeSize8()
                        .startupDistance(2000).start();
                Reclaim reclaim = db.internal().reclaim();
                byte[] v = new byte[100];
                int head = 0, next = 0;
                while (next < 6000) {
                    Trans.Builder b = db.trans();
                    for (int j = 0; j < 20; j++) {
                        b.put(queueKey(next++), v);
                    }
                    db.execute(b.build());
                }
                db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
                
                for (int i = 0; reclaim.lastDoneRow() == null; i++) {
                    Assert.assertTrue("an iteration: " + i, i < 20000);
                    time += Clock.UNITS_PER_SEC / 20;
                    clock.setTime(time);
                    Trans.Builder b = db.trans();
                    for (int j = 0; j < 8; j++) {
                        b.put(queueKey(next++), v);
                        b.delete(queueKey(head++));
                    }
                    db.execute(b.build());
                }
                final long pEnd = reclaim.lastDoneRow().pEnd;
                for (int i = 0; db.internal().getStartupPosForEvict() < pEnd; i++) {
                    Assert.assertTrue("the startup pos passes the iteration's last step: after "
                            + i + " transactions it is " 
                            + (db.getStreamLength() - db.internal().getStartupPosForEvict())
                            + " bytes behind", i < 100);
                    time += Clock.UNITS_PER_SEC / 20;
                    clock.setTime(time);
                    Trans.Builder b = db.trans();
                    for (int j = 0; j < 8; j++) {
                        b.put(queueKey(next++), v);
                        b.delete(queueKey(head++));
                    }
                    db.execute(b.build());
                }
            } finally {
                StoredTrans.recordLimit = saved;
                if (db != null) {
                    db.stop();
                }
            }
        }
        
        /**
         * bergdb 024-07, the premise of a step that makes dirty its own paths only: a delete
         * unlinks the nodes it empties (Dag.deleteUpward), so no index node that a lookup
         * reaches is left without a live key below it, where no put would make it dirty
         * again and its version would stay below the cut (testDeletedKeysAfterCut, at a
         * larger size and at the first available time too). 600 short keys and 300 long
         * ones of several segments under three prefixes; then all but the last 20 short keys
         * and the long keys of two prefixes are deleted, in key order, which empties whole
         * subtrees and segment trees; then overwrites of the 20 short keys left, until three
         * cuts. On the cut stream, which refuses every read below the cut, in the running
         * database and after a restart: every key ever put has its value, or none, at the
         * first available time and at the latest, and scans at both times give the keys.
         */
        @Nano
        public static void testEmptiedSubtreesAfterCut() {
            CoreTestClock clock = new CoreTestClock();
            long time = Clock.UNITS_PER_SEC;
            clock.setTime(time);
            CutStream stream = new CutStream();
            Db db = startForCutTest(stream, clock);
            final java.util.Map<String, java.util.TreeMap<Long, byte[]>> model = 
                    new java.util.TreeMap<String, java.util.TreeMap<Long, byte[]>>();
            final java.util.List<String> keys = new java.util.ArrayList<String>();
            for (int i = 0; i < 600; i++) {
                keys.add("/k/" + (1000 + i));
            }
            for (int i = 0; i < 300; i++) {
                keys.add("/long/prefix-number-" + (i % 3) + "/and-a-second-long-segment/" 
                        + (1000 + i));
            }
            for (String k : keys) {
                model.put(k, new java.util.TreeMap<Long, byte[]>());
            }
            
            for (int i = 0; i < keys.size(); i += 30) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                Trans.Builder b = db.trans();
                for (int j = i; j < i + 30; j++) {
                    b.put(keys.get(j), StringUtil.toBytes("v" + j));
                }
                Trans t = b.build();
                db.execute(t);
                for (int j = i; j < i + 30; j++) {
                    model.get(keys.get(j)).put(t.tt, StringUtil.toBytes("v" + j));
                }
            }
            final java.util.List<String> deleted = new java.util.ArrayList<String>();
            for (int i = 0; i < keys.size(); i++) {
                if (i < 580 || (i >= 600 && i % 3 != 0)) {
                    deleted.add(keys.get(i));
                }
            }
            for (int i = 0; i < deleted.size(); i += 30) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                Trans.Builder b = db.trans();
                for (int j = i; j < Math.min(i + 30, deleted.size()); j++) {
                    b.delete(deleted.get(j));
                }
                Trans t = b.build();
                db.execute(t);
                for (int j = i; j < Math.min(i + 30, deleted.size()); j++) {
                    model.get(deleted.get(j)).put(t.tt, null);
                }
            }
            
            java.util.Random r = new java.util.Random(7);
            long cut = 0;
            int cuts = 0;
            for (int i = 0; i < 20000 && cuts < 3; i++) {
                time += Clock.UNITS_PER_SEC / 20;
                clock.setTime(time);
                String k = keys.get(580 + r.nextInt(20));
                byte[] v = StringUtil.toBytes("w" + i);
                Trans t = db.trans().put(k, v).build();
                db.execute(t);
                model.get(k).put(t.tt, v);
                if (stream.getCut() > cut) {
                    cut = stream.getCut();
                    cuts++;
                }
            }
            Assert.assertTrue("cuts: " + cuts, cuts >= 3);
            
            for (int pass = 0; pass < 2; pass++) {
                final long first = db.getFirstAvailableLookupTime();
                Assert.assertTrue("first available time " + first, first > Clock.UNITS_PER_SEC);
                for (long lt : new long[] {first, (first + time) / 2, time}) {
                    int live = 0;
                    for (String k : keys) {
                        java.util.Map.Entry<Long, byte[]> e = model.get(k).floorEntry(lt);
                        byte[] expected = e == null ? null : e.getValue();
                        Assert.assertArrayEquals("pass " + pass + ", " + k + " at " + lt, expected,
                                DbUtil.get(db, lt, k));
                        if (expected != null) {
                            live++;
                        }
                    }
                    GetMany g = db.newGetMany();
                    g.lookupTime = lt;
                    g.startKey = Keys.toSegments("/k/");
                    final int[] count = new int[1];
                    g.stopCondition = new GetMany.StopCondition() {
                        public int handleKvt(Kvt kvt) {
                            count[0]++;
                            return CONTINUE;
                        }
                        public void eod() {}
                    };
                    db.getMany(g);
                    Assert.assertEquals("pass " + pass + ", the scan at " + lt, live, count[0]);
                }
                if (pass == 0) {
                    db.sync(SyncLevel.ORDINARY);
                    db.stop();
                    clock = new CoreTestClock();
                    clock.setTime(time);
                    db = startForCutTest(stream.copy(), clock);
                }
            }
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
