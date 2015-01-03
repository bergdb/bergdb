package bergdb.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import bergdb.common.Bug;
import bergdb.common.StringMap;
import bergdb.common.Util;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Clock;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

// NOTE Could we make this class more testable (separate from Db?).

/**
 * This class handles stream space reclaim.
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
    private Iteration iteration;
        // Current ongoing iteration or null if none is ongoing.
    private long lastIterationPStart;
        // pStart of last iteration that completed, or 0 if no iteration has completed yet.
        // Used to limit iterations not to start too often.
    private long sposAtLastPretruncateCall;
    private static final String TABLE_KEY_NAME = DbConstants.INTERNAL_KEY_PREFIX + "dreclaim/-table.txt";
    private final long initialStartupDistance;
    
    // internalFraction is the fraction of the stream allowed to be occupied by
    // internal transactions compared to the total stream size while a reclaim iteration is running.
    // A small internalFraction will reduce the stream writes (reduce lastPos)
    // but increase the total stream size (lastPos - firstPos + 1).
    
    private static final double DEFAULT_INTERNAL_FRACTION = 0.25;
    private volatile double internalFraction;
        // internal fraction for the next iteration
    
    private volatile long retainDuration;
    
    private final Object readSynch;         // From DB.
    private final Object writeLock;         // From DB.
    
    private long firstAvailableLookupTime;
    private long firstAvailablePos;
    
    private volatile long iterationCount;   // The number of iterations completed.
    
    
    public Reclaim(Db db, AppendOnlyStream aos) {
        table = new IterationTable();
        tableKey = Keys.toSegments(TABLE_KEY_NAME);
        sposAtLastPretruncateCall = 0;
        if (db == null) {
            throw new IllegalArgumentException("db == null not allowed");
        }
        
        if (aos == null) {
            throw new IllegalArgumentException("aos == null not allowed");
        }
        this.db = db;
        this.aos = aos;
        this.initialStartupDistance = db.getStartupDistance();
        this.lastIterationPStart = 0;
        
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
     * Caller should have run: [synchronized (readSynch)] block recently to ensure the last
     * value is read.
     */
    public final long getFirstAvailableLookupTime() {
        return this.firstAvailableLookupTime;
    }
    
    public final long getFirstAvailablePos() {
        // Synch note: writes to firstAvailablePos is published by DB.readSynch unlock.
        //   Caller need to to DB.readSynch lock to ensure last value is read.
        return this.firstAvailablePos;
    }
    
    /**
     * Sets the internal fraction value to use for next iteration.
     * Must be between 0.001 and 0.90 inclusive.      
     */
    public void setInternalFraction(double internalFraction) {
        if (internalFraction < 0.001 || internalFraction > 0.90) {
            throw new IllegalArgumentException("Illegal internalFraction value, " + internalFraction);
        }
        
        this.internalFraction = internalFraction;
    }
    
    /**
     * Gets the internal fraction value to be used for the next iteration.
     */
    public double getInternalFraction() {
        return this.internalFraction;
    }
    
    public long getIterationCount() {
        return this.iterationCount;
    }
    
    /**
     * Called by Db after each transaction completed.
     * 
     * @throws StreamFormatException
     * @throws StreamIoException
     * @throws InternalDataException  If DB data "table.txt" is badly formatted.
     */
    public void transactionCompleted(Trans t) {
        final boolean isInternal = t.isInternal();
        long streamSize = t.nextPos;
            // This is correct since meta blocks are written eagerly by RecoverableStream.
        
        if (!isInternal && iteration == null && retainDuration != Long.MAX_VALUE) {
            // If 
            //   there is no on-going iteration (iteration == null) 
            //   AND t is a normal non-internal transaction
            //   AND streamSize is significantly larger than pStart of last iteration.
            //   AND retainDuration is not Long.MAX_VALUE.
            // Then
            //   Start a new iteration.
            //
            
            if (streamSize > lastIterationPStart + initialStartupDistance * 2) {
                this.iteration = new Iteration(t, this.internalFraction);
                
                // Adds row to iteration table and writes to db.
                
                lastIterationPStart = iteration.pStart;
                IterationInfo info = new IterationInfo();
                info.tStart = iteration.tStart;
                info.pStart = iteration.pStart;
                info.done = false;
                table.rows.add(info);
                
                String tableString = table.serialize();
                Trans t2 = db.trans().put(tableKey, Util.toBytes(tableString)).build();
                t2.isInternal = true;
                try {
                    db.execute(t2);
                } catch (RerunException e) {
                    throw new Bug("Rerun for write-only trans unexpected, " + e.getMessage());
                }
                
            }
        }
        
        if (iteration != null) {
            if (isInternal) {
                iteration.gotInternal(t);
            } else {
                iteration.gotExternal(t);
                
                if (iteration.done) {
                    this.iterationCount++;
                    iteration.tEnd = t.time;

                    IterationInfo info = table.rows.get(table.rows.size() - 1);
                   
                    if (info.tStart != iteration.tStart) {
                        throw new Bug("tStart should be equal, " + info.tStart + ", " + iteration.tStart);
                    }
                    
                    if (info.pStart != iteration.pStart) {
                        throw new Bug("pStart should be equal, " + info.pStart + ", " + iteration.pStart);
                    }
                    
                    info.tEnd = iteration.tEnd;
                    info.kvCount = iteration.kvCount;
                    info.done = true;
                    
                    if (iteration.lastKey != null) {
                        info.lastKey = new long[iteration.lastKey.length];
                        System.arraycopy(iteration.lastKey, 0, info.lastKey, 0, iteration.lastKey.length);
                    }
                    
                    String tableString = table.serialize();
                    Trans t2 = db.trans().put(tableKey, Util.toBytes(tableString)).build();
                    t2.isInternal = true;
                    try {
                        db.execute(t2);
                    } catch (RerunException e) {
                        throw new Bug("RerunException for write-only trans unexpected, " 
                                + e.getMessage());
                    }
                    
                    pretruncateIfPossible(t.time);
                    
                    iteration = null;
                }
            }
        }
        
        // Calls pretruncateIfPossible once in a while. It is not called every time this method
        // is executed for performance reasons.
        // Also stores the iteration table at the same time.
        
        if (!isInternal && streamSize - this.sposAtLastPretruncateCall > 2 * initialStartupDistance) {
            this.sposAtLastPretruncateCall = streamSize;
            pretruncateIfPossible(t.time);
            
            if (iteration != null && table.rows.size() > 0) {
                
                // Updates last key. Used to be able to continue iteration over db restarts.
                
                IterationInfo info = table.rows.get(table.rows.size() - 1);
                
                if (iteration.lastKey != null) {
                    info.lastKey = new long[iteration.lastKey.length];
                    System.arraycopy(iteration.lastKey, 0, info.lastKey, 0, iteration.lastKey.length);
                    
                    String tableString = table.serialize();
                    Trans tt = db.trans().put(tableKey, Util.toBytes(tableString)).build();
                    tt.isInternal = true;
                    
                    try {
                        db.execute(tt);
                    } catch (RerunException e) {
                        throw new Bug("Unexpected to get RerunException for write-only transaction, " 
                                + e.getMessage());
                    }
                }
            }
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
            String s = Util.toString(value);
            table.parse(s);  // throws InternalDataException
        }
        
        if (table.rows.size() > 0) {
            IterationInfo lastRow = table.rows.get(table.rows.size() - 1);
            if (!lastRow.done)  {
                iteration = new Iteration(lastRow, this.internalFraction);
            }
        }
        
        this.sposAtLastPretruncateCall = db.getStreamLength();
            // Run a bit before first reclaim iteration.
        
        long maxPos = 0;
        long maxTime = 0;
        
        for (int i = 0; i < table.rows.size(); i++) {
            IterationInfo row = table.rows.get(i);
            if (row.done) {
                if (row.pStart > maxPos) {
                    maxPos = row.pStart;
                    maxTime = row.tStart;
                }
            }
        }
        
        synchronized (readSynch) {
            this.firstAvailableLookupTime = maxTime;
            this.firstAvailablePos = maxPos;
        }
    }
    
    /**
     * @throws StreamIoException
     */
    private void pretruncateIfPossible(long timeNow) {
        assert Thread.holdsLock(this.writeLock);
        
        final long tRetain = db.getRetainDuration();
        final long posOfLastValidMetaBlock = db.getPosOfLastValidMetaBlock();
        long maxTruncatePos = -1;
        long newFirstAvailableLookupTime = -1;
        
        // Finds max truncate pos if possible to truncate.
        
        for (int i = 0; i < table.rows.size(); i++) {
            IterationInfo row = table.rows.get(i);
            
            if (row.done) {
                long truncatePos = row.pStart;
                if (timeNow - tRetain > row.tEnd 
                        && posOfLastValidMetaBlock >= truncatePos) {
                    
                    if (truncatePos > maxTruncatePos) {
                        maxTruncatePos = truncatePos;
                        newFirstAvailableLookupTime = row.tStart;
                    }
                }
            }
        }
        
        if (maxTruncatePos != -1) {
            
            // Here, we should wait for all get operations to finish before calling
            // pretruncate(). 
            // Or rather we would like to wait for any get operation that uses a 
            // lookupTime < firstAvailableLookupTime if any such operation is executing.
            // We have no such knowledge.
            // To solve this, we could schedule a future task of pretruncate. 
            // This task would execute in a later call to transactionCompleted().
            
            synchronized (readSynch) {
                assert newFirstAvailableLookupTime != -1;
                this.firstAvailableLookupTime = newFirstAvailableLookupTime;
                this.firstAvailablePos = maxTruncatePos;
            }
            
            try {
                Thread.sleep(20);
                    //
                    // Ugly sleep instead of future task.
                    // Intends to increase the probability that read operations that have a 
                    // lookup time < newFirstAvailableLookupTime finish before the pretruncate call.
                    //
            } catch (InterruptedException e) {
                // empty
            }
            
            try {
                aos.pretruncate(maxTruncatePos);
            } catch (IOException e) {
                throw new StreamIoException(e);
            }
        }
        
        if (maxTruncatePos != -1) {
            // Removes rows no longer needed.
            
            for (int i = 0; i < table.rows.size(); i++) {
                IterationInfo row = table.rows.get(i);
                
                if (row.pStart < maxTruncatePos) {
                    table.rows.remove(i);
                    i--;      // we need to run same index again since we removed one
                }
            }
        }
    }
    
    /**
     * Information about an iteration, completed (done=true) or ongoing (done=false). 
     * The information can be serialized to a string and parse back from such a string.
     */
    final class IterationInfo {
        long pStart;
        long tStart;
        long tEnd;
        long kvCount;       // total number of KVs in the database for the iteration lookup time
        long[] lastKey;     // Last key that was iterated, or null if none was iterated.
        boolean done;
        
        /**
         * Serializes data to a string.
         */
        public String serialize() {
            // Note, lastKey = null is serialized in a special way.
            
            StringMap m = new StringMap();
            m.put("pStart", "" + pStart);
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
            
            if ( !("true".equals(doneString)) || "false".equals(doneString)) {
                throw new InternalDataException("Bad value of 'done' in " + TABLE_KEY_NAME 
                        + ", " + doneString);
            }
            
            if (doneString.equals("true")) {
                done = true;
            }
        }
        
        private long getLong(StringMap m, String key) {
            if (!m.hasLong(key)) {
                throw new InternalDataException("Missing or non-long key '" + key + "' from " 
                        + TABLE_KEY_NAME + ". Table string map: " + m.serialize());
            }
            return m.getLong(key);
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
            StringBuilder b = new StringBuilder();
            
            for (IterationInfo info : rows) {
                b.append(info.serialize() + "----next----\n");
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
     * Represents a single iteration over all the data in the database.
     */
    class Iteration {
        long pStart;
        long tStart;
        long tEnd;
        long kvCount;       
            // total number of KVs in the database for the iteration lookup time
        long[] lastKey;     
            // Last key that was iterated (key segments), or null if none was iterated.
            // This array must not have length 0.
        long totalExternalTransactionSize;
            // Total stream size occupied by external transactions during this iteration.
        long totalInternalTransactionSize;
            // Total stream size occupied by internal transactions during this iteration.
        boolean done;
        final double internalFractionForIteration;
        
        public Iteration(IterationInfo info, double internalFraction) {
            pStart = info.pStart;
            tStart = info.tStart;
            tEnd = info.tEnd;
            kvCount = info.kvCount;
            assert info.lastKey == null || info.lastKey.length > 0 
                    : "info.lastKey.length = " + info.lastKey.length;
            lastKey = info.lastKey;
            totalExternalTransactionSize = 0;
            totalInternalTransactionSize = 0;
            done = info.done;
            assert internalFraction >= 0.001;
            assert internalFraction <= 0.90;
            this.internalFractionForIteration = internalFraction;
        }
        
        public Iteration(Trans t, double internalFraction) {
            pStart = t.nextPos;
            tStart = t.time;
            tEnd = -1;
            kvCount = 0;
            lastKey = null;
            totalExternalTransactionSize = 0;
            totalInternalTransactionSize = 0;
            done = false;
            assert internalFraction >= 0.001;
            assert internalFraction <= 0.90;
            this.internalFractionForIteration = internalFraction;
        }
        
        public final void gotInternal(Trans t) {
            totalInternalTransactionSize += (t.lastPos - t.pos + 1);
        }
        
        public final void gotExternal(Trans t) {
            // reclaimSize is the size currently allowed for space reclaim transactions.
            
            totalExternalTransactionSize += (t.lastPos - t.pos + 1);
            long total = totalExternalTransactionSize + totalInternalTransactionSize;
            
            long reclaimSize = (long) ((total * internalFractionForIteration) - totalInternalTransactionSize);
            
            // Wait to "bunch up" the transactions a bit. Performance-wise it should make sense.
            
            //if (reclaimSize > 100*1000L) {  // 55 us (test.Set)
            if (reclaimSize > 10*1000L) {     // 
            //if (reclaimSize > 1*1000L) {      // 49
                step(reclaimSize);
            }
        }
        
        private void step(final long writeSize) {
            final long[][] lastKeyOfStep = new long[][] {this.lastKey};
                    // final and extra "[]" to be able to use in anonymous class below
            
            GetMany g = db.newGetMany();
            g.startKey = lastKey;
            assert g.startKey == null || g.startKey.length > 0 
                    : "g.startKey.length = " + g.startKey.length;
            g.inclusive = false;
            g.lookupTime = tStart;

            g.stopCondition = new GetMany.StopCondition() {
                private long size = 0;
                    // An approximation of the stream space the KVs of the step.
                    // Used for get a suitable step chunk size.
                
                public int handleKvt(Kvt kvt) {
                    int result;

                    size += kvt.key.length * 8;     // approximate
                    size += kvt.value.length;
                    size += 100;                    // estimated overhead
                    
                    kvCount++;
                    lastKeyOfStep[0] = kvt.key;
                    result = size > writeSize ? ADD_AND_STOP : ADD;
                    
                    return result;
                }
                
                public void eod() {
                    done = true;
                }
            };
            
            db.getMany(g);
            if (g.result.size() == 0) {
                return;
            }
            
            Trans.Builder b = db.trans();
            long stepLookupTime = -1;
            
            for (Kvt kvt : g.result) {
                GetData gd = db.newGetData();
                byte[] value;
                
                if (stepLookupTime == -1) {         // BUG Fixed 130131, was "1" instead of "-1".
                    value = db.getOne(Long.MAX_VALUE, kvt.key, gd);
                    stepLookupTime = gd.actualLookupTime;
                } else {
                    value = db.getOne(stepLookupTime, kvt.key, gd);
                }
                
                // If KV still exists and has not been modified since tStart, it is rewritten
                // to the stream.
                
                if (value != null && gd.kvTime <= tStart) {
                    b.keyRead(kvt.key);
                    b.put(kvt.key, kvt.value);  // Note, no mem copy of key and value.
                }
            }
            
            Trans t = b.build();
            t.readTime = stepLookupTime;
            t.isInternal = true;
            
            try {
                db.execute(t);
            } catch (RerunException e) {
                // empty, will be run again since lastKey not updated if exception thrown.
                return;
            }
            
            this.lastKey = lastKeyOfStep[0];
            assert this.lastKey.length > 0 : "lastKey.length = " + lastKey.length;
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
            int size = 20;
            
            Db db = Db.builder().testSetup().mainStream(stream).clock(clock)
                    .startupDistance(100*1000).start();
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            
            for (int i = 0; i < size; i++) {
                long time = (i + 1) * Clock.UNITS_PER_SEC;
                clock.setTime(time);
                Trans t = db.trans().put("k", value).build();
                db.execute(t);
            }
            
            Assert.assertTrue("" + ints[0], ints[0] > 0);
            Assert.assertTrue("" + ints[1], ints[1] > value.length);
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
