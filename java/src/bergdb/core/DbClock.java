package bergdb.core;

import static bergdb.nanotest.Assert.assertEquals;
import bergdb.dag.Klong;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbException;

/**
 * <p>A special clock for Db that implements a lookup time / transaction time concept. 
 * The lookup time is always strictly less than the transaction time of a currently 
 * running transaction. This is required; we must not read the state at time t1 if a 
 * transaction is currently modifying the state at time t1.
 * The lookup time is also strictly less than the transaction time of any 
 * future transaction. This is a useful property. A database read at time t2 will 
 * always return the same values. A future transaction cannot change this.
 * [time, key, value] tuples are immutable.</p>
 * 
 * @author Frans Lundberg
 */
public class DbClock {
    //
    // Serial transactions assumed. transactionBegin() / transactionEnd() used to 
    // mark the beginning and end of a transaction execution.
    // 
    
    private final Clock clock;
    
    /** 
     * Transaction time of the last completed transaction. 
     * "volatile" is essential here.
     */
    private volatile long lastTransactionTime;
    
    /** 
     * Transaction time of the currently running transaction. 
     * Only meaningful when transactionRunning == true.
     */
    private long transactionTime;
    
    private long lastReadTime;
    
    /** True iff a transaction is currently executing. */
    private boolean transactionRunning;
    
    /**
     * Creates a new instance based on the given Clock.
     * The clock's getTime() method must return non-decreasing time values, 
     * but not necessarily strictly increasing values.
     */
    public DbClock(Clock clock) {
        if (clock == null) {
            throw new IllegalArgumentException("clock == null not allowed");
        }
        this.clock = clock;
        this.lastTransactionTime = 0;
        this.lastReadTime = 0;
        this.transactionRunning = false;
    }
    
    /**
     * Returns the actual lookup time to use internally for a read operation given the 
     * lookup time wanted by the database user.
     * The method does not return the current time and does not call clock.getTime() 
     * (which is important for performance).
     * The returned time is less than or equal to the transaction time of the last 
     * completed transaction.
     */
    public final long lookupTime(final long wantedLookupTime) {
        //
        // Returns the "internal" or "actual" lookup time.
        // We do not need a lock here, we just read a volatile long.
        // this is OK since lastWriteTime is strictly increasing and a read from a volatile long
        // is atomic.
        // Not using "synchronized" here improves performance with 0.7% for serial GETs. More is 
        // expected for parallel access, of course.
        // Note, avoiding a call to clock.getTime() is important for performance. 
        // System.currentTimeMillis() is very slow.
        //
        
        final long last = this.lastTransactionTime;
        long result = wantedLookupTime > last ? last : wantedLookupTime;
        return result;
    }
    
    /**
     * Returns the current database time. 
     * The returned time can be used as the lookup time when reading from the database.
     * The returned time is guaranteed to be less than the transaction time of a 
     * currently executing transaction (if one is executing) and less than the 
     * transaction time of any future transaction.
     * The returned time is also greater than or equal to the transaction time of the last
     * completed transaction.
     */
    public final synchronized long currentTime() {
        //
        // The code [transactionTime - 1] is OK. transactionTime is >= 1.
        //
        
        long time;
        
        if (transactionRunning) {
            time = transactionTime - 1;
        } else {
            time = clock.getTime();
            time = time < lastTransactionTime ? lastTransactionTime : time;
            lastReadTime = time;
        }
        
        return time;
    }
    
    /**
     * Notifies this object that a new write transaction is about to start.
     * The transaction time of the new transaction is returned. 
     * The returned time is guaranteed to be strictly larger than any
     * previous read time and any previous transaction time returned by this object.
     * 
     * @return The transaction time of the new transaction, always greater than or equal to 1.
     */
    public final synchronized long transactionBegin() {
        assert !transactionRunning;
        final long clockTime = clock.getTime();
        long time = clockTime;
        time = time > lastTransactionTime ? time : lastTransactionTime + 1;
        time = time > lastReadTime ? time : lastReadTime + 1;
        
        // 2026-10-21 (bergdb 005-18): a time outside 0 to 2^56 - 1 is refused before the
        // transaction begins. A TIME klong keeps 56 bits, and a top node with a larger time
        // is refused at startup ("Time too large"), so the database could not start again.
        if (clockTime < Klong.MIN_TIME || clockTime > Klong.MAX_TIME) {
            throw new DbException("The clock's time, " + clockTime + ", is outside the range "
                    + "of database times, 0 to " + Klong.MAX_TIME + " (100 ns units since 1970;"
                    + " see Clock.getTime). No transaction is executed.");
        }
        if (time > Klong.MAX_TIME) {
            throw new DbException("No database time is left after " + (time - 1) 
                    + "; the largest is " + Klong.MAX_TIME + ". No transaction is executed.");
        }
        
        transactionTime = time;
        transactionRunning = true;
        assert transactionTime > 0;
        return time;
    }
    
    /**
     * Must always be called when a write transaction has completed.
     */
    public final synchronized void transactionEnd() {
        assert transactionRunning;
        lastTransactionTime = transactionTime;
        transactionRunning = false;
    }

    /**
     * Used for initialization when an existing database is started.
     */
    public synchronized void setLastTransTime(long lastTransTime) {
        assert !transactionRunning;
        lastTransactionTime = lastTransTime;
    }
    
    
    // ======== Testing ========
    
    /** For testing only. Factor "F". */
    private static long F = 10*1000;
    
    @Nano
    private static void test1() {
        CoreTestClock testClock = new CoreTestClock();
        DbClock dbClock = new DbClock(testClock);
        
        testClock.setTime(1*F);
        long transactionTime = dbClock.transactionBegin();
        dbClock.transactionEnd();
        
        assertEquals(1*F, transactionTime);
    }
    
    @Nano
    private static void testTime() {
        CoreTestClock testClock = new CoreTestClock();
        DbClock dbClock = new DbClock(testClock);
        
        testClock.setTime(1*F);
        
        long time1 = dbClock.currentTime();
        long time2 = dbClock.currentTime();
        
        long transactionTime = dbClock.transactionBegin();
        
        long time3 = dbClock.currentTime();
        
        dbClock.transactionEnd();
        
        long time4 = dbClock.currentTime();
        
        assertEquals(1*F, time1);
        assertEquals(1*F, time2);
        assertEquals(1*F, time3);
        assertEquals(1*F + 1, time4);
        assertEquals(1*F + 1, transactionTime);
    }
    
    /** bergdb 005-18: a clock time outside the database's range is refused. */
    @Nano
    private static void testClockOutOfRange() {
        CoreTestClock testClock = new CoreTestClock();
        DbClock dbClock = new DbClock(testClock);
        testClock.setTime(Klong.MAX_TIME + 1);
        try {
            dbClock.transactionBegin();
            throw new AssertionError("a time above the range was given");
        } catch (DbException e) {
            assertEquals(true, e.getMessage().contains("outside the range"));
        }
        
        CoreTestClock testClock2 = new CoreTestClock();
        testClock2.setTime(1000);
        DbClock dbClock2 = new DbClock(testClock2);
        dbClock2.setLastTransTime(Klong.MAX_TIME);
        try {
            dbClock2.transactionBegin();
            throw new AssertionError("a time above the range was given");
        } catch (DbException e) {
            assertEquals(true, e.getMessage().contains("No database time is left"));
        }
    }
    
    @Nano
    private static void testLookupTime() {
        CoreTestClock testClock = new CoreTestClock();
        DbClock dbClock = new DbClock(testClock);
        
        testClock.setTime(1*F);
        dbClock.transactionBegin();
        dbClock.transactionEnd();
        testClock.setTime(2*F);
        
        assertEquals(100, dbClock.lookupTime(100));
        assertEquals(1*F, dbClock.lookupTime(Long.MAX_VALUE));
        assertEquals(1*F, dbClock.lookupTime(1*F));
        
        dbClock.transactionBegin();
        
        assertEquals(100, dbClock.lookupTime(100));
        assertEquals(1*F, dbClock.lookupTime(Long.MAX_VALUE));
        assertEquals(1*F, dbClock.lookupTime(1*F));
        
        dbClock.transactionEnd();
        
        assertEquals(100, dbClock.lookupTime(100));
        assertEquals(2*F, dbClock.lookupTime(Long.MAX_VALUE));
        assertEquals(1*F, dbClock.lookupTime(1*F));
        
    }
    
}

/*

140725 Now using "lookup time" instead of "read time".
140722 Wrote some units tests.
140722 Using "transaction time" instead of "write time". More well-defined.

*/
