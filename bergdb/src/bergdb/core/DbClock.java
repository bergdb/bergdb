package bergdb.core;

import static bergdb.nanotest.Assert.assertEquals;
import bergdb.nanotest.T;
import bergdb.pub.Clock;

/**
 * <p>A special clock for Db that implements a read time / transaction time concept. 
 * The read time is always strictly less than the transaction time of a currently 
 * running transaction. This is required, we cannot read the state at time t1 if a 
 * transaction is currently modifying the state at time t1.</p>
 * 
 * <p>This class also implements timeForRead(wantedTime). The time returned by this method is
 * the actual lookup time to use given a wanted lookup time. If the wanted lookup time
 * is in the future, the lastWriteTime is returned, otherwise the wanted lookup time
 * is returned.</p>
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
     * "volatile" is required.
     */
    private volatile long lastTransactionTime;
    
    /** 
     * Transaction time of the currently running transaction. 
     * Only used when transactionRunning == true.
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
     * Returns the clock that this DbClock is based on; 
     * the clock passed as a parameter to the constructor.
     */
    public Clock getBaseClock() {
        return this.clock;
    }
    
    /**
     * Returns the time to use internally for a read operation given the wanted lookup time.
     * The method does not return the current time and does not call clock.getTime() 
     * (which is important for performance).
     * The returned time is less than or equal to the write time (transaction time)
     * of the last completed transactions.
     */
    public final long timeForRead(final long wantedTime) {
        // We do not need a lock here, we just read a volatile long.
        // this is OK since lastWriteTime is strictly increasing and a read from a volatile long
        // is atomic.
        // Not using "synchronized" here improves performance with 0.7% for serial GETs. More is 
        // expected for parallel access, of course.
        // Note, avoiding a call to clock.getTime() is important for performance. 
        // System.currentTimeMillis() is very slow.
        
        final long last = this.lastTransactionTime;
        return wantedTime > last ? last : wantedTime;
    }
    
    /**
     * Returns the current database time useful for reading from the database (as the lookup time). 
     * The returned time is guaranteed to be less than 
     * the transaction time of a currently executing transaction (if one is executing) and less
     * than the transaction time of any future transaction.
     * The returned time is also greater than or equal to the transaction time of the last
     * completed transaction.
     */
    public final synchronized long time() {
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
        long time = clock.getTime();
        time = time > lastTransactionTime ? time : lastTransactionTime + 1;
        time = time > lastReadTime ? time : lastReadTime + 1;
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
    
    @T
    private static void test1() {
        CoreTestClock testClock = new CoreTestClock();
        DbClock dbClock = new DbClock(testClock);
        
        testClock.setTime(1*F);
        long transactionTime = dbClock.transactionBegin();
        dbClock.transactionEnd();
        
        assertEquals(1*F, transactionTime);
    }
    
    @T
    private static void testGetTime() {
        CoreTestClock testClock = new CoreTestClock();
        DbClock dbClock = new DbClock(testClock);
        
        testClock.setTime(1*F);
        
        long time1 = dbClock.time();
        long time2 = dbClock.time();
        
        long transactionTime = dbClock.transactionBegin();
        
        long time3 = dbClock.time();
        
        dbClock.transactionEnd();
        
        long time4 = dbClock.time();
        
        assertEquals(1*F, time1);
        assertEquals(1*F, time2);
        assertEquals(1*F, time3);
        assertEquals(1*F + 1, time4);
        assertEquals(1*F + 1, transactionTime);
    }
    
    @T
    private static void testTimeForRead() {
        CoreTestClock testClock = new CoreTestClock();
        DbClock dbClock = new DbClock(testClock);
        
        testClock.setTime(1*F);
        dbClock.transactionBegin();
        dbClock.transactionEnd();
        testClock.setTime(2*F);
        
        assertEquals(100, dbClock.timeForRead(100));
        assertEquals(1*F, dbClock.timeForRead(Long.MAX_VALUE));
        assertEquals(1*F, dbClock.timeForRead(1*F));
        
        dbClock.transactionBegin();
        
        assertEquals(100, dbClock.timeForRead(100));
        assertEquals(1*F, dbClock.timeForRead(Long.MAX_VALUE));
        assertEquals(1*F, dbClock.timeForRead(1*F));
        
        dbClock.transactionEnd();
        
        assertEquals(100, dbClock.timeForRead(100));
        assertEquals(2*F, dbClock.timeForRead(Long.MAX_VALUE));
        assertEquals(1*F, dbClock.timeForRead(1*F));
        
    }
    
}

/*

140722 Wrote some units tests.
140722 Using "transaction time" instead of write time. More well-defined.

*/
