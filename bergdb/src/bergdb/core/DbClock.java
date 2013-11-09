package bergdb.core;

import bergdb.pub.Clock;

/**
 * A special clock for DB that implements a read-time / write-time concept. 
 * The read time is always strictly less then the transaction time (the write time) of a currently 
 * running transaction when a transaction is running.
 * This is required, we cannot read the state at time t1 if a transaction
 * is currently modifying the state at time t1.
 * The read time will then never be larger than t1 - 1 while a transaction is running
 * at transaction time t1.
 * 
 * @author Frans Lundberg
 */
public class DbClock {
    //
    // Serial transactions assumed.
    //
    
    private Clock clock;
    private volatile long lastWriteTime;    // Transaction time of last completed transaction.
    private long transWriteTime;            // Transaction time currently running transaction.
    private long lastReadTime;
    private boolean transactionRunning;
    
    public DbClock(Clock clock) {
        if (clock == null) {
            throw new IllegalArgumentException("clock == null not allowed");
        }
        this.clock = clock;
        this.lastWriteTime = 0;
        this.lastReadTime = 0;
        this.transactionRunning = false;
    }
    
    /**
     * Returns the base clock that DBClock is based on - 
     * the clock passed as a parameter to the constructor.
     */
    public Clock getBaseClock() {
        return this.clock;
    }
    
    /**
     * Returns a time to use for a GET lookup given the wanted lookup time.
     * The method does not return the current time.
     */
    public final long timeForGet(final long wantedTime) {
        // We do not need a lock here, we just read a volatile long.
        // this is OK since lastWriteTime is strictly increasing and a read from a volatile long
        // is atomic.
        // Not using "synchronized" here improved performance with 0.7% for serial GETs. More is 
        // expected for parallel access, of course.
        // Note, avoiding a call to clock.getTime() is important for performance. 
        // System.currentTimeMillis() is slow.
        
        final long last = this.lastWriteTime;
        return wantedTime > last ? last : wantedTime;
    }
    
    /**
     * Returns the current read time. The returned time is guaranteed to be strictly less then 
     * the transaction time of a currently executing transaction (if one is executing) and less
     * then the transaction time of any future transaction.
     */
    public final synchronized long getTime() {
        long time = clock.getTime();
        if (transactionRunning) {
            time = time < lastWriteTime ? time : lastWriteTime;
        }
        lastReadTime = time;
        return time;
    }
    
    /**
     * Notifies this object that a new write transaction is about to start.
     * A new write time is returned. The returned time is guaranteed to be strictly larger than any
     * previous read time or write time returned by this object.
     */
    public final synchronized long transactionBegin() {
        assert !transactionRunning;
        long time = clock.getTime();
        time = time > lastWriteTime ? time : lastWriteTime + 1;
        time = time > lastReadTime ? time : lastReadTime + 1;
        transWriteTime = time;
        transactionRunning = true;
        return time;
    }
    
    /**
     * Must always be called when a write transaction has completed.
     */
    public final synchronized void transactionEnd() {
        assert transactionRunning;
        lastWriteTime = transWriteTime;
        transactionRunning = false;
    }

    /**
     * Used for initialization when an existing database is started.
     */
    public synchronized void setLastTransTime(long lastTransTime) {
        assert !transactionRunning;
        lastWriteTime = lastTransTime;
    }
}
