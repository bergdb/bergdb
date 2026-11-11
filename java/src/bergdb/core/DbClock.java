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
     * The clock's getTime() may return equal or decreasing time values: the times of this
     * object never decrease (Clock.getTime()).
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
     * completed transaction, and to every time returned before: it is the clock's time, or,
     * when that is earlier, or after LAST_USER_TIME, the last time returned or the last
     * transaction's time (bergdb 020-23, Z1; 021-26). A clock after LAST_USER_TIME, out of
     * range or in the margin, uses up no time, as a user transaction then is refused.
     */
    public final synchronized long currentTime() {
        //
        // The code [transactionTime - 1] is OK. transactionTime is >= 1, and greater than
        // lastReadTime and every time returned before.
        //
        // 2026-11-09 (bergdb 020-23, Z1): lastReadTime never decreases. A clock that went back
        // set it to its earlier time, so that a later transaction could take a time before a
        // time returned, and a read at that time changed. The clock's time is taken at most
        // as LAST_USER_TIME: a user transaction after that is refused anyway, and a time in
        // the margin, or out of range, would take the times kept for reclaim's internal
        // transactions after a user's (bergdb 015-55).
        //
        // 2026-11-09 (bergdb 021-26): a clock's time after LAST_USER_TIME is not taken; the
        // time is the last time returned or the last transaction's. Capped, it gave
        // LAST_USER_TIME and kept it as lastReadTime, so every user transaction after it
        // was refused until a restart, also when the clock was back in the range: a
        // currentTime() while the clock was out of range used up the user transactions' times,
        // which a transaction then, refused, does not.
        //
        
        long time;
        
        if (transactionRunning) {
            // Kept as a time handed out (bergdb 024-16): if the transaction is refused
            // (transactionCancel()), the next one still takes a later time than this.
            time = transactionTime - 1;
            lastReadTime = time > lastReadTime ? time : lastReadTime;
        } else {
            time = clock.getTime();
            time = time > LAST_USER_TIME ? lastTransactionTime : time;
            time = time < lastTransactionTime ? lastTransactionTime : time;
            time = time < lastReadTime ? lastReadTime : time;
            lastReadTime = time;
        }
        
        return time;
    }
    
    /**
     * The database times below Klong.MAX_TIME that are left when user transactions are
     * refused (bergdb 015-55): room for the internal transactions that run after a user
     * transaction, reclaim's, at most five today, each at a later time than the one before;
     * as Db's TOP_ORDINAL_MARGIN keeps top node ordinals for them (bergdb 005-02).
     */
    static final long TIME_MARGIN = 1024;
    
    /** The last time of a user transaction (bergdb 015-55); the later ones are reclaim's. */
    static final long LAST_USER_TIME = Klong.MAX_TIME - TIME_MARGIN;
    
    /**
     * Notifies this object that a new write transaction is about to start.
     * The transaction time of the new transaction is returned. 
     * The returned time is guaranteed to be strictly larger than any
     * previous read time and any previous transaction time returned by this object.
     * 
     * @param user  True for a user transaction, which is refused after LAST_USER_TIME;
     *      false for an internal one, refused after Klong.MAX_TIME (bergdb 015-55).
     * @return The transaction time of the new transaction, always greater than or equal to 1.
     * @throws DbException  If the clock is out of range, or no time is left; then no
     *      transaction has begun.
     */
    public final synchronized long transactionBegin(boolean user) {
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
        // 2026-11-05 (bergdb 015-55): a user transaction leaves the last times to reclaim's
        // internal transactions after it, which run after its go point; one of them that
        // found no time left failed the database.
        if (user && time > LAST_USER_TIME) {
            throw new DbException("No database time is left for a user transaction: its time "
                    + "would be " + time + ", after the last, " + LAST_USER_TIME + " (the times"
                    + " up to " + Klong.MAX_TIME + " are kept for reclaim's internal "
                    + "transactions). No transaction is executed.");
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
     * Ends a write transaction that was refused after transactionBegin(), before its go
     * point, when nothing of it has changed (bergdb 024-16: Db.transformKeys): its time is
     * given back, not made the last transaction's, so the next transaction may take the same
     * time. A time that currentTime() handed out while it ran is kept (lastReadTime), so the
     * next transaction's time is later than every time handed out, as always.
     */
    public final synchronized void transactionCancel() {
        assert transactionRunning;
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
        long transactionTime = dbClock.transactionBegin(true);
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
        
        long transactionTime = dbClock.transactionBegin(true);
        
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
            dbClock.transactionBegin(true);
            throw new AssertionError("a time above the range was given");
        } catch (DbException e) {
            assertEquals(true, e.getMessage().contains("outside the range"));
        }
        
        CoreTestClock testClock2 = new CoreTestClock();
        testClock2.setTime(1000);
        DbClock dbClock2 = new DbClock(testClock2);
        dbClock2.setLastTransTime(Klong.MAX_TIME);
        try {
            dbClock2.transactionBegin(true);
            throw new AssertionError("a time above the range was given");
        } catch (DbException e) {
            assertEquals(true, e.getMessage().contains("No database time is left"));
        }
    }
    
    /**
     * bergdb 015-55: a user transaction is refused after LAST_USER_TIME, and an internal one,
     * reclaim's after it, still has a time, up to Klong.MAX_TIME.
     */
    @Nano
    private static void testTimeMarginForInternal() {
        CoreTestClock testClock = new CoreTestClock();
        DbClock dbClock = new DbClock(testClock);
        testClock.setTime(LAST_USER_TIME);
        assertEquals(LAST_USER_TIME, dbClock.transactionBegin(true));
        dbClock.transactionEnd();
        assertEquals(LAST_USER_TIME + 1, dbClock.transactionBegin(false));
        dbClock.transactionEnd();
        try {
            dbClock.transactionBegin(true);
            throw new AssertionError("a user transaction after the last user time was taken");
        } catch (DbException e) {
            assertEquals(true, e.getMessage().contains("for a user transaction"));
        }
        dbClock.setLastTransTime(Klong.MAX_TIME - 1);
        assertEquals(Klong.MAX_TIME, dbClock.transactionBegin(false));
        dbClock.transactionEnd();
    }
    
    /**
     * bergdb 020-23, Z1: a clock that goes back never takes back a time that currentTime()
     * gave: a later currentTime() gives that time or a later one, and a later transaction a
     * later time, so that a read at that time reads the same values after it. The second
     * currentTime() gave the clock's earlier time and kept it as the last read time, and the
     * transaction then took a time before the first one given.
     */
    @Nano
    private static void testClockGoesBack() {
        final long[] now = {1000};
        DbClock dbClock = new DbClock(() -> now[0]);
        assertEquals(1000, dbClock.transactionBegin(true));
        dbClock.transactionEnd();
        now[0] = 2000;
        assertEquals(2000, dbClock.currentTime());
        now[0] = 1500;
        assertEquals(2000, dbClock.currentTime());
        assertEquals(2001, dbClock.transactionBegin(true));
        dbClock.transactionEnd();
        assertEquals(2001, dbClock.currentTime());
        now[0] = 3000;
        assertEquals(3000, dbClock.currentTime());
    }
    
    /**
     * bergdb 020-23, Z1: currentTime() gives no time after LAST_USER_TIME but a transaction's,
     * also with the clock after it or out of range, so that the times kept for reclaim's
     * internal transactions after a user transaction stay theirs (bergdb 015-55), and a
     * later currentTime() with the clock back cannot take back a time out of range. It gave
     * the clock's time, Klong.MAX_TIME, and an internal transaction after it had no time left.
     * With the clock after LAST_USER_TIME it gives the last transaction's time (bergdb 021-26;
     * it gave LAST_USER_TIME).
     */
    @Nano
    private static void testCurrentTimeLeavesTheMargin() {
        final long[] now = {LAST_USER_TIME - 1};
        DbClock dbClock = new DbClock(() -> now[0]);
        assertEquals(LAST_USER_TIME - 1, dbClock.transactionBegin(true));
        dbClock.transactionEnd();
        now[0] = Klong.MAX_TIME;
        assertEquals(LAST_USER_TIME - 1, dbClock.currentTime());
        now[0] = Klong.MAX_TIME + 1;
        assertEquals(LAST_USER_TIME - 1, dbClock.currentTime());
        now[0] = LAST_USER_TIME;
        assertEquals(LAST_USER_TIME, dbClock.currentTime());
        now[0] = LAST_USER_TIME - 5;
        for (long i = 1; i <= TIME_MARGIN; i++) {
            assertEquals(LAST_USER_TIME + i, dbClock.transactionBegin(false));
            dbClock.transactionEnd();
            assertEquals(LAST_USER_TIME + i, dbClock.currentTime());
        }
    }
    
    /**
     * bergdb 021-26: a currentTime() while the clock is after LAST_USER_TIME, out of range
     * or in the last 1024 units, uses up no time, as a transaction then is refused and uses
     * up none: when the clock is back, user transactions go on. It gave LAST_USER_TIME and
     * kept it as the time that the next transaction must pass, so every user transaction
     * after it was refused until a restart ("No database time is left for a user
     * transaction"); found by a black-box user of the C port (022), U2-1.
     */
    @Nano
    private static void testCurrentTimeWithTheClockPastTheEnd() {
        final long[] now = {1000};
        DbClock dbClock = new DbClock(() -> now[0]);
        assertEquals(1000, dbClock.transactionBegin(true));
        dbClock.transactionEnd();
        now[0] = Klong.MAX_TIME + 1;
        assertEquals(1000, dbClock.currentTime());
        try {
            dbClock.transactionBegin(true);
            throw new AssertionError("a transaction with the clock out of range was taken");
        } catch (DbException e) {
            assertEquals(true, e.getMessage().contains("outside the range"));
        }
        now[0] = LAST_USER_TIME + 1;
        assertEquals(1000, dbClock.currentTime());
        try {
            dbClock.transactionBegin(true);
            throw new AssertionError("a user transaction after the last user time was taken");
        } catch (DbException e) {
            assertEquals(true, e.getMessage().contains("for a user transaction"));
        }
        now[0] = 2000;
        assertEquals(2000, dbClock.transactionBegin(true));
        dbClock.transactionEnd();
        assertEquals(2000, dbClock.currentTime());
    }
    
    @Nano
    private static void testLookupTime() {
        CoreTestClock testClock = new CoreTestClock();
        DbClock dbClock = new DbClock(testClock);
        
        testClock.setTime(1*F);
        dbClock.transactionBegin(true);
        dbClock.transactionEnd();
        testClock.setTime(2*F);
        
        assertEquals(100, dbClock.lookupTime(100));
        assertEquals(1*F, dbClock.lookupTime(Long.MAX_VALUE));
        assertEquals(1*F, dbClock.lookupTime(1*F));
        
        dbClock.transactionBegin(true);
        
        assertEquals(100, dbClock.lookupTime(100));
        assertEquals(1*F, dbClock.lookupTime(Long.MAX_VALUE));
        assertEquals(1*F, dbClock.lookupTime(1*F));
        
        dbClock.transactionEnd();
        
        assertEquals(100, dbClock.lookupTime(100));
        assertEquals(2*F, dbClock.lookupTime(Long.MAX_VALUE));
        assertEquals(1*F, dbClock.lookupTime(1*F));
        
    }
    
    /**
     * A refused transaction gives its time back (transactionCancel(); bergdb 024-16): the
     * last transaction's time stays, and the next transaction takes the same time, unless
     * currentTime() handed out a time while the refused one ran: then a later one, also when
     * the clock has gone back.
     */
    @Nano
    private static void testTransactionCancel() {
        final long[] now = {1*F};
        DbClock dbClock = new DbClock(() -> now[0]);
        assertEquals(1*F, dbClock.transactionBegin(true));
        dbClock.transactionEnd();
        
        now[0] = 2*F;
        assertEquals(2*F, dbClock.transactionBegin(true));
        dbClock.transactionCancel();
        assertEquals(1*F, dbClock.lookupTime(Long.MAX_VALUE));
        assertEquals(2*F, dbClock.transactionBegin(true));
        dbClock.transactionCancel();
        
        now[0] = 3*F;
        assertEquals(3*F, dbClock.transactionBegin(true));
        assertEquals(3*F - 1, dbClock.currentTime());
        dbClock.transactionCancel();
        now[0] = 2*F;
        assertEquals(3*F - 1, dbClock.currentTime());
        assertEquals(3*F, dbClock.transactionBegin(true));
        dbClock.transactionEnd();
        assertEquals(3*F, dbClock.lookupTime(Long.MAX_VALUE));
    }
    
}

/*

140725 Now using "lookup time" instead of "read time".
140722 Wrote some units tests.
140722 Using "transaction time" instead of "write time". More well-defined.

*/
