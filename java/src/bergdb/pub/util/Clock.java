package bergdb.pub.util;

/**
 * A database clock with high resolution used to timestamp transactions.
 * An implementation must be thread-safe: the database's threads call getTime() (bergdb
 * 019-44).
 * 
 * @author Frans Lundberg
 */
public interface Clock {
    
    /**
     * Number of clock units per second.
     */
    public static final long UNITS_PER_SEC = 10*1000000L;
    
    /**
     * <p>Returns number of 100 ns units (clock units) of time that has passed since 
     * 00:00:00.0, 1 Jan 1970 UTC (Unix Epoch). Leap seconds are not counted; 
     * a day is always 24*60*60 seconds.</p>
     * 
     * <p>The minimum valid time value returned is 0; the maximum valid time value 
     * returned by this method is 2^56-1. A transaction that begins while the clock is outside
     * that range is refused with a DbException: nothing is written, and the database goes
     * on. A start that creates a database throws the DbException too, as it writes the
     * database's first transaction; a start of an existing database does not read the
     * clock, and succeeds, and its transactions are refused while the clock is outside the
     * range (bergdb 020-23). The last 1024 units of the range are kept for the database's own
     * transactions, which may follow a user's: a user transaction needs a time of 2^56-1025
     * or less, and is refused in the same way when the clock, or the last transaction's
     * time, leaves it none (bergdb 005-18, 015-55, 020-25).</p>
     *
     * <p>The time may go back: a transaction's time is the clock's, or, when that is not
     * after the last transaction's time or the last time that currentTime() gave, the next
     * unit after it, so the transactions' times are unique and increasing
     * (Transaction.getTime()). The time that currentTime() gives (Connection, Database) is
     * the clock's, at most 2^56-1025, or, when that is earlier, the last time it gave or the
     * last transaction's time, so its times never decrease, and every later transaction's
     * time is after them (bergdb 020-23).</p>
     */
    public long getTime();
}

/*

Time unit discussion
--------------------

100 ns unit. -->
2^(7*8) units = 2^56 units = 7.2e16 units
Max time expanse in years = 7.2e16 / (1e7 * 3600 * 24 * 365) = 228 years. Fine!
So, we are fine with using only the first 56 bits.

The resolution is also enough. No more than 10M transactions per second will be made.
*/
