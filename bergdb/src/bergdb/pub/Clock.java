package bergdb.pub;

/**
 * A clock with high resolution used to timestamp transactions.
 * 
 * @author Frans Lundberg
 */
public interface Clock {
    
    /**
     * Number of time units per second.
     */
    public static final long UNITS_PER_SEC = 10*1000000L;
    
    /**
     * Returns number of 100 ns units of time that has passed since 00:00:00.0, 1 Jan 1970 UMT 
     * (Unix Epoch). Leap seconds are not counted; a day is always 24*60*60 seconds.
     * The minimum valid time value is 0; the maximum valid time value is 2^56-1.
     */
    public long getTime();
}

/*
-- Unit discussion --

100 ns unit. -->
2^(7*8) units = 2^56 units = 7.2e16 units
Max time expanse in years = 7.2e16 / (1e7 * 3600 * 24 * 365) = 228 years. Fine!
So, we are fine with using only the first 56 bits.

The resolution is also enough. No more than 10M transactions per second.
*/
