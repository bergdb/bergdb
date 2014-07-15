package bergdb.pub;

/**
 * A database clock with high resolution used to timestamp transactions.
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
     * 00:00:00.0, 1 Jan 1970 UMT (Unix Epoch). Leap seconds are not counted; 
     * a day is always 24*60*60 seconds.</p>
     * 
     * <p>The minimum valid time value returned is 0; the maximum valid time value 
     * returned by this method is 2^56-1.</p>
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
