package bergdb.pub;

import java.util.Date;

/**
 * A Time instance represents a time instance measure by the database
 * clock (see Clock).
 * The resolution of a Time instance is one "clock unit", that is 100 nanoseconds.
 * Internally, the time is stored as the number of 100 nanoseconds that
 * has passed since 00:00:00.0, 1 Jan 1970 UMT (Unix Epoch). 
 * Leap seconds are not counted; a day is always 24*60*60 seconds.
 * The minimum valid time value is 0 clock units (UTC 1970-01-01 00:00:00); 
 * the maximum valid time value is 2^56-1 clock units (UTC 2198-05-04 23:50:04).
 * 
 * @see Time
 * @author Frans Lundberg
 */
public class Time {
    // 2^56 - 1 = 72057594037927935
    
    private final long units;
    
    private static final long UNITS_PER_MILLISECOND = Clock.UNITS_PER_SEC / 1000;
    private static final long MIN_IN_UNITS = 0;
    private static final long MAX_IN_UNITS = 72057594037927935L;
    
    /**
     * The maximum possible Time value.
     * Corresponds to UTC 2198-05-04 23:50:04.
     */
    public static final Time MAX = new Time(MAX_IN_UNITS);
    
    private Time(long units) {
        if (units < MIN_IN_UNITS || units > MAX_IN_UNITS) {
            throw new IllegalArgumentException("Time ouf of range, units: " + units + ".");
        }
        this.units = units;
    }
    
    /**
     * Creates and returns a Time instance based on the number of clock units 
     * that has passed since Unix Epoch.
     */
    public static Time units(long units) {
        return new Time(units);
    }
    
    /**
     * Creates and returns a Time instance based on the number of milliseconds
     * that has passed since Unix Epoch.
     */
    public static Time millis(long millis) {
        return new Time(millis / UNITS_PER_MILLISECOND);
    }
    
    /**
     * Adds a Duration to this Time and returns a new Time with the result.
     */
    public Time add(Duration duration) {
        return new Time(this.units + duration.getDbUnits());
    }
    
    /**
     * Returns the number of clock units that has passed since Unix Epoch.
     */
    public long getUnits() {
        return units;
    }
    
    /**
     * Returns a Date given this Time instance. The returned Date object is 
     * created by rounding the time to the closest smaller millisecond value.
     * The returned Date has lower resolution than a Time instance.
     */
    public Date getDate() {
        return new Date(units / UNITS_PER_MILLISECOND);
    }
}
