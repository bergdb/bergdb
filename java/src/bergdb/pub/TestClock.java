package bergdb.pub;

import bergdb.pub.util.Clock;

/**
 * Deterministic clock suitable for testing. It is thread-safe: a time set by one thread
 * is the one that getTime() returns in the database's threads (bergdb 019-44).
 * 
 * @author Frans Lundberg
 */
public final class TestClock implements Clock {
    /** Volatile: the database's threads read it (bergdb 019-44). */
    private volatile long time = 0;

    /**
     * Creates a test clock. Its time is 0 until setTime() is called.
     */
    public TestClock() {
    }
    
    public long getTime() {
        return time;
    }
    
    /**
     * Sets the time of this test clock.
     * The time must be larger than or equal to the current time of the clock.
     * 
     * @throws IllegalArgumentException  If time is null, or before the clock's current
     *             time; the clock's time is then unchanged (bergdb 020-25).
     */
    public void setTime(Time time) {
        if (time == null) {
            throw new IllegalArgumentException("time == null not allowed");
        }
        
        setTimeInUnits(time.units());
    }
    
    /**
     * @param time In clock units.
     */
    private void setTimeInUnits(long time) {
        if (time < Time.MIN_IN_UNITS) {
            throw new IllegalArgumentException("time is too small, was " + time + ".");
        }
        
        if (time > Time.MAX_IN_UNITS) {
            throw new IllegalArgumentException("time is too large, was " + time + ".");
        }
        
        // The current time is allowed, as the Javadoc says, since 2026-11-05 (bergdb 015-58).
        if (time < this.time) {
            throw new IllegalArgumentException("Bad time, " + time + ", must not be less than "
                    + "the current time, " + this.time + ".");
        }
        this.time = time;
    }
}
