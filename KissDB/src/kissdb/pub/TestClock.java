package kissdb.pub;

import kissdb.core.Klong;


/**
 * Deterministic clock suitable for testing.
 * 
 * @author Frans Lundberg
 */
public final class TestClock implements Clock {
    private long time = 0;
    
    public long getTime() {
        return time;
    }
    
    /**
     * Sets the time. The time must be larger than or equal to the current time of the clock.
     * 
     * @param time In time units.
     */
    public void setTime(long time) {
        if (time < Klong.MIN_TIME) {
            throw new IllegalArgumentException("time is too small, was " + time + ".");
        }
        
        if (time > Klong.MAX_TIME) {
            throw new IllegalArgumentException("time is too large, was " + time + ".");
        }
        
        if (time <= this.time) {
            throw new IllegalArgumentException("Bad time, must be larger than current time, " 
                    + this.time + ".");
        }
        this.time = time;
    }
}
