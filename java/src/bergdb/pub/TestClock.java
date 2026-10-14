package bergdb.pub;

import bergdb.pub.util.Clock;
import bergdb.pubimp.ClockConstants;

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
     * Sets the time of this test clock.
     * The time must be larger than or equal to the current time of the clock.
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
        if (time < ClockConstants.MIN_TIME) {
            throw new IllegalArgumentException("time is too small, was " + time + ".");
        }
        
        if (time > ClockConstants.MAX_TIME) {
            throw new IllegalArgumentException("time is too large, was " + time + ".");
        }
        
        if (time <= this.time) {
            throw new IllegalArgumentException("Bad time, must be larger than current time, " 
                    + this.time + ".");
        }
        this.time = time;
    }
}
