package bergdb.core;

import bergdb.pub.util.Clock;

/**
 * Deterministic clock suitable for testing.
 * 
 * @author Frans Lundberg
 */
public class CoreTestClock implements Clock {
    private long time = 0;
    
    public long getTime() {
        return time;
    }

    /**
     * Move clock forward one unit.
     */
    public void tick() {
        time++;
    }
    
    public void setTime(long time) {
        if (time <= this.time) {
            throw new IllegalArgumentException("Bad time, must be larger than current time, " 
                    + this.time + ".");
        }
        this.time = time;
    }
}
