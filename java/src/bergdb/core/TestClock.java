package bergdb.core;

import bergdb.dag.Klong;
import bergdb.pub.util.Clock;


/**
 * Deterministic clock suitable for testing.
 * Copy of class: bergdb.pub.TestClock. Copy made to avoid package dependency db-to-pub.
 * 
 * @author Frans Lundberg
 */
public final class TestClock implements Clock {
    private long time = 0;
    
    public long getTime() {
        return time;
    }
    
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
