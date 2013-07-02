package bergdb.core;

import bergdb.pub.Clock;

/**
 * Clock based on system clock.
 * Even if system clock is set the time returned is always strictly increasing.
 * 
 * @author Frans Lundberg
 */
public class SystemClock implements Clock {
    private long lastTime = 0;
    
    /**
     * Returns a strictly increasing time in number of 100 ns that passed since Unix Epoch.
     */
    public synchronized long getTime() {
        long time = System.currentTimeMillis() * 10L*1000L;
        if (time <= lastTime) {
            lastTime++;
            time = lastTime;
        }
        return time;
    } 
}
