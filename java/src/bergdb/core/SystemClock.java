package bergdb.core;

import static bergdb.nanotest.Assert.assertEquals;

import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;

/**
 * Clock based on system clock.
 * Even if system clock is set the time returned is always strictly increasing: a system time
 * that is not later than the last time returned gives the last time plus one, 100 ns later,
 * until the system clock passes it. Kept since 2026-11-03 (bergdb 005-69): the last time
 * stayed 0, and calls within a millisecond, or after the system clock was set back, gave
 * equal or earlier times. A database does not depend on it: DbClock makes its times strictly
 * increasing with any clock.
 * 
 * @author Frans Lundberg
 */
public class SystemClock implements Clock {
    private long lastTime = 0;
    
    /**
     * Returns a strictly increasing time in number of 100 ns that passed since Unix Epoch.
     */
    public long getTime() {
        return getTime(System.currentTimeMillis());
    }
    
    /** As getTime(), with 'millis' as the system's time, in ms since the Unix Epoch. */
    synchronized long getTime(long millis) {
        long time = millis * 10L*1000L;
        if (time <= lastTime) {
            lastTime++;
            time = lastTime;
        } else {
            lastTime = time;
        }
        return time;
    } 
    
    
    // ======== Testing ========
    
    /**
     * 100,000 calls in a row, each later than the one before (bergdb 005-69). Before, calls
     * within the same millisecond gave the same time.
     */
    @Nano
    private static void testStrictlyIncreasing() {
        SystemClock clock = new SystemClock();
        long last = clock.getTime();
        for (int i = 0; i < 100 * 1000; i++) {
            final long time = clock.getTime();
            if (time <= last) {
                throw new AssertionError("call " + i + ": " + time + ", after " + last);
            }
            last = time;
        }
    }
    
    /**
     * A system time equal to the last one, or earlier (the system clock set back), gives the
     * last time plus one, until the system clock passes it (bergdb 005-69). Before, it gave
     * the system's time.
     */
    @Nano
    private static void testClockSetBack() {
        SystemClock clock = new SystemClock();
        assertEquals(1000 * 10000L, clock.getTime(1000));
        assertEquals(1000 * 10000L + 1, clock.getTime(1000));
        assertEquals(1000 * 10000L + 2, clock.getTime(999));
        assertEquals(2000 * 10000L, clock.getTime(2000));
        assertEquals(2000 * 10000L + 1, clock.getTime(0));
    }
}
