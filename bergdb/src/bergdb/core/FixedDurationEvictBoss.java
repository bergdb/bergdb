package bergdb.core;

import bergdb.coreds.EvictData;

/**
 * An IEvictBoss that has a fixed configurable cache duration.
 * Cache-duration is measured in stream-length. So the "time-scale" is the length of
 * the database stream. This class is thread-safe.
 * 
 * @author Frans Lundberg
 */
public class FixedDurationEvictBoss implements IEvictBoss {
    private final long cacheDuration;
    private volatile long counter = 12345;
    
    public FixedDurationEvictBoss() {
        long maxMem = Runtime.getRuntime().maxMemory();
        
        if (maxMem == Long.MAX_VALUE) {
            cacheDuration = 200L * 1000000;
        } else {
            cacheDuration = (long) (0.25 * maxMem);
        }
    }
    
    public FixedDurationEvictBoss(long cacheDuration) {
        if (cacheDuration < 0) {
            throw new IllegalArgumentException("Negative cacheDuration not allowed, " 
                    + cacheDuration + ".");
        }
        this.cacheDuration = cacheDuration;
    }
    
    public long getCacheDuration() {
        // No need to synch, cacheDuration is final.
        return cacheDuration;
    }
    
    public final void reportEvictCount(EvictData ed) {
        // Empty.
    }

    /**
     * This method is thread-safe (must be).
     */
    public final boolean evictOrNot() {
        // We may occasionally miss an update of counter. "counter++" is not atomic.
        // We accept this.
        
        return counter++ % 100 == 0;
        
        //return counter++ % 1 == 0;
        //return counter++ % 10 == 0;
        //return counter++ % 1000 == 0;
    }
}

/*

Feedback loop maybe?
====================

1301 Frans:
We could add a feed-back loop. The evictOrNot method could decide that evict method should 
run more often when the reported (reportEvictResult) fraction 
ed.evictCount / ed.pointerCount is high.

Example: normally evictOrNot return true 1 in 100 times. But when fraction is above 0.50
it could run every 1 on 20 instead.

*/