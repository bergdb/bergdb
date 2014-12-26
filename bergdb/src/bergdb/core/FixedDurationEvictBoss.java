package bergdb.core;

import java.util.concurrent.atomic.AtomicInteger;

import bergdb.dag.EvictData;

/**
 * An IEvictBoss that has a fixed configurable cache duration.
 * Cache-duration is measured in the "cache time-scale" (based on Db.cachedMemoryValue).
 * This class is thread-safe.
 * 
 * @author Frans Lundberg
 */
public class FixedDurationEvictBoss implements EvictBoss {
    private final long cacheDuration;
    private AtomicInteger counter = new AtomicInteger(0);
    
    /**
     * Creates a new object with a cache duraction value based on the 
     * available memory of the JVM. Runtime.maxMemory() is used.
     */
    public FixedDurationEvictBoss() {
        // Normally, maxMemory() returns a reasonable value. This is true for the 
        // Oracle JVMs. Another JVM could return Long.MAX_VALUE. In this case a
        // constant value is used for the cacheDuration.
        
        long maxMem = Runtime.getRuntime().maxMemory();
        
        if (maxMem == Long.MAX_VALUE) {
            cacheDuration = 200L * 1000000;
        } else {
            cacheDuration = (long) (0.25 * maxMem);
        }
    }
    
    /**
     * @param cacheDuration  Cache duration in cache time-scale units
     * (based on Db.cachedMemoryValue)..
     */
    public FixedDurationEvictBoss(long cacheDuration) {
        if (cacheDuration < 0) {
            throw new IllegalArgumentException("Negative cacheDuration not allowed, " 
                    + cacheDuration + ".");
        }
        this.cacheDuration = cacheDuration;
    }
    
    public long getCacheDuration() {
        // Sync note: No need to synchronize, cacheDuration is final.
        return cacheDuration;
    }
    
    /**
     * Returns true if the evict algorithm should run.
     * This method is thread-safe (must be).
     */
    public final boolean evictShouldRun() {
        // We may occasionally miss an update of counter. "counter++" is not atomic.
        // We accept this.
        
        int c = counter.getAndIncrement();
        return c % 100 == 23;
        
        //return c++ % 1 == 0;
        //return c++ % 10 == 0;
        //return c++ % 1000 == 0;
    }
    
    /**
     * The implementation in this class does nothing.
     */
    public final void reportEvict(EvictData ed) {
        // Empty.
    }
}

/*

Feedback loop?
==============

1301 Frans:
We could add a feed-back loop. The evictOrNot method could decide that evict method should 
run more often when the reported (reportEvictResult) fraction 
ed.evictCount / ed.pointerCount is high.
Example: normally evictOrNot return true 1 in 100 times. But when fraction is above 0.50
it could run every 1 on 20 instead.

*/