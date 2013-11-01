package bergdb.core;

import bergdb.dag.EvictData;

/**
 * The implementations of this interface decides when to run the node eviction.
 * Implementations must support concurrent threads.
 */
public interface IEvictBoss {
    /**
     * Reports that the evict method was run.
     * Ownership of 'ed' is kept by the caller.
     */
    public void reportEvictCount(EvictData ed);
    
    /**
     * Decides whether the DB.evict() method should be run or not.
     */
    public boolean evictOrNot();
    
    /**
     * Nodes are allowed to stay in cache for 'cache duration'. Measured with the cache-time scale
     * (based on DB.cachedMemoryValue).
     */
    public long getCacheDuration();
}
