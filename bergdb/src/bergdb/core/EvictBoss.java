package bergdb.core;

import bergdb.dag.EvictData;

/**
 * The implementations of this interface decide how often to run the node eviction
 * algorithm. Implementations must support concurrent threads.
 * 
 * @author Frans Lundberg
 */
public interface EvictBoss {
    
    /**
     * Nodes stay in cache for 'cache duration'. Measured with the "cache time-scale"
     * (see Db.Aux.cachedMemoryValue).
     */
    public long getCacheDuration();

    /**
     * Decides whether the Evictor.evict() method should be run or not when this method
     * is called. An EvictBoss implementation could return "true" always, but that
     * would not be the best solution for performance reasons.
     */
    public boolean shouldEvict();
    
    /**
     * Reports that the evict algorithm was run to this EvictBoss.
     * Ownership of 'ed' is kept by the caller (implementations of this interface 
     * must not modify it).
     */
    public void reportEvict(EvictData ed);
}
