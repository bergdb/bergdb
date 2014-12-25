package bergdb.core;

import bergdb.dag.EvictData;

/**
 * An IEvictBoss that never evicts nodes. Useful for testing, but not for
 * production use, of course. Cache grows without limit.
 * 
 * @author Frans Lundberg
 */
public class NoEvictBoss implements EvictBoss {
    
    /** Returns Long.MAX_VALUE. */
    public long getCacheDuration() {
        return Long.MAX_VALUE;
    }

    /** Does nothing. */
    public void reportEvict(EvictData ed) {}

    /** Always returns false. */
    public boolean evictShouldRun() {
        return false;
    }
}
