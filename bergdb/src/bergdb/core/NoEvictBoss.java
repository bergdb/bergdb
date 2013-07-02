package bergdb.core;

/**
 * An IEvcitBoss that never evicts nodes. Useful for testing.
 */
public class NoEvictBoss implements IEvictBoss {
    
    /**
     * Returns Long.MAX_VALUE.
     */
    public long getCacheDuration() {
        return Long.MAX_VALUE;
    }

    public void reportEvictCount(EvictData ed) {
    }

    public boolean evictOrNot() {
        return false;
    }
}
