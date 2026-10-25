package bergdb.core;

/**
 * The cache's figures at one moment, for tools that compare versions of BergDB (bergdb item
 * 009, step 1a: PauseProbe, and ScaleBench in item 009): what is resident, what was loaded,
 * and what eviction did, without reading the classes that hold them, which item 009 changes.
 * See Db.Internal.cacheStats().
 */
public final class CacheStats {
    /** The resident bytes the capacity controller counts (Residents). */
    public final long residentBytes;

    /** The node versions read from the stream by the followers (NodeCollection.loads). */
    public final long loads;

    /** Eviction's steps: the sweeps of the capacity controller. */
    public final long evictionSteps;

    /** The objects eviction released. */
    public final long evictedObjects;

    /** The time of the eviction steps, in all and the longest, in nanoseconds. */
    public final long evictionNanos, maxEvictionNanos;

    public CacheStats(long residentBytes, long loads, long evictionSteps, long evictedObjects,
            long evictionNanos, long maxEvictionNanos) {
        this.residentBytes = residentBytes;
        this.loads = loads;
        this.evictionSteps = evictionSteps;
        this.evictedObjects = evictedObjects;
        this.evictionNanos = evictionNanos;
        this.maxEvictionNanos = maxEvictionNanos;
    }

    public String toString() {
        return "resident " + residentBytes / 1000000 + " MB, " + loads + " loads, "
                + evictionSteps + " eviction steps, " + evictedObjects + " objects evicted, "
                + "eviction time " + evictionNanos / 1000000 + " ms in total, "
                + String.format("%.3f", maxEvictionNanos / 1e6) + " ms at most";
    }
}
