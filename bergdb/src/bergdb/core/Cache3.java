package bergdb.core;

import java.util.HashMap;
import bergdb.dag.Node;

/**
 * A deterministic node cache; size is known, weak references are *not* used.
 * The cache ensures there is never more than one Node object with a given
 * node id.
 * 
 * @author Frans Lundberg
 */
public class Cache3 {
    //
    // Simple, non-optimal implementation to start with. 
    // Cache-global locking to start with.
    // What synchronization do we need here? Any? Cache-global? Let consumers do it?
    // Same interface as Cache2 to start with.
    //
    
    private static final long INITIAL_CACHE_SIZE = 10*1000;
    @SuppressWarnings("unused")
    private final Cache.DbInfo dbInfo;
    private final Object lock;
    private long sizeIndicator;
    private long totalSize;     // total cache size estimation, in bytes
    private long putSize;
    private final HashMap<Long, CacheEntry> map;

    public Cache3(Cache.DbInfo dbInfo) {
        assert dbInfo != null;
        
        this.lock = new Object();
        this.dbInfo = dbInfo;
        this.totalSize = INITIAL_CACHE_SIZE;
        this.putSize = INITIAL_CACHE_SIZE;
        this.map = new HashMap<Long, CacheEntry>();
        
        synchronized (lock) {}
    }
    
    /**
     * Sets the user-suggested size of the cache (in bytes).
     */
    public void setSizeIndicator(long sizeIndicator) {
        assert sizeIndicator > 0;
        
        if (sizeIndicator < 4*1000000) {
            sizeIndicator = 4*1000000;
        }
        
        synchronized (lock) {
            this.sizeIndicator = sizeIndicator;
        }
    }
    
    public long getSizeIndicator() {
        synchronized (lock) {
            return sizeIndicator;
        }
    }
    
    public Node getIndexNode(long id) {
        return getNode(id);
    }
    
    /**
     * Gets a lock object for one specific node.
     * 
     * @param id
     *      Node ID.
     */
    public Object getLock(long id) {
        return lock;
    }
    
    public long totalSize() {
        synchronized (lock) {
            return totalSize;
        }
    }

    public long putSize() {
        synchronized (lock) {
            return putSize;
        }
    }
    
    public void pointerCreated(Node to) {
        long id = to.getId();
        
        synchronized (lock) {
            CacheEntry entry = internalGet(id);
            
            if (entry == null) {
                entry = CacheEntry.countOne(to);
                internalPut(id, entry);
            } else {
                entry.count++;
            }
        }
    }
    
    public Node getNode(long id) {
        synchronized (lock) {
            CacheEntry entry = internalGet(id);
            return entry == null ? null : entry.node;
        }
    }
    
    private void internalPut(long id, CacheEntry entry) {
        map.put(id, entry);
    }
    
    private CacheEntry internalGet(long id) {
        return map.get(id);
    }
    
    public static class AlreadyHasNode extends AssertionError {
        private static final long serialVersionUID = 1L;
        
        public AlreadyHasNode(String message) {
            super(message);
        }
    }
    
    public static class CacheEntry {
        public Node node;
        public short count;
        
        private CacheEntry() {
        }
        
        /**
         * Creates and returns a CacheEntry with cound equal to 1.
         */
        public static CacheEntry countOne(Node node) {
            CacheEntry entry = new CacheEntry();
            entry.node = node;
            entry.count = 1;
            return entry;
        }
    }
}
