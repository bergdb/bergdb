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
    //
    
    private static final long INITIAL_CACHE_SIZE = 10*1000;
    @SuppressWarnings("unused")
    private final Cache.DbInfo dbInfo;
    private final Object bigLock;
    private long sizeIndicator;
    private long totalSize;     // total cache size estimation, in bytes
    private long putSize;
    private final HashMap<Long, CacheEntry>[] maps;

    
    @SuppressWarnings("unchecked")
    public Cache3(Cache.DbInfo dbInfo) {
        assert dbInfo != null;
        
        this.bigLock = new Object();
        this.dbInfo = dbInfo;
        this.totalSize = INITIAL_CACHE_SIZE;
        this.putSize = INITIAL_CACHE_SIZE;
        this.maps = new HashMap[256];
        
        for (int i = 0; i < maps.length; i++) {
            maps[i] = new HashMap<Long, CacheEntry>();
        }
        
        synchronized (bigLock) {}
    }
    
    /**
     * Sets the user-suggested size of the cache (in bytes).
     */
    public void setSizeIndicator(long sizeIndicator) {
        assert sizeIndicator > 0;
        
        if (sizeIndicator < 4*1000000) {
            sizeIndicator = 4*1000000;
        }
        
        synchronized (bigLock) {
            this.sizeIndicator = sizeIndicator;
        }
    }
    
    public long getSizeIndicator() {
        synchronized (bigLock) {
            return sizeIndicator;
        }
    }
    
    /**
     * Gets a lock object for one specific node.
     * 
     * @param id
     *      Node ID.
     */
    public Object getLock(long id) {
        return bigLock;
    }
    
    public long totalSize() {
        synchronized (bigLock) {
            return totalSize;
        }
    }

    public long putSize() {
        synchronized (bigLock) {
            return putSize;
        }
    }
    
    public void pointerCreated(Node from, int index, Node to) {
        long id = to.getId();
        Object lock = getLock(id);
        
        synchronized (lock) {
            CacheEntry entry = internalGet(id);
            
            if (entry == null) {
                entry = CacheEntry.oneRef(to);
                internalPut(id, entry);
            } else {
                entry.refCount++;
            }
        }
    }
    
    public void pointerDestroyed(Node to) {
        long id = to.getId();
        Object lock = this.getLock(id);
        
        synchronized (lock) {
            CacheEntry entry = internalGet(id);
            
            if (entry == null) {
                // ignore, should not happen
            } else {
                entry.refCount--;
                if (entry.refCount == 0) {
                    internalRemove(id);
                }
            }
        }
    }
    
    public Node getNode(long id) {
        synchronized (bigLock) {
            CacheEntry entry = internalGet(id);
            return entry == null ? null : entry.node;
        }
    }
    
    private void internalPut(long id, CacheEntry entry) {
        map(id).put(id, entry);
    }
    
    private CacheEntry internalGet(long id) {
        return map(id).get(id);
    }
    
    private void internalRemove(long id) {
        map(id).remove(id);
    }
    
    private HashMap<Long, CacheEntry> map(long id) {
        return maps[mapIndex(id)];
    }
    
    private int mapIndex(long id) {
        long v = id;
        long temp = (v >>>  0) ^ (v >>>  8) ^ (v >>> 16) ^ (v >>> 24) ^
                    (v >>> 32) ^ (v >>> 40) ^ (v >>> 48) ^ (v >>> 56);
        int index = ((int) temp) % maps.length;
        assert index >= 0 : "index: " + index;
        assert index < maps.length : "index: " + index;
        return index;
    }
    
    public static class AlreadyHasNode extends AssertionError {
        private static final long serialVersionUID = 1L;
        
        public AlreadyHasNode(String message) {
            super(message);
        }
    }
    
    public static class CacheEntry {
        public Node node;
        public int refCount;
        
        private CacheEntry() {
        }
        
        /**
         * Creates and returns a CacheEntry with refCount equal to 1.
         */
        public static CacheEntry oneRef(Node node) {
            CacheEntry entry = new CacheEntry();
            entry.node = node;
            entry.refCount = 1;
            return entry;
        }
    }
}
