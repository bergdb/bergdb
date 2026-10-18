package bergdb.core;

import java.util.HashMap;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.dag.Node;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

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
    
    /**
     * The access clock (bergdb item 001, WP R8, change 4; docs/level4-alignment.md, M23 and
     * M40): it advances by one at every node read from the stream (NodeCollection) and every
     * node the writer makes (Db), so in read-only workloads too. The access data that an
     * operation writes into the memory pointers it follows is minus its value
     * (Db.getAccessData, dag/AccessData.java), for the age policy of eviction (J7). A field of
     * its own: before 2026-10-17 the access data was minus putSize, which nothing advances,
     * so the constant -10,000; the clock starts there. Read and advanced without a lock.
     */
    private final AtomicLong accessClock = new AtomicLong(INITIAL_CACHE_SIZE);

    /** The resident registry's accounting (bergdb item 001, WP J1); see Residents. */
    private final Residents residents = new Residents();

    
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

    /** The resident registry's accounting; see Residents. */
    public Residents residents() {
        return residents;
    }

    /**
     * Object 'node' is released (bergdb item 001, WP J2 on; the Lean model's Mem.release):
     * the node table's entry goes if it names it, and the registry forgets it.
     */
    public void released(Node node) {
        long id = node.getId();
        synchronized (getLock(id)) {
            CacheEntry entry = internalGet(id);
            if (entry != null && entry.node == node) {
                internalRemove(id);
            }
        }
        residents.released(node);
    }

    /** The objects the node table names, for the audit (Audit) and the sweeps (J2 on). */
    public java.util.List<Node> nodes() {
        synchronized (bigLock) {
            java.util.ArrayList<Node> result = new java.util.ArrayList<Node>();
            for (HashMap<Long, CacheEntry> m : maps) {
                for (CacheEntry e : m.values()) {
                    result.add(e.node);
                }
            }
            return result;
        }
    }

    /** The access clock's value; see accessClock. */
    public long accessClock() {
        return accessClock.get();
    }
    
    /** Advances the access clock by one; see accessClock. */
    public void tickAccessClock() {
        accessClock.incrementAndGet();
    }
    
    public long putSize() {
        synchronized (bigLock) {
            return putSize;
        }
    }
    
    public void pointerCreated(Node from, int index, Node to) {
        // The node table names canonical objects only (bergdb item 001, WP J1; the Lean model's
        // Level 4 memory, docs/level4-alignment.md, 5.2; WP R8's change 3 for the loader): a
        // memory slot to a snapshot, which a split copies (Dag.reportNewPointers), does not enter
        // it. Before 2026-10-18 it did, when the table had no object for the node, and a newer
        // snapshot replaced an older one; the audit found it.
        if (!to.isCanonical()) {
            return;
        }
        long id = to.getId();
        Object lock = getLock(id);
        
        synchronized (lock) {
            CacheEntry entry = internalGet(id);
            
            if (entry == null) {
                entry = CacheEntry.oneRef(to);
                internalPut(id, entry);
                residents.added(to);
            } else {
                entry.refCount++;
                if (entry.node != to && isBetter(to, entry.node)) {
                    entry.node = to;
                    residents.added(to);
                }
            }
        }
    }
    
    /**
     * Enters 'node' in the node table, unless the table has a better object for the
     * node: a canonical object is never replaced; otherwise the newest version wins
     * (docs/levels.md, level 2). Returns the table's object
     * for the node after the call.
     */
    public Node register(Node node) {
        long id = node.getId();
        
        synchronized (getLock(id)) {
            CacheEntry entry = internalGet(id);
            
            if (entry == null) {
                entry = CacheEntry.noRef(node);
                internalPut(id, entry);
                residents.added(node);
            } else if (entry.node != node && isBetter(node, entry.node)) {
                entry.node = node;
                residents.added(node);
            }
            
            return entry.node;
        }
    }
    
    /**
     * Makes the node of 'node' canonical in the node table: the table's canonical object
     * if there is one, else the newest of 'node' and the table's object, which is then
     * marked canonical. Returns that object. Called when the writer reaches a node.
     */
    public Node makeCanonical(Node node) {
        long id = node.getId();
        
        synchronized (getLock(id)) {
            CacheEntry entry = internalGet(id);
            Node result = node;
            
            if (entry != null && entry.node != node) {
                Node other = entry.node;
                if (other.isCanonical() || other.getSpos() > node.getSpos()) {
                    result = other;
                }
            }
            
            result.setCanonical(true);
            residents.promoted(result);
            
            if (entry == null) {
                internalPut(id, CacheEntry.noRef(result));
            } else {
                entry.node = result;
            }
            
            return result;
        }
    }
    
    /**
     * True if 'node' should replace 'old' in the node table: never a canonical object,
     * otherwise by a canonical object or a newer version.
     */
    private static boolean isBetter(Node node, Node old) {
        if (!node.isIndexNode()) {
            return false;       // Value nodes have one version.
        }
        
        if (old.isCanonical()) {
            assert !node.isCanonical() : "two canonical objects for node " + node.getId();
            return false;
        }
        
        return node.isCanonical() || node.getSpos() > old.getSpos();
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
        // 2026-10-13 (java/stress/LoadTest.java): was ((int) temp) % maps.length, which is
        // negative for some ids of 2^31 and more; node ids are stream positions, so every
        // stream longer than 2.1 GB failed with ArrayIndexOutOfBoundsException.
        int index = (int) ((temp & Long.MAX_VALUE) % maps.length);
        assert index >= 0 : "index: " + index;
        assert index < maps.length : "index: " + index;
        return index;
    }
    
    // ======== Tests ========
    
    /**
     * Regression test for a bug found 2026-10-13: node ids of 2^31 and more,
     * stream positions past 2.1 GB, gave a negative map index.
     */
    @Nano
    public static void testLargeIds() {
        Cache3 cache = new Cache3(new Cache.DbInfo() {
            public long getStartupPosForEvict() { return 0; }
            public PointerLocks getPointerLocks() { return null; }
        });
        long[] ids = {1L << 31, (1L << 31) + 0x94, (1L << 32) - 1, 5L << 30, 1L << 40, Long.MAX_VALUE};
        for (long id : ids) {
            Assert.assertTrue(cache.getNode(id) == null);
        }
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
        
        /**
         * Creates and returns a CacheEntry with refCount equal to 0.
         */
        public static CacheEntry noRef(Node node) {
            CacheEntry entry = new CacheEntry();
            entry.node = node;
            entry.refCount = 0;
            return entry;
        }
    }
}
