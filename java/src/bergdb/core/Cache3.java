package bergdb.core;

import java.util.Arrays;
import java.util.HashMap;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.dag.Node;
import bergdb.dag.Spos;
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

    /** The node table is 2^MAP_BITS maps; mapIndex picks one by the node id. */
    private static final int MAP_BITS = 8;

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

    /**
     * Told in pointerCreated just before it takes the node table's lock; for tests only
     * (bergdb item 005-09: EvictionReaderTester.testReleaseBeforeTheTableEntry).
     */
    interface EntryListener {
        void beforeEntry(Node to);
    }

    /** See EntryListener. Null, and so doing nothing, unless a test sets it. */
    static volatile EntryListener entryListener = null;

    
    @SuppressWarnings("unchecked")
    public Cache3(Cache.DbInfo dbInfo) {
        assert dbInfo != null;
        
        this.bigLock = new Object();
        this.dbInfo = dbInfo;
        this.totalSize = INITIAL_CACHE_SIZE;
        this.putSize = INITIAL_CACHE_SIZE;
        this.maps = new HashMap[1 << MAP_BITS];
        
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
     * its canonical flag is cleared (M31) and the node table's entry goes if it names it,
     * one step under the table's lock (bergdb item 005-09, see pointerCreated); the registry
     * forgets it.
     */
    public void released(Node node) {
        long id = node.getId();
        synchronized (getLock(id)) {
            node.setCanonical(false);       // No effect for a value node.
            CacheEntry entry = internalGet(id);
            if (entry != null && entry.node == node) {
                internalRemove(id);
            }
        }
        residents.released(node);
    }

    /**
     * The objects the node table names, for the audit (Audit) and the sweeps (J2 on), in the
     * order of the maps and their bins, which follows the node ids (mapIndex), not the tree or
     * the age. The sweeps' choices among equal candidates follow it (Eviction: the objects
     * that only the table holds, memory pointers of the same age, the random schedule's
     * draws); the records do not (EvictionInvariance).
     */
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
        //
        // The flag is read again under the table's lock, where a release clears it (released):
        // a reader's follow (NodeCollection.followStreamPointer) gets here without the write
        // lock, and a sweep may release 'to' between the first read and the lock. Until
        // 2026-10-20 only the first read was made, and the table got the released object back,
        // a snapshot (bergdb item 005-09; EvictionReaderTester.testReleaseBeforeTheTableEntry).
        if (!to.isCanonical()) {
            return;
        }
        long id = to.getId();
        Object lock = getLock(id);
        
        final EntryListener el = entryListener;
        if (el != null) el.beforeEntry(to);
        
        synchronized (lock) {
            if (!to.isCanonical()) {
                return;
            }
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
    
    /**
     * The map of node 'id': the top MAP_BITS bits of id times 2^64 divided by the golden
     * ratio (Fibonacci hashing), which depend on every bit of the id. HashMap takes the bin
     * from the low bits of h ^ (h >>> 16), h the Long's hash, so the map and the bin depend
     * on different bits (bergdb item 005-08; testBinsStaySmall). From 2017-07-31 to
     * 2026-10-19 the map was the XOR of the id's eight bytes. For the ids of one map that
     * left the low 16 bits of h ^ (h >>> 16) a function of one byte (the XOR of the id's odd
     * bytes): at most 256 bins a map, about 17 ids a bin with a million KVs, and HashMap
     * makes every bin of more than 8 a red-black tree, of 56-byte HashMap$TreeNode entries
     * instead of 24-byte HashMap$Node ones (bergdb item 006-02, section 4). An unsigned
     * shift: the index is never negative (the fault of 2026-10-13, testLargeIds).
     */
    static int mapIndex(long id) {
        return (int) ((id * 0x9E3779B97F4A7C15L) >>> (64 - MAP_BITS));
    }
    
    // ======== Tests ========
    
    /**
     * Regression test for a bug found 2026-10-13: node ids of 2^31 and more,
     * stream positions past 2.1 GB, gave a negative map index.
     */
    @Nano
    public static void testLargeIds() {
        Cache3 cache = new Cache3(new Cache.DbInfo() {
            public PointerLocks getPointerLocks() { return null; }
        });
        long[] ids = {1L << 31, (1L << 31) + 0x94, (1L << 32) - 1, 5L << 30, 1L << 40, Long.MAX_VALUE};
        for (long id : ids) {
            Assert.assertTrue(cache.getNode(id) == null);
        }
    }

    /**
     * HashMap's bins stay small (bergdb item 005-08): node ids as the writer makes them, in
     * each transaction consecutive odd numbers from the stream's end (Spos.nextVpos), go into
     * the maps by mapIndex and into the bins as HashMap puts them: the low bits of
     * h ^ (h >>> 16), h the Long's hash, the capacity doubled when the size passes three
     * quarters of it. A put into a bin of 8 makes it a red-black tree (HashMap$TreeNode).
     * With the XOR of the id's bytes about half the puts of each case below did; now, as with
     * random hashes, a few in a million at most.
     */
    @Nano
    public static void testBinsStaySmall() {
        // A million ids each: the first stream position, the nodes and the stream bytes of a
        // transaction. Props's MEM (100 small KVs a transaction); single puts on a stream past
        // 4 GB; large transactions far into the stream.
        long[][] cases = {{0, 110, 5000}, {(1L << 32) + 77, 4, 150}, {(1L << 40) + 12345, 1000, 30000}};
        int n = 1000 * 1000;
        for (long[] c : cases) {
            int[] size = new int[1 << MAP_BITS];
            long[][] ids = new long[1 << MAP_BITS][16];
            int[][] bins = new int[1 << MAP_BITS][16];
            long trees = 0;
            int largest = 0;
            int count = 0;
            for (long pos = c[0]; count < n; pos += c[2]) {
                long id = Spos.nextVpos(pos);
                for (int k = 0; k < c[1] && count < n; k++, count++, id += 2) {
                    int m = mapIndex(id);
                    int[] b = bins[m];
                    int i = bin(id, b.length);
                    if (b[i] >= 8 && b.length >= 64) trees++;
                    largest = Math.max(largest, ++b[i]);
                    if (size[m] == ids[m].length) ids[m] = Arrays.copyOf(ids[m], 2 * size[m]);
                    ids[m][size[m]++] = id;
                    if (size[m] > b.length / 4 * 3) {          // HashMap.resize()
                        b = bins[m] = new int[2 * b.length];
                        for (int j = 0; j < size[m]; j++) b[bin(ids[m][j], b.length)]++;
                    }
                }
            }
            Assert.assertTrue("puts into a bin of 8: " + trees, trees <= n / 100000);
            Assert.assertTrue("the largest bin: " + largest, largest <= 10);
        }
    }

    /** HashMap's bin of key 'id' in a table of 'capacity' bins, a power of two. */
    private static int bin(long id, int capacity) {
        int h = Long.hashCode(id);
        return (h ^ (h >>> 16)) & (capacity - 1);
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
