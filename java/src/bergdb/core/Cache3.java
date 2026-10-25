package bergdb.core;

import java.util.Arrays;
import java.util.HashMap;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * A deterministic node cache; size is known, weak references are *not* used.
 * The cache ensures there is never more than one Node object with a given
 * node id.
 *
 * <p>The node table is 4,096 HashMaps from node id to object, each with its own lock, the
 * map itself (getLock): a resize stops one map, 1/4,096 of the table (bergdb item 009, step
 * 1b; 009-02, T1a and section 8: 0.23 ms at 30 million entries under ZGC, where the 256
 * maps under one lock of before took 11.6 ms). Until 2026-10-25 the maps' values were
 * CacheEntry objects with a reference count that nothing decremented (bergdb item 004-01,
 * section 9).</p>
 *
 * <p>Since bergdb item 009, step 3a, the maps hold handles (dag/Handle.java): the live handle
 * of each index node that has one, and through it the node's one object. A memory pointer of
 * an index node holds its pointee's handle; eviction kills a handle (evict) and nothing has
 * to know which pointers hold it; a pointer that holds a dead handle finds the live one here
 * by the id (liveOrNewHandle). One live handle per node id, so one object, and at most one
 * canonical object, per node. Values have no handles and are not in the table (009-02,
 * 4.8).</p>
 *
 * @author Frans Lundberg
 */
public class Cache3 {
    //
    // Simple, non-optimal implementation to start with.
    //

    private static final long INITIAL_CACHE_SIZE = 10*1000;

    /** The node table is 2^MAP_BITS maps; mapIndex picks one by the node id. */
    static final int MAP_BITS = 12;

    @SuppressWarnings("unused")
    private final Cache.DbInfo dbInfo;
    private final Object bigLock;
    private long sizeIndicator;
    private long totalSize;     // total cache size estimation, in bytes
    private long putSize;
    private final HashMap<Long, Handle>[] maps;

    /**
     * The access clock (bergdb item 001, WP R8, change 4; docs/level4-alignment.md, M23 and
     * M40): it advances by one at every node read from the stream (NodeCollection) and every
     * node the writer makes (Db), so in read-only workloads too. The access data that an
     * operation writes into the handles it follows (bergdb item 009, step 3a; before, into
     * the memory pointers) is minus its value (Db.getAccessData, dag/AccessData.java), for the
     * age policy of eviction (J7). A field of its own: before 2026-10-17 the access data was
     * minus putSize, which nothing advances, so the constant -10,000; the clock starts there.
     * Read and advanced without a lock.
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
        this.maps = new HashMap[1 << MAP_BITS];

        for (int i = 0; i < maps.length; i++) {
            maps[i] = new HashMap<Long, Handle>();
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
     * Gets a lock object for one specific node: the lock of its map, which every change and
     * read of the node's entry takes (bergdb item 009, step 1b; before, one lock for the
     * whole table).
     *
     * @param id
     *      Node ID.
     */
    public Object getLock(long id) {
        return map(id);
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

    /** The node's live handle, or null. */
    public Handle liveHandle(long id) {
        synchronized (getLock(id)) {
            return internalGet(id);
        }
    }

    /**
     * The node's live handle, made (with no object) if it has none: a pointer that holds no
     * handle, or a dead one, resolves to it (009-02, 4.4, the slow path's step 1).
     */
    public Handle liveOrNewHandle(long id) {
        synchronized (getLock(id)) {
            Handle h = internalGet(id);
            if (h == null) {
                h = new Handle(id);
                internalPut(id, h);
            }
            return h;
        }
    }

    /**
     * The live handles, for eviction's walks and the audit, in the order of the maps and their
     * bins, which follows the node ids (mapIndex), not the tree or the age. Each map under its
     * own lock, in turn: readers add handles meanwhile.
     */
    public java.util.List<Handle> handles() {
        java.util.ArrayList<Handle> result = new java.util.ArrayList<Handle>();
        for (HashMap<Long, Handle> m : maps) {
            synchronized (m) {
                result.addAll(m.values());
            }
        }
        return result;
    }

    /**
     * The objects of the live handles, for the audit (Audit) and the walks (Residents), in the
     * order of handles().
     */
    public java.util.List<Node> nodes() {
        java.util.ArrayList<Node> result = new java.util.ArrayList<Node>();
        for (HashMap<Long, Handle> m : maps) {
            synchronized (m) {
                for (Handle h : m.values()) {
                    Node o = h.obj;
                    if (o != null) result.add(o);
                }
            }
        }
        return result;
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

    /**
     * A pointer from 'from' to 'to' was made by the writer, or swizzled by a follow (Dag,
     * TopDs, NodeCollection). An index node's handle is in the table since its object was made
     * or installed; a value counts as resident from here (Residents; a value that two leaves
     * hold is counted for each until the next resync, 009-02, 4.8).
     */
    public void pointerCreated(Node from, int index, Node to) {
        if (!to.isIndexNode()) {
            residents.added(to);
        }
    }

    /**
     * Enters 'node', an object the writer or the startup made, as its node's object:
     * canonical, in the node's live handle, made if it has none. A canonical object already
     * there is kept (one canonical object per node); otherwise 'node' replaces the handle's
     * object if it is better: canonical, or a newer version (docs/levels.md, level 2). Returns
     * the handle's object after the call.
     */
    public Node register(Node node) {
        if (!node.isIndexNode()) {
            return node;        // Values have no handles and are not in the table (009-02, 4.8).
        }
        long id = node.getId();

        synchronized (getLock(id)) {
            Handle h = internalGet(id);
            if (h == null) {
                h = handleOf(node);
                if (h == null || h.id != id || h.isDead()) h = new Handle(id);
                internalPut(id, h);
            }
            Node old = h.obj;
            if (old == null || (old != node && isBetter(node, old))) {
                setHandle(node, h);
                residents.added(node);
                h.obj = node;
                if (old != null) residents.released(old);
                return node;
            }
            if (old == node) {
                residents.added(node);      // in a handle made before (Handle.of): counted now
            }
            return old;
        }
    }

    /**
     * Installs 'node', a version read from the stream, in its live handle 'h', unless the
     * handle has a better object (canonical, or a newer version). The caller holds h's
     * monitor (a load, 009-02, T7a). Returns the handle's object after the call.
     */
    public Node install(Handle h, Node node) {
        assert Thread.holdsLock(h);
        Node old = h.obj;
        if (old == null || (old != node && isBetter(node, old))) {
            setHandle(node, h);
            residents.added(node);
            h.obj = node;
            if (old != null) residents.released(old);
            return node;
        }
        return old;
    }

    /**
     * Makes the node's object canonical, for the writer (the Lean model's Mem.promote): the
     * handle's canonical object if it has one, else the newest of 'node', the version the
     * writer followed to, which is the node's latest (INV-SLOT), and the handle's object,
     * which is then marked canonical. Returns that object. Called when the writer reaches a
     * node, with h the node's live handle.
     */
    public Node makeCanonical(Handle h, Node node) {
        synchronized (h) {
            Node other = h.obj;
            Node result = node;

            if (other != null && other != node) {
                if (other.isCanonical() || other.getSpos() > node.getSpos()) {
                    result = other;
                }
            }

            result.setCanonical(true);
            if (other != result) {
                setHandle(result, h);
                h.obj = result;
                if (other != null) residents.released(other);
                residents.added(result);
            }
            residents.promoted(result);
            return result;
        }
    }

    /**
     * Evicts handle h's object (009-02, 4.7): h dies (unless a loader holds it: then false),
     * its written position is set from a canonical object's, the object's canonical flag is
     * cleared (as M31: a reader that holds the object may finish with it), the object leaves
     * the handle and the handle the table. The caller holds Db.writeLock, between
     * transactions, and has checked that the object may be evicted (Eviction.detachable).
     */
    public boolean evict(Handle h) {
        synchronized (getLock(h.id)) {
            Node o = h.obj;
            if (!h.casState(Handle.LIVE, Handle.DEAD)) {
                return false;
            }
            kill(h, o);
            if (internalGet(h.id) == h) {
                internalRemove(h.id);
            }
            return true;
        }
    }

    /**
     * The rest of an eviction of h, which the caller has made DEAD under h's map lock; the
     * caller removes h from the map. Returns the bytes h's object was counted with.
     */
    private int kill(Handle h, Node o) {
        if (o == null) return 0;
        if (o.isCanonical()) {
            long spos = o.getSpos();
            if (Spos.isValid(spos) && !Spos.isVpos(spos)) h.writtenPos = spos;
            o.setCanonical(false);
        }
        h.obj = null;
        return residents.released(o);
    }

    /** Whether eviction may take an object (Eviction.detachable, with the batch's roots). */
    interface Detachable {
        boolean detachable(Node o);
    }

    /**
     * One CLOCK step (bergdb item 009, step 3b; 009-02, 4.7, T2a): the handles of map k,
     * under its lock. A handle whose CLOCK bit is set gets it cleared (a second chance); one
     * with the bit clear and a detachable object is evicted; a live handle with no object
     * (a read that kept nothing) leaves the table too. A handle that a loader holds (LOADING)
     * is skipped. The work is one map's: 1/4,096 of the handles. Returns the bytes freed, the
     * objects evicted, the handles examined and the detachable objects met.
     */
    long[] clockStep(int k, Detachable d) {
        HashMap<Long, Handle> m = maps[k];
        long bytes = 0, objects = 0, examined = 0, candidates = 0;
        synchronized (m) {
            java.util.Iterator<Handle> it = m.values().iterator();
            while (it.hasNext()) {
                Handle h = it.next();
                examined++;
                Node o = h.obj;
                if (o == null) {
                    if (h.casState(Handle.LIVE, Handle.DEAD)) it.remove();
                    continue;
                }
                if (!d.detachable(o)) continue;
                candidates++;
                if (h.ref != 0) {
                    h.ref = 0;
                    continue;
                }
                if (!h.casState(Handle.LIVE, Handle.DEAD)) continue;
                bytes += kill(h, o);
                objects++;
                it.remove();
            }
        }
        return new long[] {bytes, objects, examined, candidates};
    }

    /** The number of maps, for the CLOCK hand. */
    static int maps() {
        return 1 << MAP_BITS;
    }

    /**
     * Removes live handle h if it has no object: a read that kept nothing (a cache policy
     * that caches nothing) leaves no empty handle behind. The caller holds no handle monitor.
     */
    void dropIfEmpty(Handle h) {
        synchronized (getLock(h.id)) {
            if (h.obj == null && internalGet(h.id) == h && h.casState(Handle.LIVE, Handle.DEAD)) {
                internalRemove(h.id);
            }
        }
    }

    /**
     * True if 'node' should replace 'old' in a handle: never a canonical object, otherwise by
     * a canonical object or a newer version.
     */
    private static boolean isBetter(Node node, Node old) {
        if (old.isCanonical()) {
            assert !node.isCanonical() : "two canonical objects for node " + node.getId();
            return false;
        }

        return node.isCanonical() || node.getSpos() > old.getSpos();
    }

    /** The handle an index node's object is in (KeyNode.handle, TopNode.handle), or null. */
    static Handle handleOf(Node node) {
        if (node instanceof KeyNode) return ((KeyNode) node).handle;
        if (node instanceof TopNode) return ((TopNode) node).handle;
        return null;
    }

    private static void setHandle(Node node, Handle h) {
        if (node instanceof KeyNode) ((KeyNode) node).handle = h;
        else if (node instanceof TopNode) ((TopNode) node).handle = h;
    }

    /** The object of the node's live handle, or null. */
    public Node getNode(long id) {
        synchronized (getLock(id)) {
            Handle h = internalGet(id);
            return h == null ? null : h.obj;
        }
    }

    private void internalPut(long id, Handle h) {
        map(id).put(id, h);
    }

    private Handle internalGet(long id) {
        return map(id).get(id);
    }

    private void internalRemove(long id) {
        map(id).remove(id);
    }

    private HashMap<Long, Handle> map(long id) {
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
            Assert.assertTrue(mapIndex(id) >= 0 && mapIndex(id) < 1 << MAP_BITS);
        }
    }

    /**
     * One live handle per node id (bergdb item 009, step 3a): liveOrNewHandle makes it once;
     * an evicted handle is dead, out of the table, and the next resolve makes a new one.
     */
    @Nano
    public static void testOneLiveHandle() {
        Cache3 cache = new Cache3(new Cache.DbInfo() {
            public PointerLocks getPointerLocks() { return null; }
        });
        Handle h1 = cache.liveOrNewHandle(7);
        Assert.assertTrue(h1 == cache.liveOrNewHandle(7));
        Assert.assertTrue(h1 == cache.liveHandle(7));
        Assert.assertTrue(cache.evict(h1));
        Assert.assertTrue(h1.isDead());
        Assert.assertTrue(cache.liveHandle(7) == null);
        Handle h2 = cache.liveOrNewHandle(7);
        Assert.assertTrue(h2 != h1 && !h2.isDead());
        Assert.assertTrue(!cache.evict(h1));    // dead already
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
}
