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
import bergdb.storage.StreamFormatException;

/**
 * A deterministic node cache; size is known, weak references are *not* used.
 * The cache ensures there is never more than one Node object with a given
 * node id.
 *
 * <p>The node table is 4,096 HashMaps from node id to object, each with its own lock, its
 * Table (getLock): a resize stops one map, 1/4,096 of the table (bergdb item 009, step
 * 1b; 009-02, T1a and section 8: 0.23 ms at 30 million entries under ZGC, where the 256
 * maps under one lock of before took 11.6 ms). Until 2026-10-25 the maps' values were
 * CacheEntry objects with a reference count that nothing decremented (bergdb item 004-01,
 * section 9).</p>
 *
 * <p>A map shrinks as well as grows (bergdb 024-33; 024-05, ST6): HashMap only doubles its
 * table, so after a fill and a mass delete the 4,096 tables kept their peak size. A removal
 * that leaves a map's entries under 1/8 of its capacity replaces the map by a copy at a
 * capacity of at least twice its entries (Table.shrinkIfSparse); HashMap grows it again
 * above 3/4. So after either a map is 1/4 to 1/2 full, and only a change of its entries
 * by a factor of at least 1.5 up or 2 down resizes it again.</p>
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
    private final Table[] tables;

    /**
     * The access clock (bergdb item 001, WP R8, change 4; bergdb 001-08, M23 and
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
        this.tables = new Table[1 << MAP_BITS];

        for (int i = 0; i < tables.length; i++) {
            tables[i] = new Table();
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
        return table(id);
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
        for (Table t : tables) {
            synchronized (t) {
                result.addAll(t.map.values());
            }
        }
        return result;
    }

    /**
     * The node table's entries, each a node id and its live handle, in the order of handles(),
     * each map under its own lock; for the trace exporter (stress/TraceExport.java, bergdb item
     * 009, step 4c), which writes the table as the Lean model's (HMem.table).
     */
    java.util.List<java.util.Map.Entry<Long, Handle>> entries() {
        java.util.ArrayList<java.util.Map.Entry<Long, Handle>> result =
                new java.util.ArrayList<java.util.Map.Entry<Long, Handle>>();
        for (Table t : tables) {
            synchronized (t) {
                for (java.util.Map.Entry<Long, Handle> e : t.map.entrySet()) {
                    result.add(new java.util.AbstractMap.SimpleImmutableEntry<Long, Handle>(e));
                }
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
        for (Table t : tables) {
            synchronized (t) {
                for (Handle h : t.map.values()) {
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

    /**
     * A pointer from 'from' to 'to' was made by the writer (Dag, TopDs). An index node's
     * handle is in the table since its object was made or installed. A value is counted with
     * 'from' at the next count of 'from', its write (Residents.grown), not here: Residents.added
     * counts no value alone (bergdb 015-15; a value that two leaves hold is counted for each,
     * 009-02, 4.8).
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
     * object if it is better: canonical, or a newer version (bergdb 011-04, level 2). Returns
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
            checkType(old, node);
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
     * One node, one type (2026-11-06, bergdb 019-32): a node from a damaged stream whose id
     * was changed to that of a node of another type (its checksum right) went into that
     * node's handle, and a pointer to the other node got it: a ClassCastException.
     * 
     * @throws StreamFormatException  If 'old', the handle's object, is of another type.
     */
    private static void checkType(Node old, Node node) {
        if (old != null && old.getType() != node.getType()) {
            throw new StreamFormatException("Two nodes with the id " + node.getId()
                    + ": of type " + old.getType() + " at " + old.getSpos() + ", and of type "
                    + node.getType() + " at " + node.getSpos() + ".");
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
        checkType(old, node);
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
            if (!h.casState(Handle.LIVE, Handle.DEAD)) {
                return false;
            }
            kill(h, h.obj);     // read after the compareAndSet (kill)
            if (internalGet(h.id) == h) {
                internalRemove(h.id);
            }
            return true;
        }
    }

    /**
     * The rest of an eviction of h, which the caller has made DEAD under h's map lock; the
     * caller removes h from the map. Returns the bytes h's object was counted with. The
     * caller reads h's object after the compareAndSet that made h DEAD (bergdb item 009,
     * step 3d): a loader sets the object only while h is LOADING, so not after it, but it
     * may have installed one since the caller last read it. (Read before, the object stayed
     * in the dead handle; the audit found it.)
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

    /**
     * 'node', a key node that its transaction made and took back (bergdb 023-07, section 5.1;
     * Dag.takeBack, Dag.takeBackRoot), leaves the table as an
     * evicted object does: its handle dies, its canonical flag is cleared, and the handle
     * leaves the table. It was never written, and no node names it. The caller holds
     * Db.writeLock (or is the startup).
     */
    public void dropNode(Node node) {
        final long id = node.getId();
        synchronized (getLock(id)) {
            final Handle h = internalGet(id);
            if (h == null || h.obj != node) {
                node.setCanonical(false);
                return;
            }
            if (!h.casState(Handle.LIVE, Handle.DEAD)) {
                return;
            }
            kill(h, node);
            internalRemove(id);
        }
    }
    
    /** Whether eviction may take an object (Eviction.detachable, with the batch's roots). */
    interface Detachable {
        boolean detachable(Node o);
    }

    /**
     * One CLOCK step (bergdb item 009, step 3b; 009-02, 4.7, T2a): the handles of map k,
     * under its lock, if it has at most 'max' (else null, and nothing done: the caller takes
     * the map in parts, clockStep(int, Handle[], ...); bergdb 015-67). A handle whose CLOCK
     * bit is set gets it cleared (a second chance); one with the bit clear and a detachable
     * object is evicted; a live handle with no object (a read that kept nothing) leaves the
     * table too. A handle that a loader holds (LOADING) is skipped. Returns the bytes freed,
     * the objects evicted, the handles examined and the detachable objects met; adds the
     * objects that are not detachable (pinned) to 'pinned', for their values and their bytes.
     */
    long[] clockStep(int k, Detachable d, java.util.List<Node> pinned, long max) {
        Table t = tables[k];
        long[] c = new long[4];
        synchronized (t) {
            HashMap<Long, Handle> m = t.map;
            if (m.size() > max) return null;
            java.util.Iterator<Handle> it = m.values().iterator();
            while (it.hasNext()) {
                if (clockStep(it.next(), d, pinned, c)) it.remove();
            }
            t.shrinkIfSparse();
        }
        return c;
    }

    /**
     * The handles of map k, copied under its lock: for a map that a CLOCK step takes in parts
     * (bergdb 015-67). A map has no maximum size; the copy is its only work that grows with
     * it, a reference a handle.
     */
    Handle[] mapHandles(int k) {
        Table t = tables[k];
        synchronized (t) {
            return t.map.values().toArray(new Handle[t.map.size()]);
        }
    }

    /**
     * One part of a CLOCK step over map k (bergdb 015-67): handles from to to-1 of 'part',
     * a copy of the map's handles (mapHandles), under the map's lock, as clockStep(int, ...)
     * does with each; one that has left the map since the copy (an eviction, dropIfEmpty) is
     * skipped, and one added since is met in the next round. So the work of a step is
     * bounded by its handles however large the map, and the next batch goes on in the same
     * map where this one stopped. Returns as clockStep(int, ...) does; the handles examined
     * are to - from.
     */
    long[] clockStep(int k, Handle[] part, int from, int to, Detachable d,
            java.util.List<Node> pinned) {
        Table t = tables[k];
        long[] c = new long[4];
        synchronized (t) {
            HashMap<Long, Handle> m = t.map;
            for (int j = from; j < to; j++) {
                Handle h = part[j];
                if (m.get(h.id) != h) {
                    c[2]++;
                    continue;
                }
                if (clockStep(h, d, pinned, c)) m.remove(h.id);
            }
            t.shrinkIfSparse();
        }
        return c;
    }

    /**
     * Handle h in a CLOCK step, under its map's lock; adds to c, as the step returns it.
     * Returns true if h leaves the map (the caller removes it).
     */
    private boolean clockStep(Handle h, Detachable d, java.util.List<Node> pinned, long[] c) {
        c[2]++;
        Node o = h.obj;
        if (o == null) {
            if (h.casState(Handle.LIVE, Handle.DEAD)) {
                o = h.obj;      // a loader may have installed one since (kill)
                if (o != null) {
                    c[0] += kill(h, o);
                    c[1]++;
                }
                return true;
            }
            return false;
        }
        if (!d.detachable(o)) {
            pinned.add(o);
            return false;
        }
        c[3]++;
        if (h.ref != 0) {
            h.ref = 0;
            return false;
        }
        if (!h.casState(Handle.LIVE, Handle.DEAD)) return false;
        c[0] += kill(h, h.obj);    // again: a loader may have replaced o (kill)
        c[1]++;
        return true;
    }

    /**
     * One part of a step of the dead hand over map k (bergdb 023-05, P6): handles from to
     * to-1 of 'part', a copy of the map's handles (mapHandles), under the map's lock, as
     * clockStep(int, Handle[], ...) takes them. An object stored before 'cut', the decided
     * cut position (Reclaim.getFirstAvailablePos), is evicted whatever its CLOCK bit, if it
     * is detachable: no lookup at an available time reaches it (Reclaim's class comment:
     * every node reachable from the first available time on is stored at the cut or later,
     * or is dirty, so pinned). A live handle with no object leaves the table, as in a CLOCK
     * step. The key nodes that stay are added to 'kept', for the values below the cut that
     * their pointers hold (Eviction.deadStep). Returns the bytes freed, the objects evicted
     * and the handles examined.
     */
    long[] deadStep(int k, Handle[] part, int from, int to, long cut, Detachable d,
            java.util.List<Node> kept) {
        Table t = tables[k];
        long[] c = new long[3];
        synchronized (t) {
            HashMap<Long, Handle> m = t.map;
            for (int j = from; j < to; j++) {
                Handle h = part[j];
                c[2]++;
                if (m.get(h.id) != h) continue;     // left the map since the copy
                Node o = h.obj;
                if (o == null) {
                    if (h.casState(Handle.LIVE, Handle.DEAD)) {
                        o = h.obj;      // a loader may have installed one since (kill)
                        if (o != null) {
                            c[0] += kill(h, o);
                            c[1]++;
                        }
                        m.remove(h.id);
                    }
                    continue;
                }
                long spos = o.getSpos();
                if (Spos.isValid(spos) && !Spos.isVpos(spos) && spos < cut && d.detachable(o)) {
                    if (!h.casState(Handle.LIVE, Handle.DEAD)) continue;   // a loader holds it
                    c[0] += kill(h, h.obj);     // again: a loader may have replaced o (kill)
                    c[1]++;
                    m.remove(h.id);
                    continue;
                }
                if (o instanceof KeyNode) kept.add(o);
            }
            t.shrinkIfSparse();
        }
        return c;
    }

    /** The number of maps, for the CLOCK hand. */
    static int maps() {
        return 1 << MAP_BITS;
    }

    /**
     * Removes live handle h if it has no object: a read that kept nothing (a cache policy
     * that caches nothing) leaves no empty handle behind. The caller holds no handle monitor,
     * and not the write lock: the writer may be in a transaction meanwhile.
     *
     * <p>The test that h is empty decides only after h is DEAD (bergdb 019-46). Until then a
     * loader could fill h after the test: a reader's version, or the writer's, which its
     * follow then makes canonical (NodeCollection.followStreamPointer, steps 4 and 6; the
     * writer takes h from the map before this method takes the map's lock, and fills it
     * under h's monitor). The drop killed h with that object in it (kill): the writer's
     * object lost its canonical flag and left the table while the writer went on with it in
     * its transaction, and the parent's pointer kept h, whose written position names the
     * version before the transaction: the parent's record named a stale version, readers got
     * old values, and the audit found INV-SLOT, or an object of D that was not canonical.
     * Once h is DEAD, no loader fills it (install needs h LOADING, which only a LIVE handle
     * becomes), register does not take it (it holds the map's lock, which this method holds,
     * and replaces a dead handle), and the writer's makeCanonical only marks the object that
     * its follow found in h or installed there, never fills an empty h. So an object seen
     * after the compareAndSet was put there before it, and h is LIVE again with it; one not
     * seen will not come, and h leaves the table. The DEAD between is not seen by
     * liveOrNewHandle (the map's lock); a loader that sees it resolves the node again under
     * that lock, and so gets h again.</p>
     */
    void dropIfEmpty(Handle h) {
        synchronized (getLock(h.id)) {
            if (h.obj != null || internalGet(h.id) != h) {
                return;
            }
            final Runnable hook = dropIfEmptyHook;
            if (hook != null) {
                hook.run();
            }
            if (!h.casState(Handle.LIVE, Handle.DEAD)) {
                return;         // a loader holds it (LOADING): not empty for long
            }
            final Runnable deadHook = dropIfEmptyDeadHook;
            if (deadHook != null) {
                deadHook.run();
            }
            if (h.obj != null) {
                boolean live = h.casState(Handle.DEAD, Handle.LIVE);
                assert live : "a dead handle changed state";
                return;
            }
            internalRemove(h.id);
        }
    }
    
    /**
     * Run by dropIfEmpty between its test that the handle is empty and its compareAndSet,
     * if not null: a forced schedule of bergdb 019-46. For tests only.
     */
    static volatile Runnable dropIfEmptyHook = null;

    /**
     * Run by dropIfEmpty after its compareAndSet made the handle DEAD and before it looks for
     * an object (and makes the handle LIVE again if one came), if not null: a forced schedule
     * in that window (bergdb 019-46, the writer's assert). For tests only.
     */
    static volatile Runnable dropIfEmptyDeadHook = null;

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
        table(id).put(id, h);
    }

    private Handle internalGet(long id) {
        return table(id).map.get(id);
    }

    private void internalRemove(long id) {
        Table t = table(id);
        t.map.remove(id);
        t.shrinkIfSparse();
    }

    private Table table(long id) {
        return tables[mapIndex(id)];
    }

    /**
     * One map of the node table and its lock (getLock), with the map's capacity, the length
     * of its HashMap's table (bergdb 024-33). The lock is the Table, not the map, since a
     * shrink replaces the map: every access reads 'map' under the Table's monitor.
     */
    static final class Table {
        /** HashMap's first capacity, and the least a shrink leaves. */
        static final int MIN_CAPACITY = 16;

        HashMap<Long, Handle> map = new HashMap<Long, Handle>();

        /**
         * The capacity as HashMap sets it: 16 at the first put, doubled when a put takes the
         * size over 3/4 of it (put), and what a shrink chose. HashMap also doubles a table
         * under 64 slots that gets a bin of 8 (treeifyBin), which the hashing makes rare
         * (testBinsStaySmall); this value is then lower than the table's, and the next shrink
         * comes later than it would, never sooner.
         */
        int capacity = MIN_CAPACITY;

        void put(long id, Handle h) {
            map.put(id, h);
            if (map.size() > capacity / 4 * 3) capacity *= 2;
        }

        /**
         * Shrinks the map if its entries are under 1/8 of its capacity: a copy with a
         * capacity of the least power of two that is at least twice the entries (and at
         * least 16), so 1/4 to 1/2 full. Called under this Table's monitor after a removal,
         * never during an iteration of the map. Its work, a copy of fewer than capacity / 8
         * entries, is paid for by the more than capacity / 8 removals since the capacity last
         * changed: a grow or a shrink leaves more than capacity / 4 entries.
         */
        void shrinkIfSparse() {
            int n = map.size();
            if (capacity <= MIN_CAPACITY || n >= capacity / 8) return;
            int c = Math.max(MIN_CAPACITY, Integer.highestOneBit(Math.max(1, 2 * n - 1)) << 1);
            HashMap<Long, Handle> m = new HashMap<Long, Handle>(c);
            m.putAll(map);
            map = m;
            capacity = c;
        }
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
        Cache3 cache = new Cache3(new Cache.DbInfo() {});
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
        Cache3 cache = new Cache3(new Cache.DbInfo() {});
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
     * The tables shrink (bergdb 024-33; 024-05, ST6): 300,000 handles put and then all but
     * every 100th removed leave each map at most 4 times the capacity its entries need, and
     * every handle left is found; all removed, each map is back at 16. Then puts grow them
     * again.
     */
    @Nano
    public static void testTablesShrink() {
        Cache3 cache = new Cache3(new Cache.DbInfo() {});
        int n = 300 * 1000;
        long peak = 0;
        for (int i = 0; i < n; i++) cache.liveOrNewHandle(2 * i + 1);
        for (Table t : cache.tables) peak += t.capacity;
        for (int i = 0; i < n; i++) {
            if (i % 100 != 0) cache.dropIfEmpty(cache.liveHandle(2 * i + 1));
        }
        long sum = 0;
        for (Table t : cache.tables) {
            Assert.assertTrue("capacity " + t.capacity + " for " + t.map.size(),
                    t.capacity == Table.MIN_CAPACITY || t.capacity <= 8 * t.map.size());
            sum += t.capacity;
        }
        Assert.assertTrue("after: " + sum + ", peak: " + peak, sum * 4 < peak);
        for (int i = 0; i < n; i++) {
            Handle h = cache.liveHandle(2 * i + 1);
            Assert.assertTrue((h != null) == (i % 100 == 0));
            if (h != null) cache.dropIfEmpty(h);
        }
        for (Table t : cache.tables) {
            Assert.assertEquals(0, t.map.size());
            Assert.assertEquals(Table.MIN_CAPACITY, t.capacity);
        }
        for (int i = 0; i < n; i++) cache.liveOrNewHandle(2 * i + 1);
        sum = 0;
        for (Table t : cache.tables) sum += t.capacity;
        Assert.assertEquals(peak, sum);
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
