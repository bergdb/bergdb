package bergdb.core;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.Pointee;
import bergdb.dag.Pointer;
import bergdb.dag.PointerFollower;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;
import bergdb.stream.MemoryStream;

/**
 * A node collection for Db to use.
 * An instance of this class adds a cache to NodeStream
 * and implements PointerFollower for Db.
 * 
 * <p>Since 2026-10-12 (bergdb 011-04, level 2), the cache is the node table 
 * shared with Db: one canonical object per node, and Rule R for pointers followed into 
 * the stream. This object is the follower for readers; writer() is the follower for 
 * the writer.</p>
 *
 * <p>Since bergdb item 009 (items/009-handles/02-implementation-plan.md, 4.4), a pointer to
 * an index node holds the node's handle (dag/Handle.java): a follow takes the handle's
 * object if it may serve the pointer (Handle.usable), without a lock (step 3c; the barriers
 * of 02, 3.4); else the slow path resolves the pointer to the node's live handle by the id,
 * with the reference raised to the newer of the pointer's after Rule R and its dead
 * handle's written position (written back into the pointer: no record changes), and loads
 * that version into the handle under its monitor, so that two readers do not read the same
 * node (T7a). A pointer to a value holds the value (Pointee).</p>
 * 
 * @author Frans Lundberg
 */
public class NodeCollection implements PointerFollower {
    //
    // Idea is to split into 1000 maps and do evict by
    // map scan (whole map, but that's 1/1000 of whole cache).
    //
    
    private NodeStream nodeStream;
    private Cache3 cache;
    private final PointerFollower writer = new WriterFollower();
    private volatile StartupSection section;
    
    /**
     * True from setStartupSection() until endReconstruction(): while DbStarter rebuilds the
     * database. Only then is a key node version of the startup section that a pointer leads
     * to cut back to the startup time; a load at runtime never is (bergdb item 001, WP R8,
     * change 2; bergdb 001-08, M22: the Level 4 loader, `Mem.follow4`, lean/SIS/Evict.lean until
     * bergdb 005-62).
     */
    private volatile boolean reconstructing = false;
    
    /** Node ids read from node headers, by position; see idOf(). */
    @SuppressWarnings("serial")
    private final Map<Long, Long> idByPos = new LinkedHashMap<Long, Long>(1024, 0.75f, true) {
        protected boolean removeEldestEntry(Map.Entry<Long, Long> eldest) {
            return size() > 100 * 1000;
        }
    };
    
    /**
     * Told of every first touch of a stream pointer; for tests only (bergdb item 001,
     * WP L5: java/stress/TraceExport.java records them for the trace checker). Null, and
     * so doing nothing, unless a test sets it.
     */
    public interface FirstTouchListener {
        /**
         * A first touch of node id through a stream pointer that names position ref after
         * Rule R. result is the object followed: the node table's canonical object (read is
         * false), or the version just read at ref (read is true; cutBack is true if it was
         * cut back to the startup time). Called before the writer makes result canonical.
         */
        void firstTouch(long id, long ref, Node result, boolean read, boolean cutBack);
    }
    
    /** See FirstTouchListener. For tests only. */
    public static volatile FirstTouchListener firstTouchListener = null;
    
    /**
     * Told after a reader followed a stream pointer, when it holds no lock any more
     * (bergdb item 001, WP J7: the capacity controller's load-triggered sweeps, Eviction).
     */
    public interface LoadListener {
        /**
         * op is the follow's: a reader's GetData, or a transaction's warmup's
         * (Trans.WarmupGetData), whose loads do not wait for eviction (bergdb 005-52).
         */
        void loaded(OpData op);
    }
    
    private volatile LoadListener loadListener = null;
    
    /** Loads since the start (the readers', the writer's and maintenance), a metric. */
    private final java.util.concurrent.atomic.AtomicLong loads =
            new java.util.concurrent.atomic.AtomicLong();
    
    /** See LoadListener. */
    public void setLoadListener(LoadListener listener) {
        this.loadListener = listener;
    }
    
    /** The versions read from the stream since the start, by every follower. */
    public long loads() {
        return loads.get();
    }
    
    /** Rule R, see setStartupSection(). Immutable. */
    private static final class StartupSection {
        final Map<Long, Long> newById;
        final long startPos;
        final long startupTime;
        
        StartupSection(Map<Long, Long> newById, long startPos, long startupTime) {
            this.newById = newById;
            this.startPos = startPos;
            this.startupTime = startupTime;
        }
    }
    
    /** Creates a collection with a node table of its own; for tests. */
    public NodeCollection(Cache.DbInfo dbInfo, NodeStream nodeStream) {
        this(dbInfo, nodeStream, new Cache3(dbInfo));
    }
    
    /**
     * @param nodeTable  The node table, shared with Db.
     */
    public NodeCollection(Cache.DbInfo dbInfo, NodeStream nodeStream, Cache3 nodeTable) {
        this.nodeStream = nodeStream;
        this.cache = nodeTable;
    }
    
    /**
     * Returns the follower for the writer (puts and the rerun at startup). It differs
     * from this one in that every node it reaches is made canonical.
     */
    public PointerFollower writer() {
        return writer;
    }
    
    /**
     * Returns a new follower for maintenance reads: reclaim's scan and its reads of each
     * KV (bergdb item 001, WP R8, change 5: M28; bergdb 011-05, 5.1). It loads as
     * the readers' follower does (the canonical object, or the version the slot names after
     * Rule R), but it does not swizzle what it reads into the slot, the node table gets
     * nothing, and it leaves the slots' access data as they are. What it reads stays in a
     * map of its own, by the slot's position, while the follower is in use (one reclaim
     * step), so a version is read once per step. It counts what it follows and loads (WP
     * J6): see MaintenanceFollower.
     */
    public MaintenanceFollower maintenance() {
        return new MaintenanceFollower();
    }

    public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
        //
        // With handles (bergdb item 009, step 3a; items/009-handles/02-implementation-plan.md,
        // 4.4): pointer i holds its pointee's handle, or a value, or nothing yet. If the
        // handle holds an object that may serve the pointer (Handle.usable), the follow
        // takes it; else the slow path resolves the pointer to the node's live handle and
        // loads a version into it, under the handle's monitor, so that two readers do not
        // read the same node (followStreamPointer).
        //

        Node result;
        assert pointerIndex >= 0 : "pointerIndex: " + pointerIndex;
        assert predecessor != null : "predecessor is null";
        assert op.accessData == AccessData.ZERO || AccessData.isValid(op.accessData);

        // The fast path, without a lock (bergdb item 009, step 3c; 009-02, 3.3 and 3.4):
        // an acquire read of the pointer, a handle or a value (getPointee), which pairs with
        // the release store that put it there; then, ordered by it, the opaque read of the
        // reference, the handle's object by its volatile read (Handle.obj), and the test of
        // Handle.usable. Before bergdb 015-14, a pointer to a handle was read plainly (T6b),
        // and the reads after it were ordered by the address dependency only (016-06/R1,
        // R1-F3). Until step 3c the whole follow held the pointer's lock (PointerLocks), the
        // read of the stream included.
        Pointee pointee = predecessor.getPointee(pointerIndex);
        long pointerPos = predecessor.getPointerPos(pointerIndex);

        Node mem = memoryObject(pointee, pointerPos);
        if (mem != null) {
            touch(pointee, op);
            op.pointerListener.pointerFollowed(
                    predecessor, pointerIndex, mem, Pointer.TYPE_MEMORY);
            return mem;
        }

        // The slow path: the pair again under the node's monitor (C2), then resolve and
        // load (followStreamPointer), under the handle's monitor (T7a). Locks are cheap
        // beside a read of the stream.
        synchronized (predecessor) {
            pointee = predecessor.getPointee(pointerIndex);
            pointerPos = predecessor.getPointerPos(pointerIndex);
        }
        assert pointee != null || pointerPos != Spos.NULL : "Pointer is null, index "
                + pointerIndex + " of " + predecessor.getId();
        mem = memoryObject(pointee, pointerPos);
        if (mem != null) {
            touch(pointee, op);
            op.pointerListener.pointerFollowed(
                    predecessor, pointerIndex, mem, Pointer.TYPE_MEMORY);
            return mem;
        }
        result = followStreamPointer(predecessor, pointerIndex, pointerPos,
                (Handle) (pointee instanceof Handle ? pointee : null), op, false, null);

        // The capacity controller (WP J7), told the follow's op (bergdb 005-52).
        final LoadListener l = loadListener;
        if (l != null) l.loaded(op);
        return result;
    }

    /**
     * The object that pointee (what a pointer holds) gives a pointer with reference ref
     * without a load: a value; or the handle's object if the handle is live and the object
     * may serve the pointer (Handle.usable); else null.
     */
    static Node memoryObject(Pointee pointee, long ref) {
        if (pointee instanceof ValueNode) return (ValueNode) pointee;
        if (pointee == null) return null;
        Handle h = (Handle) pointee;
        Node o = h.obj;
        return o != null && Handle.usable(o, ref) ? o : null;
    }

    /**
     * A follow sets the pointee's CLOCK bit (bergdb item 009, step 3b; 009-02, 4.7), and only
     * when it is clear, so that a hot handle's line is not written on every follow. Before
     * step 3b (since 3a), the follow's access data went into the handle, for an age order;
     * before 3a, into the pointer.
     */
    private static void touch(Pointee pointee, OpData op) {
        if (pointee instanceof Handle) {
            Handle h = (Handle) pointee;
            if (h.ref == 0) h.ref = 1;
        }
    }

    /** The follower for the writer, see writer(). */
    private final class WriterFollower implements PointerFollower {
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node result;
            assert pointerIndex >= 0 : "pointerIndex: " + pointerIndex;
            assert predecessor != null : "predecessor is null";
            assert op.accessData == AccessData.ZERO || AccessData.isValid(op.accessData);

            Pointee pointee;
            long pointerPos;
            synchronized (predecessor) {        // a coherent pair (C2; bergdb 009, step 3c)
                pointee = predecessor.getPointee(pointerIndex);
                pointerPos = predecessor.getPointerPos(pointerIndex);
            }

            assert pointee != null || pointerPos != Spos.NULL : "Pointer is null, index "
                    + pointerIndex + " of " + predecessor.getId();

            Node mem = memoryObject(pointee, pointerPos);
            if (mem != null) {
                result = mem;
                if (!result.isCanonical()) {
                    result = cache.makeCanonical((Handle) pointee, result);
                }
                touch(pointee, op);
                op.pointerListener.pointerFollowed(
                        predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);

            } else {
                result = followStreamPointer(predecessor, pointerIndex, pointerPos,
                        (Handle) (pointee instanceof Handle ? pointee : null), op, true,
                        null);
            }

            return result;
        }
    }

    /**
     * The follower for maintenance reads, see maintenance(). It counts the index nodes it
     * follows, by node id, which is the same whatever is resident (a reclaim step's reserve,
     * bergdb item 001, WP J6: these are the nodes its touch makes dirty), and the versions it
     * loads from the stream, with their memory size (Reclaim.Stats). One thread: the writer.
     */
    public final class MaintenanceFollower implements PointerFollower {
        private final Map<Long, Node> read = new HashMap<Long, Node>();
        private final java.util.HashSet<Long> indexIds = new java.util.HashSet<Long>();
        private long loads = 0, loadBytes = 0;

        /** The index nodes followed so far, by id. */
        public int indexNodes() {
            return indexIds.size();
        }

        /** The versions loaded from the stream so far. */
        public long loads() {
            return loads;
        }

        /** The memory size of the versions loaded so far (Node.getMemSize()). */
        public long loadBytes() {
            return loadBytes;
        }

        void loaded(Node node) {
            loads++;
            loadBytes += node.getMemSize();
        }

        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            assert pointerIndex >= 0 : "pointerIndex: " + pointerIndex;
            assert predecessor != null : "predecessor is null";

            {
                Pointee pointee;
                long pointerPos;
                synchronized (predecessor) {    // a coherent pair (C2; bergdb 009, step 3c)
                    pointee = predecessor.getPointee(pointerIndex);
                    pointerPos = predecessor.getPointerPos(pointerIndex);
                }

                assert pointee != null || pointerPos != Spos.NULL : "Pointer is null, index "
                        + pointerIndex + " of " + predecessor.getId();

                Node mem = memoryObject(pointee, pointerPos);
                if (mem != null) {
                    if (mem.isIndexNode()) indexIds.add(mem.getId());
                    op.pointerListener.pointerFollowed(
                            predecessor, pointerIndex, mem, Pointer.TYPE_MEMORY);
                    return mem;
                }

                // By the version the pointer names: a dead handle's written position counts
                // (followStreamPointer; bergdb item 009, step 3a), so two pointers with the same
                // position may name two versions.
                Handle h = (Handle) (pointee instanceof Handle ? pointee : null);
                long key = h == null ? pointerPos : newerPos(pointerPos, h.writtenPos);
                Node result = read.get(key);
                if (result == null) {
                    result = followStreamPointer(predecessor, pointerIndex, pointerPos, h, op,
                            false, this);
                    read.put(key, result);
                    if (result.isIndexNode()) indexIds.add(result.getId());
                } else {
                    op.pointerListener.pointerFollowed(
                            predecessor, pointerIndex, result, Pointer.TYPE_STREAM);
                }
                return result;
            }
        }
    }

    /**
     * Follows a pointer whose handle holds no object that may serve it (or that holds no
     * handle): the slow path of 009-02, 4.4. The caller holds no lock (since bergdb item
     * 009, step 3c; before, the pointer's lock); every change of the predecessor's pointer
     * is made under its monitor (setRef, setPointee; C2). A maintenance
     * read (maintenance not null) does not swizzle, makes no handle and installs nothing, and
     * the maintenance follower counts a load.
     *
     * <p>A pointer to a value: the value read at the pointer's position, put into the
     * pointer (unless maintenance, or the cache policy says no). A pointer to an index node:
     * (1) the node id: the handle's, a vpos, or the header at the position; (2) Rule R: the
     * newest version in the startup section, written into the pointer's reference, which
     * changes no record (the writer applies Rule R to every reference it writes, and Rule R
     * applied twice gives what it gives once); (3) the node's live handle, made if it has
     * none; (4) under the handle's monitor, its object if it may serve the pointer, else
     * the version read at the newer of the reference and the position this process last
     * wrote the node at, installed in the handle (Cache3.install), unless a better object is
     * there; (5) the live handle into the pointer; (6) for the writer, the canonical
     * object.</p>
     */
    private Node followStreamPointer(Node predecessor, int pointerIndex, long pointerPos,
            Handle handle, OpData op, boolean isWriter, MaintenanceFollower maintenance) {
        final boolean isMaintenance = maintenance != null;

        if (!pointsToIndexNode(predecessor, pointerIndex)) {
            return followValuePointer(predecessor, pointerIndex, pointerPos, op, maintenance);
        }

        // 1. The id of the node. A vpos is the id of a node that had not been written
        //    when the pointer was written.

        final long id;
        if (handle != null) {
            id = handle.id;
        } else if (Spos.isVpos(pointerPos)) {
            id = pointerPos;
        } else {
            // A check, not an assert (2026-11-06, bergdb 019-32): stream data.
            if (pointerPos < 0) {
                throw new StreamFormatException("Bad pointer " + pointerPos + ", index "
                        + pointerIndex + " of node " + predecessor.getId() + ".");
            }
            id = nodeStream.readNodeHeader(pointerPos).id();
        }

        // 2. The version the pointer names, after Rule R: a newer version in the startup
        //    section replaces it.

        final StartupSection mySection = this.section;
        long ref = pointerPos;
        if (mySection != null) {
            Long newPos = mySection.newById.get(id);
            if (newPos != null && Spos.newer(newPos, ref)) {
                ref = newPos;
            }
        }
        // A dead handle names the position this process last wrote the node at, if the node
        // was evicted from a canonical object (Cache3.evict): the pointer then names that
        // version, as an unswizzled pointer did before (the record rule, 009-02, 4.6).
        if (handle != null) {
            ref = newerPos(ref, handle.writtenPos);
        }
        if (ref != pointerPos && !isMaintenance) {
            predecessor.raiseRef(pointerIndex, ref);    // never lowered (step 3d)
        }

        // 3. The node's live handle. A maintenance read makes none.

        Handle live = handle != null && !handle.isDead() ? handle
                : isMaintenance ? cache.liveHandle(id) : cache.liveOrNewHandle(id);

        // 4. The handle's object, or a version read and installed, under the handle's monitor
        //    (009-02, T7a). The loader's state is LOADING meanwhile, so eviction leaves the
        //    handle alone; a handle that died since step 3 is resolved again.

        Node result = null;
        boolean read = false;
        boolean cutBack = false;

        while (result == null) {
            if (live == null) {
                // A maintenance read of a node with no live handle: read, keep nothing.
                Node node = readVersion(id, ref, pointerIndex, predecessor, maintenance);
                cutBack = cutBack(node, ref);
                result = node;
                read = true;
                break;
            }
            synchronized (live) {
                if (live.isDead()) {
                    live = isMaintenance ? cache.liveHandle(id) : cache.liveOrNewHandle(id);
                    continue;
                }
                Node o = live.obj;
                if (o != null && Handle.usable(o, ref)) {
                    result = o;
                    break;
                }
                if (!live.casState(Handle.LIVE, Handle.LOADING)) {
                    continue;       // evicted meanwhile: dead, resolved again above
                }
                try {
                    Node node = readVersion(id, ref, pointerIndex, predecessor, maintenance);
                    cutBack = cutBack(node, ref);
                    read = true;
                    // A version cut back to the startup time (the reconstruction) is not the
                    // version at its position: only the writer's rerun, which makes it
                    // canonical, keeps it in the handle (M22). The writer keeps every index
                    // node it reaches, whatever its op's cache policy (bergdb 019-46, after
                    // review): its handle then holds an object from here on, which no drop
                    // takes (Cache3.dropIfEmpty) and step 6 makes canonical.
                    if (!isMaintenance && (isWriter || op.cachePolicy.shouldCache(node))
                            && (!cutBack || isWriter)) {
                        result = cache.install(live, node);
                        if (!Handle.usable(result, ref)) result = node;
                    } else {
                        result = node;
                    }
                } finally {
                    live.casState(Handle.LOADING, Handle.LIVE);
                }
            }
        }

        // Also an object of the handle (bergdb 019-32): a damaged node's id names another.
        checkPointeeType(predecessor, pointerIndex, result, ref);

        final FirstTouchListener ftl = firstTouchListener;
        if (ftl != null) {
            ftl.firstTouch(id, ref, result, read, cutBack);
        }

        // A read that kept nothing in a new handle (a cache policy that caches nothing)
        // leaves no empty handle in the table.
        if (live != null && live.obj == null && !isMaintenance) {
            cache.dropIfEmpty(live);
        }

        // 5. Swizzle: the live handle into the pointer. A reader's swizzle replaces only what
        //    it read there (Node.swizzle; bergdb item 009, step 3d): another follow or the
        //    writer may have put a newer handle there since, whose written position a dead
        //    handle of this follow must not hide (EvictionReaderTester's readers under the
        //    capacity controller found the lost update: stale reads). Before the swizzle,
        //    step 2 raised the reference to the written position of the handle it replaces.
        //    The writer's swizzle always replaces: its handle holds the canonical object.
        //    Under the predecessor's monitor, as its count: a pointer that held no handle
        //    holds one now, and the predecessor is counted with it (Residents.handleIn,
        //    bergdb 015-13).

        if (!isMaintenance && live != null && (isWriter || op.cachePolicy.shouldCache(result))
                && (!cutBack || isWriter) && predecessor.getPointee(pointerIndex) != live) {
            synchronized (predecessor) {
                final boolean held = predecessor.getPointee(pointerIndex) instanceof Handle;
                final boolean swizzled;
                if (isWriter) {
                    predecessor.setPointee(pointerIndex, live);
                    swizzled = true;
                } else {
                    swizzled = predecessor.swizzle(pointerIndex, handle, live);
                }
                if (swizzled && !held) cache.residents().handleIn(predecessor);
            }
        }

        // 6. The canonical object, for the writer, in its live handle, which holds an object
        //    since step 4 and so is in the table (bergdb 019-46, after review).

        assert !isWriter || (live != null && live.obj != null && !live.isDead())
                : "the writer's handle of node " + id + " is empty or dead";
        if (isWriter && !result.isCanonical()) {
            result = cache.makeCanonical(live, result);
        }

        if (live != null) touch(live, op);
        op.pointerListener.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_STREAM);
        return result;
    }

    /**
     * The newer of reference ref and position w (Spos.NULL: none): a stream position is
     * newer than a vpos, as Rule R compares them.
     */
    static long newerPos(long ref, long w) {
        if (!Spos.isValid(w) || Spos.isVpos(w)) return ref;
        return Spos.isVpos(ref) || Spos.isNull(ref) || w > ref ? w : ref;
    }

    /**
     * Reads version 'pos' of node 'id' from the stream; during the reconstruction only, a key
     * node version of the section is cut back to the startup time (M22).
     */
    private Node readVersion(long id, long pos, int pointerIndex, Node predecessor,
            MaintenanceFollower maintenance) {
        if (Spos.isVpos(pos)) {
            throw new StreamFormatException("Pointer to node " + id + ", which is not "
                    + "in the stream and not in memory, index " + pointerIndex
                    + " of node " + predecessor.getId() + ".");
        }
        Node node = nodeStream.readNode(pos);
        checkPointeeType(predecessor, pointerIndex, node, pos);     // before an install
        assert node.getId() == id : "ids differ, " + node.getId() + " != " + id;
        cache.tickAccessClock();
        loads.incrementAndGet();
        if (maintenance != null) maintenance.loaded(node);

        final StartupSection mySection = this.section;
        if (reconstructing && mySection != null && pos >= mySection.startPos
                && node.getType() == Node.TYPE_KEY_NODE) {
            ((KeyNode) node).toPreviousState(mySection.startupTime);
        }
        return node;
    }

    /** True if a version just read at pos was cut back by readVersion. */
    private boolean cutBack(Node node, long pos) {
        final StartupSection mySection = this.section;
        return reconstructing && mySection != null && pos >= mySection.startPos
                && node.getType() == Node.TYPE_KEY_NODE;
    }

    /**
     * Follows a stream pointer to a value: the value read at the pointer's position, and put
     * into the pointer (a direct pointer, no handle; 009-02, 4.8), unless maintenance or the
     * cache policy says no (large values).
     */
    private Node followValuePointer(Node predecessor, int pointerIndex, long pointerPos,
            OpData op, MaintenanceFollower maintenance) {
        final boolean isMaintenance = maintenance != null;
        // Checks, not an assert (2026-11-06, bergdb 019-32): the pointer is stream data, and
        // the node it names is a value.
        if (pointerPos < 0 || Spos.isVpos(pointerPos)) {
            throw new StreamFormatException("Bad value pointer " + pointerPos + ", index "
                    + pointerIndex + " of node " + predecessor.getId() + ".");
        }
        Node node = nodeStream.readNode(pointerPos);
        checkPointeeType(predecessor, pointerIndex, node, pointerPos);
        cache.tickAccessClock();
        loads.incrementAndGet();
        if (isMaintenance) maintenance.loaded(node);

        final FirstTouchListener ftl = firstTouchListener;
        if (ftl != null) {
            ftl.firstTouch(node.getId(), pointerPos, node, true, false);
        }

        if (!isMaintenance && op.cachePolicy.shouldCache(node)) {
            // Into the pointer, and counted with its holder (Residents.valueIn), under the
            // holder's monitor, as eviction counts the holder out (bergdb item 009, step 3b).
            synchronized (predecessor) {
                if (predecessor.getPointee(pointerIndex) == null) {
                    predecessor.setPointee(pointerIndex, (ValueNode) node);
                    cache.residents().valueIn(predecessor, (ValueNode) node);
                }
            }
        }
        op.pointerListener.pointerFollowed(predecessor, pointerIndex, node, Pointer.TYPE_STREAM);
        return node;
    }

    /**
     * Sets Rule R (docs/sis-model.md, 6.2) for this process: newById maps the id of
     * each index node that has a version in the startup section to the position of its
     * newest version there. Key node versions from the section are cut back to their
     * state at startupTime when read. Called by DbStarter.
     */
    public void setStartupSection(Map<Long, Long> newById, long sectionStartPos,
            long startupTime) {
        this.section = new StartupSection(new HashMap<Long, Long>(newById), sectionStartPos,
                startupTime);
        this.reconstructing = true;
    }

    /**
     * Ends the reconstruction (DbStarter): from now on, a version read through a pointer is
     * never cut back to the startup time (M22). Rule R stays.
     */
    public void endReconstruction() {
        this.reconstructing = false;
    }

    /** The position of the newest version of node 'id' in the startup section, or null. */
    Long newestInSection(long id) {
        StartupSection mySection = this.section;
        return mySection == null ? null : mySection.newById.get(id);
    }


    /**
     * Before an index node is written: makes each of its pointers to an index node name
     * the latest version of that node (bergdb 011-04, level 2; the Lean model's
     * `Mem.refOf`). A pointee in the pinned set, a node of D or of the record being written
     * (its canonical object, dirty: the writer calls this before it cleans the record's
     * nodes), is resolved by node id: the pointer gets the node's live handle, which holds
     * the canonical object, so a node written in the same record is named by its new
     * position, and a node in D is seen by the still-dirty test (DbHelper.hasDirtyChild).
     * Any other pointee keeps its pointer: its reference after Rule R, or the position this
     * process last wrote the node at (the record rule, 009-02, 4.6; KeyNode.getSerializedRef).
     * Called by the writer.
     */
    public void resolvePointers(Node node, long accessData) {
        final int count = node.getSize();

        for (int i = 0; i < count; i++) {
            if (!pointsToIndexNode(node, i)) {
                continue;       // Value nodes have one version and are never dirty.
            }

            synchronized (node) {               // C2 (bergdb item 009, step 3c)
                Pointee pointee = node.getPointee(i);
                long pos = node.getPointerPos(i);
                Handle h = (Handle) pointee;
                if (h == null && Spos.isNull(pos)) {
                    continue;
                }
                Node o = h == null ? null : h.obj;
                if (o != null && o.isCanonical()) {
                    continue;
                }

                // 2026-10-13 (Reclaim.Tester.testWritesAfterCut): a stream pointer
                // below the first position of the stream names a version that reclaim cut
                // away. It is dead for every lookup time still available, so it is left as
                // it is; reading its header failed.
                if (h == null && !Spos.isVpos(pos) && pos < nodeStream.getFirstPos()) {
                    continue;
                }

                long id = h != null ? h.id : idOf(pos);

                // 1. A pinned pointee, by node id: its live handle, with its canonical object.
                Handle live = cache.liveHandle(id);
                Node pinned = live == null ? null : live.obj;
                if (pinned != null && pinned.isCanonical() && pinned.isDirty()) {
                    if (h != live) node.setPointee(i, live);
                    continue;
                }

                // 2. Any other: the pointer's reference after Rule R.
                long ref = pos;
                Long newPos = newestInSection(id);
                if (newPos != null && Spos.newer(newPos, ref)) {
                    ref = newPos;
                }
                if (ref != pos) {
                    node.setRef(i, ref);
                }
            }
        }
    }

    /**
     * Rule 4 at startup (DbStarter.linkD; the Lean model's `HMem.linkD`; bergdb item 001,
     * WP R8, change 1: bergdb 001-08, M44): each pointer of 'node' to an index
     * node that has a canonical object gets that node's live handle. A stream
     * pointer below the first position of the stream is left as it is (M33).
     *
     * <p>The node is found by the pointer's position, without reading the stream (bergdb
     * 005-57): a vpos is its id; 'ids' gives the id of each index node version of the
     * startup section and of the version before each key node version there (DbStarter's
     * posToId); 'byPos' gives the live handle of each canonical object by the position of
     * its version. A pointer of a node of D whose position is in neither names no node
     * with a canonical object: every write of a node after the version that a node of D
     * names is in the startup section (005-57's report, section 2; 001-08, 5.4, case 5).
     * Top node versions have no prevPos (011-03, G3), so a top node's pointer that neither
     * resolves reads the header at its position, as every pointer did before 005-57.</p>
     *
     * <p>With 'check' (DbStarter, when assertions are on), each pointer is also resolved by
     * node id, reading the header, and a different result throws an AssertionError.</p>
     */
    public void linkToCanonical(Node node, Map<Long, Long> ids, Map<Long, Handle> byPos,
            boolean check) {
        final int count = node.getSize();
        final boolean top = node.getType() == Node.TYPE_TOP_NODE;

        for (int i = 0; i < count; i++) {
            if (!pointsToIndexNode(node, i)) {
                continue;
            }
            synchronized (node) {               // C2 (bergdb item 009, step 3c)
                Pointee pointee = node.getPointee(i);
                long pos = node.getPointerPos(i);
                if (pointee != null || Spos.isNull(pos)) {
                    continue;
                }
                if (!Spos.isVpos(pos) && pos < nodeStream.getFirstPos()) {
                    continue;
                }
                Long id = Spos.isVpos(pos) ? Long.valueOf(pos) : ids.get(pos);
                Handle live = id != null ? cache.liveHandle(id) : byPos.get(pos);
                if (live == null && id == null && top) {
                    live = cache.liveHandle(idOf(pos));
                }
                Node canonical = live == null ? null : live.obj;
                if (canonical == null || !canonical.isCanonical()) {
                    live = null;
                }
                if (check) {
                    checkLinkById(node, i, pos, live);
                }
                if (live != null) {
                    // The pointer held nothing: its holder's count takes the handle's bytes,
                    // as a follow's swizzle does (Residents.handleIn; bergdb 019-21, R5's F4
                    // of night 006-12: the start's recount runs before linkD).
                    node.setPointee(i, live);
                    cache.residents().handleIn(node);
                }
            }
        }
    }

    /**
     * linkToCanonical's check (bergdb 005-57): 'linked', the handle that rule 4 by position
     * gives pointer i of 'node', at 'pos', or null, is the one that rule 4 by node id gives,
     * with a read of the header.
     */
    private void checkLinkById(Node node, int i, long pos, Handle linked) {
        Handle byId = cache.liveHandle(idOf(pos));
        Node o = byId == null ? null : byId.obj;
        Handle expected = o != null && o.isCanonical() ? byId : null;
        if (linked != expected) {
            throw new AssertionError("rule 4 by position is not rule 4 by node id (bergdb 005-57): "
                    + "pointer " + i + " of node " + node.getId() + " names " + pos + "; by position "
                    + (linked == null ? "no canonical object" : "node " + linked.id)
                    + ", by node id " + (expected == null ? "no canonical object"
                            : "node " + expected.id + "'s, at " + o.getSpos()));
        }
    }

    /**
     * Checks that 'pointee', the node at 'pos' that pointer i of 'node' names, is of the type
     * the pointer names (2026-11-06, bergdb 019-32): a top node's root pointer (0) names a
     * key node and its skip pointers top nodes; a key node's pointers name key nodes, and
     * values where pointsToIndexNode says so. A pointer of a damaged node (its checksum
     * right) that named a node of another type threw a ClassCastException where it was used.
     * 
     * @throws StreamFormatException  If it is of another type.
     */
    static void checkPointeeType(Node node, int i, Node pointee, long pos) {
        byte type = node.isTopNode() ? (i == 0 ? Node.TYPE_KEY_NODE : Node.TYPE_TOP_NODE)
                : pointsToIndexNode(node, i) ? Node.TYPE_KEY_NODE : Node.TYPE_VALUE;
        if (pointee.getType() != type) {
            throw new StreamFormatException("Pointer " + i + " of node " + node.getId()
                    + " names a node of type " + pointee.getType() + " at " + pos + ", not "
                    + type + ".");
        }
    }

    /** True if pointer i of 'node' points to an index node: a key node or a top node. */
    static boolean pointsToIndexNode(Node node, int i) {
        switch (node.getType()) {
        case Node.TYPE_TOP_NODE:
            return true;
        case Node.TYPE_KEY_NODE:
            // In a segment leaf, a key klong of length 7 points to the root of the next
            // key segment, and shorter ones point to value nodes (Keys.toSegments).
            KeyNode k = (KeyNode) node;
            long klong = k.klongs[i];
            return Klong.isKey(klong) 
                    && (!k.isSegmentLeaf() || Klong.getLength(klong) == Klong.MAX_SIZE);
        default:
            return false;
        }
    }
    
    /** The id of the node version at position 'pos', or the vpos itself. */
    private long idOf(long pos) {
        if (Spos.isVpos(pos)) {
            return pos;
        }
        
        synchronized (idByPos) {
            Long id = idByPos.get(pos);
            if (id != null) {
                return id;
            }
        }
        
        long id = nodeStream.readNodeHeader(pos).id();
        synchronized (idByPos) {
            idByPos.put(pos, id);
        }
        return id;
    }
    
    
    // ======== Tests ========
    
    /** A NodeStream that serves the nodes in a map, for tests. */
    private static class TestStream extends NodeStream {
        final Map<Long, Node> nodes = new HashMap<Long, Node>();
        int reads = 0;
        int headerReads = 0;
        
        TestStream() {
            super(new RecoverableStream(new MemoryStream(), new MetaBlock()), new Object());
        }
        
        public NodeHeader readNodeHeader(long pos) {
            headerReads++;
            Node n = nodes.get(pos);
            return new NodeHeader(n.getType(), n.getId());
        }
        
        public Node readNode(long pos) {
            reads++;
            return nodes.get(pos);
        }
    }
    
    private static Cache.DbInfo testDbInfo() {
        return new Cache.DbInfo() {};
    }
    
    /** A key node version: id, position, and one key klong at each of the given times. */
    private static KeyNode testKeyNode(long id, long pos, long... times) {
        KeyNode k = new KeyNode(true);
        for (long time : times) {
            k.addToEnd(Klong.createTime(time), null, -1);
            k.addToEnd(Klong.compareValueToKeyKlong(Keys.toSegments("k" + time)[0]), null, 1000 + time * 8);
        }
        k.setId(id);
        k.setSpos(pos);
        return k;
    }
    
    /** A node whose pointer 0 is a stream pointer to 'pos'. */
    private static TopNode testParent(long id, long pos) {
        TopNode t = new TopNode(0, null, pos, 1, id - 1);
        t.setId(id);
        return t;
    }
    
    private static GetData testGetData(final int[] listenerCalls) {
        GetData op = new GetData();
        op.accessData = AccessData.DEFAULT_ACCESS_DATA;
        op.cachePolicy = Dag.CACHE_ALL;
        op.pointerListener = new Dag.PointerListener() {
            public void superRootAccessed(TopNode superRoot) {}
            public void pointerFollowed(Node pred, int index, Node result, int type) {
                listenerCalls[0]++;
            }
        };
        return op;
    }
    
    /**
     * Following a pointer to a newer version of a node than the one in the node table 
     * must give the newer version; the pointer listener is called on every follow, and
     * the pointer becomes a memory pointer. Regression test for bugs found 2026-10-12 
     * (level 2): the cache, keyed by id, gave
     * the older version, did not call the listener, and left the pointer as it was.
     */
    @Nano
    private static void testFollowNewerVersion() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        stream.nodes.put(200L, testKeyNode(101, 200, 10, 20));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        int[] calls = new int[1];
        GetData op = testGetData(calls);
        
        TopNode parent1 = testParent(301, 100);
        TopNode parent2 = testParent(401, 200);
        Node a = c.followPointer(parent1, 0, op);
        Node b = c.followPointer(parent2, 0, op);
        
        Assert.assertEquals(100, a.getSpos());
        Assert.assertEquals("version followed", 200, b.getSpos());
        Assert.assertEquals("listener calls", 2, calls[0]);
        Assert.assertTrue("second pointer is a memory pointer", parent2.getPointerNode(0) == b);
    }
    
    /**
     * Rule R: a pointer to an old version of a node that has a version in the startup 
     * section, or a vpos for it, is followed to the node's newest version in the 
     * section, cut back to the startup time during the reconstruction. A version cut back
     * is not the version at its position, so a reader does not keep it in the node's
     * handle (only the writer's rerun does, which makes it canonical), and a second pointer
     * reads it again (bergdb item 001, WP R8, change 3: M27; with handles since bergdb item
     * 009, step 3a). The pointer's reference becomes Rule R's, which changes no record.
     */
    @Nano
    private static void testFollowRuleR() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        stream.nodes.put(300L, testKeyNode(101, 300, 10, 20, 30));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        Map<Long, Long> newById = new HashMap<Long, Long>();
        newById.put(101L, 300L);
        c.setStartupSection(newById, 250, 25);
        GetData op = testGetData(new int[1]);
        
        TopNode parent = testParent(401, 100);
        Node a = c.followPointer(parent, 0, op);
        Assert.assertEquals("old version followed to the newest", 300, a.getSpos());
        Assert.assertEquals("cut at startup time 25", 4, a.getSize());
        Assert.assertEquals("the reference after Rule R", 300, parent.getPointerPos(0));
        
        Assert.assertTrue("not in the node's handle", c.cache.getNode(101) == null);
        
        Node b = c.followPointer(testParent(501, 101), 0, op);
        Assert.assertEquals("vpos followed to the same version", 300, b.getSpos());
        Assert.assertEquals("read again", 2, stream.reads);
    }
    
    /**
     * The loader takes the object of the node's handle if it may serve the pointer: a
     * canonical object, or a version at the pointer's reference or later (lemma M), without
     * a read; else it reads the version the pointer names and puts it into the handle, where
     * it replaces an older version (bergdb item 009, step 3a; 009-02, 4.4). From 2026-10-17
     * to step 3a a newer snapshot in the node table was not taken (M27): the record a
     * pointer gave depended on the object it led to, which handles no longer do (4.6).
     */
    @Nano
    private static void testLoaderTakesTheHandlesObject() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        stream.nodes.put(300L, testKeyNode(101, 300, 10, 20, 30));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        KeyNode snapshot = testKeyNode(101, 200, 10, 20);
        c.cache.register(snapshot);
        snapshot.setCanonical(false);
        GetData op = testGetData(new int[1]);
        
        TopNode parent = testParent(301, 100);
        Node a = c.followPointer(parent, 0, op);
        Assert.assertTrue("the newer version in the handle", a == snapshot);
        Assert.assertEquals("no read", 0, stream.reads);
        Assert.assertTrue("swizzled", parent.getPointerNode(0) == a);
        Assert.assertEquals("the reference kept", 100, parent.getPointerPos(0));
        
        // A pointer to a newer version reads it, and the handle takes it.
        Node b = c.followPointer(testParent(401, 300), 0, op);
        Assert.assertEquals("the version named", 300, b.getSpos());
        Assert.assertEquals("one read", 1, stream.reads);
        Assert.assertTrue("the handle's object", c.cache.getNode(101) == b);
        Assert.assertTrue("the first pointer gets it too", parent.getPointerNode(0) == b);
        
        // A canonical object serves every pointer.
        b.setCanonical(true);
        Node d = c.followPointer(testParent(501, 300), 0, op);
        Assert.assertTrue("the canonical object", d == b);
        Assert.assertEquals("still one read", 1, stream.reads);
    }
    
    /**
     * Regression test for bergdb 019-46: a reader's Cache3.dropIfEmpty, which runs without the
     * write lock, found its handle empty, and before its compareAndSet to DEAD the writer
     * loaded the node into that handle and made the object canonical (the slow path's steps
     * 4 and 6). The drop then killed the handle with the canonical object in it: the object
     * lost its canonical flag and left the node table, while the writer went on with it in
     * its transaction, and the parent's pointer kept the dead handle, whose written position
     * names the version before the transaction (the INV-SLOT of 019-46: a stale pointer in
     * the parent's record). A forced schedule: the hook between dropIfEmpty's test and its
     * compareAndSet runs the writer's follow, on the same thread (the map's lock is
     * reentrant), as the writer's thread would run it in that window.
     */
    @Nano
    private static void testDropIfEmptyKeepsTheWritersObject() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        final NodeCollection c = new NodeCollection(testDbInfo(), stream);
        final TopNode parent = testParent(301, 100);
        final GetData op = testGetData(new int[1]);
        final Node[] followed = new Node[1];
        Handle h = c.cache.liveOrNewHandle(101);     // a reader's new handle, which it leaves empty
        Cache3.dropIfEmptyHook = new Runnable() {
            public void run() {
                Cache3.dropIfEmptyHook = null;
                followed[0] = c.writer().followPointer(parent, 0, op);
            }
        };
        try {
            c.cache.dropIfEmpty(h);
        } finally {
            Cache3.dropIfEmptyHook = null;
        }
        Node o = followed[0];
        Assert.assertTrue("the writer followed to the node", o != null && o.getId() == 101);
        Assert.assertTrue("the writer's object is canonical", o.isCanonical());
        Assert.assertTrue("its handle is live", !h.isDead());
        Assert.assertTrue("the node table's object", c.cache.getNode(101) == o);
        Assert.assertTrue("the parent's pointer holds the live handle", parent.getPointee(0) == h);
        Assert.assertEquals("no written position", Spos.NULL, h.writtenPos);
        Assert.assertEquals("the record's reference", 100, parent.getSerializedRef(0));
        
        // An empty handle that stays empty is still dropped.
        Handle e = c.cache.liveOrNewHandle(102);
        c.cache.dropIfEmpty(e);
        Assert.assertTrue("dead", e.isDead());
        Assert.assertTrue("out of the table", c.cache.liveHandle(102) == null);
    }
    
    /**
     * bergdb 019-46, after review: the writer keeps every index node it follows to in the
     * node's handle, whatever its op's cache policy. makeCanonical (step 6) never fills an
     * empty handle that a drop could have taken from the table, as the writer's handle holds
     * its object from step 4 on. The writer's PutData caches every index node; with a policy
     * that cached none, the follow dropped its own empty handle (Cache3.dropIfEmpty) and then
     * made the version canonical in that dead handle, out of the table.
     */
    @Nano
    private static void testWriterKeepsTheNodeWhateverItsPolicy() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        TopNode parent = testParent(301, 100);
        GetData op = testGetData(new int[1]);
        op.cachePolicy = Dag.CACHE_NOTHING;
        Node o = c.writer().followPointer(parent, 0, op);
        Assert.assertTrue("the writer followed to the node", o != null && o.getId() == 101);
        Assert.assertTrue("the writer's object is canonical", o.isCanonical());
        Handle h = c.cache.liveHandle(101);
        Assert.assertTrue("a live handle in the table", h != null && !h.isDead());
        Assert.assertTrue("the handle holds the canonical object", h.obj == o);
        Assert.assertTrue("the node table's object", c.cache.getNode(101) == o);
        Assert.assertTrue("the parent's pointer holds the handle", parent.getPointee(0) == h);
    }
    
    /**
     * The maintenance follower (bergdb item 001, WP R8, change 5: M28) loads as the
     * readers' follower does, but leaves the pointer as it is and the node table without
     * the version read (and without a handle for it); it reads a version once; a memory
     * pointer gives its object, with the handle's access data unchanged.
     */
    @Nano
    private static void testMaintenanceFollower() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        int[] calls = new int[1];
        GetData op = testGetData(calls);
        PointerFollower m = c.maintenance();
        
        TopNode parent = testParent(301, 100);
        Node a = m.followPointer(parent, 0, op);
        Assert.assertEquals("the version named", 100, a.getSpos());
        Assert.assertTrue("not swizzled", parent.getPointerNode(0) == null);
        Assert.assertEquals("the slot's position", 100, parent.getPointerPos(0));
        Assert.assertTrue("not in the node table", c.cache.getNode(101) == null);
        
        Node b = m.followPointer(testParent(401, 100), 0, op);
        Assert.assertTrue("the same object", a == b);
        Assert.assertEquals("read once", 1, stream.reads);
        Assert.assertEquals("listener calls", 2, calls[0]);
        
        TopNode memParent = testParent(501, 100);
        Handle h = Handle.of(a);
        memParent.setPointee(0, h);
        Assert.assertTrue("a memory pointer's object", m.followPointer(memParent, 0, op) == a);
        Assert.assertEquals("the CLOCK bit unchanged", 0, h.ref);
        
        c.followPointer(testParent(601, 100), 0, op);
        Assert.assertEquals("a reader reads it again", 2, stream.reads);
    }
    
    /**
     * The CLOCK bit (bergdb item 009, step 3b): a follow sets it in the pointee's handle,
     * and never writes into the pointer, whose reference stays; and the access clock
     * advances at every node read from the stream, not at a follow of a memory pointer.
     * (From 2026-10-17 to step 3a, access data was written only into a memory pointer, so
     * that a stream pointer's position survived a reader that saw a memory pointer before an
     * unswizzle: M23, M24; in step 3a into the handle.)
     */
    @Nano
    private static void testAccessData() {
        TopNode top = testParent(301, 100);
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        long clock = c.cache.accessClock();
        GetData op = testGetData(new int[1]);
        Node a = c.followPointer(top, 0, op);
        Assert.assertEquals("the clock advances at a read", clock + 1, c.cache.accessClock());
        
        Pointer p = new Pointer();
        top.getPointer(0, p);
        Assert.assertTrue("a memory pointer", p.node == a);
        Assert.assertEquals("its reference", 100, p.pos);
        Handle h = (Handle) top.getPointee(0);
        Assert.assertEquals("the CLOCK bit, in the handle", 1, h.ref);
        
        h.ref = 0;
        Assert.assertTrue("followed from memory", c.followPointer(top, 0, op) == a);
        Assert.assertEquals("no read, no tick", clock + 1, c.cache.accessClock());
        Assert.assertEquals("the CLOCK bit set again", 1, h.ref);
        Assert.assertEquals("the reference stays", 100, top.getPointerPos(0));
    }
    
    /**
     * After the reconstruction, Rule R stays, and a version read is not cut back to the
     * startup time (bergdb item 001, WP R8, change 2: M22). Before 2026-10-17 it was, also
     * at runtime.
     */
    @Nano
    private static void testNoCutBackAfterReconstruction() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        stream.nodes.put(300L, testKeyNode(101, 300, 10, 20, 30));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        Map<Long, Long> newById = new HashMap<Long, Long>();
        newById.put(101L, 300L);
        c.setStartupSection(newById, 250, 25);
        c.endReconstruction();
        GetData op = testGetData(new int[1]);
        
        Node a = c.followPointer(testParent(401, 100), 0, op);
        Assert.assertEquals("old version followed to the newest", 300, a.getSpos());
        Assert.assertEquals("not cut back", 6, a.getSize());
    }
    
    /**
     * Before a node is written, its pointers to index nodes are resolved by node id: a
     * stream pointer to a node that has a canonical object becomes a memory pointer to
     * it. So the parent stays dirty while the child is in D (Rule A), and a child
     * written in the same record is named by its new position. Regression test for bugs
     * found 2026-10-12 (level 2): the parent was
     * taken as clean, and written with the child's old position.
     */
    @Nano
    private static void testResolvePointers() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        
        // The child's canonical object, with a change since its version at 100.
        KeyNode child = testKeyNode(101, 100, 10, 20);
        child.setCanonical(true);
        child.setDirty(true);
        c.cache.register(child);
        
        // An internal node whose pointer is a stream pointer to the child's version at 100.
        KeyNode parent = new KeyNode(false);
        parent.addToEnd(Klong.createTime(10), null, -1);
        parent.addToEnd(Klong.compareValueToKeyKlong(Keys.toSegments("k")[0]), null, 100);
        parent.setId(103);
        parent.setSpos(200);
        parent.setCanonical(true);
        
        c.resolvePointers(parent, AccessData.DEFAULT_ACCESS_DATA);
        Assert.assertTrue("memory pointer to the canonical child", parent.getPointerNode(1) == child);
        Assert.assertTrue("still dirty, since the child is in D", DbHelper.hasDirtyChild(parent));
        
        // Child and parent written in the same record.
        TransNodes transNodes = new TransNodes();
        transNodes.addKeyNode(child);
        transNodes.addKeyNode(parent);
        StoredTrans.Serializer serializer = new StoredTrans.Serializer();
        serializer.serialize(transNodes, 30, 1024, 0, new java.util.ArrayList<Node>());
        StoredTrans.Parser parser = new StoredTrans.Parser();
        parser.parse(1024, serializer.getTransBuffer());
        
        long written = -1;
        for (StoredNode stored : parser.nodes) {
            if (stored.getNode().getId() == 103) {
                written = stored.getNode().getPointerPos(1);
            }
        }
        Assert.assertTrue("child written anew", child.getSpos() > 1024);
        Assert.assertEquals("parent names the child's new position", child.getSpos(), written);
    }
    
    /**
     * A pointee outside the pinned set keeps its slot when its parent is written: the
     * node table's newer snapshot, or a canonical object that is not dirty, is not taken
     * (bergdb item 001, WP R8, change 1: M21). Before 2026-10-17 it was.
     */
    @Nano
    private static void testResolvePointersUnpinned() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        stream.nodes.put(150L, testKeyNode(104, 150, 10));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        
        // A newer snapshot of node 101, and a clean canonical object of node 104.
        KeyNode snapshot = testKeyNode(101, 200, 10, 20);
        c.cache.register(snapshot);
        KeyNode clean = testKeyNode(104, 150, 10);
        clean.setCanonical(true);
        c.cache.register(clean);
        
        KeyNode parent = new KeyNode(false);
        parent.addToEnd(Klong.createTime(10), null, -1);
        parent.addToEnd(Klong.compareValueToKeyKlong(Keys.toSegments("k")[0]), null, 100);
        parent.addToEnd(Klong.compareValueToKeyKlong(Keys.toSegments("m")[0]), null, 150);
        parent.setId(103);
        parent.setSpos(300);
        parent.setCanonical(true);
        
        c.resolvePointers(parent, AccessData.DEFAULT_ACCESS_DATA);
        Assert.assertTrue("no snapshot taken", parent.getPointerNode(1) == null);
        Assert.assertEquals("the slot's version", 100, parent.getPointerPos(1));
        Assert.assertTrue("no clean canonical object taken", parent.getPointerNode(2) == null);
        Assert.assertEquals("the slot's version", 150, parent.getPointerPos(2));
    }
    
    /** A key node of D, canonical, with a key klong at time 10 for each of 'pointers'. */
    private static KeyNode testNodeOfD(long id, long... pointers) {
        KeyNode k = new KeyNode(false);
        k.addToEnd(Klong.createTime(10), null, -1);
        for (int i = 0; i < pointers.length; i++) {
            k.addToEnd(Klong.compareValueToKeyKlong(Keys.toSegments("k" + i)[0]), null, pointers[i]);
        }
        k.setId(id);
        k.setCanonical(true);
        return k;
    }
    
    /** byPos for linkToCanonical: the node table's canonical objects by position. */
    private static Map<Long, Handle> testByPos(NodeCollection c) {
        Map<Long, Handle> byPos = new HashMap<Long, Handle>();
        for (Handle h : c.cache.handles()) {
            if (h.obj != null && h.obj.isCanonical()) {
                byPos.put(h.obj.getSpos(), h);
            }
        }
        return byPos;
    }
    
    /**
     * Rule 4 at startup: a stream pointer to a node with a canonical object, of any
     * version, gets its handle (bergdb item 001, WP R8, change 1: M44); a pointer to a node
     * without one stays a stream pointer. By position, without a read (bergdb 005-57): a
     * version older than the canonical object's is found by the startup section's ids,
     * here as the version before the node's version in the section; a pointer whose
     * position is in no map is left, unread.
     */
    @Nano
    private static void testLinkToCanonical() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        stream.nodes.put(150L, testKeyNode(104, 150, 10));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        
        // Node 101's canonical object, its version at 200 in the section, written since its
        // version at 100, which is the version's prevPos.
        KeyNode canonical = testKeyNode(101, 200, 10, 20);
        canonical.setCanonical(true);
        c.cache.register(canonical);
        Map<Long, Long> ids = new HashMap<Long, Long>();
        ids.put(200L, 101L);
        ids.put(100L, 101L);
        
        KeyNode parent = testNodeOfD(103, 100, 150);
        c.linkToCanonical(parent, ids, testByPos(c), false);
        Assert.assertTrue("memory pointer to the canonical object", parent.getPointerNode(1) == canonical);
        Assert.assertTrue("no canonical object, a stream pointer", parent.getPointerNode(2) == null);
        Assert.assertEquals("its position", 150, parent.getPointerPos(2));
        Assert.assertEquals("no read", 0, stream.headerReads + stream.reads);
    }
    
    /**
     * Rule 4 by position (bergdb 005-57): a pointer to the version a canonical object was
     * loaded from, and one that holds a vpos, the id of a node not yet written, get their
     * nodes' handles, without a read.
     */
    @Nano
    private static void testLinkToCanonicalByPosition() {
        TestStream stream = new TestStream();
        stream.nodes.put(150L, testKeyNode(104, 150, 10));     // for the check's read
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        
        KeyNode loaded = testKeyNode(104, 150, 10);         // loaded from 150, not in the section
        loaded.setCanonical(true);
        c.cache.register(loaded);
        KeyNode created = testKeyNode(1001, 1001, 30);      // made by the rerun, not written
        created.setCanonical(true);
        c.cache.register(created);
        
        KeyNode parent = testNodeOfD(103, 150, 1001);
        c.linkToCanonical(parent, new HashMap<Long, Long>(), testByPos(c), true);
        Assert.assertTrue("the loaded object", parent.getPointerNode(1) == loaded);
        Assert.assertTrue("the object of the vpos", parent.getPointerNode(2) == created);
    }
    
    /**
     * Rule 4 by position (bergdb 005-57): a top node's pointer that the maps do not resolve
     * reads the header, since top node versions have no prevPos and so are not in the
     * section's ids as the version before a version in the section (011-03, G3).
     */
    @Nano
    private static void testLinkToCanonicalTopNode() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        KeyNode canonical = testKeyNode(101, 200, 10, 20);
        canonical.setCanonical(true);
        c.cache.register(canonical);
        Map<Long, Long> ids = new HashMap<Long, Long>();
        ids.put(200L, 101L);
        
        TopNode top = testParent(301, 100);
        c.linkToCanonical(top, ids, testByPos(c), false);
        Assert.assertTrue("the handle, by node id", top.getPointerNode(0) == canonical);
        Assert.assertEquals("one header read", 1, stream.headerReads);
    }
    
    /**
     * The check (bergdb 005-57): rule 4 by position against rule 4 by node id. Section ids
     * without the version before the node's version in the section miss the link that the
     * node id gives, and the check says so.
     */
    @Nano
    private static void testLinkToCanonicalCheck() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        KeyNode canonical = testKeyNode(101, 200, 10, 20);
        canonical.setCanonical(true);
        c.cache.register(canonical);
        Map<Long, Long> ids = new HashMap<Long, Long>();
        ids.put(200L, 101L);
        
        KeyNode parent = testNodeOfD(103, 100);
        boolean failed = false;
        try {
            c.linkToCanonical(parent, ids, testByPos(c), true);
        } catch (AssertionError e) {
            failed = true;
        }
        Assert.assertTrue("the check found the missing link", failed);
    }
}
