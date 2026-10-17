package bergdb.core;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.Pointer;
import bergdb.dag.PointerFollower;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
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
 * <p>Since 2026-10-12 (docs/levels.md, level 2), the cache is the node table 
 * shared with Db: one canonical object per node, and Rule R for pointers followed into 
 * the stream. This object is the follower for readers; writer() is the follower for 
 * the writer. Following a memory pointer is the same for readers as before.</p>
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
    private PointerLocks pointerLocks;
    private final PointerFollower writer = new WriterFollower();
    private volatile StartupSection section;
    
    /**
     * True from setStartupSection() until endReconstruction(): while DbStarter rebuilds the
     * database. Only then is a key node version of the startup section that a pointer leads
     * to cut back to the startup time; a load at runtime never is (bergdb item 001, WP R8,
     * change 2; docs/level4-alignment.md, M22: the Level 4 loader, `Mem.follow4`).
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
         * Rule R. result is the object followed: the node table's (read is false), or the
         * version just read at ref (read is true; cutBack is true if it was cut back to the
         * startup time). Called before the writer makes result canonical.
         */
        void firstTouch(long id, long ref, Node result, boolean read, boolean cutBack);
    }
    
    /** See FirstTouchListener. For tests only. */
    public static volatile FirstTouchListener firstTouchListener = null;
    
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
        this.pointerLocks = dbInfo.getPointerLocks();
    }
    
    /**
     * Returns the follower for the writer (puts and the rerun at startup). It differs
     * from this one in that every node it reaches is made canonical.
     */
    public PointerFollower writer() {
        return writer;
    }

    public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
        //
        // It is possible that concurrent threads will read same node 
        // from stream and try to add it to the cache. That is why we need to use existing 
        // node from cache if there is one there. See [synchronized (cacheLock)]
        // clauses in this method.
        //
        // Note, it is possible to avoid holding 'lock' while reading from stream, 
        // I believe. The node in the stream is immutable. 
        // So, the algo would be to first acquire 'lock', then if pointer is
        // a memory pointer (isMem() == true), just set access data and call 
        // listener.pointerFollowed().
        // If it is a stream pointer, release 'lock', read node, and acquire lock 
        // again. Then do the same, if isMem() do the same as above, else handle
        // the stream pointer case, but now we have read the node already and can 
        // quickly do what we should without blocking I/O call while holding 'lock'.
        //
        
        Node result;
        assert pointerIndex >= 0 : "pointerIndex: " + pointerIndex;
        assert predecessor != null : "predecessor is null";
        assert op.accessData == AccessData.ZERO || AccessData.isValid(op.accessData);

        final Object pointerLock = pointerLocks.getLock(predecessor, pointerIndex);

        synchronized (pointerLock) {
            Node pointerNode = predecessor.getPointerNode(pointerIndex);
            long pointerPos = predecessor.getPointerPos(pointerIndex);

            assert !Pointer.isNull(pointerNode, pointerPos) : "Pointer is null: " + pointerNode
                    + ", " + pointerPos;

            if (Pointer.isMem(pointerNode)) {
                result = pointerNode;
                if (op.accessData != AccessData.ZERO) {
                    predecessor.setPointerAccessData(pointerIndex, op.accessData);
                }
                
                op.pointerListener.pointerFollowed(
                        predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
            
            } else {
                result = followStreamPointer(predecessor, pointerIndex, pointerPos, op, false);
            }
        }
        
        return result;
    }
    
    /** The follower for the writer, see writer(). */
    private final class WriterFollower implements PointerFollower {
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node result;
            assert pointerIndex >= 0 : "pointerIndex: " + pointerIndex;
            assert predecessor != null : "predecessor is null";
            assert op.accessData == AccessData.ZERO || AccessData.isValid(op.accessData);

            final Object pointerLock = pointerLocks.getLock(predecessor, pointerIndex);

            synchronized (pointerLock) {
                Node pointerNode = predecessor.getPointerNode(pointerIndex);
                long pointerPos = predecessor.getPointerPos(pointerIndex);

                assert !Pointer.isNull(pointerNode, pointerPos) : "Pointer is null: " 
                        + pointerNode + ", " + pointerPos;

                if (Pointer.isMem(pointerNode)) {
                    result = pointerNode;
                    if (!result.isCanonical()) {
                        result = makeCanonical(predecessor, pointerIndex, result, op);
                    }
                    if (op.accessData != AccessData.ZERO) {
                        predecessor.setPointerAccessData(pointerIndex, op.accessData);
                    }
                    
                    op.pointerListener.pointerFollowed(
                            predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
                
                } else {
                    result = followStreamPointer(predecessor, pointerIndex, pointerPos, op, true);
                }
            }
            
            return result;
        }
    }
    
    /**
     * Follows a stream pointer, the first touch of a node through this pointer
     * (docs/levels.md, level 2). The caller holds the pointer lock.
     */
    private Node followStreamPointer(Node predecessor, int pointerIndex, long pointerPos, 
            OpData op, boolean isWriter) {
        
        // 1. The id of the node. A vpos is the id of a node that had not been written
        //    when the pointer was written.
        
        final long id;
        if (Spos.isVpos(pointerPos)) {
            id = pointerPos;
        } else {
            assert pointerPos >= 0 : "bad pointerPos (" + pointerPos + "), to read from stream"
                    + ", pointerIndex:" + pointerIndex + ", predecessor:" + predecessor.print();
            id = nodeStream.readNodeHeader(pointerPos).id();
        }
        
        // 2. The version the pointer names, after Rule R: a newer version in the startup
        //    section replaces it.
        
        final StartupSection mySection = this.section;
        long ref = pointerPos;
        if (mySection != null) {
            Long newPos = mySection.newById.get(id);
            if (newPos != null && newPos > ref) {
                ref = newPos;
            }
        }
        
        // 3. The node table's object, if it is canonical or at least as new as ref.
        //    Otherwise, read version ref; during the reconstruction only, a key node
        //    version of the section is cut back to the startup time (M22).
        
        Node result = cache.getNode(id);
        boolean usable = result != null && (result.isCanonical() 
                || (!Spos.isVpos(ref) && result.getSpos() >= ref));
        boolean cutBack = false;
        
        if (!usable) {
            if (Spos.isVpos(ref)) {
                throw new StreamFormatException("Pointer to node " + id + ", which is not "
                        + "in the stream and not in memory, index " + pointerIndex 
                        + " of node " + predecessor.getId() + ".");
            }
            
            Node node = nodeStream.readNode(ref);
            assert node.getId() == id : "ids differ, " + node.getId() + " != " + id;
            
            if (reconstructing && mySection != null && ref >= mySection.startPos 
                    && node.getType() == Node.TYPE_KEY_NODE) {
                ((KeyNode) node).toPreviousState(mySection.startupTime);
                cutBack = true;
            }
            
            result = op.cachePolicy.shouldCache(node) ? cache.register(node) : node;
        }
        
        final FirstTouchListener ftl = firstTouchListener;
        if (ftl != null) {
            ftl.firstTouch(id, ref, result, !usable, cutBack);
        }
        
        // 4. Swizzle, and make canonical for the writer.
        
        if (op.cachePolicy.shouldCache(result)) {
            cache.pointerCreated(predecessor, pointerIndex, result);
            predecessor.setPointer(pointerIndex, result, op.accessData);
        }
        
        if (isWriter && !result.isCanonical()) {
            result = makeCanonical(predecessor, pointerIndex, result, op);
        }
        
        op.pointerListener.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_STREAM);
        return result;
    }
    
    /**
     * Makes the node of 'node' canonical, in the node table and in the predecessor's
     * pointer. The caller holds the pointer lock.
     */
    private Node makeCanonical(Node predecessor, int pointerIndex, Node node, OpData op) {
        Node canonical = cache.makeCanonical(node);
        if (canonical != node) {
            cache.pointerCreated(predecessor, pointerIndex, canonical);
            predecessor.setPointer(pointerIndex, canonical, op.accessData);
        }
        return canonical;
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
     * the latest version of that node (docs/levels.md, level 2; the Lean model's
     * `Mem.refOf`). A pointee in the pinned set, a node of D or of the record being written
     * (its canonical object, dirty: the writer calls this before it cleans the record's
     * nodes), is resolved by node id: the pointer becomes a memory pointer to its
     * canonical object, so a node written in the same record is named by its new position,
     * and a node in D is seen by the still-dirty test (DbHelper.hasDirtyChild). Any other
     * pointee keeps its slot: a memory pointer names its object's position, a stream
     * pointer the version it names after Rule R. No snapshot from the node table (bergdb
     * item 001, WP R8, change 1; docs/level4-alignment.md, M20, M21, M26: with the
     * invariant INV-SLOT, the slot names the latest version, so the references are
     * today's). Called by the writer.
     */
    public void resolvePointers(Node node, long accessData) {
        final int count = node.getSize();
        
        for (int i = 0; i < count; i++) {
            if (!pointsToIndexNode(node, i)) {
                continue;       // Value nodes have one version and are never dirty.
            }
            
            final Object pointerLock = pointerLocks.getLock(node, i);
            
            synchronized (pointerLock) {
                Node child = node.getPointerNode(i);
                long pos = node.getPointerPos(i);
                if (Pointer.isNull(child, pos) || (child != null && child.isCanonical())) {
                    continue;
                }
                
                // 2026-10-13 (Reclaim.Tester.testWritesAfterCut): a stream pointer
                // below the first position of the stream names a version that reclaim cut
                // away. It is dead for every lookup time still available, so it is left as
                // it is; reading its header failed.
                if (child == null && !Spos.isVpos(pos) && pos < nodeStream.getFirstPos()) {
                    continue;
                }
                
                long id = child != null ? child.getId() : idOf(pos);
                
                // 1. A pinned pointee, by node id: its canonical object.
                Node pinned = cache.getNode(id);
                if (pinned != null && pinned != child && pinned.isCanonical() && pinned.isDirty()) {
                    cache.pointerCreated(node, i, pinned);
                    node.setPointer(i, pinned, accessData);
                    continue;
                }
                
                // 2. Any other: the slot. A stream pointer names the version after Rule R.
                if (child == null) {
                    long ref = pos;
                    Long newPos = newestInSection(id);
                    if (newPos != null && newPos > ref) {
                        ref = newPos;
                    }
                    if (ref != pos) {
                        node.setPointer(i, null, ref);
                    }
                }
            }
        }
    }
    
    /**
     * Rule 4 at startup (DbStarter.linkD; the Lean model's `Mem.linkD`; bergdb item 001,
     * WP R8, change 1: docs/level4-alignment.md, M44): each stream pointer of 'node' to an
     * index node that has a canonical object becomes a memory pointer to it, by node id. A
     * stream pointer below the first position of the stream is left as it is (M33).
     */
    public void linkToCanonical(Node node, long accessData) {
        final int count = node.getSize();
        
        for (int i = 0; i < count; i++) {
            if (!pointsToIndexNode(node, i)) {
                continue;
            }
            synchronized (pointerLocks.getLock(node, i)) {
                Node child = node.getPointerNode(i);
                long pos = node.getPointerPos(i);
                if (child != null || Pointer.isNull(child, pos)) {
                    continue;
                }
                if (!Spos.isVpos(pos) && pos < nodeStream.getFirstPos()) {
                    continue;
                }
                Node canonical = cache.getNode(idOf(pos));
                if (canonical != null && canonical.isCanonical()) {
                    cache.pointerCreated(node, i, canonical);
                    node.setPointer(i, canonical, accessData);
                }
            }
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
        
        TestStream() {
            super(new RecoverableStream(new MemoryStream(), new MetaBlock()), new Object());
        }
        
        public NodeHeader readNodeHeader(long pos) {
            Node n = nodes.get(pos);
            return new NodeHeader(n.getType(), n.getId());
        }
        
        public Node readNode(long pos) {
            return nodes.get(pos);
        }
    }
    
    private static Cache.DbInfo testDbInfo() {
        return new Cache.DbInfo() {
            final PointerLocks locks = new PointerLocks();
            public long getStartupPosForEvict() { return 0; }
            public PointerLocks getPointerLocks() { return locks; }
        };
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
     * section, cut back to the startup time during the reconstruction.
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
        
        Node a = c.followPointer(testParent(401, 100), 0, op);
        Assert.assertEquals("old version followed to the newest", 300, a.getSpos());
        Assert.assertEquals("cut at startup time 25", 4, a.getSize());
        
        Node b = c.followPointer(testParent(501, 101), 0, op);
        Assert.assertTrue("vpos followed to the same object", a == b);
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
    
    /**
     * Rule 4 at startup: a stream pointer to a node with a canonical object, of any
     * version, becomes a memory pointer to it, by node id (bergdb item 001, WP R8, change
     * 1: M44); a pointer to a node without one stays a stream pointer.
     */
    @Nano
    private static void testLinkToCanonical() {
        TestStream stream = new TestStream();
        stream.nodes.put(100L, testKeyNode(101, 100, 10));
        stream.nodes.put(150L, testKeyNode(104, 150, 10));
        NodeCollection c = new NodeCollection(testDbInfo(), stream);
        
        // Node 101's canonical object, written since its version at 100.
        KeyNode canonical = testKeyNode(101, 200, 10, 20);
        canonical.setCanonical(true);
        c.cache.register(canonical);
        
        KeyNode parent = new KeyNode(false);
        parent.addToEnd(Klong.createTime(10), null, -1);
        parent.addToEnd(Klong.compareValueToKeyKlong(Keys.toSegments("k")[0]), null, 100);
        parent.addToEnd(Klong.compareValueToKeyKlong(Keys.toSegments("m")[0]), null, 150);
        parent.setId(103);
        parent.setCanonical(true);
        
        c.linkToCanonical(parent, AccessData.DEFAULT_ACCESS_DATA);
        Assert.assertTrue("memory pointer to the canonical object", parent.getPointerNode(1) == canonical);
        Assert.assertTrue("no canonical object, a stream pointer", parent.getPointerNode(2) == null);
        Assert.assertEquals("its position", 150, parent.getPointerPos(2));
    }
}
