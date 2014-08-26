package bergdb.dag;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.Set;

import bergdb.common.Bug;
import bergdb.dag.GetMany.StopCondition;
import bergdb.pub.DbException;
import bergdb.pub.IllegalDbStateException;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;

// TODO LATER Consider: should cache eviction be here or in Db? Caching is in this class
// (followPointer). Maybe cache eviction should be too?

/**
 * <p>The DAG (directed acyclic graph) is the main data structure of the database.
 * An instance of this class handles the in-memory (cached) part of the DAG.</p>
 * 
 * <p>Features/scope:</p>
 * <ul>
 * <li>Walking the DAG, followPointer()</li>
 * <li>getOne(), getMany(), putOne()</li>
 * <li>Making nodes dirty</li>
 * <li>Dag testable in isolation</li>
 * <li>Cache: adding nodes to cache</li>
 * <li>Reads nodes (from interface NodeReader instance)</li>
 * <li>Pointer locks</li>
 * <li>Factory methods: newGetData(), newGetMany(), new PutData().</li>
 * </ul>
 * 
 * <p>Not in scope:</p>
 * <ul>
 * <li>DbClock - clock for the database</li>
 * <li>Concurrency - limited locking support, only pointer locks.</li>
 * <li>Transaction: collecting transaction node set, adding transaction nodes
 * to stream, ...</li>
 * <li>STM implementation</li>
 * </ul>
 * 
 * <p>This class was created in September 2013 during a heavy refactoring.
 * I wanted a smaller, cleaner Db class and a DAG class that is testable in isolation.
 * This is a change to review the code for correctness and add more unit test
 * to show that code works.</p> 
 * 
 * @author Frans Lundberg
 */
public class Dag implements TopDs.DagForMe, GetMany.DagForMe {
    /** Empty array of KlongWithPointer (new KlongWithPointer[0]). */
    private static final KlongWithPointer[] ZERO_LONG_KWP = new KlongWithPointer[0];
    
    private final TopDs topDs;
    private final NodeReader nodeReader;
    private final TransSeq seq;
    private final int maxNodeSize;
    private final int POINTER_LOCKS_LENGTH = 128;
    private final PointerLock[] pointerLocks;
    
    public Dag(NodeReader nodeReader, TopDs topDs, TransSeq transSeq, int maxNodeSize) {
        this.nodeReader = nodeReader;
        this.topDs = topDs;
        this.seq = transSeq;
        this.maxNodeSize = maxNodeSize;
        this.pointerLocks = createPointerLocks();
    }
    
    /**
     * Factory method to create minimal Dag with two nodes: a top node and a key node.
     * The database is empty; no KVs.
     */
    public static Dag createEmpty(long time, int maxNodeSize, NodeReader nodeReader) {
        return new Dag(time, maxNodeSize, nodeReader);
    }
    
    private Dag(long time, int maxNodeSize, NodeReader nodeReader) {
        this.nodeReader = nodeReader;
        this.topDs = TopDs.createFromFirstRoot(time, new KeyNode(), AccessData.DEFAULT_ACCESS_DATA);
        this.seq = new TransSeq();
        this.maxNodeSize = maxNodeSize;
        this.pointerLocks = createPointerLocks();
    }

    private PointerLock[] createPointerLocks() {
        PointerLock[] locks = new PointerLock[POINTER_LOCKS_LENGTH];
        for (int i = 0; i < POINTER_LOCKS_LENGTH; i++) {
            locks[i] = new PointerLock();
        }
        return locks;
    }
    
        
    // ======== General utility methods ========
    
    /**
     * Prints the in memory part of the DB graph. Useful for test and development.
     */
    public void printGraph(PrintStream out) {
        TopNode top = topDs.getSuperRoot();
        top.printGraph(out, "", 0);
    }
    
    /**
     * Visits all nodes cached in memory.
     */
    public void visitMemoryNodes(NodeVisitor visitor) {
        Set<INode> visited = new HashSet<INode>();
        INode start = topDs.getSuperRoot();
        visitNodeWithChildren(visitor, visited, start);
    }
    
    private void visitNodeWithChildren(NodeVisitor visitor, Set<INode> visited, INode node) {
        if (visited.contains(node)) {
            return;
        } else {
            visited.add(node);
        }
        
        node.accept(visitor);
        
        Pointer p = new Pointer();
        
        int count = node.getPointerCount();
        for (int i = 0; i < count; i++) {
            node.getPointer(i, p);
            if (p.isMem()) {
                visitNodeWithChildren(visitor, visited, p.getNode());
            }
        }
    }
    
    /**
     * Returns the super root node.
     * Use for testing only.
     */
    public TopNode getSuperRoot() {
        return topDs.getSuperRoot();
    }

    public INode findNode(int[] choices, GetData gd) {        
        if (choices == null) {
            throw new IllegalArgumentException("choices == null not allowed");
        }
        
        INode node = this.getSuperRoot();
        
        for (int i = 0; i < choices.length; i++) {
            int choice = choices[i];
            node = this.followPointer(node, choice, 0, gd.pointerListener, gd.cachePolicy);
            if (node == null) {
                break;
            }
        }
        
        return node;
    }
    
    public final TransSeq getTransSeq() {
        return seq;
    }
    
    /**
     * Creates a GetData object suitable for use with as a parameter to Graph.getOne().
     * Use Db.newGetData() instead if you want to use the GetData object
     * in Db.getOne().
     */
    public GetData newGetData() {
        final GetData g = new GetData();
        
        g.pointerListener = new Dag.PointerListener() {
            public void pointerFollowed(
                    INode predecessor, int pointerIndex, INode result, int pointerType) {
                switch (pointerType) {
                case Pointer.TYPE_MEMORY:
                    g.followMemoryPointerCount++;
                    break;
                case Pointer.TYPE_STREAM:
                    g.followStreamPointerCount++;
                    break;
                default:
                    assert false : "Bad pointer type: " + pointerType + ".";
                    break;
                }
            }

            public void superRootAccessed(TopNode superRoot) {}
        };
        
        return g;
    }
    
    /**
     * This is the preferred way to create a GetMany object used together with 
     * this Dag object.
     */
    public GetMany newGetMany() {
        return new GetMany();
    }
    
    /**
     * Creates a PutData object suitable for use with as a parameter to Graph.putKv().
     * Use Db.newPutData() instead if you want to use the PutData object as a 
     * parameter with methods of Db.
     */
    public PutData newPutData() {        
        final PutData p = new PutData();
        
        p.pointerListener = new Dag.PointerListener() {
            public void pointerFollowed(
                    INode predecessor, int pointerIndex, INode result, int pointerType) { 
                if (result != null) {
                    if (result.getType() == INode.TYPE_KEY_NODE) {
                        if (predecessor.getType() == INode.TYPE_TOP_NODE) {
                            p.keyAccessPath.add(Klong.NULL, (KeyNode) result); 
                        } else if (predecessor.getType() == INode.TYPE_KEY_NODE) {
                            KeyNode pre = (KeyNode) predecessor;
                            KeyNode res = (KeyNode) result;
                            p.keyAccessPath.add(pre.getKlong(pointerIndex), res);
                        }
                    }
                }
            }

            public void superRootAccessed(TopNode superRoot) {}
        };
        
        p.splitListener = new SplitListener() {
            public void nodeSplit(int splitType) {
                switch (splitType) {
                case TIME_SPLIT_1:
                case TIME_SPLIT_2:
                    p.timeSplitCount += 1;
                    break;
                case SPACE_SPLIT_1:
                case SPACE_SPLIT_2:
                case SPACE_SPLIT_3:
                    p.spaceSplitCount += 1;
                    break;
                }
            }
        };
        
        return p;
    }

    
    // ======== followPointers() and helpers ========
    
    /**
     * Follows a pointer. This method must always be used when a pointer is
     * followed. This is an essential method. It is used both by get and put operations.
     * Besides following a pointer, it handles add-to-cache, and sets access data for
     * the pointer (when was it last used). The access data is used by the 
     * cache eviction algorithm.
     * 
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    public final INode followPointer(final INode predecessor, int pointerIndex, long accessData, 
            PointerListener pointerListener, CachePolicy cachePolicy) {
        INode result;
        assert predecessor != null;
        assert accessData == 0 || AccessData.isValid(accessData);

        final Object lock = getPointerLock(predecessor, pointerIndex);

        synchronized (lock) {
            INode pointerNode = predecessor.getPointerNode(pointerIndex);
            long pointerPos = predecessor.getPointerPos(pointerIndex);

            assert !Pointer.isNull(pointerNode, pointerPos) : "Pointer is null: " + pointerNode
                    + ", " + pointerPos;

            if (Pointer.isMem(pointerNode)) {
                result = pointerNode;
                if (accessData != 0) {
                    predecessor.setPointerAccessData(pointerIndex, accessData);
                }
                pointerListener.pointerFollowed(
                        predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
            
            } else {
                result = nodeReader.readNode(pointerPos);
                
                pointerListener.pointerFollowed(
                        predecessor, pointerIndex, result, Pointer.TYPE_STREAM);
                if (cachePolicy.shouldCache(result)) {
                    predecessor.setPointer(pointerIndex, result, accessData);
                }
            }
        }

        return result;
    }
    
    /**
     * Returns a lock for the pointerIndex'th pointer of node 'node'.
     */
    public final Object getPointerLock(final INode node, final int pointerIndex) {
        int value = (node.hashCode() + 13 * pointerIndex);
        value = (value < 0) ? -value : value;
        return pointerLocks[value % POINTER_LOCKS_LENGTH];
    }

    
    // ==== getOne() with helpers ========
    
    /**
     * Gets one KV value or returns null if it does not exist.
     * 
     * @param time  The lookup time.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    public byte[] getOne(long time, long[] keySegments, final GetData gd) {
        assert gd.pointerListener != null;
        assert gd.cachePolicy != null;
        
        KeyNode segmentRoot = topDs.findRoot(this, time, gd);

        if (segmentRoot == null) {
            return null;
        }
        
        INode item;
        KeyNode node;
        final int segmentCount = keySegments.length;
        final int lastIndex = keySegments.length - 1;
        byte[] result = null;

        for (int i = 0; i < segmentCount; i++) {
            item = getEqNodeInSegment(time, segmentRoot, keySegments[i], gd);

            if (i == lastIndex) {
                result = null;
                if (item != null && item instanceof ValueNode) {
                    result = ((ValueNode) item).getValue();
                }
                break;
            } else {
                if (item instanceof KeyNode) {
                    node = (KeyNode) item;
                } else {
                    node = null;
                }

                if (node == null) {
                    result = null;
                    break;
                }
                gd.nodeDepth++;
                segmentRoot = node;
            }
        }
        
        return result;
    }
    

    /**
     * Gets a ValueNode or KeyNode from a segment in the DB graph. Returns null
     * if none was found.
     * 
     * @param time
     *            The lookup time.
     * @param segmentRoot
     *            The segment root key node.
     * @param compareValue
     *            The compareValue to search for.
     * @param gd
     *            GetData to the lookup operation.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    private final INode getEqNodeInSegment(long time, KeyNode segmentRoot, long compareValue,
            GetData gd) {
        final KlongWithPointer kwi = gd.kwi;
        KeyNode current = segmentRoot;
        INode result;

        while (true) {
            if (current.isSegmentLeaf()) {
                current.searchEq(time, compareValue, kwi);

                if (kwi.klong == Klong.NULL) {
                    result = null;
                } else {
                    result = followPointer(
                            current, kwi.pointerIndex, gd.accessData, 
                            gd.pointerListener, gd.cachePolicy);
                }
                break;

            } else {
                current.searchLte(time, compareValue, kwi);

                if (kwi.klong == Klong.NULL) {
                    result = null;
                    break;
                } else {
                    assert kwi.node == null || kwi.node instanceof KeyNode 
                            : "Expected a KeyNode, got " + kwi.node;

                    KeyNode nextCurrent = (KeyNode) followPointer(current, kwi.pointerIndex,
                            gd.accessData, gd.pointerListener, gd.cachePolicy);
                    current = nextCurrent;
                }
            }
        }

        return result;
    }
    
    
    
    // ======== getMany() ========
    
    /**
     * Get multiple KVs in increasing (or decreasing) key order.
     * 
     * @param g
     *            Input and output parameters. The GetMany object should have been createed
     *            with the newGetMany() factory method.
     * @see GetMany
     * @throws IllegalDbStateException
     *             If start() has not been called.
     * @throws StreamFormatException
     *             If the database stream is corrupt.
     * @throws StreamIoException
     *             If there was an i/o error with the database stream.
     */
    public void getMany(GetMany g) {
        //
        // Note, multiple get operations may be running in parallel.
        // All data used must be thread safe. Temporary, operation-local data is stored in 
        // the 'g' object.
        //

        KeyNode root = topDs.findRoot(this, g.actualLookupTime, g.gd);
        
        if (root == null) {
            return;
        }

        GetMany.Chain chain = g.new Chain((GetMany.DagForMe) this);
        chain.setup(root);

        outer: while (true) {
            Kvt kvt = chain.next();

            if (kvt == null) {
                g.stopCondition.eod();
                break outer;
            }
            
            g.getOpCount++;
            int shouldStop = g.stopCondition.handleKvt(kvt);

            switch (shouldStop) {
            case StopCondition.STOP:
                break outer;
            case StopCondition.ADD:
                g.result.add(kvt);
                break;
            case StopCondition.ADD_AND_STOP:
                g.result.add(kvt);
                break outer;
            case StopCondition.CONTINUE:
                // empty
                break;
            default:
                assert false : "Bad int value: " + shouldStop;
                break;
            }
        }
    }    
    

    // ======== putKv() with helpers ========
    
    /**
     * <p>Adds a KV to the graph.
     * If a value for the key exists, the previous value for the key is replaced.
     * If value is null, this is a delete operation.</p>
     * 
     * <p>This method runs with exclusive write access to the data structure 
     * (synchronized on Db.writeLock). However, there may be concurrent readers 
     * that read with a lookup time strictly less than the transaction time.</p>
     * 
     * @param key     The key (as segments).
     * @param value   The value; null for delete operation.
     * @throws DbException
     */
    public void putKv(long[] key, byte[] value, PutData pd) {
        //
        // in:   time, key, value.
        // out:  changes to graph, 
        //       changed/new nodes reported to pd.nodeChangeListener.
        //       accessed nodes ensured "dirty"
        //
        
        assert pd.tt >= 0;
        assert pd.nodeChangeListener != null;
        assert pd.pointerListener != null;
        assert key != null && key.length > 0;
        
        Pointer tempPointer = new Pointer();
        final KeyNode root = topDs.findRoot((TopDs.DagForMe) this, pd.tt, pd.accessData,
                tempPointer, pd.pointerListener, pd.cachePolicy);
        
        if (root == null) {
            throw new DbException("Found no root node at t=" + pd.tt + ", cannot continue put.");
        }
        
        KeyNode segmentRoot = root;
        final int segmentCount = key.length;
        final int lastSegment = segmentCount - 1;
        
        for (int i = 0; i < segmentCount; i++) {            
            if (i == lastSegment) {
                setValue(segmentRoot, key[i], key, value, pd);
            } else {
                segmentRoot = setNode(segmentRoot, key[i], pd);
            }
        }
    }
    
    /**
     * Sets a value in the segment that has 'node' as its root node. If a Kv
     * with the key already exists, its value is overwritten.
     * 
     * @param node
     *            The segment root node.
     */
    private void setValue(KeyNode node, long compareValue, long[] key, byte[] value, PutData pd) {
        assert node != null : "node is null";
        
        while (!node.isSegmentLeaf()) {
            node.searchLte(pd.tt, compareValue, pd.kwi);
            assert pd.kwi.klong != Klong.NULL;
            node = (KeyNode) followPointer(node, pd.kwi.pointerIndex, pd.accessData,
                    pd.pointerListener, pd.cachePolicy);
            assert node != null;
        }

        if (value == null) {
            // If a delete operation.
            
            // 130514 Frans: Added delete ValueNode to transaction nodes. Needed to store choices for
            // the delete operation. But only non-noop deletes added.
            
            // Inserts a delete klong if needed.
            
            boolean isNoop = appendDeleteKlong(node, pd.keyAccessPath.size - 1, compareValue, pd);
            if (!isNoop) {
                //pd.nodeChangeListener.keyNodeChanged(node);
                ValueNode valueNode = new ValueNode(null);
                pd.nodeChangeListener.newValueNode(valueNode, key);
            }
            
        } else {
            //pd.nodeChangeListener.keyNodeChanged(node);
            ValueNode valueNode = new ValueNode(value);
            pd.nodeChangeListener.newValueNode(valueNode, key);
            
            // We need to be able to fit two more klongs. A TIME klong might be needed.
            // This is sub-optimal. Sometimes a node can be added without adding a TIME klong.
            // Little to gain from optimizing this, however.
            
            // "+1" needed, there may be a need to insert a TIME klong too.
            if (node.size + 1 < this.maxNodeSize) {
                node.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        valueNode, pd.accessData);
                pd.nodeChangeListener.keyNodeChanged(node);
            } else {
                pd.oneKwi[0].klong = Klong.compareValueToKeyKlong(compareValue);
                pd.oneKwi[0].node = valueNode;
                pd.oneKwi[0].pos = pd.accessData;
                appendKlongs(node, pd.keyAccessPath.size - 1, pd.oneKwi, pd);
            }
        }
    }
        
    /**
     * Ensures a klong-and-node with compareValue exists in the segment of the
     * data structure with 'segmentRoot' as the root node. If it does not exist,
     * a new klong is inserted pointing to a new node. The new node is the
     * segment root of a newly created segment. Returns the next segment root.
     */
    private KeyNode setNode(KeyNode segmentRoot, long compareValue, PutData pd) {
        KeyNode current = segmentRoot;
        KeyNode result;
        
        assert current.assertOk(this.maxNodeSize);
        
        while (!current.isSegmentLeaf()) {
            current.searchLte(pd.tt, compareValue, pd.kwi);
            assert pd.kwi.klong != Klong.NULL;
            current = (KeyNode) followPointer(current, pd.kwi.pointerIndex, pd.accessData,
                    pd.pointerListener, pd.cachePolicy);
            assert current != null;
            assert current.assertOk(this.maxNodeSize);
        }
        
        current.searchEq(pd.tt, compareValue, pd.kwi);

        if (pd.kwi.klong == Klong.NULL) {
            // If not found, create the node

            KeyNode child = new KeyNode(true); // New segment leaf node.
            pd.nodeChangeListener.keyNodeChanged(child);
            
            // "+1" needed since there might be a need to insert a TIME klong too.
            if (current.size + 1 < this.maxNodeSize) {
                current.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        child, pd.accessData);
                pd.nodeChangeListener.keyNodeChanged(current);
            } else {
                pd.oneKwi[0].klong = Klong.compareValueToKeyKlong(compareValue);
                pd.oneKwi[0].node = child;
                pd.oneKwi[0].pos = pd.accessData;
                appendKlongs(current, pd.keyAccessPath.size - 1, pd.oneKwi, pd);
            }
            
            result = child;
            
        } else {
            // If found
            result = (KeyNode) followPointer(current, pd.kwi.pointerIndex, pd.accessData, 
                    pd.pointerListener, pd.cachePolicy);
        }

        return result;
    }
    

    /**
     * Appends a delete klong to 'node' if needed to delete the klong with the
     * given compare value.
     * 
     * @return True if the operation is a noop (no operation).
     */
    private boolean appendDeleteKlong(final KeyNode node, final int depth,
            final long compareValueToDelete, PutData pd) {
        //
        // If needed, a delete bitmap klong is added to the node for the current
        // transaction time to delete a key klong with the specified compareValue.
        // If no such key klong exists, or if it is already deleted, no action
        // is taken (it is a NOOP).
        // If 'node' ends with a delete klong of the current transaction (same transaction time), 
        // the delete klong is updated to set a delete bit for the specified compareValue.
        //
        // -- Implementation notes --
        // Loop through. Is it a noop? If not, can it be added to existing
        // delete klong of transaction or not? At end if noop, do nothing. If not, either modify
        // existing delete klong or add one to 'node'.
        //

        final short sz = node.size;
        assert sz <= this.maxNodeSize : "Bad node size: " + sz;
        long arrayTime = -1;
        long tTime = pd.tt;
        long arrayDel = Klong.createDeleteBitmap();
        long del = Klong.createDeleteBitmap();
        boolean hasTransDel = false;
            // Set to true if last klong is a delete for the same time as this transaction.

        for (int i = 0; i < sz; i++) {
            long klong = node.klongs[i];
            int type = Klong.getIntType(klong);

            switch (type) {
            case Klong.INT_TYPE_TIME:
                arrayTime = Klong.getTime(klong);
                if (arrayTime > tTime) {
                    throw new Bug("Bad state of node, arrayTime > transaction time."
                            + " arrayTime=" + arrayTime + ", tTime=" + tTime + ", node="
                            + node.toString() + ".");
                }
                break;
            case Klong.INT_TYPE_KEY:
                long arrayCompareValue = Klong.getCompareValue(klong);
                if (compareValueToDelete == arrayCompareValue) {
                    del = Klong.delete(del, i);
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                arrayDel = klong;
                if (arrayTime == tTime && i == sz - 1) {
                    hasTransDel = true;
                }
                break;
            default:
                assert false : "Bad klong type at " + i + ": " + type + ".";
                break;
            }
        }

        long union = (del | arrayDel);
        boolean isNoop = (union == arrayDel);
        
        if (!isNoop) {
            if (hasTransDel) {
                node.klongs[sz - 1] = union;
                pd.nodeChangeListener.keyNodeChanged(node);
                
                // Direct modification, but still OK. A reader will always have a lookup
                // time < trans.transTime. So, a reader is guaranteed not to see
                // the delete at trans.transTime before the transaction completes.
                // No need to add 'node' to transaction nodes. It is there
                // already since it has a delete klong for transationTime.
                
            } else {                
                if (node.size + 1 < this.maxNodeSize) {
                    node.addKlong(tTime, union, null, pd.accessData);
                    pd.nodeChangeListener.keyNodeChanged(node);
                    
                } else {                    
                    KeyNode last = node.lastVersionGivenDel(sz, tTime, union);
                    pd.nodeChangeListener.keyNodeChanged(last);
                    
                    handleLastVersionOfFullNode(node, depth, ZERO_LONG_KWP, tTime, last, pd);
                }
            }
        }
        
        return isNoop;
    }
    
    
    // ======== appendKlongs() and helpers ========
    
    /**
     * Inserts one or two non-delete klongs to 'node' for the current
     * transaction. This method splits 'node' and its ancestors if needed.
     * 
     * @param node
     *            Node into which to insert.
     * @param depth
     *            Depth of 'node' in the access path.
     * @param toAppend
     *            The klongs, pointers, accessData to insert. 1 or 2 long array.
     */
    private void appendKlongs(final KeyNode node, final int depth, 
            final KlongWithPointer[] toAppend, PutData pd) {
        //
        // This should be the only way the DB adds klongs to KeyNodes. It is the
        // central point of code for node splitting.
        //
        // Implementation note: we allow memory allocation for a split, avoid it otherwise.
        //
        // For performance, we use special code for the most common case of
        // inserting exactly one klong to a non-full node.
        //

        assert toAppend.length < 3 : "toInsert.length = " + toAppend.length;
        assert node.assertOk(maxNodeSize);

        // "+1" is needed since a TIME klong could be added along with the toInsert klongs.
        final boolean isFull = node.size + toAppend.length + 1 > this.maxNodeSize;

        if (!isFull) {
            for (int i = 0; i < toAppend.length; i++) {
                KlongWithPointer kwi = toAppend[i];
                node.addKlong(pd.tt, kwi.klong, kwi.node, pd.accessData);
            }
            pd.nodeChangeListener.keyNodeChanged(node);
            assert node.assertOk(maxNodeSize);
            
        } else {
            // 'node' is full. We cannot append 'toInsert' to it.
            // It is either space-full or time-full.
            
            KeyNode last = node.lastVersion(pd.tt);
            pd.nodeChangeListener.keyNodeChanged(last);
            
            assert last.assertOk(maxNodeSize);
            handleLastVersionOfFullNode(node, depth, toAppend, pd.tt, last, pd);
        }
    }
    
    /**
     * This is a central and important method. 
     * All calls to splitNode() and replaceNodeWithLastVersion() goes through this method.
     * This is an "hourglass method" - multiple callers and multiple callees.
     * appendKlongs()/appendDelete() methods call this method.
     * If last.size > maxNodeSize / 2, then 'node' is split into two nodes 
     * a space-split is made.
     * Otherwise, 'node' is replaced by the last version of it, a time-split.
     */
    private void handleLastVersionOfFullNode(final KeyNode node, final int depth,
            final KlongWithPointer[] toInsert, final long tTime, KeyNode last, PutData pd) {
        if (last.size > this.maxNodeSize / 2) {
            spaceSplit(node, last, depth, toInsert, pd);
        } else {
            timeSplit(tTime, last, depth, toInsert, pd);
        }
    }
    
    /**
     * A time split "replaces" the time-full node with the last version of it.
     * This method handles both: time-split-1 and time-split-2 cases.
     */
    private void timeSplit(final long tTime, KeyNode last, final int depth,
            KlongWithPointer[] toAppend, PutData pd) {
        // 131005, added the last.replaceKlong() method call. A bit of a hack.
        //   See Graph.testTimeSplit1a.
        //   TODO LATER. Consider other solution. Maybe last should include toInsert.
        //
        // Last version is small enough not to split into two nodes, but not empty.
        //
        
        final KeyNode parent = pd.getParent(depth);

        for (int i = 0; i < toAppend.length; i++) {
            KlongWithPointer kwi = toAppend[i];    
            boolean replaced = last.replaceKlong(tTime, kwi.klong, kwi.node, pd.accessData);
            if (!replaced) last.addKlong(tTime, kwi.klong, kwi.node, pd.accessData);
        }
        pd.nodeChangeListener.keyNodeChanged(last);

        if (parent == null) {
            // time-split-2:
            // 'node' is the current space root. Replace it with 'last'.
            
            topDs.newSuperRoot(tTime, last, pd.accessData);
            pd.nodeChangeListener.topNodeChanged(topDs.getSuperRoot());
            pd.splitListener.nodeSplit(Dag.TIME_SPLIT_2);
            assert last.checkWithMessage() == null;
            
        } else {
            // time-split-1:
            // 'node' is an ordinary node (not space root).
            
            long klong1 = pd.keyAccessPath.getKlong(depth);
            assert klong1 != Klong.NULL;

            pd.oneKwi[0].klong = klong1;
            pd.oneKwi[0].node = last;
            pd.oneKwi[0].pos = pd.accessData;
            appendKlongs(parent, depth - 1, pd.oneKwi, pd);
            
            pd.splitListener.nodeSplit(Dag.TIME_SPLIT_1);
            assert parent.checkWithMessage() == null : parent.checkWithMessage() + " node:\n"
                    + parent.print();
        }
    }
    
    /**
     * Called to space split 'node'.
     * There are three kinds of space splits:
     * space-split-1: The node is not a segment root.
     * space-split-2: The node is a segment root (parent is segment leaf).
     * space-split-3: The node is the space root node (parent == null).
     * 
     * @param node    The node that is full and needs to be split.
     * @param last    The last version of 'node'.
     * @param depth   The current depth in the tree, used together with pd.getParent().
     * @param toInsert  Klongs to insert.
     */
    private void spaceSplit(final KeyNode node, KeyNode last, final int depth,
            final KlongWithPointer[] toInsert, PutData pd) {
        final long tt = pd.tt;
        final boolean isSegmentLeaf = node.isSegmentLeaf();
        final KeyNode first = new KeyNode(isSegmentLeaf);
        final KeyNode second = new KeyNode(isSegmentLeaf);
        final KeyNode parent = pd.getParent(depth);
        
        if (parent == null) {
            //
            // space-split-3:
            // 'node' is the space root node.
            //
            
            KeyNode newRoot = new KeyNode(false);
            pd.nodeChangeListener.keyNodeChanged(newRoot);
            
            long secondKlong = node.firstAndSecond(tt, last, toInsert, first, second);
            pd.nodeChangeListener.keyNodeChanged(first);
            pd.nodeChangeListener.keyNodeChanged(second);
            
            newRoot.addKlong(tt, Klong.EMPTY_KEY, first, pd.accessData);
            newRoot.addKlong(tt, secondKlong, second, pd.accessData);
            pd.nodeChangeListener.keyNodeChanged(newRoot);

            topDs.newSuperRoot(tt, newRoot, pd.accessData);
            pd.nodeChangeListener.topNodeChanged(topDs.getSuperRoot());
                     
            pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_3);
            assert newRoot.checkWithMessage() == null;

        } else if (parent.isSegmentLeaf()) {
            //
            // space-split-2:
            // 'node' is a segment root since parent is a segment leaf.
            //

            KeyNode newSegmentRoot = new KeyNode(false);
            long secondKlong = node.firstAndSecond(tt, last, toInsert, first, second);
            pd.nodeChangeListener.keyNodeChanged(first);
            pd.nodeChangeListener.keyNodeChanged(second);

            newSegmentRoot.addKlong(tt, Klong.EMPTY_KEY, first, pd.accessData);
            newSegmentRoot.addKlong(tt, secondKlong, second, pd.accessData);
            pd.nodeChangeListener.keyNodeChanged(newSegmentRoot);

            long klong1 = pd.keyAccessPath.getKlong(depth);
            assert klong1 != Klong.NULL;

            pd.oneKwi[0].klong = klong1;
            pd.oneKwi[0].node = newSegmentRoot;
            pd.oneKwi[0].pos = pd.accessData;
            appendKlongs(parent, depth - 1, pd.oneKwi, pd);

            pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_2);
            assert parent.checkWithMessage() == null : parent.checkWithMessage() + " node:\n"
                    + parent.print();
            assert newSegmentRoot.checkWithMessage() == null;
            
        } else {
            //
            // space-split-1:
            // 'node' is not a segment root since parent is not a segment leaf.
            //
            long secondKlong = node.firstAndSecond(tt, last, toInsert, first, second);
            pd.nodeChangeListener.keyNodeChanged(first);
            pd.nodeChangeListener.keyNodeChanged(second);
            
            long firstKlong = pd.keyAccessPath.getKlong(depth);

            pd.twoKwis[0].klong = firstKlong;
            pd.twoKwis[0].node = first;
            pd.twoKwis[0].pos = pd.accessData;
            pd.twoKwis[1].klong = secondKlong;
            pd.twoKwis[1].node = second;
            pd.twoKwis[1].pos = pd.accessData;

            appendKlongs(parent, depth - 1, pd.twoKwis, pd);

            pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_1);
            assert parent.checkWithMessage() == null : parent.checkWithMessage();
        }
    }

    
    // ======== Inner types ========
    
    /** Special type for pointer lock object; useful for debug. */
    public static class PointerLock {}
    
    /**
     * A NodeReader has method readNode() that can read a node from the DB stream
     * give the spos of the node.
     */
    public static interface NodeReader {
        
        /**
         * Reader a node from the stream. Assumes the item exists at the location 
         * and that it is valid.
         * 
         * @throws StreamFormatException
         * @throws StreamIoException
         */
        public INode readNode(long spos);
    }
    
    
    /**
     * A PointerListener is used to listen to pointer-followed events
     * and super-root-node-accessed events.
     */
    public static interface PointerListener {
        /**
         * Called from TopDs findRoot() to report that the super root node was
         * accessed.
         */
        public void superRootAccessed(TopNode superRoot);
        
        /**
         * Reports that a pointer was followed.
         * 
         * @param pointerType One of Pointer.TYPE_MEMORY, Pointer.TYPE_STREAM.
         */
        public void pointerFollowed(
                INode predecessor, int pointerIndex, INode result, int pointerType);
    }
    
    public static final PointerListener DO_NOTHING_POINTER_LISTENER = new PointerListener() {
        public void pointerFollowed(INode predecessor, int pointerIndex, INode result,
                int pointerType) {}

        public void superRootAccessed(TopNode mySuperRoot) {}
    };
    
    
    /**
     * The cache policy determines whether to cache nodes read from stream.
     * This interface enables us to easily set a cache policy such as:
     * cache all nodes read from stream, cache no nodes, cache only KeyNodes, cache all
     * KeyNodes and all ValueNodes that are smaller than 400k in size.
     * Cache policy can be set per get operation (or even per call to DbGraph.followPointer()).
     */
    public static interface CachePolicy {
        /**
         * If true is returned, the node will be cached.
         * 
         * @param node  A node that was just read from the stream.
         * @return True to cache the node.
         */
        public boolean shouldCache(INode node);
    }
    
    public static final CachePolicy CACHE_ALL = new CachePolicy() {
        public boolean shouldCache(INode node) {
            return true;
        }
    };
    
    public static final CachePolicy CACHE_NOTHING = new CachePolicy() {
        public boolean shouldCache(INode node) {
            return false;
        }
    };
    
    /**
     * Cache policy that caches all nodes except for ValueNodes with a value larger 
     * than 1 MiB.
     */
    public static final CachePolicy CACHE_ALL_EXCEPT_LARGE_VALUE_NODES = new CachePolicy() {
        public boolean shouldCache(INode node) {
            boolean result;
            int type = node.getType();
            if (type == INode.TYPE_VALUE) {
                result = ((ValueNode) node).getValue().length <= 1024*1024;
            } else {
                result = true;
            }
            return result;
        }
    };
    
    /**
     * Listens to DB graph nodes that are created or changed.
     */
    public static interface NodeChangeListener {
        
        /**
         * Reports that TopNode was created or modified.
         */
        public void topNodeChanged(TopNode node);
        
        /**
         * Reports that a KeyNode was created or modified.
         */
        public void keyNodeChanged(KeyNode node);
        
        /**
         * Reports about a new ValueNode.
         */
        public void newValueNode(ValueNode node, long[] key);
    }
    
    public static final NodeChangeListener DO_NOTHING_NODE_CHANGE_LISTENER = new NodeChangeListener() {
        public void topNodeChanged(TopNode node) {}
        public void keyNodeChanged(KeyNode node) {}
        public void newValueNode(ValueNode node, long[] key) {}
    };
    
    
    public static interface NodeAccessListener {
        /**
         * Reports that a node was accessed.
         */
        public void nodeAccessed(INode node);
    }
    
    
    public static final int TIME_SPLIT_1 = 1;
    public static final int TIME_SPLIT_2 = 2;
    public static final int SPACE_SPLIT_1 = 11;
    public static final int SPACE_SPLIT_2 = 12;
    public static final int SPACE_SPLIT_3 = 13;
    
    /**
     * Used to listen to node split events.
     */
    public static interface SplitListener {
        public void nodeSplit(int splitType);
    }
    
    public static final SplitListener DO_NOTHING_SPLIT_LISTENER = new SplitListener() {
        public void nodeSplit(int splitType) {}
    };
}
