package bergdb.dag;

import java.io.PrintStream;
import java.util.HashSet;
import java.util.Set;
import bergdb.common.Bug;
import bergdb.dag.GetMany.StopCondition;
import bergdb.pub.util.DbException;

/**
 * <p>The Dag (directed acyclic graph) is the main data structure of the database.</p>
 * 
 * <p>Features/scope:</p>
 * <ul>
 * <li>Walking the Dag.</li>
 * <li>getOne(), getMany(), putOne()</li>
 * <li>Dag testable in isolation (Db instance not needed)</li>
 * <li>Reads nodes (from interface NodeReader instance)</li>
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
 * <li>TransSeq</li>
 * <li>followPointer() implementation</li>
 * <li>node caching</li>
 * </ul>
 * 
 * <p>This class was created in September 2013 during a heavy refactoring.
 * I wanted a smaller, cleaner Db class and a Dag class that is testable in isolation.
 * This is a change to review the code for correctness and add more unit test
 * to show that code works. The refactoring was done without much performance penalty.</p> 
 * 
 * @author Frans Lundberg
 */
public class Dag {
    /** Empty array of KlongWithPointer (new KlongWithPointer[0]). */
    private static final KlongWithPointer[] ZERO_LONG_KWP = new KlongWithPointer[0];    
    private final TopDs topDs;
    private final int maxNodeSize;
    
    public Dag(TopNode superRoot, int maxNodeSize) {
        this.topDs = new TopDs(superRoot);
        this.maxNodeSize = maxNodeSize;
    }
    
    /**
     * Factory method to create minimal Dag with two nodes: a top node and a key node.
     * The database is empty; no KVs.
     */
    public static Dag createEmpty(long time, int maxNodeSize, PointerFollower pointerFollower, 
            Dag.PointerCreatedListener pointerCreationListener) {
        return new Dag(time, maxNodeSize, pointerFollower, pointerCreationListener);
    }
    
    private Dag(long time, int maxNodeSize, PointerFollower pointerFollower, Dag.PointerCreatedListener pointerCreationListener) {
        this.topDs = TopDs.createFromFirstRoot(time, new KeyNode(), AccessData.DEFAULT_ACCESS_DATA,
                pointerCreationListener);
        this.maxNodeSize = maxNodeSize;
    }
        
    // ======== General utility methods ========
    
    /**
     * Prints the in memory part of the DB graph. Useful for test and development.
     */
    public void printGraph(PrintStream out) {
        TopNode top = topDs.getSuperRoot();
        top.printGraph(out, "", 0);
    }
    
    public void visitMemoryPointersOnce(PointerVisitor visitor) {
        HashSet<Node> visited = new HashSet<Node>();
        
        Pointer pointer = new Pointer();   // mutable memory to avoid mem alloc.
        Node superRoot = topDs.getSuperRoot();
        visitMemoryPointersOnceFromNode(superRoot, visitor, pointer, visited);
    }
    
    private void visitMemoryPointersOnceFromNode(Node node, PointerVisitor visitor, 
            Pointer pointer, HashSet<Node> visited) {
        if (visited.contains(node)) {
            return;
        }
        
        visited.add(node);
        visitor.visitNode(node);
        
        int size = node.getSize();
        
        for (int i = 0; i < size; i++) {
            node.getPointer(i, pointer);
            if (pointer.isMem()) {
                visitor.visitPointer(node, pointer);
                
                Node child = pointer.getNode();
                visitMemoryPointersOnceFromNode(child, visitor, pointer, visited);
            }
        }
    }

    /**
     * Visits all nodes cached in memory.
     */
    public void visitMemoryNodes(NodeVisitor visitor) {
        Set<Node> visited = new HashSet<Node>();
        Node start = topDs.getSuperRoot();
        visitNodeWithChildren(visitor, visited, start);
    }
    
    private void visitNodeWithChildren(NodeVisitor visitor, Set<Node> visited, Node node) {
        if (visited.contains(node)) {
            return;
        } else {
            visited.add(node);
        }
        
        node.accept(visitor);
        
        Pointer p = new Pointer();
        
        int size = node.getSize();
        for (int i = 0; i < size; i++) {
            node.getPointer(i, p);
            if (p.isMem()) {
                visitNodeWithChildren(visitor, visited, p.getNode());
            }
        }
    }
    
    public TopDs getTopDs() {
        return topDs;
    }

    public Node findNode(int[] choices, GetData gd) {        
        if (choices == null) {
            throw new IllegalArgumentException("choices == null not allowed");
        }
        
        Node node = topDs.getSuperRoot();
        
        for (int i = 0; i < choices.length; i++) {
            int choice = choices[i];
            
            node = gd.followPointer(node, choice);
            
            if (node == null) {
                break;
            }
        }
        
        return node;
    }
    
    /**
     * Creates a GetData object suitable for use with as a parameter to Graph.getOne().
     * Use Db.newGetData() instead if you want to use the GetData object
     * in Db.getOne().
     */
    public GetData newGetData() {
        // TODO A. We need to set g.pointerFollower somehow, I suppose.
        
        final GetData g = new GetData();
        
        g.pointerListener = new Dag.PointerListener() {
            public void pointerFollowed(
                    Node predecessor, int pointerIndex, Node result, int pointerType) {
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
     * Creates a PutData object suitable for use with as a parameter to Dag.putKv().
     * Use Db.newPutData() instead if you want to use the PutData object as a 
     * parameter with methods of Db.
     */
    public PutData newPutData() {        
        final PutData p = new PutData();
        
        p.pointerListener = new Dag.PointerListener() {
            public void pointerFollowed(
                    Node predecessor, int pointerIndex, Node result, int pointerType) { 
                if (result != null) {
                    if (result.getType() == Node.TYPE_KEY_NODE) {
                        if (predecessor.getType() == Node.TYPE_TOP_NODE) {
                            p.keyAccessPath.add(Klong.NULL, (KeyNode) result); 
                        } else if (predecessor.getType() == Node.TYPE_KEY_NODE) {
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
    
    // ==== getOne() with helpers ========
    
    /**
     * Gets one KV value or returns null if it does not exist.
     * gd.kvTime is set if a value is found.
     * gd.tpos is set if a value is found: ValueNode.getTpos(), Spos.NULL if it is not
     * written yet.
     * 
     * @param time  The lookup time.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    public byte[] getOne(long time, long[] keySegments, final GetData gd) {
        assert gd.pointerListener != null;
        assert gd.cachePolicy != null;
        
        KeyNode segmentRoot = topDs.findRoot(time, gd);

        if (segmentRoot == null) {
            return null;
        }
        
        Node item;
        KeyNode node;
        final int segmentCount = keySegments.length;
        final int lastIndex = keySegments.length - 1;
        byte[] result = null;

        for (int i = 0; i < segmentCount; i++) {
            item = getEqNodeInSegment(time, segmentRoot, keySegments[i], gd);

            if (i == lastIndex) {
                result = null;
                if (item != null && item instanceof ValueNode) {
                    ValueNode valueNode = (ValueNode) item;
                    result = valueNode.getValue();
                    gd.tpos = valueNode.getTpos();
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
     * Gets a ValueNode or KeyNode from a segment in the Db graph. Returns null
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
    private final Node getEqNodeInSegment(long time, KeyNode segmentRoot, long compareValue,
            GetData gd) {
        final KlongWithPointer kwi = gd.kwi;
        KeyNode current = segmentRoot;
        Node result;

        while (true) {
            if (current.isSegmentLeaf()) {
                current.searchEq(time, compareValue, kwi);

                if (kwi.klong == Klong.NULL) {
                    result = null;
                } else {
                    assert !kwi.isNullPointer()
                            : "bad pointer " + kwi.pointerIndex + " of node " + current
                              + ", KeyNode.searchEq() found result, but there is no pointer "
                              + "(no mem pointer, no stream pointer)";
                    
                    result = gd.followPointer(current, kwi.pointerIndex);
                    gd.kvTime = kwi.klongTime;
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

                    KeyNode nextCurrent = (KeyNode) gd.followPointer(current, kwi.pointerIndex);
                    current = nextCurrent;
                }
            }
        }

        return result;
    }
    
    
    
    // ======== dirtyNodeBound() ========
    
    /**
     * An upper bound on the number of index nodes that a transaction with these puts and
     * deletes, at a later time, can make dirty or create (2026-10-24, bergdb 005-31), for
     * Db's check before the go point. Walks the paths of the keys at 'time', as a get does,
     * loading nodes. Counts:
     * 
     * <ul>
     * <li>the distinct key nodes on the paths: a put makes dirty its leaf and every node above
     * it, up to the space root;</li>
     * <li>the nodes that splits can make. A node that gets k klongs (one for each put and each
     * new segment below it, those of its children's splits, and a TIME klong) with room for r
     * more overflows at most once if k exceeds r, and once more for every further half node
     * of klongs (a replacement holds at most half a node): 1 + (k - r - 1) / q times, q = M/2
     * - 3 or 1. The first overflow of a node that existed replaces it by up to two new nodes
     * and adds two klongs to its parent; later ones split new nodes in place, one new node and
     * one klong each. An overflow of the space root adds a new root;</li>
     * <li>the new segment trees of keys whose segment is not there, counted the same way from
     * an empty node.</li>
     * </ul>
     * 
     * @param deletes  deletes[i] is true if keys[i] is deleted; a delete of a missing key
     *      changes nothing.
     */
    public long dirtyNodeBound(long time, long[][] keys, boolean[] deletes, GetData gd) {
        final KeyNode root = topDs.findRoot(time, gd);
        if (root == null) {
            return 0;
        }
        final java.util.IdentityHashMap<KeyNode, Walked> walked =
                new java.util.IdentityHashMap<KeyNode, Walked>();
        final KlongWithPointer kwi = gd.kwi;
        
        for (int k = 0; k < keys.length; k++) {
            final long[] key = keys[k];
            KeyNode node = root;
            Walked w = walked(walked, node, null);
            for (int i = 0; i < key.length; i++) {
                while (!node.isSegmentLeaf()) {
                    node.searchLte(time, key[i], kwi);
                    if (kwi.klong == Klong.NULL) {
                        break;
                    }
                    node = (KeyNode) gd.followPointer(node, kwi.pointerIndex);
                    w = walked(walked, node, w);
                }
                if (i == key.length - 1) {
                    w.klongs++;
                    break;
                }
                node.searchEq(time, key[i], kwi);
                if (kwi.klong == Klong.NULL) {
                    if (!deletes[k]) {
                        w.fresh(key, i);
                    }
                    break;
                }
                node = (KeyNode) gd.followPointer(node, kwi.pointerIndex);
                w = walked(walked, node, w);
            }
        }
        
        long count = walked.size();
        final java.util.List<Walked> deepestFirst = new java.util.ArrayList<Walked>(walked.values());
        java.util.Collections.sort(deepestFirst, new java.util.Comparator<Walked>() {
            public int compare(Walked a, Walked b) {
                return Integer.compare(b.depth, a.depth);
            }
        });
        for (Walked w : deepestFirst) {
            if (w.freshKeys != null) {
                for (java.util.List<long[]> l : w.freshKeys.values()) {
                    count += freshTreeBound(l, w.freshLevel + 1);
                }
            }
            final long overflows = overflows(w.klongs, w.node.size);
            if (overflows > 0) {
                count += overflows + 1;
                if (w.up != null) {
                    w.up.klongs += overflows + 1;
                } else {
                    count += overflows;             // new roots
                }
            }
        }
        return count;
    }
    
    /** A node that dirtyNodeBound() walked. */
    private static final class Walked {
        final KeyNode node;
        final Walked up;                // the node above it on the path, null for the space root
        final int depth;
        long klongs = 0;                // that it gets
        java.util.HashMap<Long, java.util.List<long[]>> freshKeys = null;
        int freshLevel;                 // the segment of the keys in freshKeys missing here
        
        Walked(KeyNode node, Walked up) {
            this.node = node;
            this.up = up;
            this.depth = up == null ? 0 : up.depth + 1;
        }
        
        /** A key whose segment i is not in this leaf: a new segment tree below it. */
        void fresh(long[] key, int i) {
            if (freshKeys == null) {
                freshKeys = new java.util.HashMap<Long, java.util.List<long[]>>();
                freshLevel = i;
            }
            java.util.List<long[]> l = freshKeys.get(key[i]);
            if (l == null) {
                l = new java.util.ArrayList<long[]>();
                freshKeys.put(key[i], l);
                klongs++;                       // the pointer to the new segment tree
            }
            l.add(key);
        }
    }
    
    private static Walked walked(java.util.IdentityHashMap<KeyNode, Walked> walked, KeyNode node,
            Walked up) {
        Walked w = walked.get(node);
        if (w == null) {
            w = new Walked(node, up);
            walked.put(node, w);
        }
        return w;
    }
    
    /** How many times a node of 'size' klongs, given 'klongs' more and a TIME klong, can overflow. */
    private long overflows(long klongs, int size) {
        if (klongs == 0) {
            return 0;
        }
        final long k = klongs + 1;
        final long room = Math.max(0, maxNodeSize - 2 - size);
        if (k <= room) {
            return 0;
        }
        final long q = Math.max(2, maxNodeSize / 2 - 3);
        return 1 + (k - room - 1) / q;
    }
    
    /**
     * The nodes of the new segment trees of 'keys', which share their segments before 'level'
     * and whose segment 'level' is in a new tree: its root, the in-place splits of its new
     * nodes (one new node and one klong above a split), a new root for each level, and the
     * trees below.
     */
    private long freshTreeBound(java.util.List<long[]> keys, int level) {
        long klongs = 0;
        java.util.HashMap<Long, java.util.List<long[]>> below =
                new java.util.HashMap<Long, java.util.List<long[]>>();
        for (long[] key : keys) {
            if (key.length == level + 1) {
                klongs++;                       // a value
            } else {
                java.util.List<long[]> l = below.get(key[level]);
                if (l == null) {
                    l = new java.util.ArrayList<long[]>();
                    below.put(key[level], l);
                    klongs++;                   // the pointer to the tree below
                }
                l.add(key);
            }
        }
        long count = 1;
        for (long ov = overflows(klongs, 0); ov > 0; ov = overflows(ov, 1)) {
            count += ov + 1;                    // the splits, and a new node above them
        }
        for (java.util.List<long[]> l : below.values()) {
            count += freshTreeBound(l, level + 1);
        }
        return count;
    }
    
    // ======== getMany() ========
    
    /**
     * Get multiple KVs in increasing (or decreasing) key order.
     * 
     * @param g
     *            Input and output parameters. The GetMany object should have been createed
     *            with the newGetMany() factory method.
     * @see GetMany
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

        KeyNode root = topDs.findRoot(g.actualLookupTime, g.gd);
        
        if (root == null) {
            return;
        }

        GetMany.Chain chain = g.new Chain();
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
     * that read with a lookup time strictly less than the transaction time
     * of the current transaction.</p>
     * 
     * @param key     The key (as segments).
     * @param value   The value; null for delete operation.
     * @throws DbException
     */
    public void putKv(long[] key, byte[] value, PutData pd) {
        //
        // in:   time, key, value.
        // out:  changes to dag, 
        //       changed/new nodes reported to pd.nodeChangeListener.
        //       new pointers reported to pd.pointerCreatedListener.
        //
        // ALL modifications to the Dag are done through this method.
        // The call graph has recursion; appendKlongs() is called by successors of appendKlong()
        // on call graph.
        //
        
        assert pd.tt >= 0;
        assert pd.nodeChangeListener != null;
        assert pd.pointerListener != null;
        assert pd.pointerCreatedListener != null;
        assert key != null && key.length > 0 : "key not non-null and with length > 0";
        
        final KeyNode root = topDs.findRoot(pd.tt, pd);
        
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
                segmentRoot = setNode(segmentRoot, key[i], value != null, pd);
                if (segmentRoot == null) {
                    // A delete of a key that does not exist, a noop. No node must be
                    // created; noops are not stored, so the rerun at startup would not
                    // create it, and node ids would differ after a restart.
                    return;
                }
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
            assert pd.kwi.klong != Klong.NULL : 
                "pd.kwi.klong is Klong.NULL, non-null expected, node: " + node.print();
            
            node = (KeyNode) pd.followPointer(node, pd.kwi.pointerIndex);
            assert node != null;
        }

        if (value == null) {
            // A delete operation. A ValueNode (of delete type) is created
            // only for the pd.nodeChangeListener.
            
            boolean isNoop = appendDeleteKlong(node, pd.keyAccessPath.size - 1, compareValue, pd);
            if (!isNoop) {
                pd.nodeChangeListener.valueNodeCreated(ValueNode.createDelete(), key);
            }
            
        } else {
            ValueNode valueNode = new ValueNode(value);
            pd.nodeChangeListener.valueNodeCreated(valueNode, key);
            
            // "+1" is needed. We need to be able to fit two more klongs. 
            // A TIME klong may be needed.
            
            if (node.size + 1 < this.maxNodeSize) {
                node.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        valueNode, pd.accessData);
                pd.pointerCreatedListener.pointerCreated(node, node.size - 1, valueNode);
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
     * If 'create' is false, nothing is created and null is returned if the
     * node does not exist.
     */
    private KeyNode setNode(KeyNode segmentRoot, long compareValue, boolean create, PutData pd) {
        KeyNode current = segmentRoot;
        KeyNode result;
        
        assert current.assertOk(this.maxNodeSize);
        
        while (!current.isSegmentLeaf()) {
            current.searchLte(pd.tt, compareValue, pd.kwi);
            assert pd.kwi.klong != Klong.NULL 
                    : "LTE search -> Klong.NULL, tt=" + pd.tt + ", node:" + current.print();
            assert pd.kwi.pointerIndex >= 0 
                    : "LTE search found klong, but pointerIndex=" + pd.kwi.pointerIndex;
            
            current = (KeyNode) pd.followPointer(current, pd.kwi.pointerIndex);
            assert current.assertOk(this.maxNodeSize);
        }
        
        current.searchEq(pd.tt, compareValue, pd.kwi);

        if (pd.kwi.klong == Klong.NULL && !create) {
            result = null;

        } else if (pd.kwi.klong == Klong.NULL) {
            // If not found, create the node

            KeyNode child = new KeyNode(true); // New segment leaf node.
            pd.nodeChangeListener.keyNodeCreated(child);
            
            // "+1" needed since there might be a need to insert a TIME klong too.
            if (current.size + 1 < this.maxNodeSize) {
                current.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        child, pd.accessData);
                pd.pointerCreatedListener.pointerCreated(current, current.size-1, child);
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
            result = (KeyNode) pd.followPointer(current, pd.kwi.pointerIndex);
        }

        return result;
    }
    

    /**
     * Appends a delete klong to 'node' if needed to delete the node with the
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
        // said delete klong is updated to set a delete bit for the specified compareValue.
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
        long arrayDel = Klong.createDelete();
        long del = Klong.createDelete();
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
                
            } else {                
                if (node.size + 1 < this.maxNodeSize) {
                    node.addDeleteKlong(tTime, union);
                    pd.nodeChangeListener.keyNodeChanged(node);
                } else {                    
                    KeyNode last = node.lastVersionGivenDel(sz, tTime, union);
                    handleFullNode(node, depth, ZERO_LONG_KWP, tTime, last, pd);
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
        // This should be the only way the db adds klongs to KeyNodes. It is the
        // central point of code for node splitting.
        //
        // Recursion is used, this method is called from methods called directly or 
        // indirectly from this method (method call graph has directed cycles).
        //
        // Implementation note: we allow memory allocation for a split, avoid it otherwise.
        // 

        assert toAppend.length < 3 : "toAppend.length = " + toAppend.length;
        assert toAppend.length > 0 : "toAppend.length = " + toAppend.length;
        assert node.assertOk(maxNodeSize);

        // "+1" is needed since a TIME klong could be added along with the toInsert klongs.
        final boolean isFull = node.size + toAppend.length + 1 > this.maxNodeSize;

        if (!isFull) {
            for (int i = 0; i < toAppend.length; i++) {
                KlongWithPointer kwi = toAppend[i];
                node.addKlong(pd.tt, kwi.klong, kwi.node, pd.accessData);
                if (kwi.node != null) {
                    pd.pointerCreatedListener.pointerCreated(node, node.size - 1, kwi.node);
                }
            }
            pd.nodeChangeListener.keyNodeChanged(node);
            assert node.assertOk(maxNodeSize);
            
        } else {
            // 'node' is full. We cannot append 'toInsert' to it.
            // It is either space-full or time-full.
            //
            // 'last' is created, but note this is not always a node
            // that will be used in the DAG. If 'node' is space-full, 
            // 'first' and 'second' nodes will be used instead.
            // Therefore, pd.nodeChangeListener.keyNodeCreated()
            // is not called here for 'last'.
            //
            
            KeyNode last = node.lastVersion(pd.tt);
            
            assert last.assertOk(maxNodeSize);
            handleFullNode(node, depth, toAppend, pd.tt, last, pd);
        }
    }
    
    /**
     * This is an important method.
     * If last.size > maxNodeSize / 2, then 'node' is split into two nodes -
     * a space-split is made. Otherwise, 'node' is replaced by the last version 
     * of it - a time-split.
     * 
     * <p>A node that the current transaction created is not replaced: it is split in place
     * (timeSplitInPlace, spaceSplitInPlace). A node that existed before is replaced, and then
     * loses the klongs of the current transaction, which its replacement has. So a
     * transaction leaves no node that it created unreachable at its time, and no klong of
     * its time in a node that is not reachable at that time: a whole transaction is one
     * transaction of the Lean model (assumptions A2 and A3; docs/level2-alignment.md,
     * M1). Before 2026-10-16, a later key of a transaction could replace a node that an
     * earlier key had created or changed.</p>
     */
    private void handleFullNode(final KeyNode node, final int depth,
            final KlongWithPointer[] toInsert, final long tTime, KeyNode last, PutData pd) {
        //
        // When this method is called, 'last' has not been added reported as a new node
        // (pd.nodeChangeListener.keyNodeChanged(last) not called).
        //
        // A node with no klong before tTime was created by this transaction (or was empty
        // before it). No reader can see its klongs: readers use lookup times before tTime,
        // and it is linked only by klongs of tTime. So it can be changed in place.
        //
        
        final boolean newInTrans = node.getFirstTime() == tTime;
        
        if (last.size > this.maxNodeSize / 2) {
            if (newInTrans) {
                spaceSplitInPlace(node, last, depth, toInsert, pd);
            } else {
                spaceSplit(node, last, depth, toInsert, pd);
            }
        } else {
            if (newInTrans) {
                timeSplitInPlace(tTime, node, last, toInsert, pd);
            } else {
                timeSplit(tTime, last, depth, toInsert, pd);
            }
        }
        
        if (!newInTrans) {
            // 'node' is no longer current. Its klongs of tTime are in its replacement
            // ('last' copies every live klong), and no reader sees them (lookup times are
            // before tTime), so they go: otherwise the node would keep klongs that no lookup
            // ever sees. See the class comment of KeyNode about the size of a replaced node.
            node.toPreviousState(tTime - 1);
            pd.nodeChangeListener.keyNodeReplaced(node);
        }
    }
    
    /**
     * A time split of a node that the current transaction created: the node is compacted
     * in place to its last version, instead of being replaced by it. See handleFullNode().
     */
    private void timeSplitInPlace(final long tTime, final KeyNode node, KeyNode last,
            KlongWithPointer[] toAppend, PutData pd) {
        for (int i = 0; i < toAppend.length; i++) {
            KlongWithPointer kwi = toAppend[i];
            boolean replaced = last.replaceKlong(tTime, kwi.klong, kwi.node, pd.accessData);
            if (!replaced) last.addKlong(tTime, kwi.klong, kwi.node, pd.accessData);
        }
        
        node.setContentFrom(last);
        reportNewPointers(node, pd.pointerCreatedListener);
        pd.nodeChangeListener.keyNodeChanged(node);
        pd.splitListener.nodeSplit(Dag.TIME_SPLIT_1);
        assert node.checkWithMessage() == null : node.checkWithMessage();
    }
    
    /**
     * A space split of a node that the current transaction created: the node keeps the first
     * half, in place, and only the second half is a new node. A space root or a segment root
     * gets a new root above both halves, as in spaceSplit(). See handleFullNode().
     */
    private void spaceSplitInPlace(final KeyNode node, KeyNode last, final int depth,
            final KlongWithPointer[] toInsert, PutData pd) {
        final long tt = pd.tt;
        final boolean isSegmentLeaf = node.isSegmentLeaf();
        final KeyNode first = new KeyNode(isSegmentLeaf);     // only holds the first half
        final KeyNode second = new KeyNode(isSegmentLeaf);
        final KeyNode parent = pd.getParent(depth);
        
        pd.nodeChangeListener.keyNodeCreated(second);
        long secondKlong = node.firstAndSecond(tt, last, toInsert, first, second);
        node.setContentFrom(first);
        reportNewPointers(node, pd.pointerCreatedListener);
        reportNewPointers(second, pd.pointerCreatedListener);
        pd.nodeChangeListener.keyNodeChanged(node);
        pd.nodeChangeListener.keyNodeChanged(second);
        
        if (parent == null || parent.isSegmentLeaf()) {
            // 'node' is the space root or a segment root: a new root above both halves.
            KeyNode newRoot = new KeyNode(false);
            pd.nodeChangeListener.keyNodeCreated(newRoot);
            newRoot.addKlong(tt, Klong.EMPTY_KEY, node, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newRoot, newRoot.size - 1, node);
            newRoot.addKlong(tt, secondKlong, second, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newRoot, newRoot.size - 1, second);
            
            if (parent == null) {
                topDs.newSuperRoot(tt, newRoot, pd.accessData, pd.pointerCreatedListener,
                        pd.nodeChangeListener);
                pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_3);
            } else {
                long klong1 = pd.keyAccessPath.getKlong(depth);
                assert klong1 != Klong.NULL : "Missing klong in keyAccessPath, " + depth;
                pd.oneKwi[0].klong = klong1;
                pd.oneKwi[0].node = newRoot;
                pd.oneKwi[0].pos = pd.accessData;
                appendKlongs(parent, depth - 1, pd.oneKwi, pd);
                pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_2);
            }
            assert newRoot.checkWithMessage() == null;
        } else {
            // The parent already points to 'node', the first half.
            pd.oneKwi[0].klong = secondKlong;
            pd.oneKwi[0].node = second;
            pd.oneKwi[0].pos = pd.accessData;
            appendKlongs(parent, depth - 1, pd.oneKwi, pd);
            pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_1);
        }
    }
    
    /**
     * A time split "replaces" the time-full node with the last version of it.
     * This method handles both: time-split-1 and time-split-2 cases.
     */
    private void timeSplit(final long tTime, KeyNode last, final int depth,
            KlongWithPointer[] toAppend, PutData pd) {
        //
        // 131005, added the last.replaceKlong() method call. A bit of a hack.
        //   See Graph.testTimeSplit1a().
        //   TODO LATER. Consider other solution. Maybe last should include toAppend.
        //
        // Last version is small enough not to split into two nodes, but not empty.
        //
                
        final KeyNode parent = pd.getParent(depth);

        for (int i = 0; i < toAppend.length; i++) {
            KlongWithPointer kwi = toAppend[i];    
            boolean replaced = last.replaceKlong(tTime, kwi.klong, kwi.node, pd.accessData);
            if (!replaced) last.addKlong(tTime, kwi.klong, kwi.node, pd.accessData);
        }
        
        pd.nodeChangeListener.keyNodeCreated(last);
        reportNewPointers(last, pd.pointerCreatedListener);
        
        if (parent == null) {
            // time-split-2:
            // No parent, 'last' is the new super root.
            
            topDs.newSuperRoot(tTime, last, pd.accessData, pd.pointerCreatedListener, pd.nodeChangeListener);
            
            pd.splitListener.nodeSplit(Dag.TIME_SPLIT_2);
            assert last.checkWithMessage() == null;
            
        } else {
            // time-split-1:
            // There is a parent.
            
            long klong1 = pd.keyAccessPath.getKlong(depth);
            assert klong1 != Klong.NULL : "time-split-1, missing klong in keyAccessPath, " + depth;

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

        pd.nodeChangeListener.keyNodeCreated(first);
        pd.nodeChangeListener.keyNodeCreated(second);
        
        if (parent == null) {
            //
            // space-split-3:
            // 'node' is the space root node.
            //
            KeyNode newRoot = new KeyNode(false);
            pd.nodeChangeListener.keyNodeCreated(newRoot);
            
            long secondKlong = node.firstAndSecond(tt, last, toInsert, first, second);
            reportNewPointers(first, pd.pointerCreatedListener);
            reportNewPointers(second, pd.pointerCreatedListener);
            
            newRoot.addKlong(tt, Klong.EMPTY_KEY, first, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newRoot, newRoot.size - 1, first);
            newRoot.addKlong(tt, secondKlong, second, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newRoot, newRoot.size - 1, second);
            
            pd.nodeChangeListener.keyNodeChanged(first);
            pd.nodeChangeListener.keyNodeChanged(second);

            topDs.newSuperRoot(tt, newRoot, pd.accessData, pd.pointerCreatedListener, pd.nodeChangeListener);

            pd.splitListener.nodeSplit(Dag.SPACE_SPLIT_3);
            assert newRoot.checkWithMessage() == null;

        } else if (parent.isSegmentLeaf()) {
            //
            // space-split-2:
            // 'node' is a segment root since parent is a segment leaf.
            //
            
            KeyNode newSegmentRoot = new KeyNode(false);
            pd.nodeChangeListener.keyNodeCreated(newSegmentRoot);
            long secondKlong = node.firstAndSecond(tt, last, toInsert, first, second);
            reportNewPointers(first, pd.pointerCreatedListener);
            reportNewPointers(second, pd.pointerCreatedListener);
            
            newSegmentRoot.addKlong(tt, Klong.EMPTY_KEY, first, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newSegmentRoot, newSegmentRoot.size - 1, first);
            newSegmentRoot.addKlong(tt, secondKlong, second, pd.accessData);
            pd.pointerCreatedListener.pointerCreated(newSegmentRoot, newSegmentRoot.size - 1, second);
            
            pd.nodeChangeListener.keyNodeChanged(first);
            pd.nodeChangeListener.keyNodeChanged(second);

            long klong1 = pd.keyAccessPath.getKlong(depth);
            assert klong1 != Klong.NULL : "Missing klong in keyAccessPath, " + depth;

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
            reportNewPointers(first, pd.pointerCreatedListener);
            reportNewPointers(second, pd.pointerCreatedListener);
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

    private void reportNewPointers(KeyNode node, PointerCreatedListener listener) {
        int size = node.size;
        for (int i = 0; i < size; i++) {
            Node pointee = node.pointers[i];
            if (pointee != null) {
                listener.pointerCreated(node, i, pointee);
            }
        }
    }
    
    
    // ======== Inner types ========
    
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
        public Node readNode(long spos);
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
                Node predecessor, int pointerIndex, Node result, int pointerType);
    }
    
    public static final PointerListener DO_NOTHING_POINTER_LISTENER = new PointerListener() {
        public void pointerFollowed(Node predecessor, int pointerIndex, Node result,
                int pointerType) {}

        public void superRootAccessed(TopNode mySuperRoot) {}
    };
    
    
    public static interface PointerCreatedListener {
        /**
         * Reports that a node from 'from' to 'to' was created.
         * Report this AFTER 'from' and 'to' have been created and the node creation
         * has been reported to the NodeChangeListener.
         * 
         * @param index  Pointer index of pointer created.
         */
        public void pointerCreated(Node from, int index, Node to);
    }
    
    public static final PointerCreatedListener DO_NOTHING_POINTER_CREATED_LISTENER = 
        new PointerCreatedListener() {
            public void pointerCreated(Node from, int index, Node to) {}
        };
    
    
    /**
     * The cache policy determines whether to cache nodes read from stream.
     * This interface enables us to easily set a cache policy such as:
     * cache all nodes read from stream, cache no nodes, cache only KeyNodes, cache all
     * KeyNodes and all ValueNodes that are smaller than 400k in size.
     * Cache policy can be set per get operation.
     */
    public static interface CachePolicy {
        /**
         * If true is returned, the node will be cached.
         * 
         * @param node  A node that was just read from the stream.
         * @return True to cache the node.
         */
        public boolean shouldCache(Node node);
    }
    
    public static final CachePolicy CACHE_ALL = new CachePolicy() {
        public boolean shouldCache(Node node) {
            return true;
        }
    };
    
    public static final CachePolicy CACHE_NOTHING = new CachePolicy() {
        public boolean shouldCache(Node node) {
            return false;
        }
    };
    
    /**
     * Cache policy that caches all nodes except for ValueNodes with a value larger 
     * than 1 MiB.
     */
    public static final CachePolicy CACHE_ALL_EXCEPT_LARGE_VALUE_NODES = new CachePolicy() {
        public boolean shouldCache(Node node) {
            boolean result;
            int type = node.getType();
            if (type == Node.TYPE_VALUE) {
                result = ((ValueNode) node).getValue().length <= 1024*1024;
            } else {
                result = true;
            }
            return result;
        }
    };
    
    /**
     * Listens to Db graph nodes that are created or changed.
     */
    public static interface NodeChangeListener {
        
        /**
         * Reports that a TopNode was created.
         */
        public void topNodeCreated(TopNode node);
        
        /**
         * Reports that a new KeyNode was created.
         */
        public void keyNodeCreated(KeyNode node);
        
        /**
         * Reports that a ValueNode was created.
         */
        public void valueNodeCreated(ValueNode node, long[] key);
        
        /**
         * Reports that an existing KeyNode was appended to.
         */
        public void keyNodeChanged(KeyNode node);
        
        /**
         * Reports that a KeyNode that existed before the current transaction was replaced by
         * a split: it is no longer current, and it has no klongs of the transaction
         * (Dag.handleFullNode). Added 2026-10-16; does nothing by default.
         */
        public default void keyNodeReplaced(KeyNode node) {}
        
        /**
         * Reports that the super root, which existed before the current transaction, was
         * replaced by a new super root (TopDs.newSuperRoot). Added 2026-10-16; does nothing
         * by default.
         */
        public default void topNodeReplaced(TopNode node) {}
    }
    
    public static final NodeChangeListener DO_NOTHING_NODE_CHANGE_LISTENER = new NodeChangeListener() {
        public void topNodeCreated(TopNode node) {}
        public void keyNodeCreated(KeyNode node) {}
        public void keyNodeChanged(KeyNode node) {}
        public void valueNodeCreated(ValueNode node, long[] key) {}
    };
    
    
    
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
