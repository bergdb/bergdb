package bergdb.coreds;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

import bergdb.storage.StreamFormatException;

/**
 * The DB graph is the core data structure of the database.
 * 
 * @author Frans Lundberg
 */
public class Graph implements TopDs.DbGraphForMe {
    private final TopDs topDs;
    private NodeReader nodeReader;
    private final int POINTER_LOCKS_LENGTH = 128;
    private final Object[] pointerLocks;
    private int maxNodeSize;
    
    /**
     * Private constructor; see the create methods for how to create
     * a DbGraph object.
     */
    private Graph(TopDs topDs) {
        if (topDs == null) throw new IllegalArgumentException("topDs == null not allowed");
        
        this.topDs = topDs;
        
        this.nodeReader = new NodeReader() {
            public INode readNode(long spos, byte[] tempBuffer) {
                throw new IllegalStateException("No nodeReader was set, use " 
                        + Graph.class.getName() + ".setNodeReader().");
            }
        };
        
        this.pointerLocks = new Object[POINTER_LOCKS_LENGTH];
        for (int i = 0; i < POINTER_LOCKS_LENGTH; i++) {
            pointerLocks[i] = new Object();
        }
    }
    
    /**
     * Creates and returns a new, minimal DbGraph.
     * The returned graph has exactly one top node and one key node.
     * Nothing is written to the node stream.
     */
    private static Graph create(long time) {
        KeyNode root = new KeyNode();
        TopDs topDs = TopDs.createFromFirstRoot(time, root, Spos.DEFAULT_ACCESS_DATA);
        Graph g = new Graph(topDs);
        return g;
    }
    
    /**
     * Creates a DbGraph from the stream nodes of the startup interval 
     * of the DB stream.
     * 
     * @param accessData
     * @param posMap
     * @param nextMap
     * @return
     */
    private static Graph createFromStreamNodes(long accessData,
            HashMap<Long, INode> posMap, HashMap<Long, INode> nextMap) {
        //
        // Pointer reconciliation phase
        // * Refreshes stream pointers
        // * Creates memory pointers
        // * Finds the superRoot TopNode among the startup nodes.
        //

        TopNode superRoot = null;
        Pointer pointer = new Pointer();

        for (Map.Entry<Long, INode> entry : posMap.entrySet()) {
            INode node = entry.getValue();

            int pointerCount = node.getPointerCount();
            for (int i = 0; i < pointerCount; i++) {
                node.getPointer(i, pointer);
                if (pointer.isNull()) {
                    continue;
                }

                long pos = pointer.getPos();

                while (true) {
                    INode next = nextMap.get(pos);
                    if (next == null) {
                        break;
                    }
                    pos = next.getSpos();
                }

                if (pointer.getPos() != pos) {
                    node.setPointer(i, null, pos);
                }
            }

            // Check for super root node.

            if (node instanceof TopNode) {
                TopNode potentialSuperRoot = (TopNode) node;
                if (superRoot == null) {
                    superRoot = potentialSuperRoot;
                }

                if (potentialSuperRoot.topNodeId > superRoot.topNodeId) {
                    superRoot = potentialSuperRoot;
                }
            }
        }

        if (superRoot == null) {
            throw new StreamFormatException("Could not find root node within startup node set.");
        }

        // Creates memory pointers from stream pointers.

        Pointer p2 = new Pointer();

        for (Map.Entry<Long, INode> entry : posMap.entrySet()) {
            INode node = entry.getValue();

            int pointerCount = node.getPointerCount();
            for (int i = 0; i < pointerCount; i++) {
                node.getPointer(i, p2);
                if (p2.isNull()) {
                    continue;
                }

                INode pointee = posMap.get(p2.pos);
                if (pointee != null) {
                    node.setPointer(i, pointee, accessData);
                }
            }
        }
        
        Graph g = new Graph(new TopDs(superRoot));
        return g;
    }
    
    public void setNodeReader(NodeReader nodeReader) {
        if (nodeReader == null) {
            throw new IllegalArgumentException("nodeReader == null not allowed");
        }
        this.nodeReader = nodeReader;
    }
    
    /**
     * Prints the in memory part of the DB graph. Useful for test and development.
     */
    public void printGraph(PrintStream out) {
        TopNode top = topDs.getSuperRoot();
        top.printGraph(out, "", 0);
    }
    
    // ---- getOne() with helpers ----
    
    /**
     * Gets one KV value or returns null if it does not exist.
     * 
     * @param time  The lookup time.
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
     * @param choices
     *            The choice path records pointer indexes chosen, may be null to
     *            disable the choice recording.
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
                    result = followPointer(current, kwi.pointerIndex, gd.accessData, gd.pointerListener, gd.cachePolicy);
                }
                break;

            } else {
                current.searchLte(time, compareValue, kwi);

                if (kwi.klong == Klong.NULL) {
                    result = null;
                    break;
                } else {
                    assert kwi.node == null || kwi.node instanceof KeyNode : "Expected a KeyNode, got "
                            + kwi.node;

                    KeyNode nextCurrent = (KeyNode) followPointer(current, kwi.pointerIndex,
                            gd.accessData, gd.pointerListener, gd.cachePolicy);
                    current = nextCurrent;
                }
            }
        }

        return result;
    }
    
    
    
    //
    // ---- putKv() with helpers ----
    // Does DbGraph need to know about transactions? Or is putKv() enough?
    //
    
    
    /**
     * <p>Adds a KV to the graph.
     * If a KV with the given key exists, the last value for the key is replaced.
     * If value is null, this is a delete operation.</p>
     * 
     * <p>This method runs with exclusive write access to the data structure 
     * (synchronized on Db.writeLock). However, there may be concurrent readers 
     * that read with a lookup time strictly less than the transaction time.
     * Caller must hold Db.writeLock.</p>
     * 
     * @param tt      Transaction time.
     * @param key     The key segments.
     * @param value   The value; null for delete operation.
     */
    public void putKv(long[] key, byte[] value, PutData pd) {
        //
        // in:   time, key, value.
        // out:  changes to graph, 
        //       changed/new nodes added to transactionNodes,
        //       accessed nodes ensured "dirty"
        //
        
        assert pd.tt >= 0;
        assert pd.nodeChangeListener != null;
        assert pd.pointerListener != null;
        assert key != null && key.length > 0;
        
        Pointer tempPointer = new Pointer();
        final KeyNode root = topDs.findRoot((TopDs.DbGraphForMe) this, pd.tt, pd.accessData,
                tempPointer, pd.pointerListener, pd.cachePolicy);
        
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
        
        while (!node.isSegmentLeaf()) {
            node.searchLte(pd.tt, compareValue, pd.kwi);
            assert pd.kwi.klong != Klong.NULL;
            node = (KeyNode) followPointer(node, pd.kwi.pointerIndex, pd.accessData,
                    pd.pointerListener, pd.cachePolicy);
            assert node != null;
        }
        
        //assert node.size <= this.maxNodeSize : "Overfull node, node.size=" + node.size 
        //        + ", maxNodeSize=" + maxNodeSize + ", node: " + node.toString();

        if (value == null) {
            // If a delete operation.
            
            // 130514 Frans: Added delete ValueNode to transaction nodes. Needed to store choices for
            // the delete operation. But only non-noop deletes added.
            
            // Inserts a delete klong if needed.
            
            throw new Error("Delete not implemented yet!");   // TODO B. Implement.
            
            /*boolean isNoop = insertDeleteKlong(node, keyAccessPath.size - 1, compareValue);
            if (!isNoop) {
                transactionNodes.add(node);
                ValueNode valueNode = new ValueNode(null);
                transactionNodes.add(valueNode, kv.keySegments);
            }*/
        } else {
            //transactionNodes.add(node);
            pd.nodeChangeListener.keyNodeChanged(node);
            
            ValueNode valueNode = new ValueNode(value);
            //transactionNodes.add(valueNode, kv.keySegments);
            pd.nodeChangeListener.newValueNode(valueNode, key);
            
            // We need to be able to fit two more klongs. A TIME klong might be needed.
            // This is sub-optimal. Sometimes a node can be added without adding a TIME klong.
            // Little to gain from optimizing this, however.
            
            // "+1" needed, there may be a need to insert a TIME klong too.
            if (node.size + 1 < this.maxNodeSize) {
                node.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        valueNode, pd.accessData);
            } else {
                
                throw new Error("insertKlongs not implemented, node: " + node);  // TODO B. Implement!
                
                /*
                oneKwi[0].klong = Klong.compareValueToKeyKlong(compareValue);
                oneKwi[0].node = valueNode;
                oneKwi[0].pos = this.transAccessData;
                insertKlongs(node, keyAccessPath.size - 1, oneKwi);
                */
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
        
        while (!current.isSegmentLeaf()) {
            current.searchLte(pd.tt, compareValue, pd.kwi);
            assert pd.kwi.klong != Klong.NULL;
            current = (KeyNode) followPointer(current, pd.kwi.pointerIndex, pd.accessData,
                    pd.pointerListener, pd.cachePolicy);
            assert current != null;
        }
        
        current.searchEq(pd.tt, compareValue, pd.kwi);

        if (pd.kwi.klong == Klong.NULL) {
            // If not found, create the node

            KeyNode child = new KeyNode(true); // New segment leaf node.

            // "+1" needed since there might be a need to insert a TIME klong too.
            if (current.size + 1 < this.maxNodeSize) {
                current.addKlong(pd.tt, Klong.compareValueToKeyKlong(compareValue),
                        child, pd.accessData);
            } else {
                pd.oneKwi[0].klong = Klong.compareValueToKeyKlong(compareValue);
                pd.oneKwi[0].node = child;
                pd.oneKwi[0].pos = pd.tt;
                
                throw new Error("insertKlongs not implemented!");    // TODO B. implement
                // insertKlongs(current, keyAccessPath.size - 1, oneKwi);
                
            }
            result = child;

            pd.nodeChangeListener.keyNodeChanged(current);
            pd.nodeChangeListener.keyNodeChanged(child);
            
        } else {
            // If found
            result = (KeyNode) followPointer(current, pd.kwi.pointerIndex, pd.accessData, 
                    pd.pointerListener, pd.cachePolicy);
        }

        return result;
    }
    
    
    
    // ---- followPointers() and helpers ----
    
    /**
     * Follows a pointer. This method must always be used when a pointer is
     * followed. This is an essential method. It is used both by get and put operations.
     * Besides following a pointer, it handles add-to-cache, and sets access data for
     * the pointer (when was it last used). The access data is used by the 
     * cache eviction algorithm.
     */
    public final INode followPointer(final INode predecessor, int pointerIndex, long accessData, 
            PointerListener pointerListener, CachePolicy cachePolicy) {
        //
        // 130928 Frans: Made listener and cachePolicy interfaces. Very flexible.
        //      We will see if it is fast enough.
        //
        
        INode result;
        assert predecessor != null;

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
                pointerListener.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
            
            } else {
                result = nodeReader.readNode(pointerPos, null);
                
                pointerListener.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_STREAM);
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
    private final Object getPointerLock(final INode node, final int pointerIndex) {
        int value = (node.hashCode() + 13 * pointerIndex);
        value = (value < 0) ? -value : value;
        return pointerLocks[value % POINTER_LOCKS_LENGTH];
    }
    
    /**
     * The way to create a Builder.
     */
    public static Builder builder() {
        return new Builder();
    }
    
    // ---- The Builder ----
    
    /**
     * An object of this class is used to properly build a DB object.
     */
    public static class Builder {
        private int maxNodeSize;
        
        private Builder() {
            maxNodeSize30();    // Default and best max node size.
        }
        
        /** 
         * Use for testing only.
         */
        public Builder maxNodeSize4() {
            this.maxNodeSize = 4;
            return this;
        }
        
        /** 
         * Use for testing only.
         */
        public Builder maxNodeSize8() {
            this.maxNodeSize = 8;
            return this;
        }

        public Builder maxNodeSize14() {
            this.maxNodeSize = 16 - 2;
            return this;
        }

        public Builder maxNodeSize30() {
            this.maxNodeSize = 32 - 2;
            return this;
        }

        public Builder maxNodeSize62() {
            this.maxNodeSize = 64 - 2;
            return this;
        }
        
        /**
         * Creates a new DbGraph in its initial state created at t=time.
         */
        public Graph createEmpty(long time) {
            Graph g = Graph.create(time);
            g.maxNodeSize = this.maxNodeSize;
            return g;
        }
        
        public Graph createFromStreamNodes(long accessData, 
                HashMap<Long, INode> posMap, HashMap<Long, INode> nextMap) {
            Graph g = Graph.createFromStreamNodes(accessData, posMap, nextMap);
            g.maxNodeSize = this.maxNodeSize;
            return g;
        }
    }
    
    
    // ---- Inner interfaces / classes ----
    
    /**
     * A NodeReader has method readNode() that can read a node from the DB stream
     * give the spos of the node.
     */
    public static interface NodeReader {
        
        /**
         * Reader a node from the stream. Assumes the item exists at the location 
         * and that it is valid.
         * 
         * @param tempBuffer A buffer to read to. Avoids some mem alloc. If non-null it must be at
         * least 4 bytes long. If long enough to read the node into it, it will save some 
         * memory allocation.
         * @throws StreamFormatException
         * @throws StreamIoException
         */
        public INode readNode(long spos, byte[] tempBuffer);
    }
    
    
    /**
     * A listener that listens to what happens when the DB graph is walked
     * and a Walker also determines whether a read stream node should be cached or not.
     */
    public static interface PointerListener {
        
        /**
         * Reports that a pointer was followed.
         * 
         * @param pointerType One of Pointer.TYPE_MEMORY, Pointer.TYPE_STREAM.
         */
        public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType);
    }
    
    public static final PointerListener DO_NOTHING_POINTER_LISTENER = new PointerListener() {
        public void pointerFollowed(INode predecessor, int pointerIndex, INode result,
                int pointerType) {}
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
    
    public static final CachePolicy CACHE_ALL_BUT_VERY_LARGE_VALUE_NODES = new CachePolicy() {
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
    
    /**
     * Common for a transaction (a number of putKv operations).
     */
    public static class PutData {
        /** Transaction time. */
        public long tt;
        
        /** Access data. */
        public long accessData;
        
        // ---- Temp data ---
        
        /** Temporary working data. */
        public final Pointer tempPointer;
        
        /** Temporary working data. */
        public final KlongWithPointer kwi;
        
        /** Temporary working data, length = 1. */
        public final KlongWithPointer[] oneKwi;
        
        public NodeChangeListener nodeChangeListener;
        
        public PointerListener pointerListener;
        
        public CachePolicy cachePolicy;
        
        public KeyAccessPath keyAccessPath;
        
        public PutData() {
            tempPointer = new Pointer();
            kwi = new KlongWithPointer();
            oneKwi = new KlongWithPointer[1];
            oneKwi[0] = new KlongWithPointer();
            keyAccessPath = new KeyAccessPath();
            
            nodeChangeListener = Graph.DO_NOTHING_NODE_CHANGE_LISTENER;
            pointerListener = new Graph.PointerListener() {
                public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) { 
                    if (result != null) {
                        if (result.getType() == INode.TYPE_KEY_NODE) {
                            if (predecessor.getType() == INode.TYPE_TOP_NODE) {
                                keyAccessPath.add(Klong.NULL, (KeyNode) result); 
                            } else if (predecessor.getType() == INode.TYPE_KEY_NODE) {
                                KeyNode pre = (KeyNode) predecessor;
                                KeyNode res = (KeyNode) result;
                                keyAccessPath.add(pre.getKlong(pointerIndex), res);
                            }
                        }
                    }
                }
            };
            
            cachePolicy = Graph.CACHE_ALL;
        }
    }
}

/*

Dev notes
=========

Start with beautiful, understandable code. Possibly later add "Optimized" ending to 
certain methods if optimization is needed. Keep original and go back to it it there 
are bugs. We could even have a switch, if (highPerformance) {....

Concepts:

* Optimized, non-optimized switching.
* Self-testing data structure.


General walking - what is needed?
=================================

Use cases:

1. GetOne operation.
2. Follow choices.
3. Set KV - find where to insert klong (or split, ...).
4. Walk all in-memory nodes.
5. Warm-up get (before writeLock).


*/