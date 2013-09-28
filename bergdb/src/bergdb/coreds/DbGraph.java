package bergdb.coreds;

import java.util.HashMap;
import java.util.Map;

import bergdb.storage.StreamFormatException;

/**
 * The DB Graph is the core data structure of the database.
 * 
 * @author Frans Lundberg
 */
public class DbGraph implements TopDs.DbGraphForMe {
    private final TopDs topDs;
    private NodeReader nodeReader;
    private final int POINTER_LOCKS_LENGTH = 128;
    private final Object[] pointerLocks;
    
    /**
     * Private constructor; see the create methods for how to create
     * a DbGraph object.
     */
    private DbGraph(TopDs topDs) {
        if (topDs == null) throw new IllegalArgumentException("topDs == null not allowed");
        this.topDs = topDs;
        this.nodeReader = new NodeReader() {
            public INode readNode(long spos, byte[] tempBuffer) {
                throw new IllegalStateException("No nodeReader was set, use " 
                        + DbGraph.class.getName() + ".setNodeReader().");
            }
        };
        
        pointerLocks = new Object[POINTER_LOCKS_LENGTH];
        for (int i = 0; i < POINTER_LOCKS_LENGTH; i++) {
            pointerLocks[i] = new Object();
        }
    }
    
    /**
     * Creates and returns a new, minimal DbGraph.
     * The returned graph has exactly one top node and one key node.
     * Nothing is written to the node stream.
     */
    public static DbGraph create(long time) {
        KeyNode root = new KeyNode();
        TopDs topDs = TopDs.createFromFirstRoot(time, root, Spos.DEFAULT_ACCESS_DATA);
        DbGraph g = new DbGraph(topDs);
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
    public static DbGraph createFromStreamNodes(long accessData,
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
        
        DbGraph g = new DbGraph(new TopDs(superRoot));
        return g;
    }
    
    public void setNodeReader(NodeReader nodeReader) {
        if (nodeReader == null) {
            throw new IllegalArgumentException("nodeReader == null not allowed");
        }
        this.nodeReader = nodeReader;
    }
    
    /**
     * Gets one KV value or return null if it does not exist.
     * 
     * @param time  The lookup time.
     */
    public byte[] getOne(long time, long[] keySegments, final GetData gd) {

        if (gd.walker == null) {
            gd.walker = new PointerListener() {
                public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) {
                    switch (pointerType) {
                    case Pointer.TYPE_MEMORY:
                        gd.followMemoryPointerCount++;
                        break;
                    case Pointer.TYPE_STREAM:
                        gd.followStreamPointerCount++;
                        break;
                    default:
                        assert false : "Bad pointer type: " + pointerType + ".";
                    }
                }
            };
        }
        
        if (gd.cachePolicy == null) {
            gd.cachePolicy = new CachePolicy() {
                public boolean shouldCache(INode node) {
                    return true;
                }
            };
        }
        
        KeyNode segmentRoot = topDs.findRoot(this, time, gd);

        if (segmentRoot == null) {
            return null;
        }
        
        INode item;
        KeyNode node;
        final int segmentCount = keySegments.length;
        final int lastIndex = keySegments.length - 1;
        byte[] result = null;

        // For each segment in key segment array
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
                    result = followPointer(current, kwi.pointerIndex, gd.accessData, gd.walker, gd.cachePolicy);
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
                            gd.accessData, gd.walker, gd.cachePolicy);
                    current = nextCurrent;
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
     * Follows a pointer. This method must always be used when a pointer is
     * followed. This is an essential method.
     */
    public final INode followPointer(final INode predecessor, int pointerIndex, 
            long accessData, PointerListener walker, CachePolicy cachePolicy) {
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
                walker.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
            
            } else {
                result = nodeReader.readNode(pointerPos, null);
                
                walker.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_STREAM);
                if (cachePolicy.shouldCache(result)) {
                    predecessor.setPointer(pointerIndex, result, accessData);
                }
            }
        }

        return result;
    }
    
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