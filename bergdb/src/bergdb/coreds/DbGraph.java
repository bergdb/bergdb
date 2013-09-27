package bergdb.coreds;

import java.util.HashMap;
import java.util.Map;

import bergdb.storage.StreamFormatException;

/**
 * The DB Graph is the core data structure of the database.
 * 
 * @author Frans Lundberg
 */
public class DbGraph {
    public interface DbForMe {
        public INode followPointer(INode predecessor, int pointerIndex, 
                boolean cache, long accessData, GetData gd);
    }
    
    private static class DummyDb implements DbForMe {
        public INode followPointer(INode predecessor, int pointerIndex,
                boolean cache, long accessData, GetData gd) {
            INode result;
            assert predecessor != null;
            assert gd != null : "gd == null, not allowed";

            //final Object lock = getPointerLock(predecessor, pointerIndex);
            final Object lock = new Object();
            
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
                    gd.followMemoryPointerCount++;
                } else {
                    throw new IllegalStateException("No support for reading from stream.");
                    /*
                    result = nodeStream.readNode(pointerPos, null);
                    if (cache) {
                        predecessor.setPointer(pointerIndex, result, accessData);
                        cachedMemoryValue.addAndGet(result.getMemSize());
                    }
                    
                    gd.followStreamPointerCount++;
                    */
                }
            }

            return result;
        }
        
    }
    
    private TopDs topDs;
    private DbForMe db;
    
    
    /**
     * Private constructor; see the create methods for how to create
     * a DbGraph object.
     */
    private DbGraph() {
        db = new DummyDb();
    }
    
    /**
     * Creates and returns a new, minimal DbGraph.
     * The returned graph has exactly one top node and one key node.
     * Nothing is written to the node stream.
     */
    public static DbGraph create(long time) {
        DbGraph g = new DbGraph();
        KeyNode root = new KeyNode();
        g.topDs = TopDs.createFromFirstRoot(time, root, Spos.DEFAULT_ACCESS_DATA);
        return g;
    }
    
    /**
     * Creates a DbGraph from stream nodes.
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

        DbGraph g = new DbGraph();
        
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

        g.topDs = new TopDs(superRoot);

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
        
        return g;
    }
    
    public void setDb(DbForMe db) {
        this.db = db;
    }
    
    /**
     * Gets one KV value or return null if it does not exist.
     * 
     * @param time  The lookup time.
     */
    public byte[] getOne(long time, long[] keySegments, GetData gd) {
        KeyNode segmentRoot = topDs.findRootNEW(db, time, null, gd);

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
            item = getEqNodeInSegment(time, segmentRoot, keySegments[i], gd, null);

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
            GetData gd, Choices choices) {
        final KlongWithPointer kwi = gd.kwi;
        KeyNode current = segmentRoot;
        INode result;

        while (true) {
            if (current.isSegmentLeaf()) {
                current.searchEq(time, compareValue, kwi);

                if (kwi.klong == Klong.NULL) {
                    result = null;
                } else {
                    if (choices != null) choices.add(kwi.pointerIndex);
                    result = db.followPointer(current, kwi.pointerIndex, gd.cache, gd.accessData, gd);
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

                    if (choices != null) choices.add(kwi.pointerIndex);
                    KeyNode nextCurrent = (KeyNode) db.followPointer(current, kwi.pointerIndex,
                            gd.cache, gd.accessData, gd);
                    current = nextCurrent;
                    gd.nodeDepth++;
                }
            }
        }

        return result;
    }
}

/*

Maybe a builder?


*/