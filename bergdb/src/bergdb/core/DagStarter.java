package bergdb.core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import bergdb.dag.Dag.NodeReader;
import bergdb.dag.Dag;
import bergdb.dag.INode;
import bergdb.dag.Pointer;
import bergdb.dag.Spos;
import bergdb.dag.TopDs;
import bergdb.dag.TopNode;
import bergdb.dag.TransSeq;
import bergdb.storage.StreamFormatException;

/**
 * An instance of this class is used to create the in-memory data structure
 * of the database given the transactions in the stream startup section.
 * The instance is only used for the restart process and is no longer used
 * once the database has been started.
 * 
 * @author Frans Lundberg
 */
public class DagStarter {
    // 140824 Class introduced in main branch. 
    
    private final TransSeq seq = new TransSeq();
    private long cachedMemoryValue = Db.MIN_CACHE_MEMORY_VALUE;
    final HashMap<Long, INode> posMap = new HashMap<Long, INode>();  // pos -> node
    final HashMap<Long, INode> nextMap = new HashMap<Long, INode>(); // posPrevious -> node
    private final List<StoredTrans> transactions;
    private TopNode superRoot;
    private TopDs topDs;
    private final long accessData;
    private final NodeReader nodeReader;
    private final int maxNodeSize;
    private Dag dag;
    
    /**
     * Creates a new object.
     * 
     * @param transactions  The stored transactions from the startup interval of the db stream.
     * @param accessData    The access data for the in-memory pointers that are created.
     */
    private DagStarter(List<StoredTrans> transactions, long accessData, 
            NodeReader nodeReader, int maxNodeSize) {
        
        if (transactions == null) {
            throw new IllegalArgumentException("transactions == null not allowed");
        }
        
        if (nodeReader == null) {
            throw new IllegalArgumentException("nodeReader == null not allowed");
        }
        
        if (maxNodeSize < 1) {
            throw new IllegalArgumentException("bad maxNodeSize " + maxNodeSize);
        }
        
        this.transactions = transactions;
        this.accessData = accessData;
        this.nodeReader = nodeReader;
        this.maxNodeSize = maxNodeSize;
        this.superRoot = null;
    }
    
    /**
     * Runs the startup algorithms; the result is available from
     * getDag(), getCachedMemoryValue().
     */
    public static DagStarter start(List<StoredTrans> transactions, long accessData, 
            NodeReader nodeReader, int maxNodeSize) {
        DagStarter dagStarter = new DagStarter(transactions, accessData, nodeReader, maxNodeSize);
        dagStarter.startInternal();
        return dagStarter;
    }
    
    /**
     * Runs the startup algorithm.
     */
    public void startInternal() {
        createTransSeq();
        createMaps();
        refreshStreamPointers();
        createMemoryPointers();
        
        this.topDs = new TopDs(superRoot);
        this.dag = new Dag(nodeReader, topDs, seq, maxNodeSize);
    }
    
    public long getCachedMemoryValue() {
        return cachedMemoryValue;
    }
    
    public Dag getDag() {
        return dag;
    }
    
    /**
     * Creates seq (the TransSeq).
     */
    private void createTransSeq() {
        for (StoredTrans trans : transactions) {
            ArrayList<INode> tnodes = new ArrayList<INode>();
            
            for (StoredNode storedNode : trans.nodes) {
                INode node = storedNode.getNode();
                
                if (node.isIndexNode()) {
                    tnodes.add(node);
                }
            }
            
            INode[] nodeArray = new INode[tnodes.size()];
            tnodes.toArray(nodeArray);
            seq.add(new TransSeq.Tset(nodeArray, trans.pos, trans.lastPos));
        }
    }
    
    /** 
     * Creates posMap and nextMap and increases cachedMemoryValue. 
     * Also calls the handler callback for top nodes.
     */
    private void createMaps() {
        for (StoredTrans trans : transactions) {
            for (StoredNode storedNode : trans.nodes) {
                INode node = storedNode.getNode();
                long spos = node.getSpos();
                
                assert Spos.isValid(spos) : "spos: " + spos;
                assert posMap.get(spos) == null 
                        : "posMap already has node for spos " + spos + ": " + posMap.get(spos);
                
                posMap.put(node.getSpos(), node);
                
                long prev = storedNode.getPrevPos();
                if (prev != Spos.NULL) {
                    nextMap.put(prev, node);
                }

                this.cachedMemoryValue += node.getMemSize();
                
                if (node.getType() == INode.TYPE_TOP_NODE) {
                    handleTopNode((TopNode) node);
                }
            }
        }
    }
    
    private void handleTopNode(TopNode potentialSuperRoot) {                
        if (superRoot == null) {
            superRoot = potentialSuperRoot;
        } else if (potentialSuperRoot.topNodeId > superRoot.topNodeId) {
            superRoot = potentialSuperRoot;
        } else if (potentialSuperRoot.topNodeId == superRoot.topNodeId) {
            if (potentialSuperRoot.getSpos() > superRoot.getSpos()) {
                superRoot = potentialSuperRoot;
            }
        }
    }
    
    /** 
     * Refreshes stream pointers and calls topNodeHandler callback.
     */
    private void refreshStreamPointers() {
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
        }

        if (superRoot == null) {
            throw new StreamFormatException("Could not find super root node within startup node set.");
        }
    }
    
    /**
     * Creates memory pointers from stream pointers.
     */
    private void createMemoryPointers() {
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
    }
}
