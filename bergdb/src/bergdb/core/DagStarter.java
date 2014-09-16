package bergdb.core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import bergdb.dag.Dag.NodeReader;
import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.INode;
import bergdb.dag.Pointer;
import bergdb.dag.Spos;
import bergdb.dag.TopDs;
import bergdb.dag.TopNode;
import bergdb.dag.TransSeq;
import bergdb.storage.StreamFormatException;

/**
 * A function-class, see the one public method.
 * 
 * @see #start(List, long, NodeReader, int)
 * @author Frans Lundberg
 */
public class DagStarter {
    // 140824 Class introduced to keep startup algo separate.
    
    private final TransSeq transSeq = new TransSeq();
    private long cachedMemoryValue = Db.MIN_CACHE_MEMORY_VALUE;
    private final HashMap<Long, INode> posMap = new HashMap<Long, INode>();  // pos -> node
    private final HashMap<Long, INode> nextMap = new HashMap<Long, INode>(); // posPrevious -> node
    private final List<StoredTrans> transactions;
    private TopNode superRoot;
    private final long accessData;
    
    /**
     * Runs the startup algorithms and returns the result from it.
     * 
     * @param transactions  The stored transactions from the startup interval of the db stream.
     * @param accessData    The access data for the in-memory pointers that are created.
     */
    public static DagStarter.Result start(List<StoredTrans> transactions, long accessData) {
        DagStarter dagStarter = new DagStarter(transactions, accessData);
        dagStarter.startInternal();
        return dagStarter.new Result();
    }
    
    private DagStarter(List<StoredTrans> transactions, long accessData) {
        validateTransactions(transactions);
        validateAccessData(accessData);
        this.transactions = transactions;
        this.accessData = accessData;
        this.superRoot = null;
    }
    
    private void validateTransactions(List<StoredTrans> transactions) {
        // This code could be removed, or just called when when asserts enabled if
        // it is determined that it takes significant time to run.
        
        if (transactions == null) {
            throw new IllegalArgumentException("transactions == null not allowed");
        }
        
        for (int i = 0; i < transactions.size(); i++) {
            StoredTrans t = transactions.get(i);
            if (t == null) {
                throw new IllegalArgumentException("null transaction, i = " + i);
            }
            
            if (!Spos.isValid(t.pos)) {
                throw new IllegalArgumentException("Bad spos of transaction, " + t.toString());
            }
            
            for (StoredNode stored : t.nodes) {
                INode node = stored.getNode();
                if (node == null) {
                    throw new IllegalArgumentException("getNode() returned null, " + t.toString());
                }
                
                long spos = node.getSpos();
                if (!Spos.isValid(spos)) {
                    throw new IllegalArgumentException("Bad spos of node, spos=" + spos + ", node: " + node);
                }
            }
        }
    }
    
    private void validateAccessData(long accessData) {
        if (!AccessData.isValid(accessData)) {
            throw new IllegalArgumentException("bad accessData when starting database, " + accessData + ".");
        }
    }
    
    /**
     * Runs the startup algorithm.
     */
    private void startInternal() {
        createTransSeq();
        createMaps();
        refreshStreamPointers();
        createMemoryPointers();
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
            transSeq.add(new TransSeq.Tset(nodeArray, trans.pos, trans.lastPos));
        }
    }
    
    /** 
     * Creates posMap and nextMap and increases cachedMemoryValue. 
     * Also calls the handler for top nodes.
     */
    private void createMaps() {
        for (StoredTrans trans : transactions) {
            for (StoredNode storedNode : trans.nodes) {
                INode node = storedNode.getNode();
                long spos = node.getSpos();
                
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
        
        if (superRoot == null) {
            throw new StreamFormatException("Could not find super root node within startup node set.");
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
     * Refreshes stream pointers.
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
    
    /**
     * The result of starting the Dag.
     */
    public class Result {
        public Dag createDag(NodeReader nodeReader, int maxNodeSize) {
            if (nodeReader == null) {
                throw new IllegalArgumentException("nodeReader == null not allowed");
            }
            
            if (maxNodeSize < 1) {
                throw new IllegalArgumentException("bad maxNodeSize " + maxNodeSize);
            }
            
            TopDs topDs = new TopDs(superRoot);
            return new Dag(nodeReader, topDs, maxNodeSize);
        }
        
        public TransSeq getTransSeq() {
            return transSeq;
        }
        
        public long getCachedMemoryValue() {
            return cachedMemoryValue;
        }
        
    }
}
