package bergdb.core;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import bergdb.dag.Dag.NodeReader;
import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.INode;
import bergdb.dag.KeyNode;
import bergdb.dag.Pointer;
import bergdb.dag.PutData;
import bergdb.dag.Spos;
import bergdb.dag.TopDs;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamException;
import bergdb.storage.StreamFormatException;

/**
 * A function-class, see the public method.
 * 
 * @author Frans Lundberg
 */
public class DagStarter {
    // 140923 kv2 branch - new algorigthm.
    // 140824 Class introduced to keep startup algo separate.
    
    private final KvTransSeq kvTransSeq = new KvTransSeq();
    private long cachedMemoryValue = Db.MIN_CACHE_MEMORY_VALUE;
    private final HashMap<Long, INode> posMap = new HashMap<Long, INode>();  // pos -> node
    private final HashMap<Long, INode> nextMap = new HashMap<Long, INode>(); // posPrevious -> node
    private final List<StoredTrans> transactions;
    private TopNode superRoot;
    private final long accessData;
    private NodeReader nodeReader;
    private int maxNodeSize;
    private KvTransSeq.TransInfo transInfo;
    private Dag dag;
        
    /**
     * Runs the startup algorithms and returns the result from it.
     * 
     * @param transactions  The stored transactions from the startup section of the db stream.
     * @param accessData    The access data for the in-memory pointers that are created.
     */
    public static DagStarter.Result start(List<StoredTrans> transactions, long accessData,
            NodeReader nodeReader, int maxNodeSize) {
        DagStarter dagStarter = new DagStarter(transactions, accessData, nodeReader, maxNodeSize);
        dagStarter.startInner();
        return dagStarter.new Result();
    }
    
    private DagStarter(List<StoredTrans> transactions, long accessData, 
            NodeReader nodeReader, int maxNodeSize) {
        validateTransactions(transactions);
        validateAccessData(accessData);
        if (nodeReader == null) throw new IllegalArgumentException("nodeReader == null not allowed");
        
        this.transactions = transactions;
        this.accessData = accessData;
        this.superRoot = null;
        this.nodeReader = nodeReader;
        this.maxNodeSize = maxNodeSize;
    }
    
    /**
     * Runs the startup algorithm.
     */
    private void startInner() throws StreamException {
        //
        // * Handle first startup.
        // * Find super root, at t = tInit
        // * Change nodes to their state at t = tInit.
        // * Re-run transactions - no add to stream, no stats, but create KvTransSeq.
        // * For kv transactions, call dag.putKv, append to kvTransSeq.
        // * For node transactions, set nodes to not dirty.
        //
        
        // XXX work here!
        
        // TODO A. clean-up this code!        
        
        if (isPrimordialTransaction()) {
            doFirstStartup();
            return;
        }
        
        StoredTrans first = transactions.get(0);
        long tFirst = first.tt;
        long tInit = first.isPrimordial() ? tFirst : tFirst - 1;
            // Time to initialize dag to before re-running transactions.
        if (tInit < 0) {
            throw new StreamFormatException("Unexpected tFirst, " + tFirst);
        }
        
        createMapsAndSearchForSuperRoot();
        refreshStreamPointers();
        createMemoryPointers();
        
        TopDs topDs = new TopDs(superRoot);
        dag = new Dag(nodeReader, topDs, maxNodeSize);
        TopNode superRoot = topDs.findSuperRootAtTime(dag, tInit, dag.newGetData());
        if (superRoot == null) {
            throw new StreamFormatException("No super root at time " + tInit + " was found.");
        }
        
        changeNodesToPreviousState(tInit);
        
        PutData pd = dag.newPutData();
        
        final Dag.PointerListener pListener = pd.pointerListener;
        
        pd.pointerListener = new Dag.PointerListener() {
            public void superRootAccessed(TopNode superRoot) {
                pListener.superRootAccessed(superRoot);
                
                if (!superRoot.isDirty) {
                    superRoot.setDirty(true);
                    transInfo.gotDirtyNodes.add(superRoot);
                }
            }
            
            public void pointerFollowed(INode predecessor, int pointerIndex, INode result, int pointerType) {
                pListener.pointerFollowed(predecessor, pointerIndex, result, pointerType);
                
                if (!result.isDirty() && result.isIndexNode()) {
                    result.setDirty(true);
                    transInfo.gotDirtyNodes.add(result);
                }
            }
        };
        
        
        for (StoredTrans stored : transactions) {
            if (stored.isNodeTransaction()) {
                for (StoredNode n : stored.nodes) {
                    n.getNode().setDirty(false);
                }
            } else {
                // kv transaction assumed
                
                pd.tt = stored.tt;
                transInfo = new KvTransSeq.TransInfo();
                transInfo.tpos = stored.pos;
                transInfo.lastPos = stored.lastPos;
                
                for (StoredNode n : stored.nodes) {
                    INode node = n.getNode();
                    if (node.isIndexNode()) {
                        throw new StreamFormatException("kv transaction with index node: " + node);
                    }
                    
                    int type = node.getType();
                    
                    // DELETES not yet handled
                    if (type == INode.TYPE_VALUE) {
                        long[] key = ((StoredValueNode) n).getKey();
                        assert key != null : "key is null, in startup";
                        assert key.length > 0 : "bad key length " + key.length;
                        byte[] value;
                        
                        if (type == INode.TYPE_VALUE) {
                            ValueNode vNode = (ValueNode) node;
                            value = vNode.getValue();
                        } else if (type == INode.TYPE_DELETE) {
                            value = null;
                        } else {
                            throw new IllegalStateException("Bad type: " + type);
                        }
                        
                        dag.putKv(key, value, pd);
                        
                        pd.clearFast();
                    }
                }
                
                pd.clear();
                
                kvTransSeq.add(transInfo);
            }
        }
        
        //throw new IllegalStateException("STARTUP NOT IMPLEMENTED, " + transactions.size());
        
    }

    private void changeNodesToPreviousState(long tInit) {
        for (Map.Entry<Long, INode> entry : posMap.entrySet()) {
            INode node = entry.getValue();
            if (node.getType() == INode.TYPE_KEY_NODE) {
                KeyNode k = (KeyNode) node;
                k.toPreviousState(tInit);
            }
        }
    }

    private boolean isPrimordialTransaction() {
        return transactions.size() == 1 && transactions.get(0).pos == RecoverableStream.META_BLOCK_SIZE;
    }
    
    private void doFirstStartup() {
        StoredNode[] nodes = transactions.get(0).nodes;
        if (nodes.length != 2) {
            throw new StreamFormatException("expected 2, got " + nodes.length + " nodes.");
        }
        
        INode n0 = nodes[0].getNode();
        INode n1 = nodes[1].getNode();
        
        if (!(n0 instanceof TopNode)) {
            throw new StreamFormatException("Expected TopNode, got " + n0);
        }
        
        if (!(n1 instanceof KeyNode)) {
            throw new StreamFormatException("Expected KeyNode, got " + n1);
        }
        
        superRoot = (TopNode) n0;
        KeyNode keyNode = (KeyNode) n1;
        
        superRoot.setPointer(0, keyNode, AccessData.DEFAULT_ACCESS_DATA);
        
        TopDs topDs = new TopDs(superRoot);
        dag = new Dag(nodeReader, topDs, maxNodeSize);
        
        assert keyNode.isDirty() == false;
        assert superRoot.isDirty() == false;
    }
    
    /**
     * @throws StreamFormatException
     */
    private void validateTransactions(List<StoredTrans> transactions) {
        // This code could be removed, or just called when when asserts enabled if
        // it is determined that it takes significant time to run.
        
        if (transactions == null) {
            throw new StreamFormatException("transactions == null not allowed");
        }
        
        if (transactions.size() == 0) {
            throw new StreamFormatException("zero transactions for startup algorithm");
        }
        
        for (int i = 0; i < transactions.size(); i++) {
            StoredTrans t = transactions.get(i);
            if (t == null) {
                throw new StreamFormatException("null transaction, i = " + i);
            }
            
            if (!Spos.isValid(t.pos)) {
                throw new StreamFormatException("Bad spos of transaction, " + t.toString());
            }
            
            for (StoredNode stored : t.nodes) {
                INode node = stored.getNode();
                if (node == null) {
                    throw new StreamFormatException("getNode() returned null, " + t.toString());
                }
                
                long spos = node.getSpos();
                if (!Spos.isValid(spos)) {
                    throw new StreamFormatException("Bad spos of node, spos=" + spos + ", node: " + node);
                }
            }
        }
    }
    
    private void validateAccessData(long accessData) {
        if (!AccessData.isValid(accessData)) {
            throw new IllegalArgumentException("bad accessData when starting database, " 
                    + accessData + ".");
        }
    }
    
    
    /** 
     * Creates posMap and nextMap and increases cachedMemoryValue. 
     * Also calls the handler for top nodes.
     * 
     * @throws StreamFormatException  If super root cannot be found.
     */
    private void createMapsAndSearchForSuperRoot() {
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
        public Dag getDag() {
            return dag;
        }
        
        public long getCachedMemoryValue() {
            return cachedMemoryValue;
        }

        public KvTransSeq getKvTransSeq() {
            return kvTransSeq;
        }
    }
}
