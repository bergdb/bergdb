package bergdb.core;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import bergdb.dag.Dag.NodeChangeListener;
import bergdb.dag.Dag.NodeReader;
import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.INode;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
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
 * A function-class, see the single public method.
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
    private SetSposNodeChangeListener setSposListener;
        
    /**
     * Runs the startup algorithms and returns the result from it.
     * 
     * @param transactions  The stored transactions from the startup section of the db stream.
     * @param accessData    The access data for the in-memory pointers that are created.
     */
    public static DagStarter.Result start(List<StoredTrans> transactions, long accessData,
            NodeReader nodeReader, int maxNodeSize) {
        DagStarter dagStarter = new DagStarter(transactions, accessData, nodeReader, maxNodeSize);
        dagStarter.start();
        return dagStarter.new Result();
    }
    
    private DagStarter(List<StoredTrans> transactions, long accessData, 
            NodeReader nodeReader, int maxNodeSize) {
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
    private void start() throws StreamException {
        validateTransactions(transactions, 0);
        validateAccessData(accessData);
        
        if (isPrimordialTransaction()) {
            doFirstStartup();
            return;
        }
        
        createMapsAndSearchForSuperRoot();
        refreshStreamPointers();
        createMemoryPointers();
        
        long initTime = computeInitTime();
        validateTransactions(transactions, initTime);
        createDag(initTime);
        changeNodesToPreviousState(initTime);
        
        PutData pd = createPutData();
        rerunTransactions(pd);
    }

    private void rerunTransactions(PutData pd) {
        for (StoredTrans stored : transactions) {            
            if (stored.isNodeTransaction()) {
                for (StoredNode n : stored.nodes) {
                    n.getNode().setDirty(false);
                }
            } else {
                // kv transaction
               
                pd.tt = stored.tt;
                transInfo = new KvTransSeq.TransInfo();
                transInfo.tpos = stored.pos;
                transInfo.lastPos = stored.lastPos;
                transInfo.tt = stored.tt;
                
                for (StoredNode n : stored.nodes) {
                    putRerunKv(pd, n);
                }
                
                pd.clear();
                
                kvTransSeq.add(transInfo);
            }
        }
    }

    private void putRerunKv(PutData pd, StoredNode n) {
        
        
        INode node = n.getNode();
        if (node.isIndexNode()) {
            throw new StreamFormatException("kv transaction with index node: " + node);
        }
        
        int type = node.getType();
        
        if (type == INode.TYPE_VALUE || type == INode.TYPE_DELETE) {
            long[] key = ((StoredValueNode) n).getKey();
            assert key != null : "key is null, in startup";
            assert key.length > 0 : "bad key length " + key.length;
            byte[] value;
            
            ValueNode vNode;
            
            if (type == INode.TYPE_VALUE) {
                vNode = (ValueNode) node;
                value = vNode.getValue();
            } else if (type == INode.TYPE_DELETE) {
                vNode = (ValueNode) node;
                value = null;
            } else {
                throw new IllegalStateException("Bad type: " + type);
            }
            
            setSposListener.setSpos(vNode.getSpos());
            
            assert pd.kwi.klong == Klong.NULL : "db.kwi.klong not Klong.NULL";
            
            dag.putKv(key, value, pd);
            
            pd.clearFast();
        }
    }

    private long computeInitTime() {
        StoredTrans first = transactions.get(0);
        long tFirst = first.tt;
        long tInit = first.isPrimordial() ? tFirst : tFirst - 1;
            // Time to initialize dag to before re-running transactions.
        if (tInit < 0) {
            throw new StreamFormatException("Unexpected tFirst, " + tFirst);
        }
        return tInit;
    }

    private PutData createPutData() {
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
        
        setSposListener = new SetSposNodeChangeListener();
        pd.nodeChangeListener = setSposListener;
        return pd;
    }

    private void createDag(long initTime) {
        TopDs topDs = new TopDs(superRoot);
        dag = new Dag(nodeReader, topDs, maxNodeSize);
        TopNode superRoot = topDs.findSuperRootAtTime(dag, initTime, dag.newGetData());
        if (superRoot == null) {
            throw new StreamFormatException("No super root at time " + initTime + " was found.");
        }
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
     * Validates stream transactions, pointers for time > initTime are allowed 
     * to be NULL (-1).
     * 
     * @throws StreamFormatException 
     *      If a transaction does not follow the db stream format. This should only happen
     *      if the db stream was tampered with.
     */
    private void validateTransactions(List<StoredTrans> transactions, long initTime) {
        
        /*System.out.println("==== Startup transactions:");
        for (StoredTrans s : transactions) {
            System.out.println("stored trans: " + s);
            for (StoredNode n : s.nodes) {
                System.out.println("  " + n);
            }
        }*/
        
        if (transactions.size() == 0) {
            throw new StreamFormatException("No transactions for startup algorithm.");
        }
        
        for (int i = 0; i < transactions.size(); i++) {
            StoredTrans t = transactions.get(i);
            
            if (t == null) {
                throw new StreamFormatException("null transaction, i = " + i);
            }
            
            // t.version --- stream format version? Check?
            
            if (!Spos.isValid(t.pos)) {
                throw new StreamFormatException("Bad spos of transaction, " + t.toString());
            }
            
            for (StoredNode stored : t.nodes) {
                validateNode(stored, initTime);
            }
        }
    }

    private void validateNode(StoredNode stored, long initTime) {
        INode node = stored.getNode();
        if (node == null) {
            throw new StreamFormatException("getNode() returned null");
        }
        
        long spos = node.getSpos();
        if (!Spos.isValid(spos)) {
            throw new StreamFormatException("Bad spos of node, spos=" + spos + ", node: " + node);
        }
        
        switch (node.getType()) {
        case INode.TYPE_KEY_NODE:
            KeyNode knode = (KeyNode) node;
            knode.validateStreamNode(initTime);
            break;
        case INode.TYPE_TOP_NODE:
            
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
    
    private static class SetSposNodeChangeListener implements NodeChangeListener {
        private long spos;
        
        void setSpos(long spos) {
            this.spos = spos;
        }

        public void newTopNode(TopNode node) {
            // nothing
        }

        public void keyNodeChanged(KeyNode node) {
            // nothing
        }

        public void newValueNode(ValueNode node, long[] key) {
            node.setSpos(spos);   
        }
    }
}
