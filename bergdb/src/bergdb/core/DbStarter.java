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
import bergdb.dag.Spos;
import bergdb.dag.TopDs;
import bergdb.dag.TopNode;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamException;
import bergdb.storage.StreamFormatException;

/**
 * A function-class, see the single public method.
 * 
 * @author Frans Lundberg
 */
public class DbStarter {
    private final KvTransSeq kvTransSeq = new KvTransSeq();
    private long cachedMemoryValue = Db.MIN_CACHE_MEMORY_VALUE;
    private final HashMap<Long, INode> posMap = new HashMap<Long, INode>();  // pos -> node
    private final HashMap<Long, INode> nextMap = new HashMap<Long, INode>(); // posPrevious -> node
    private final Db db;
    private final List<StoredTrans> transactions;
    private TopNode superRoot;
    private final long accessData;
    private NodeReader nodeReader;
    private int maxNodeSize;
    private Dag dag;
        
    /**
     * Runs the startup algorithms and returns the result from it.
     * 
     * @param transactions  The stored transactions from the startup section of the db stream.
     * @param accessData    The access data for the in-memory pointers that are created.
     */
    public static DbStarter.Result start(Db db, List<StoredTrans> transactions, long accessData,
            NodeReader nodeReader, int maxNodeSize) {
        DbStarter s = new DbStarter(db, transactions, accessData, nodeReader, maxNodeSize);
        s.start();
        return s.new Result();
    }
    
    private DbStarter(Db db, List<StoredTrans> transactions, long accessData, 
            NodeReader nodeReader, int maxNodeSize) {
        if (nodeReader == null) throw new IllegalArgumentException("nodeReader == null not allowed");
        
        this.db = db;
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
        
        db.internal().setKvTransSeq(kvTransSeq);
        
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
        
        db.internal().createPutAndGetData();
        rerunTransactions();
    }
    
    private void rerunTransactions() {
        // Rerun transactions.
        // For an index transaction, just set nodes to dirty.
        // For a kv transaction, rerun corresponding transaction.
        
        for (StoredTrans stored : transactions) {            
            if (stored.isIndexTransaction()) {
                for (StoredNode n : stored.nodes) {
                    n.getNode().setDirty(false);
                }
            } else {
                Trans t = stored.createRerunTransaction();
                db.internal().executeInner(t);
            }
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

    private void createDag(long initTime) {
        TopDs topDs = new TopDs(superRoot);
        dag = new Dag(nodeReader, topDs, maxNodeSize);
        db.internal().setDag(dag);
        
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
        db.internal().setDag(dag);
        
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
        
        if (transactions.size() == 0) {
            throw new StreamFormatException("No transactions for startup algorithm.");
        }
        
        for (int i = 0; i < transactions.size(); i++) {
            StoredTrans t = transactions.get(i);
            
            if (t == null) {
                throw new StreamFormatException("null transaction, i = " + i);
            }
            
            // NOTE t.version --- stream format version? Check?
            
            if (t.pos < RecoverableStream.META_BLOCK_SIZE) {
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
}
