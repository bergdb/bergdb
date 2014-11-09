package bergdb.core;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import bergdb.dag.Dag.NodeReader;
import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.INode;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Pointer;
import bergdb.dag.Spos;
import bergdb.dag.TopDs;
import bergdb.dag.TopNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamException;
import bergdb.storage.StreamFormatException;

// TODO D. S104, 328 -> -1, too few mem pointers are created. Rethink node.pos backtrack!

/**
 * A function-class, see the single public method.
 * 
 * @author Frans Lundberg
 */
public class DbStarter2 {
    //
    // DbStarter2 -- focus on state at t = startupTime directly (instead of latest state first).
    // Status 141109. Tests: unit:2,f:2. Mem pointer creation has issues. Backtrack does not 
    // work properly. Lots of backtrack to -1... not correct.
    //
    // This implementation is not optimized for CPU performance. Clean code takes precedence.
    // Startup is not that performance-sensitive and its likely I/O bound anyway.
    //
    
    private final KvTransSeq kvTransSeq = new KvTransSeq();
    private long cachedMemoryValue = Db.MIN_CACHE_MEMORY_VALUE;
    private final HashMap<Long, INode> posMap = new HashMap<Long, INode>();  // pos -> node
    private final HashMap<Long, INode> posMap2 = new HashMap<Long, INode>();  // pos -> node
    private final HashMap<Long, INode> nextMap = new HashMap<Long, INode>(); // prev pos -> node
    private final PrevMap prevMap = new PrevMap();   // pos -> prev pos
    private final Db db;
    private final List<StoredTrans> transactions;
    private final StoredTrans firstTrans;
    private TopNode superRoot;
    private final long accessData;
    private NodeReader nodeReader;
    private int maxNodeSize;
    private Dag dag;
    private final long startupPos;
    private final long startupTime;
    
    /**
     * Runs the startup algorithms and returns the result from it.
     * 
     * @param transactions  The stored transactions from the startup section of the db stream.
     * @param accessData    The access data for the in-memory pointers that are created.
     */
    public static DbStarter2.Result start(Db db, List<StoredTrans> transactions, long accessData,
            NodeReader nodeReader, int maxNodeSize) {
        DbStarter2 s = new DbStarter2(db, transactions, accessData, nodeReader, maxNodeSize);
        s.start();
        return s.new Result();
    }
    
    private DbStarter2(Db db, List<StoredTrans> transactions, long accessData, 
            NodeReader nodeReader, int maxNodeSize) {
        if (nodeReader == null) throw new IllegalArgumentException("nodeReader == null not allowed");
        if (transactions == null) throw new IllegalArgumentException("transactions == null not allowed");
        if (transactions.size() == 0) throw new IllegalArgumentException("transactions.size() == 0");
        
        this.db = db;
        this.transactions = transactions;
        this.firstTrans = transactions.get(0);
        this.accessData = accessData;
        this.superRoot = null;
        this.nodeReader = nodeReader;
        this.maxNodeSize = maxNodeSize;
        this.startupPos = firstTrans.tpos;
        this.startupTime = firstTrans.tt;
    }
    
    /**
     * Runs the startup algorithm.
     */
    private void start() throws StreamException {
        
        // TODO B. Is KeyNode.getId() ok after rerun?
        
        //if (startupPos > RecoverableStream.META_BLOCK_SIZE) {
        //    System.out.println("startupPos: " + startupPos + ", startupTime: " + startupTime);
        //}
        
        db.internal().setKvTransSeq(kvTransSeq);
        
        validateTransactions(transactions, 0);
        validateAccessData(accessData);
        
        if (isPrimordialTransaction()) {
            doFirstStartup();
            return;
        }
        
        createMaps();
        increaseCachedMemoryValue();
        findSuperRoot();
        
        changeKeyNodesToPreviousState();
        checkKeyNodeStreamPointers();
        
        updateStreamPointers();
        updateNodePos();
        
        createPosMap2();
        createMemoryPointers();
        checkKeyNodeStreamPointers();
        
        createDag();
        db.internal().createPutAndGetData();
        
        rerunTransactions();
    }
    
    private void createPosMap2() {
        for (Map.Entry<Long, INode> entry : posMap.entrySet()) {
            INode node = entry.getValue();
            long pos = node.getSpos();
            
            if (!Spos.isNull(pos)) {
                posMap2.put(pos, node);
            }
        }
        
        
        for (INode node : posMap.values()) {
            long pos = node.getSpos();
            if (!Spos.isNull(pos)) {
                posMap2.put(pos, node);
            }
        }
    }

    /**
     * Checks that there are no stream pointers of KeyNodes that
     * are equal to Spos.NULL.
     */
    private void checkKeyNodeStreamPointers() {
        for (INode node : posMap2.values()) {
            if (node.isKeyNode()) {
                KeyNode k = (KeyNode) node;
                
                for (int i = 0; i < k.size; i++) {
                    long klong = k.klongs[i];
                    if (Klong.isKey(klong)) {
                        long pos = node.getSpos();
                        if (pos == Spos.NULL) {
                            throw new StreamFormatException("Unexpected stream pointer, was " 
                                    + pos + ", index " + i + ", node: " + node);
                        }
                    }
                }
            }
        }
    }

    private void findSuperRoot() {
        StoredTopNode first = null;   // first top node in startup section
        
        LabelA: 
        for (StoredTrans trans : transactions) {
            for (StoredNode storedNode : trans.nodes) {
                INode node = storedNode.getNode();
                
                if (node.isTopNode()) {
                    first = (StoredTopNode) storedNode;
                    break LabelA;
                }
            }
        }
        
        if (first == null) {
            throw new StreamFormatException("No top node in startup interval, startupPos: " + startupPos);
        }
        
        TopDs topDs = new TopDs(first.getNode());
        Dag myDag = new Dag(nodeReader, topDs, maxNodeSize);
        
        superRoot = topDs.findSuperRootAtTime(myDag, startupTime, myDag.newGetData());
        if (superRoot == null) {
            throw new StreamFormatException("No super root at time " + startupTime + " was found.");
        }
    }
    
    private void rerunTransactions() {
        // Reruns transactions, except the first one.
        
        int count = transactions.size();
        
        for (int i = 0; i < count; i++) {
            StoredTrans trans = transactions.get(i);
            if (i > 0) {
                db.internal().executeInner(trans.createRerunTransaction());
            }
            
            for (StoredNode stored : trans.nodes) {
                INode n = stored.getNode();
                if (n.isIndexNode()) {
                    n.setDirty(false);
                }
            }
        }
    }

    private void createDag() {
        TopDs topDs = new TopDs(superRoot);
        dag = new Dag(nodeReader, topDs, maxNodeSize);
        db.internal().setDag(dag);
    }

    /**
     * Changes key nodes to state at t = startupTime.
     */
    private void changeKeyNodesToPreviousState() {
        // Note, we do get k.size == 0 cases.
        
        for (StoredTrans trans : transactions) {
            for (StoredNode stored : trans.nodes) {
                INode node = stored.getNode();
                if (node.getType() == INode.TYPE_KEY_NODE) {
                    KeyNode k = (KeyNode) node;
                    k.toPreviousState(startupTime);
                }
            }
        }
    }

    private boolean isPrimordialTransaction() {
        return transactions.size() == 1 && transactions.get(0).tpos == RecoverableStream.META_BLOCK_SIZE;
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
     * Validates stream transactions, pointers for time > startupTime are allowed 
     * to be Spos.NULL.
     * 
     * @throws StreamFormatException 
     *      If a transaction does not follow the db stream format. This should only happen
     *      if the db stream was tampered with.
     */
    private void validateTransactions(List<StoredTrans> transactions, long startupTime) {
        // NOTE t.version --- stream format version. We should check that this
        // software supports the version of the transactions in the stream.
        
        if (transactions.size() == 0) {
            throw new StreamFormatException("No transactions for startup algorithm.");
        }
        
        long tpos = -1;
        long tt = -1;
        
        for (int i = 0; i < transactions.size(); i++) {
            StoredTrans t = transactions.get(i);
            
            if (t == null) {
                throw new StreamFormatException("null transaction, i = " + i);
            }
            
            if (t.tpos < RecoverableStream.META_BLOCK_SIZE) {
                throw new StreamFormatException("Bad spos of transaction, " + t.toString());
            }
            
            if (t.tpos <= tpos) {
                throw new StreamFormatException("non-increasing tpos, " + t.toString());
            }
            
            if (t.tt <= tt) {
                throw new StreamFormatException("non-increasing tt, " + t.toString());
            }
            
            for (StoredNode stored : t.nodes) {
                validateNode(stored, startupTime);
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
            break;
            
        }
    }
    
    private void validateAccessData(long accessData) {
        if (!AccessData.isValid(accessData)) {
            throw new IllegalArgumentException("bad accessData when starting database, " 
                    + accessData + ".");
        }
    }
    
    
    /** 
     * Creates posMap, nextMap, prevMap.
     */
    private void createMaps() {
        int transCount = transactions.size();
        
        for (int i = 0; i < transCount; i++) {
            StoredTrans trans = transactions.get(i);
            
            for (StoredNode storedNode : trans.nodes) {
                INode node = storedNode.getNode();
                long spos = node.getSpos();
                long prevPos = storedNode.getPrevPos();
                
                posMap.put(spos, node);
                
                prevMap.put(spos, prevPos);
                
                if (prevPos != Spos.NULL) {
                    nextMap.put(prevPos, node);
                }
            }
        }
    }
    
    private void increaseCachedMemoryValue() {
        for (StoredTrans trans : transactions) {
            for (StoredNode storedNode : trans.nodes) {
                this.cachedMemoryValue += storedNode.getNode().getMemSize();
            }
        }
    }
    
    /** 
     * Updates stream pointers "backwards" so pointer.pos <= firstTrans.lastPos.
     */
    private void updateStreamPointers() {
        Pointer p = new Pointer();
        
        for (Map.Entry<Long, INode> entry : posMap.entrySet()) {
            INode node = entry.getValue();

            int pointerCount = node.getPointerCount();
            for (int i = 0; i < pointerCount; i++) {
                node.getPointer(i, p);
                if (p.isNull()) {
                    continue;
                }

                long pos = p.getPos();
                long newPos = prevMap.backtrack(firstTrans.lastPos, pos);
                node.setPointer(i, null, newPos);
            }
        }
    }
    
    
    /** 
     * Updates node positions so node.getPos() <= firstTrans.lastSpos.
     */
    private void updateNodePos() {
        for (Map.Entry<Long, INode> entry : posMap.entrySet()) {
            INode node = entry.getValue();
            long pos = node.getSpos();
            long newPos = prevMap.backtrack(firstTrans.lastPos, pos);
            node.setSpos(newPos);
        }
    }
    
    /**
     * Creates memory pointers from stream pointers when possible.
     */
    private void createMemoryPointers() {
        Pointer p = new Pointer();

        for (INode node : posMap2.values()) {
            int pointerCount = node.getPointerCount();
            for (int i = 0; i < pointerCount; i++) {
                node.getPointer(i, p);
                if (p.isNull()) {
                    continue;
                }

                INode pointee = posMap2.get(p.pos);
                if (pointee != null) {
                    node.setPointer(i, pointee, accessData);
                    
                    //System.out.println("*** mem pointer created: " + node + " ==> " + pointee);
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
    
    /**
     * Pos-to-prevPos map.
     */
    private static class PrevMap {
        private HashMap<Long, Long> map = new HashMap<Long, Long>();
        
        void put(long pos, long previousPos) {
            if (!Spos.isValid(pos)) {
                throw new IllegalArgumentException("bad pos: " + pos);
            }
            
            if (!Spos.isValidOrNull(previousPos)) {
                throw new IllegalArgumentException("bad previousPos: " + previousPos);
            }
            
            if (!(previousPos < pos)) {
                throw new IllegalArgumentException("previousPos not less than pos, " + previousPos + ", " + pos);
            }
            
            map.put(pos, previousPos);
        }
        
        long backtrack(long limit, long pos) {
            while (pos > limit) {
                Long posLong = map.get(pos);
                
                if (posLong == null) {
                    pos = Spos.NULL;
                    break;
                } else {
                    pos = posLong;
                }
            }
            
            return pos;
        }
    }
    
    // ======== Tests ========
    
    @T
    private static void testPrevMap1() {
        PrevMap m = new PrevMap();
        m.put(40, 30);
        m.put(30, 20);
        m.put(20, 10);
        
        Assert.assertEquals(20, m.backtrack(25, 40));
        Assert.assertEquals(10, m.backtrack(15, 40));
    }
    
    @T
    private static void testPrevMap2() {
        PrevMap m = new PrevMap();
        m.put(40, 30);
        m.put(30, 20);
        m.put(20, 10);
        
        Assert.assertEquals(Spos.NULL, m.backtrack(0, 40));
        Assert.assertEquals(40, m.backtrack(40, 40));
    }
    
    @T
    private static void testPrevMap3() {
        IllegalArgumentException ex = null;
        PrevMap m = new PrevMap();
        
        try {
            m.put(100, 200);
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    @T
    private static void testEmptyPrevMap() {
        PrevMap m = new PrevMap();
        Assert.assertEquals(Spos.NULL, m.backtrack(10, 40));
    }
}
