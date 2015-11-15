package bergdb.core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import bergdb.common.Util;
import bergdb.core.Db.ExecuteData;
import bergdb.core.StoredTrans.Parser;
import bergdb.core.StoredTrans.Serializer;
import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.NodeVisitor;
import bergdb.dag.Pointer;
import bergdb.dag.PointerFollower;
import bergdb.dag.Spos;
import bergdb.dag.TopDs;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;

/**
 * A function-class for the database startup algorithm; see start().
 * 
 * @author Frans Lundberg
 */
public class DbStarter {
    //
    // This implementation is not optimized for CPU performance. Clean code takes precedence.
    // Startup is not that performance-sensitive and it is likely I/O bound.
    //
    
    private final TransSeq transSeq = new TransSeq();
    private final HashMap<Long, StoredNode> posMap = new HashMap<Long, StoredNode>();
    private final HashMap<Long, Node> posMap2 = new HashMap<Long, Node>();
    private final NextMap nextMap = new NextMap();
    private final Db db;
    private final List<StoredTrans> transactions;
    private final StoredTrans firstTrans;
    private TopNode superRoot;
    private final long accessData;
    private PointerFollower pointerFollower;
    private int maxNodeSize;
    private Dag dag;
    private final long startupPos;
    private final long startupTime;
    
    
    private DbStarter(Db db, List<StoredTrans> transactions, long accessData, 
            PointerFollower pointerFollower, int maxNodeSize) {
        if (pointerFollower == null) throw new IllegalArgumentException("pointerFollower == null not allowed");
        if (transactions == null) throw new IllegalArgumentException("transactions == null not allowed");
        if (transactions.size() == 0) throw new IllegalArgumentException("transactions.size() == 0");
        
        this.db = db;
        this.transactions = transactions;
        this.firstTrans = transactions.get(0);
        this.accessData = accessData;
        this.superRoot = null;
        this.pointerFollower = pointerFollower;
        this.maxNodeSize = maxNodeSize;
        this.startupPos = firstTrans.tpos;
        this.startupTime = firstTrans.tt;
    }
    
    /**
     * Runs the startup algorithm.
     * 
     * @param transactions  The stored transactions from the startup section of the db stream.
     * @param accessData    The access data for the in-memory pointers that are created.
     */
    public static void start(Db db, List<StoredTrans> transactions, long accessData,
            PointerFollower pointerFollower, int maxNodeSize) {
        DbStarter s = new DbStarter(db, transactions, accessData, pointerFollower, maxNodeSize);
        s.startup();
    }
    
    /**
     * Runs the startup algorithm.
     * 
     * @throws StreamFormatException
     */
    private void startup() {
        validateTransactions(transactions, startupTime);
        validateAccessData(accessData);
        
        if (isPrimordialTransaction()) {
            doPrimordialStartup();
        } else {
            doOrdinaryStartup();
        }
    }

    private void doPrimordialStartup() {
        StoredNode[] nodes = transactions.get(0).nodes;
        checkPrimordialTransaction(nodes);
        
        Node n0 = nodes[0].getNode();
        Node n1 = nodes[1].getNode();
        
        superRoot = (TopNode) n0;
        KeyNode keyNode = (KeyNode) n1;
        
        superRoot.setPointer(0, keyNode, AccessData.DEFAULT_ACCESS_DATA);
        
        TopDs topDs = new TopDs(superRoot);
        dag = new Dag(pointerFollower, topDs, maxNodeSize);
        db.internal().setDag(dag);
        db.internal().setKvTransSeq(transSeq);
        db.internal().createPutAndGetData();
        
        assert keyNode.isDirty() == false;
        assert superRoot.isDirty() == false;
    }

    private void doOrdinaryStartup() {
        createMaps();
        updateStreamPointers();
        changeKeyNodesToStateAtStartupTime();
        checkStreamPointers();
        createMemoryPointers();
        findSuperNodeAtStartupTime();
        prepareDb();
        rerunTransactions();
        postStartupCheck();
    }

    private void createMaps() {
        //
        // * Creates nextMap.
        // * Creates posMap
        //      Only latest version of nodes added. Nodes created after startupTime, not added.
        //
        
        int transCount = transactions.size();
        
        for (int i = 0; i < transCount; i++) {
            StoredTrans trans = transactions.get(i);
            
            for (StoredNode storedNode : trans.nodes) {
                long pos = storedNode.getNode().getSpos();
                long prevPos = storedNode.getPrevPos();
                
                if (Spos.isValid(prevPos)) {          
                    nextMap.put(prevPos, pos);                    
                }
            }
        }
        
        for (StoredTrans trans : transactions) {
            for (StoredNode storedNode : trans.nodes) {
                long pos = storedNode.getNode().getSpos();
                if (!nextMap.containsKey(pos) && !wasCreatedInRerunSection(storedNode)) {
                    posMap.put(storedNode.getNode().getSpos(), storedNode);
                }
            }
        }
    }

    /** 
     * Updates stream pointers to point to last node version.
     */
    private void updateStreamPointers() {
        Pointer p = new Pointer();
        
        for (Map.Entry<Long, StoredNode> entry : posMap.entrySet()) {
            Node node = entry.getValue().getNode();
            long key = entry.getKey();
            
            assert key == node.getSpos() : "key:" + key + ", pos:" + node.getSpos();
    
            int pointerCount = node.getSize();
            for (int i = 0; i < pointerCount; i++) {
                node.getPointer(i, p);
                if (p.isNull()) {
                    continue;
                }
    
                long pos = p.getPos();
                long newPos = nextMap.forward(pos);
                node.setPointer(i, null, newPos);
            }
        }
    }

    /**
     * Changes key nodes to state at t = startupTime.
     */
    private void changeKeyNodesToStateAtStartupTime() {
        for (StoredTrans trans : transactions) {
            for (StoredNode stored : trans.nodes) {
                Node node = stored.getNode();
                if (node.getType() == Node.TYPE_KEY_NODE) {
                    KeyNode k = (KeyNode) node;
                    k.toPreviousState(startupTime);
                }
            }
        }
    }

    /**
     * Creates memory pointers from stream pointers when possible.
     */
    private void createMemoryPointers() {
        Pointer p = new Pointer();
    
        for (StoredNode storedNode : posMap.values()) {
            Node node = storedNode.getNode();
            int pointerCount = node.getSize();
            for (int i = 0; i < pointerCount; i++) {
                node.getPointer(i, p);
                if (p.isNull()) {
                    continue;
                }
    
                StoredNode storedPointee = posMap.get(p.pos);
                if (storedPointee != null) {
                    Node pointee = storedPointee.getNode();
                    node.setPointer(i, pointee, accessData);
                    
                    //System.out.println("*** mem pointer created: " + node + " ==> " + pointee);
                }
            }
        }
    }

    private void findSuperNodeAtStartupTime() {
        TopNode lastSuperNode = findLatestSuperNode(transactions);
        
        if (lastSuperNode == null) {
            throw new StreamFormatException("Could not find super node in startup section, "
                    + "starting at pos " + startupPos + " and time " + startupTime + ".");
        }
        
        // We found the latest super node, but we need the one at t = startupTime.
        
        TopDs tempTopDs = new TopDs(lastSuperNode);
        Dag tempDag = new Dag(pointerFollower, tempTopDs, maxNodeSize);
        superRoot = tempTopDs.findSuperRootAtTime(tempDag, startupTime, tempDag.newGetData());
        if (superRoot == null) {
            throw new StreamFormatException("No super root at time " + startupTime + " was found.");
        }
    }

    private static TopNode findLatestSuperNode(List<StoredTrans> transactions) {
        TopNode current = null;
        
        for (StoredTrans trans : transactions) {
            for (StoredNode storedNode : trans.nodes) {
                Node node = storedNode.getNode();
                
                if (node.isTopNode()) {
                    TopNode candidate = (TopNode) node;
                    
                    if (current == null) {
                        current = candidate;
                    } else {
                        /*
                        OLD code before 150721 that caused a lot of problems!
                        Now unit tested. A simple unit test would have save A LOT of time!
                        
                        if (current.topNodeId > candidate.topNodeId) {
                            current = candidate;
                        } else if (current.topNodeId == candidate.topNodeId) {
                            if (candidate.getSpos() > current.getSpos()) {
                                current = candidate;
                            }
                        }
                        */
                        
                        if (candidate.topNodeId >= current.topNodeId) {
                            current = candidate;
                        }
                    }
                }
            }
        }
        
        return current;
    }

    private void prepareDb() {
        TopDs topDs = new TopDs(superRoot);
        dag = new Dag(pointerFollower, topDs, maxNodeSize);        
        db.internal().setDag(dag);
        db.internal().setKvTransSeq(transSeq);
        db.internal().createPutAndGetData();
    }

    private void rerunTransactions() {
        // Reruns transactions, except the first one.
        
        int count = transactions.size();
        
        for (int i = 0; i < count; i++) {
            final StoredTrans storedTrans = transactions.get(i);
            
            Trans.Listener listener = new Trans.Listener() {
                public void transExecuted(ExecuteData x) {}

                public void valueNodeCreated(ValueNode node, long[] key) {
                    ValueNode v = storedTrans.getValueNode(key);
                    assert v != null : "Could not find value node for given key";
                    assert v.getSpos() >= 0 : "v2 spos: " + v.getSpos();
                    node.setSpos(v.getSpos());
                }
            };
            
            if (i > 0) {
                Trans t = storedTrans.createRerunTransaction(db.trans());
                t.listener = listener;
                db.internal().executeInner(t);
            }
        }
    }

    /**
     * @throws AssertionError
     */
    private void postStartupCheck() {
        checkThatValueNodesHaveSpos();
        db.checkNodes();
    }
    
    private void checkThatValueNodesHaveSpos() {
        dag.visitMemoryNodes(new NodeVisitor() {
            public void visit(TopNode node) {
            }

            public void visit(KeyNode node) {
            }

            public void visit(ValueNode node) {
                long pos = node.getSpos();
                if (!(pos >= 0)) {
                    throw new AssertionError("value node got no spos during startup, " + node);
                }
            }
        });
    }

    /**
     * True if node was created in "rerun" section; that is, in a transaction
     * in the startup section, but not in the first transaction of the startup section.
     */
    private boolean wasCreatedInRerunSection(StoredNode storedNode) {
        Node node = storedNode.getNode();
        boolean result = false;
        
        switch (node.getType()) {
        case Node.TYPE_TOP_NODE:
            TopNode top = (TopNode) node;
            if (top.rootTime > startupTime) {
                result = true;
            }
            break;
            
        case Node.TYPE_KEY_NODE:
            KeyNode key = (KeyNode) node;
            if (key.getFirstTime() > startupTime) {
                result = true;
            }
            break;
            
        case Node.TYPE_VALUE:
        case Node.TYPE_DELETE:
            ValueNode valueNode = (ValueNode) node;
            if (valueNode.getSpos() > firstTrans.lastPos) {
                result = true;
            }
            break;
        }
        
        return result;
    }

    private boolean isPrimordialTransaction() {
        return transactions.size() == 1 && transactions.get(0).tpos == RecoverableStream.META_BLOCK_SIZE;
    }

    private void validateAccessData(long accessData) {
        if (!AccessData.isValid(accessData)) {
            throw new IllegalArgumentException("bad accessData when starting database, " 
                    + accessData + ".");
        }
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
        // TODO D. check: t.version --- stream format version. We should check that this
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
        Node node = stored.getNode();
        if (node == null) {
            throw new StreamFormatException("getNode() returned null");
        }
        
        long spos = node.getSpos();
        if (!Spos.isValid(spos)) {
            throw new StreamFormatException("Bad spos of node, spos=" + spos + ", node: " + node);
        }
        
        switch (node.getType()) {
        case Node.TYPE_KEY_NODE:
            KeyNode knode = (KeyNode) node;
            knode.validateStreamNode(initTime);
            break;
        case Node.TYPE_TOP_NODE:
            break;
            
        }
    }

    /**
     * @throws StreamFormatException
     */
    private void checkStreamPointers() {
        for (Node node : posMap2.values()) {
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
            } else {
                Pointer p = new Pointer();
                int count = node.getSize();
                for (int i = 0; i < count; i++) {
                    node.getPointer(i, p);
                    if (!p.isNull()) {
                        if (Spos.isNull(p.getPos())) {
                            throw new StreamFormatException("Unexpected stream pointer, was " 
                                    + p.getPos() + ", index " + i + ", node: " + node);
                        }
                    }
                }
            }
        }
    }

    /**
     * @throws StreamFormatException
     */
    private void checkPrimordialTransaction(StoredNode[] nodes) {
        if (nodes.length != 2) {
            throw new StreamFormatException("expected 2, got " + nodes.length + " nodes.");
        }
        
        Node n0 = nodes[0].getNode();
        Node n1 = nodes[1].getNode();
        
        if (!n0.isTopNode()) {
            throw new StreamFormatException("Expected TopNode, got " + n0);
        }
        
        if (!n1.isKeyNode()) {
            throw new StreamFormatException("Expected KeyNode, got " + n1);
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
    
    
    // ======== Testing =======
    
    @Nano
    private static void testPrevMap1() {
        PrevMap m = new PrevMap();
        m.put(40, 30);
        m.put(30, 20);
        m.put(20, 10);
        
        Assert.assertEquals(20, m.backtrack(25, 40));
        Assert.assertEquals(10, m.backtrack(15, 40));
    }
    
    @Nano
    private static void testPrevMap2() {
        PrevMap m = new PrevMap();
        m.put(40, 30);
        m.put(30, 20);
        m.put(20, 10);
        
        Assert.assertEquals(Spos.NULL, m.backtrack(0, 40));
        Assert.assertEquals(40, m.backtrack(40, 40));
    }
    
    @Nano
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
    
    @Nano
    private static void testEmptyPrevMap() {
        PrevMap m = new PrevMap();
        Assert.assertEquals(Spos.NULL, m.backtrack(10, 40));
    }
    
    @Nano
    private static void testFindLatestSuperNode1() {
        TopNode top = findLatestSuperNode(new ArrayList<StoredTrans>());
        Assert.assertNull(top);
    }
    
    @Nano
    private static void testFindLatestSuperNode2() {
        ArrayList<StoredTrans> transactions = new ArrayList<StoredTrans>();
        
        transactions.add(withOneTopNode(1000, 12));
        transactions.add(trans1(2000));
        transactions.add(trans2(3000));
                
        TopNode top = findLatestSuperNode(transactions);
        
        Assert.assertEquals(12, top.getTopNodeId());
    }
    
    @Nano
    private static void testFindLatestSuperNode3() {
        ArrayList<StoredTrans> transactions = new ArrayList<StoredTrans>();
        
        transactions.add(trans1(1000));
        transactions.add(trans2(2000));
        transactions.add(trans1(3000));
                
        TopNode top = findLatestSuperNode(transactions);
        
        Assert.assertEquals(2, top.getTopNodeId());
    }
    
    @Nano
    private static void testFindLatestSuperNode4() {
        ArrayList<StoredTrans> transactions = new ArrayList<StoredTrans>();
        
        transactions.add(withOneTopNode(4000, 123));
        transactions.add(trans1(1000));
        transactions.add(trans2(2000));
        transactions.add(trans1(3000));
                
        TopNode top = findLatestSuperNode(transactions);
        
        Assert.assertEquals(123, top.getTopNodeId());
    }
    
    private static StoredTrans trans1(long tpos) {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        ValueNode v0 = new ValueNode(new byte[]{});
        ValueNode v1 = new ValueNode(new byte[]{12});
        ValueNode v2 = new ValueNode(new byte[]{13, 14});
        
        KeyNode n = new KeyNode();
        n.addKlong(10, Klong.create(Util.toBytes("a")), v0, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.create(Util.toBytes("b")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.create(Util.toBytes("c")), v2, AccessData.DEFAULT_ACCESS_DATA);
        
        transNodes.addValueNode(v0, Keys.toSegments("a"));
        transNodes.addValueNode(v1, Keys.toSegments("b"));
        transNodes.addValueNode(v2, Keys.toSegments("c"));
        transNodes.addKeyNode(n);
        
        serializer.serialize(transNodes, 100, 200, -1);
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(tpos, buffer);
        
        return new StoredTrans(parser);
    }
    
    private static StoredTrans trans2(long tpos) {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        TopNode t1 = TopNode.createDummy(1);
        TopNode t2 = TopNode.createDummy(2);
        
        transNodes.addTopNode(t1);
        transNodes.addTopNode(t2);
        
        serializer.serialize(transNodes, 100, 200, -1);
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(tpos, buffer);
        
        return new StoredTrans(parser);
    }
    
    private static StoredTrans withOneTopNode(long tpos, int topNodeId) {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        transNodes.addTopNode(TopNode.createDummy(topNodeId));
        
        serializer.serialize(transNodes, 100, 200, -1);
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(tpos, buffer);
        
        return new StoredTrans(parser);
    }
}
