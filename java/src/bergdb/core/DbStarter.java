package bergdb.core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import bergdb.common.StringUtil;
import bergdb.core.StoredTrans.Parser;
import bergdb.core.StoredTrans.Serializer;
import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.NodeVisitor;
import bergdb.dag.Pointer;
import bergdb.dag.PutData;
import bergdb.dag.Spos;
import bergdb.dag.TopDs;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;

/**
 * A one-function class for the database startup algorithm; see start().
 * start() creates the Dag and runs the startup algorithm.
 * 
 * @author Frans Lundberg
 */
public class DbStarter {
    //
    // This implementation is not optimized for CPU performance. Clean code 
    // takes precedence. Startup is not that performance-sensitive and is 
    // likely I/O bound anyway.
    //
    
    private final TransSeq transSeq = new TransSeq();
    private final HashMap<Long, StoredNode> posMap = new HashMap<Long, StoredNode>();
    private final HashMap<Long, Long> newById = new HashMap<Long, Long>();
    private final HashMap<Long, Long> posToId = new HashMap<Long, Long>();
    private final Db db;
    private final List<StoredTrans> transactions;
    private final StoredTrans firstTrans;
    private TopNode superRoot;
    private final long accessData;
    private int maxNodeSize;
    private Dag dag;
    private final long startupPos;
    private final long startupTime;
    
    private DbStarter(Db db, List<StoredTrans> transactions, long accessData, int maxNodeSize) {
        if (transactions == null) throw new IllegalArgumentException("transactions == null not allowed");
        if (transactions.size() == 0) throw new IllegalArgumentException("transactions.size() == 0");
        
        this.db = db;
        this.transactions = transactions;
        this.firstTrans = transactions.get(0);
        this.accessData = accessData;
        this.superRoot = null;
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
    public static void start(Db db, List<StoredTrans> transactions, long accessData, int maxNodeSize) {
        DbStarter s = new DbStarter(db, transactions, accessData, maxNodeSize);
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
        
        Cache3 nodeTable = db.internal().cache();
        superRoot.setCanonical(true);
        keyNode.setCanonical(true);
        nodeTable.register(superRoot);
        nodeTable.register(keyNode);
        
        dag = new Dag(superRoot, maxNodeSize);
        db.internal().setDag(dag);
        db.internal().setTransSeq(transSeq);
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
        registerSectionNodes();
        findSuperNodeAtStartupTime();
        prepareDb();
        rerunTransactions();
        postStartupCheck();
    }

    private void createMaps() {
        //
        // * Creates newById, Rule R (docs/sis-model.md, 6.2): the id of each index node
        //      with a version in the startup section, to the position of its newest
        //      version there. Top nodes included.
        // * Creates posToId: the id of each index node version in the section, and of
        //      the earlier version that a key node version names as its prevPos.
        // * Creates posMap
        //      Only latest version of nodes added. Nodes created after startupTime
        //      are not added.
        //
        
        for (StoredTrans trans : transactions) {
            for (StoredNode storedNode : trans.nodes) {
                Node node = storedNode.getNode();
                if (!node.isIndexNode()) {
                    continue;
                }
        
                long id = node.getId();
                long pos = node.getSpos();
                newById.put(id, pos);       // in stream order, so the newest version wins
                posToId.put(pos, id);
            
                long prevPos = storedNode.getPrevPos();
                if (Spos.isValid(prevPos)) {
                    posToId.put(prevPos, id);
                }
            }
        }
        
        for (StoredTrans trans : transactions) {
            for (StoredNode storedNode : trans.nodes) {
                Node node = storedNode.getNode();
                long pos = node.getSpos();
                boolean isNewest = !node.isIndexNode() || newById.get(node.getId()) == pos;
                if (isNewest && !wasCreatedInRerunSection(storedNode)) {
                    posMap.put(node.getSpos(), storedNode);
                }
            }
        }
    }

    /** 
     * Updates stream pointers to point to last node version: Rule R, for the pointers
     * whose node id is known without reading the stream (a vpos, or a position in
     * posToId). NodeCollection applies Rule R to the others when they are followed.
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
                Long id = Spos.isVpos(pos) ? Long.valueOf(pos) : posToId.get(pos);
                Long newPos = id == null ? null : newById.get(id);
                if (newPos != null && newPos > pos) {
                    node.setPointer(i, null, newPos);
                }
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
                }
            }
        }
    }

    /**
     * Makes the nodes of posMap the canonical objects of their nodes, in the node table,
     * and gives Rule R to the node collection for the rest of the process.
     */
    private void registerSectionNodes() {
        Cache3 nodeTable = db.internal().cache();
        
        for (StoredNode storedNode : posMap.values()) {
            Node node = storedNode.getNode();
            node.setCanonical(true);
            nodeTable.register(node);
        }
        
        db.internal().nodeCollection().setStartupSection(newById, startupPos, startupTime);
    }

    private void findSuperNodeAtStartupTime() {
        TopNode lastSuperNode = findLatestSuperRoot(transactions);
        
        if (lastSuperNode == null) {
            throw new StreamFormatException("Could not find super node in startup section, "
                    + "starting at pos " + startupPos + " and time " + startupTime + ".");
        }
        
        // We found the latest super node, but we need the one at t = startupTime.
        
        Dag tempDag = new Dag(lastSuperNode, maxNodeSize);
        TopDs tempTopDs = tempDag.getTopDs();
        GetData gd = tempDag.newGetData();
        gd.pointerFollower = db.internal().nodeCollection();
        superRoot = tempTopDs.findSuperRootAtTime(startupTime, gd);
        if (superRoot == null) {
            throw new StreamFormatException("No super root at time " + startupTime + " was found.");
        }
    }

    private static TopNode findLatestSuperRoot(List<StoredTrans> transactions) {
        TopNode current = null;
        
        for (StoredTrans trans : transactions) {
            for (StoredNode storedNode : trans.nodes) {
                Node node = storedNode.getNode();
                
                if (node.isTopNode()) {
                    TopNode candidate = (TopNode) node;
                    
                    if (current == null) {
                        current = candidate;
                    } else {
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
        dag = new Dag(superRoot, maxNodeSize);        
        db.internal().setDag(dag);
        db.internal().setTransSeq(transSeq);
        db.internal().createPutAndGetData();
    }
    
    /**
     * Reruns transactions, except the first one.
     */
    private void rerunTransactions() {
        TransSeq transSeq = db.internal().transSeq();
        int count = transactions.size();
        
        for (int i = 1; i < count; i++) {
            TransSeq.TransInfo tinfo = new TransSeq.TransInfo();
            rerunTransaction(tinfo, transactions.get(i));
            transSeq.add(tinfo);
        }
    }
    
    private PutData createPutData() {
        return db.internal().newPutData();
    }

    private void rerunTransaction(TransSeq.TransInfo tinfo, final StoredTrans storedTrans) {
        final long[] vpos = new long[]{Spos.nextVpos(storedTrans.tpos)};
        
        List<StoredValueNode> valueNodes = storedTrans.getValueNodes();
        
        PutData pd = createPutData();
        
        for (StoredValueNode node : valueNodes) {
            long[] key = node.getKey();
            byte[] value = node.getNode().getValue();
            
            pd.tt = storedTrans.tt;
            pd.nodeChangeListener = new Dag.NodeChangeListener() {
                public void topNodeCreated(TopNode node) {
                    nodeCreated(node);
                }
                
                public void keyNodeCreated(KeyNode node) {
                    nodeCreated(node);
                }

                public void valueNodeCreated(ValueNode node, long[] key) {
                    nodeCreated(node);
                }

                public void keyNodeChanged(KeyNode node) {}
                
                private void nodeCreated(Node node) {
                    long id = vpos[0];
                    vpos[0] = Spos.nextVpos(vpos[0]);
                    
                    node.setId(id);
                    node.setSpos(id);         // initially, we use vpos as spos
                    
                    Node n = storedTrans.findNode(id);
                    if (n != null) {
                        node.setSpos(n.getSpos());
                    }
                    
                    if (node.isIndexNode()) {
                        // A node created and written in the section: its spos is the
                        // position of its newest version, as in the run without restarts.
                        Long newPos = newById.get(id);
                        if (newPos != null) {
                            node.setSpos(newPos);
                        }
                        node.setCanonical(true);
                        db.internal().cache().register(node);
                    }
                }
            };
            
            dag.putKv(key, value, pd);
            
            pd.clearFast();
        }
        
        int dirtyCount = storedTrans.gotDirtyIdsAndSpos.length / 2;
        for (int i = 0; i < dirtyCount; i++) {
            long id = storedTrans.gotDirtyIdsAndSpos[i*2];
            long spos = storedTrans.gotDirtyIdsAndSpos[i*2 + 1];

            Node gotDirtyNode = canonicalNode(id, spos);
            if (gotDirtyNode == null) {                
                Node inTable = db.internal().cache().getNode(id);
                String message = "startup error, node " + id 
                        + ":" + spos + " not found, got dirty in trans tt=" 
                        + storedTrans.tt + ", tpos=" + storedTrans.tpos
                        + "; startup pos " + startupPos + ", time " + startupTime
                        + "; in node table: " + (inTable == null ? "no" 
                                : "a snapshot of " + inTable.getSpos())
                        + (Spos.isValid(spos) && !Spos.isVpos(spos) ? "; type at " + spos + ": "
                                + db.internal().nodeStream().readNodeHeader(spos).type() : "");
                throw new StreamFormatException(message);
            }
            
            gotDirtyNode.setDirty(true);
            tinfo.addGotDirtyNode(gotDirtyNode);
        }
        
        tinfo.tt = storedTrans.tt;
        tinfo.tpos = storedTrans.tpos;
        tinfo.startupPos = storedTrans.startupPos;
        tinfo.lastPos = storedTrans.lastPos;
    }

    /**
     * Returns the canonical object of a node in D: the node table's; or else the node's
     * newest version in the startup section, cut back to the startup time; or else
     * the version at 'spos', the position stored with the got-dirty id, which is then the
     * node's latest version. Null if none of these. 
     * 
     * The rerun does not reach every node in D: a delete of a key that does not exist
     * makes the nodes on its path dirty, but it is not stored, so it is not rerun. D is
     * rebuilt from the stored ids (docs/sis-model.md, 6.2, step 2), not from the rerun.
     */
    private Node canonicalNode(long id, long spos) {
        Cache3 nodeTable = db.internal().cache();
        Node node = nodeTable.getNode(id);
        if (node != null && node.isCanonical()) {
            return node;
        }
        
        Long newPos = newById.get(id);
        if (newPos == null && (!Spos.isValid(spos) || Spos.isVpos(spos))) {
            return null;
        }
        
        node = db.internal().nodeStream().readNode(newPos != null ? newPos : spos);
        assert node.getId() == id : "ids differ, " + node.getId() + " != " + id;
        if (node.getType() == Node.TYPE_KEY_NODE) {
            ((KeyNode) node).toPreviousState(startupTime);
        }
        node.setCanonical(true);
        return nodeTable.register(node);
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

    /**
     * @throws StreamFormatException
     */
    private void validateNode(StoredNode stored, long startupTime) {
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
            
            try {
                knode.validateStreamNode(startupTime);
            } catch (KeyNode.Invalid e) {
                throw new StreamFormatException(e.getMessage(), e);
            }
            
            break;
        case Node.TYPE_TOP_NODE:
            break;
        }
    }

    /**
     * @throws StreamFormatException
     */
    private void checkStreamPointers() {
        for (StoredNode storedNode : posMap.values()) {
            checkStreamPointers(storedNode.getNode());
        }
    }
                
    /**
     * Checks the stream pointers of a node read at startup, after they have been forwarded
     * and the node has been cut back to its state at the startup time: each must name a
     * node version in the stream, not be NULL or a vpos.
     * 
     * @throws StreamFormatException
     */
    static void checkStreamPointers(Node node) {
        if (node.isKeyNode()) {
            KeyNode k = (KeyNode) node;
            
            for (int i = 0; i < k.size; i++) {
                long klong = k.klongs[i];
                if (Klong.isKey(klong) && k.pointers[i] == null) {
                    long pos = k.pos[i];
                    if (Spos.isNull(pos) || Spos.isVpos(pos)) {
                        throw new StreamFormatException("Unexpected stream pointer from KeyNode, was " 
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
                    long pos = p.getPos();
                    if (Spos.isNull(pos) || Spos.isVpos(pos)) {
                        throw new StreamFormatException("Unexpected stream pointer, was " 
                                + pos + ", index " + i + ", node: " + node);
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
    
    /**
     * A key node read at startup with a key klong that points to an unwritten node (a 
     * vpos) must be rejected. Regression test for a bug found 2026-10-12 (
     * level 2): the check tested the node's own position instead of the
     * pointer's, so it never rejected anything.
     */
    @Nano
    private static void testCheckStreamPointersOfKeyNode() {
        KeyNode good = KeyNode.nodeWithTime(10);
        good.addToEnd(Klong.compareValueToKeyKlong(Keys.toSegments("a")[0]), null, 2000);
        good.setSpos(1000);
        checkStreamPointers(good);
        
        KeyNode bad = KeyNode.nodeWithTime(10);
        bad.addToEnd(Klong.compareValueToKeyKlong(Keys.toSegments("a")[0]), null, 2001);
        bad.setSpos(1000);
        boolean rejected = false;
        try {
            checkStreamPointers(bad);
        } catch (StreamFormatException e) {
            rejected = true;
        }
        Assert.assertTrue("key node pointing to vpos 2001 rejected", rejected);
    }
    
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
        TopNode top = findLatestSuperRoot(new ArrayList<StoredTrans>());
        Assert.assertNull(top);
    }
    
    @Nano
    private static void testFindLatestSuperNode2() {
        ArrayList<StoredTrans> transactions = new ArrayList<StoredTrans>();
        
        transactions.add(withOneTopNode(1000, 12));
        transactions.add(testTrans1(2000));
        transactions.add(testTrans2(3000));
                
        TopNode top = findLatestSuperRoot(transactions);
        
        Assert.assertEquals(12, top.getTopNodeId());
    }
    
    @Nano
    private static void testFindLatestSuperNode3() {
        ArrayList<StoredTrans> transactions = new ArrayList<StoredTrans>();
        
        transactions.add(testTrans1(1000));
        transactions.add(testTrans2(2000));
        transactions.add(testTrans1(3000));
                
        TopNode top = findLatestSuperRoot(transactions);
        
        Assert.assertEquals(2, top.getTopNodeId());
    }
    
    @Nano
    private static void testFindLatestSuperNode4() {
        ArrayList<StoredTrans> transactions = new ArrayList<StoredTrans>();
        
        transactions.add(withOneTopNode(4000, 123));
        transactions.add(testTrans1(1000));
        transactions.add(testTrans2(2000));
        transactions.add(testTrans1(3000));
                
        TopNode top = findLatestSuperRoot(transactions);
        
        Assert.assertEquals(123, top.getTopNodeId());
    }
    
    private static StoredTrans testTrans1(long tpos) {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        ValueNode v0 = new ValueNode(new byte[]{});
        ValueNode v1 = new ValueNode(new byte[]{12});
        ValueNode v2 = new ValueNode(new byte[]{13, 14});
        
        KeyNode n = new KeyNode();
        n.addKlong(10, Klong.createKey(StringUtil.toBytes("a")), v0, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.createKey(StringUtil.toBytes("b")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.createKey(StringUtil.toBytes("c")), v2, AccessData.DEFAULT_ACCESS_DATA);
        n.setId(103);
        
        transNodes.addValueNode(v0, Keys.toSegments("a"));
        transNodes.addValueNode(v1, Keys.toSegments("b"));
        transNodes.addValueNode(v2, Keys.toSegments("c"));
        transNodes.addKeyNode(n);
        
        serializer.serialize(transNodes, 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(tpos, buffer);
        
        return new StoredTrans(parser);
    }
    
    private static StoredTrans testTrans2(long tpos) {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        TopNode t1 = TopNode.createDummy(1);
        TopNode t2 = TopNode.createDummy(2);
        
        transNodes.addTopNode(t1);
        transNodes.addTopNode(t2);
        
        serializer.serialize(transNodes, 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(tpos, buffer);
        
        return new StoredTrans(parser);
    }
    
    private static StoredTrans withOneTopNode(long tpos, int topNodeId) {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        transNodes.addTopNode(TopNode.createDummy(topNodeId));
        
        serializer.serialize(transNodes, 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(tpos, buffer);
        
        return new StoredTrans(parser);
    }
}
