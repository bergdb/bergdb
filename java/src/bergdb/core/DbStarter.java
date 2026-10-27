package bergdb.core;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import bergdb.common.AssertStatus;
import bergdb.dag.Handle;
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
        
        superRoot.setPointer(0, Handle.of(keyNode), keyNode.getSpos());
        
        Cache3 nodeTable = db.internal().cache();
        superRoot.setCanonical(true);
        keyNode.setCanonical(true);
        nodeTable.register(superRoot);
        nodeTable.register(keyNode);
        
        dag = new Dag(superRoot, maxNodeSize);
        db.internal().setDag(dag);
        db.internal().setTransSeq(transSeq);
        db.internal().setNewestWrittenTop(superRoot);
        db.internal().createPutAndGetData();
        
        assert keyNode.isDirty() == false;
        assert superRoot.isDirty() == false;
    }

    private void doOrdinaryStartup() {
        createMaps();
        Audit.Oracle oracle = db.internal().oracle();
        if (oracle != null) oracle.section(newById);       // the audit (WP J1; test-only)
        updateStreamPointers();
        changeKeyNodesToStateAtStartupTime();
        checkStreamPointers();
        createMemoryPointers();
        registerSectionNodes();
        findSuperNodeAtStartupTime();
        prepareDb();
        rerunTransactions();
        linkD();
        postStartupCheck();
        db.internal().nodeCollection().endReconstruction();
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
                if (newPos != null && Spos.newer(newPos, pos)) {
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
                    node.setPointer(i, Handle.pointeeOf(pointee), p.pos);
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
        TopNode lastSuperNode = topNodeOfLastTransaction();
        
        // It is the super root at the startup time (bergdb 011-11, 8.3): a top node
        // is written only after the startup pos has reached the transaction that created it.
        
        Dag tempDag = new Dag(lastSuperNode, maxNodeSize);
        TopDs tempTopDs = tempDag.getTopDs();
        GetData gd = tempDag.newGetData();
        gd.pointerFollower = db.internal().nodeCollection();
        superRoot = tempTopDs.findSuperRootAtTime(startupTime, gd);
        if (superRoot == null) {
            throw new StreamFormatException("No super root at time " + startupTime + " was found.");
        }
        // 2026-10-16 (bergdb item 001, WP A3; review-13-claude, 7.1): a check, not an assert,
        // so that a stream that breaks it is refused also without -ea.
        if (superRoot != lastSuperNode) {
            throw new StreamFormatException("The newest written top node " + lastSuperNode.getId()
                    + " is not the super root at the startup time, " + superRoot.getId() + ".");
        }
        db.internal().setNewestWrittenTop(lastSuperNode);
    }

    /**
     * Returns the canonical object of the top node whose latest version the last transaction
     * names (StoredTrans.topPos): the newest written top node. Before 2026-10-15, startup
     * scanned the section for the newest top node, which the section need not hold: when the
     * startup pos moved past every top node version, the database could not start
     * (bergdb 011-11, M18).
     */
    private TopNode topNodeOfLastTransaction() {
        StoredTrans last = transactions.get(transactions.size() - 1);
        long pos = last.topPos;
        if (!Spos.isValid(pos) || Spos.isVpos(pos)) {
            throw new StreamFormatException("The last transaction, at " + last.tpos
                    + ", names no top node (topPos " + pos + ").");
        }
        
        Long id = posToId.get(pos);
        if (id == null) {
            id = db.internal().nodeStream().readNodeHeader(pos).id();
        }
        
        Long newPos = newById.get(id);     // Rule R; topPos names the latest version anyway
        assert newPos == null || newPos == pos : "topPos " + pos + " is not the newest version "
                + newPos + " of top node " + id;
        long ref = newPos != null && Spos.newer(newPos, pos) ? newPos : pos;
        
        Node node;
        StoredNode stored = posMap.get(ref);
        if (stored != null) {
            node = stored.getNode();        // canonical, registerSectionNodes()
        } else {
            Cache3 nodeTable = db.internal().cache();
            Node inTable = nodeTable.getNode(id);
            if (inTable != null && inTable.isCanonical()) {
                node = inTable;
            } else {
                node = db.internal().nodeStream().readNode(ref);
                node.setCanonical(true);
                node = nodeTable.register(node);
            }
        }
        
        if (!(node instanceof TopNode)) {
            throw new StreamFormatException("topPos " + pos + " of the last transaction names a "
                    + node.getClass().getSimpleName() + ", not a top node.");
        }
        return (TopNode) node;
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
                        if (node instanceof ValueNode && n instanceof ValueNode) {
                            // Its transaction's position, for a get (2026-10-24, bergdb
                            // 005-34): a value rerun here had its own position as it.
                            ((ValueNode) node).offsetFromTrans = ((ValueNode) n).offsetFromTrans;
                        }
                        node.setSpos(n.getSpos());
                    }
                    
                    if (!node.isIndexNode()) {
                        // The resident registry and the audit's oracle (WP J1).
                        db.internal().cache().residents().added(node);
                        Audit.Oracle oracle = db.internal().oracle();
                        if (oracle != null) oracle.value(id, node.getSpos());
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
    /**
     * Rule 4 (bergdb item 001, WP R8, change 1; the Lean model's `Mem.linkD`;
     * bergdb 001-08, M44): every stream pointer of the canonical object of a
     * node of D that names a node with a canonical object gets that node's handle.
     * createMemoryPointers links the section's objects by exact position
     * only, and NodeCollection.resolvePointers resolves by node id only the pinned set,
     * so without it a node of D could name an older version of a node written since.
     * The root needs nothing: TopDs holds its super root by reference.
     *
     * <p>Since bergdb 005-57 (2026-10-27) without reading the stream: the node a pointer
     * names is found by posToId, or among the canonical objects by the position of their
     * versions (byPos); see NodeCollection.linkToCanonical. Before, it read the header at
     * each pointer's position to learn the node's id: a random read for each stream
     * pointer of D, most of a cold startup (007-05). When assertions are on, so in every
     * test, each pointer is also found by node id, with that read, and a difference fails:
     * 005-57's argument checked at every startup of the tests.</p>
     */
    private void linkD() {
        final NodeCollection collection = db.internal().nodeCollection();
        final Map<Long, Handle> byPos = new HashMap<Long, Handle>();
        for (Handle h : db.internal().cache().handles()) {
            Node o = h.obj;
            if (o != null && o.isCanonical()) {
                byPos.put(o.getSpos(), h);
            }
        }
        final boolean check = AssertStatus.enabled();
        db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                collection.linkToCanonical(node, posToId, byPos, check);
            }
        });
    }
    
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
        // The versions are checked where they are read: each transaction's format and its
        // nodes' by the parsers (StoredTrans.Parser, Stored*Node.parse), the meta blocks' by
        // recovery (RecoverableStream.readMetaBlock); a stream of another version is refused
        // there with a VersioningStreamException. Until 2026-10-25 (bergdb 005-40), a TODO of
        // 2014 here asked for this check; the parsers have made it since 2015-07-24.
        
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
                if (Klong.isKey(klong) && k.getPointerNode(i) == null) {
                    long pos = k.getPointerPos(i);
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
    
}
