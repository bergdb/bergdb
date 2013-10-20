package bergdb.coreds;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * An instance of this class keeps a sequence of node sets in the
 * startup interval. Each node set contains the index nodes of a particular 
 * transaction.
 * This class is not thread-safe, use external synchronization.
 * Normally, an object of this class is protected by Db.writeLock.
 * 
 * @author Frans Lundberg
 */
public class TransSeq {
    private Tset first;     // Head of linked list, may be null.
    private Tset last;      // Last set of linked list, may be null.
    private int size;
    
    public TransSeq() {
        first = null;
        last = null;
        size = 0;
    }
    
    public boolean isEmpty() {
        return first == null;
    }
    
    public int getSize() {
        return size;
    }
    
    /**
     * Adds a TSet to the end of the list.
     * 
     * @param set  The TSet to add, condition: tset.tpos > last.tpos (or empty list).
     */
    public void add(Tset set) {
        if (set == null) throw new IllegalArgumentException("tset == null not allowed");
        
        if (isEmpty()) {
            first = set;
            last = set;
        } else {
            if (set.tpos <= last.tpos) {
                throw new IllegalArgumentException(
                        "tset.tpos <= last.tpos, " + set.tpos + ", " + last.tpos);
            }
            last.next = set;
            last = set;
        }
        
        size += 1;
    }
    
    /**
     * Removes all Tsets with a tpos < limit.
     * 
     * @return The number of sets removed from the list.
     */
    public int removeBeforeSpos(long limit) {
        int result = 0;
        
        if (isEmpty()) {
            return 0;
        }
        
        while (first != null && first.tpos < limit) {
            first = first.next;
            size -= 1;
            result += 1;
        }
        
        // To avoid possible memory leak.
        if (first == null) {
            last = null;
        }
        
        return result;
    }

    /**
     * For an update interval pos >= tpos, this method returns the greatest possible
     * spos of a node included in the update interval.
     * To test whether a node belongs to the update interval use: node.spos <= result;
     * where 'result' is the result of this method.
     */
    public long lastPosOfUpdateInterval(long tpos) {
        if (isEmpty()) return Long.MAX_VALUE;
        
        Tset s = first;
        while (s != null && s.tpos <= tpos) s = s.next;
        
        if (s == null) return Long.MAX_VALUE;
        
        return s.tpos - 1;
    }
    
    /**
     * Accepts the visitors over all TSets and nodes with a tpos < limit.
     */
    public void acceptVisitor(long limit, Visitor visitor) {
        if (isEmpty()) {
            return;
        }
        
        Tset s = first;
        while (s != null && s.tpos < limit) {
            visitor.tset(s);
            for (int i = 0; i < s.nodes.length; i++) {
                visitor.node(s.nodes[i]);
            }
            s = s.next;
        }
    }
    
    /**
     * Adds nodes with a tpos < limit to the supplied transaction node collection.
     */
    public void addToTransactionNodes(long limit, TransactionNodesForMe tNodes) {
        //
        // TODO B. Consider: we may have multiple objects representing same node! I suppose, we
        // should not use an INode as key, but use node.getSpos() instead, or possibly 
        // node.getId(). Would be first functional use of node.getId() in that case, I believe.
        // But, is this really true, can we have this provided that we always keep startup 
        // interval index nodes in memory?
        //
        // 1. Iterate nodes in update interval to create nodeToTpos.
        // 2. Iterate nodes in update interval to create forwardNodesA and childToParents.
        // 3. Iterate nodes in forwardNodesA, add all ancestors that are also in childToParents.
        //
        
        final HashMap<INode, Long> nodeToTpos = new HashMap<INode, Long>();
        final HashSet<INode> forwardNodesA = new HashSet<INode>();
        final HashMap<INode, ArrayList<INode>> childToParents = new HashMap<INode, ArrayList<INode>>();
        
        acceptVisitor(limit, new Visitor() {
            long tpos;
            
            public void tset(Tset set) {
                tpos = set.tpos;
            }

            public void node(INode node) {
                nodeToTpos.put(node, tpos);
            }
        });
        
        acceptVisitor(limit, new Visitor() {
            long tpos;
            Pointer p = new Pointer();
            
            public void tset(Tset set) {
                tpos = set.tpos;
            }

            public void node(INode node) {
                boolean isForward = false;
                int count = node.getPointerCount();
                
                for (int i = 0; i < count; i++) {
                    node.getPointer(i, p);
                    
                    if (!p.isNull() && p.isMem()) {
                        INode child = p.getNode();
                        assert child != null;
                        Long tposLong = nodeToTpos.get(child);
                        if (tposLong != null) {
                            long tpos2 = tposLong;
                            if (tpos2 > tpos) {
                                isForward = true;
                            }
                        } else {
                            if (child.getSpos() > tpos) {
                                isForward = true;
                            }
                        }
                        
                        if (tposLong != null && child.isTopOrKeyNode()) {
                            ArrayList<INode> parents = childToParents.get(child);
                            if (parents == null) {
                                parents = new ArrayList<INode>();
                                parents.add(node);
                                childToParents.put(child, parents);
                            } else {
                                if (!parents.contains(node)) {
                                    parents.add(node);
                                }
                            }
                            
                        }
                    }
                }
                
                if (isForward) {
                    forwardNodesA.add(node);
                }
            }
        });
        
        final HashSet<INode> forwardNodesB = new HashSet<INode>();
        
        for (INode node : forwardNodesA) {
            forwardNodesB.add(node);
            addAncestors(node, forwardNodesB, childToParents, 0);
        }
        
        for (INode node : forwardNodesB) {
            switch (node.getType()) {
            case INode.TYPE_TOP_NODE:
                tNodes.addTopNode((TopNode) node);
                break;
            case INode.TYPE_KEY_NODE:
                tNodes.addKeyNode((KeyNode) node);
                break;
            default:
                throw new AssertionError("Bad node type: " + node);
            }
        }
    }
    
    /**
     * Adds all ancestors of node that exist in childToParents to 'set'.
     */
    private void addAncestors(INode node, Set<INode> set, HashMap<INode, 
            ArrayList<INode>> childToParents, int recurseDepth) {
        List<INode> parents = childToParents.get(node);
        
        //if (recurseDepth > 30) {
        //    System.out.println("TransSequence.addAncestors, node: " + node);
        //}
        
        if (parents != null) {
            for (INode p : parents) {
                set.add(p);
                addAncestors(p, set, childToParents, recurseDepth + 1);   // TODO A. Loops forever for StartupDistanceTester.
            }
        }
    }
    
    /**
     * The method subset of core.TransactionNodes needed by this class.
     * This type is useful to minimize dependency, good for testing / mocks.
     */
    public static interface TransactionNodesForMe {
        public void addTopNode(TopNode node);
        public void addKeyNode(KeyNode node);
    }
    
    public static class TNodes implements TransactionNodesForMe {
        public ArrayList<INode> nodes;

        public TNodes() {
            nodes = new ArrayList<INode>();
        }
        
        public void addTopNode(TopNode node) {
            nodes.add(node);
        }

        public void addKeyNode(KeyNode node) {
            nodes.add(node);
        }
        
    }
    
    public static interface Visitor {
        public void tset(Tset tset);
        public void node(INode node);
    }
    
    /**
     * A TSet is a collection of all top node and key nodes for a particular 
     * transaction.
     */
    public static class Tset {
        /** Next element in the linked list. */
        public Tset next;
        
        /** Transaction stream position. */
        public final long tpos;
        
        /** The top/key nodes of the transaction. */
        public final INode[] nodes;
        
        private static final INode[] EMPTY = new INode[0];
        
        public Tset(long tpos) {
            nodes = EMPTY;
            this.tpos = tpos;
        }
        
        public Tset(INode[] nodes, long tpos) {
            this.nodes = nodes;
            this.tpos = tpos;
        }
    }
    
    
    // ======== Tests ========
    
    @T
    public static void test0() {
        TransSeq s = new TransSeq();
        
        Assert.assertEquals(0, s.getSize());
        Assert.assertTrue(s.isEmpty());
    }
    
    @T
    public static void test1() {
        TransSeq s = new TransSeq();
        Tset ts = new Tset(100);
        s.add(ts);
        
        Assert.assertEquals(1, s.getSize());
        Assert.assertFalse(s.isEmpty());
    }
    
    @T
    public static void test2() {
        TransSeq s = new TransSeq();
        Tset ts1 = new Tset(100);
        Tset ts2 = new Tset(200);
        
        s.add(ts1);
        s.add(ts2);
        
        Assert.assertEquals(2, s.getSize());
        Assert.assertFalse(s.isEmpty());
        s.removeBeforeSpos(99);
        Assert.assertEquals(2, s.getSize());
        s.removeBeforeSpos(100);
        Assert.assertEquals(2, s.getSize());
        s.removeBeforeSpos(101);
        Assert.assertEquals(1, s.getSize());
        s.removeBeforeSpos(400);
        Assert.assertEquals(0, s.getSize());
        Assert.assertTrue(s.isEmpty());
    }
    
    @T
    public static void testLastPos0() {
        TransSeq s = new TransSeq();
        Tset ts1 = new Tset(100);
        Tset ts2 = new Tset(200);
        
        s.add(ts1);
        s.add(ts2);
        
        Assert.assertEquals(199, s.lastPosOfUpdateInterval(100));
        Assert.assertEquals(99, s.lastPosOfUpdateInterval(0));
    }
    
    @T
    public static void testLastPos1() {
        TransSeq s = new TransSeq();
        Tset ts1 = new Tset(100);
        Tset ts2 = new Tset(200);
        
        s.add(ts1);
        s.add(ts2);
        
        Assert.assertEquals(Long.MAX_VALUE, s.lastPosOfUpdateInterval(200));
        Assert.assertEquals(Long.MAX_VALUE, s.lastPosOfUpdateInterval(300));
    }
    
    @T
    public static void testNullInLongMap() {
        HashMap<String, Long> m = new HashMap<String, Long>();
        m.put("a", 1L);
        
        long a = m.get("a");
        long b = 0;
        Exception ex = null;
        
        try {
            b = m.get("b");
        } catch (NullPointerException e) {
            ex = e;
        }
        
        Assert.assertEquals(0L, b);
        Assert.assertEquals(1L, a);
        Assert.assertTrue(ex != null);
    }
    
    @T
    public static void testAddToTransactionNodes0() {
        // Test with no nodes at all.
        
        TransSeq s = new TransSeq();
        Tset ts1 = new Tset(100);
        Tset ts2 = new Tset(200);
        Tset ts3 = new Tset(300);
        
        s.add(ts1);
        s.add(ts2);
        s.add(ts3);
        
        TNodes t = new TNodes();
        s.addToTransactionNodes(250, t);
        
        Assert.assertEquals(0, t.nodes.size());
    }
    
    @T
    public static void testAddToTransactionNodes1() {
        // Test with a single forward node. Forward pointer to outside the update interval.
        
        KeyNode k11 = new KeyNode();
        k11.setSpos(101);
        
        KeyNode k21 = new KeyNode();
        k21.setSpos(201);
        
        KeyNode k31 = new KeyNode();
        k31.setSpos(301);
        
        k11.addKlong(100, Klong.create(Keys.toBytes("abc")), k31, AccessData.DEFAULT_ACCESS_DATA);
            // Forward pointer k11 --> k31
        
        TransSeq s = new TransSeq();
        s.add(new Tset(new INode[]{k11}, 100));
        s.add(new Tset(new INode[]{k21}, 200));
        s.add(new Tset(new INode[]{k31}, 300));
        
        TNodes t = new TNodes();
        s.addToTransactionNodes(150, t);
        Assert.assertEquals(1, t.nodes.size());
        Assert.assertEquals(k11, t.nodes.get(0));
        
        t = new TNodes();
        s.addToTransactionNodes(300, t);
        Assert.assertEquals(1, t.nodes.size());
        
        t = new TNodes();
        s.addToTransactionNodes(50, t);
        Assert.assertEquals(0, t.nodes.size());
    }
    
    @T
    public static void testAddToTransactionNodes2() {
        // Test with intra-transaction pointers.
        
        KeyNode k11 = new KeyNode();
        k11.setSpos(101);
        KeyNode k12 = new KeyNode();
        k12.setSpos(102);
        KeyNode k13 = new KeyNode();
        k13.setSpos(103);
        
        KeyNode k21 = new KeyNode();
        k21.setSpos(201);
        KeyNode k22 = new KeyNode();
        k22.setSpos(201);
        
        KeyNode k31 = new KeyNode();
        k31.setSpos(301);
        
        // Intra-transaction pointers, not a forward pointers.
        
        k11.addKlong(100, Klong.create(Keys.toBytes("aaa")), k12, AccessData.DEFAULT_ACCESS_DATA);
        k11.addKlong(100, Klong.create(Keys.toBytes("aaa")), k13, AccessData.DEFAULT_ACCESS_DATA);
        k12.addKlong(100, Klong.create(Keys.toBytes("bbb")), k13, AccessData.DEFAULT_ACCESS_DATA);
        k21.addKlong(100, Klong.create(Keys.toBytes("aaa")), k22, AccessData.DEFAULT_ACCESS_DATA);
     
        TransSeq s = new TransSeq();
        s.add(new Tset(new INode[]{k11, k12, k13}, 100));
        s.add(new Tset(new INode[]{k21, k22}, 200));
        s.add(new Tset(new INode[]{k31}, 300));
        
        TNodes t = new TNodes();
        s.addToTransactionNodes(350, t);
        Assert.assertEquals(0, t.nodes.size());
    }
    
    @T
    public static void testAddToTransactionNodes3() {
        // Test with ancestors.
        
        KeyNode k11 = new KeyNode();
        k11.setSpos(101);
        KeyNode k12 = new KeyNode();
        k12.setSpos(102);
        KeyNode k13 = new KeyNode();
        k13.setSpos(103);
        
        KeyNode k21 = new KeyNode();
        k21.setSpos(201);
        KeyNode k22 = new KeyNode();
        k22.setSpos(201);
        
        KeyNode k31 = new KeyNode();
        k31.setSpos(301);
        
        k11.addKlong(100, Klong.create(Keys.toBytes("a")), k13, AccessData.DEFAULT_ACCESS_DATA);
            // k11 is parent of k13
        k12.addKlong(100, Klong.create(Keys.toBytes("a")), k13, AccessData.DEFAULT_ACCESS_DATA);
            // k12 is parent of k13
        k13.addKlong(100, Klong.create(Keys.toBytes("a")), k31, AccessData.DEFAULT_ACCESS_DATA);
            // forward pointer
        
        TransSeq s = new TransSeq();
        s.add(new Tset(new INode[]{k11, k12, k13}, 100));
        s.add(new Tset(new INode[]{k21, k22}, 200));
        s.add(new Tset(new INode[]{k31}, 300));
        
        TNodes t = new TNodes();
        s.addToTransactionNodes(250, t);
        Assert.assertEquals(1+2, t.nodes.size());
    }
    
    
    @T
    public static void testAddToTransactionNodes4() {
        // Test with a mix of different forward pointers, intra-pointers, backward pointers...
        
        KeyNode k11 = new KeyNode();
        k11.setSpos(101);
        KeyNode k12 = new KeyNode();
        k12.setSpos(102);
        KeyNode k13 = new KeyNode();
        k13.setSpos(103);
        KeyNode k14 = new KeyNode();
        k14.setSpos(104);
        
        KeyNode k21 = new KeyNode();
        k21.setSpos(201);
        KeyNode k22 = new KeyNode();
        k22.setSpos(201);
        
        KeyNode k31 = new KeyNode();
        k31.setSpos(301);
        KeyNode k32 = new KeyNode();
        k32.setSpos(302);
        KeyNode k33 = new KeyNode();
        k33.setSpos(303);
        
        
        k11.addKlong(100, Klong.create(Keys.toBytes("a")), k12, AccessData.DEFAULT_ACCESS_DATA);
            // k11 is parent of k12
        k33.addKlong(100, Klong.create(Keys.toBytes("a")), k12, AccessData.DEFAULT_ACCESS_DATA);
            // k33 is parent of k12
        k12.addKlong(100, Klong.create(Keys.toBytes("a")), k13, AccessData.DEFAULT_ACCESS_DATA);
            // k12 is parent of k13
        k13.addKlong(100, Klong.create(Keys.toBytes("a")), k31, AccessData.DEFAULT_ACCESS_DATA);
            // k13 has forward pointer to k31.
        k13.addKlong(100, Klong.create(Keys.toBytes("a")), k32, AccessData.DEFAULT_ACCESS_DATA);
            // k13 has forward pointer to k32.
        k14.addKlong(100, Klong.create(Keys.toBytes("a")), k32, AccessData.DEFAULT_ACCESS_DATA);
            // k14 has forward pointer to k22.
        
        TransSeq s = new TransSeq();
        s.add(new Tset(new INode[]{k11, k12, k13, k14}, 100));
        s.add(new Tset(new INode[]{k21, k22}, 200));
        s.add(new Tset(new INode[]{k31, k32, k33}, 300));
        
        TNodes t = new TNodes();
        s.addToTransactionNodes(250, t);
        
        // t should include: k11, k12, k13, k14
        Assert.assertEquals(4, t.nodes.size());
        Assert.assertTrue(t.nodes.contains(k11));
        Assert.assertTrue(t.nodes.contains(k12));
        Assert.assertTrue(t.nodes.contains(k13));
        Assert.assertTrue(t.nodes.contains(k14));
    }
    
    public static void main(String[] args) {
        testAddToTransactionNodes1();
    }
}

// Linked list? 
// -> a -> b -> c
// Add new one, d, to end.
// -> a -> b -> c -> d.
// Remove from beginning. Set new head.
