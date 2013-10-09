package bergdb.coreds;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;

import bergdb.core.TransactionNodes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * 
 * @author Frans Lundberg
 */
public class DirtyNodes2 implements IDirtyNodes {
    //
    // Note, ordinary TreeMap used. There could be room for performance 
    // optimization here. We could have buckets, say 1M big. Put all there as if
    // they all had the same spos.
    //
    
    //private final TreeMap<Long, TopNode> topNodes;
    //private final TreeMap<Long, KeyNode> keyNodes;
    private final TreeMap<Long, INode> nodes;
    
    /**
     * Creates a new collection of dirty nodes.
     */
    public DirtyNodes2() {
        nodes = new TreeMap<Long, INode>();
        //topNodes = new TreeMap<Long, TopNode>();
        //keyNodes = new TreeMap<Long, KeyNode>();
    }
    
    /* (non-Javadoc)
     * @see bergdb.coreds.IDirtyNodes#getSize()
     */
    public final int getSize() {
        return nodes.size();
    }
    
    /* (non-Javadoc)
     * @see bergdb.coreds.IDirtyNodes#add(bergdb.coreds.INode)
     */
    public void add(INode node) {
        nodes.put(node.getSpos(), node);
    }
    
    public void remove(INode node) {
        INode existing = nodes.remove(node.getSpos());
        if (existing == null) {
            throw new AssertionError("No node in collection with spos " + node.getSpos());
        }
    }
    
    /* (non-Javadoc)
     * @see bergdb.coreds.IDirtyNodes#getAndRemoveTooDirtyNodes(long, bergdb.coreds.DirtyNodes.TransactionNodesForMe)
     */
    public void getAndRemoveTooDirtyNodes(long dirtyLimit, DirtyNodes1.TransactionNodesForMe list) {
        getTooDirtyNodes(dirtyLimit, true, list);
    }
    
    /**
     * Adds all nodes that are "too dirty" to "list". The too dirty nodes are the nodes in the 
     * collection with spos < dirtyLimit.
     * Caller must hold DB.writeLock.
     * 
     * @param dirtyLimit A node with an spos less than this is "too dirty".
     * @param remove If true, the read entries will be removed from
     * the collection; a get-and-remove operation.
     * @param list The list to add the too dirty nodes to.
     */
    private void getTooDirtyNodes(long dirtyLimit, boolean remove, DirtyNodes1.TransactionNodesForMe list) {
        
        // TopNodes
        
        Iterator<Map.Entry<Long, INode>> iter = nodes.entrySet().iterator();
        while (iter.hasNext()) {
            Map.Entry<Long, INode> entry = iter.next();
            INode node = entry.getValue();
            long keyPos = entry.getKey().longValue();
            
            // Happens when node was written to stream after added to dirty nodes.
            if (keyPos != node.getSpos()) {
                iter.remove();
                continue;
            }
            
            if (node.getSpos() < dirtyLimit) {
                if (node.isDirty()) {
                    switch (node.getType()) {
                    case INode.TYPE_TOP_NODE:
                        list.addTopNode((TopNode) node);
                        break;
                    case INode.TYPE_KEY_NODE:
                        list.addKeyNode((KeyNode) node);
                        break;
                    default:
                        throw new AssertionError("never happens");
                    }
                }
                
                if (remove) iter.remove();
                
            } else {
                break;
                // keys are sorted, if keyPos >= dirtyLimit, the rest of the keys will also be
                // >= dirtyLimit, so we can break here.
            }
        }
    }
    
    /**
     * Inefficient, for debug/test only.
     */
    private int tooDirtyCount(long dirtyLimit) {
        TransactionNodes nodes = new TransactionNodes();
        getTooDirtyNodes(dirtyLimit, false, nodes);
        return nodes.size();
    }
    
    // ======== Types ========
    
    
    
    // ======== Testing ========
    
    private static class TestTransactionNodes implements DirtyNodes1.TransactionNodesForMe {
        ArrayList<TopNode> topNodes = new ArrayList<TopNode>();
        ArrayList<KeyNode> keyNodes = new ArrayList<KeyNode>();
        
        public void addTopNode(TopNode node) {
            topNodes.add(node);
        }

        public void addKeyNode(KeyNode node) {
            keyNodes.add(node);
        }
    }
    
    @T
    public static void test1() {
        DirtyNodes2 d = new DirtyNodes2();
        KeyNode k = new KeyNode();
        k.setSpos(10);
        k.setIsDirty(true);
        d.add(k);
        
        k = new KeyNode();
        k.setSpos(20);
        k.setIsDirty(true);
        d.add(k);
        
        k = new KeyNode();
        k.setSpos(30);
        k.setIsDirty(true);
        d.add(k);
        
        Assert.assertEquals("tooDirtyCount", 2, d.tooDirtyCount(25));
    }
    
    private static KeyNode testNode(long spos) {
        KeyNode k = new KeyNode();
        k.setSpos(spos);
        k.setIsDirty(true);
        return k;
    }
    
    @T
    public static void test2() {
        DirtyNodes2 d = new DirtyNodes2();
        d.add(testNode(10));
        d.add(testNode(20));
        d.add(testNode(30));
        Assert.assertEquals("tooDirtyCount", 3, d.tooDirtyCount(100));
        
        d = new DirtyNodes2();
        d.add(testNode(10));
        d.add(testNode(20));
        d.add(testNode(30));
        Assert.assertEquals("tooDirtyCount", 1, d.tooDirtyCount(20));
    }
    
    @T
    public static void testGetTooDirtyNodes1() {
        DirtyNodes2 d = new DirtyNodes2();
        KeyNode n1 = testNode(10);
        KeyNode n2 = testNode(20);
        KeyNode n3 = testNode(30);
        d.add(n1);
        d.add(n2);
        d.add(n3);
        
        TestTransactionNodes list = new TestTransactionNodes();
        d.getTooDirtyNodes(100, false, list);
        Assert.assertEquals(n1, list.keyNodes.get(0));
        Assert.assertEquals(n2, list.keyNodes.get(1));
        Assert.assertEquals(n3, list.keyNodes.get(2));
    }
    
    @T
    public static void testGetTooDirtyNodes2() {
        DirtyNodes2 d = new DirtyNodes2();
        KeyNode n1 = testNode(10);
        KeyNode n2 = testNode(20);
        KeyNode n3 = testNode(30);
        d.add(n1);
        d.add(n2);
        d.add(n3);
        n2.setSpos(999);
        
        TestTransactionNodes list = new TestTransactionNodes();
        d.getTooDirtyNodes(100, false, list);
        Assert.assertEquals(n1, list.keyNodes.get(0));
        Assert.assertEquals(n3, list.keyNodes.get(1));
        Assert.assertEquals(2, d.nodes.size());
    }
}