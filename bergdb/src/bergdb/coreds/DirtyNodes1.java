package bergdb.coreds;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;

import bergdb.core.TransactionNodes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * <p>Simple implementation of the dirty node set, nodes are
 * stored in one sorted spos-to-TopNode map and one sorted spos-to-KeyNode map.
 * Synch note: this class itself is not thread-safe. 
 * Access is protected externally by Db.writeLock.</p>
 * 
 * <p>The nodes on this set are dirty when added to the set, but the set can still 
 * contain nodes that are not dirty. If a node in this set is written to stream, 
 * it will no longer be dirty, but it will still remain in this set.
 * The idea is that this set only handles adding nodes until they get too dirty
 * (if still dirty) when they are removed. If removing of single nodes is omitted, this
 * data structure could be more specialized and possibly perform better
 * (current implementation using TreeMap would allow removing nodes, however).</p>
 * 
 * @author Frans Lundberg
 */
public class DirtyNodes1 implements IDirtyNodes {
    //
    // Note, ordinary TreeMap used. There could be room for performance 
    // optimization here. We could have buckets, say 1M big. Put all there as if
    // they all had the same spos.
    //
    
    private final TreeMap<Long, TopNode> topNodes;
    private final TreeMap<Long, KeyNode> keyNodes;
    
    /**
     * Creates a new collection of dirty nodes.
     */
    public DirtyNodes1() {
        topNodes = new TreeMap<Long, TopNode>();
        keyNodes = new TreeMap<Long, KeyNode>();
    }
    
    /* (non-Javadoc)
     * @see bergdb.coreds.IDirtyNodes#getSize()
     */
    public final int getSize() {
        return topNodes.size() + keyNodes.size();
    }
    
    /**
     * Adds 'node' to the node collection if: node.getSpos() != Spos.NULL.
     * Caller must hold DB.writeLock.
     */
    private final void add(TopNode node) {
        assert node.isDirty == true;
        long pos = node.getSpos();
        if (pos != Spos.NULL) {   
            topNodes.put(pos, node);
        }
    }
    
    /**
     * Adds 'node' to the node collection if: node.getSpos() != Spos.NULL.
     * Caller must hold DB.writeLock.
     */
    private final void add(KeyNode node) {
        assert node.isDirty == true;
        long pos = node.getSpos();
        if (pos != Spos.NULL) {   
            keyNodes.put(pos, node);
        }
    }
    
    /* (non-Javadoc)
     * @see bergdb.coreds.IDirtyNodes#add(bergdb.coreds.INode)
     */
    public void add(INode node) {
        switch (node.getType()) {
        case INode.TYPE_TOP_NODE:
            add((TopNode) node);
            break;
        case INode.TYPE_KEY_NODE:
            add((KeyNode) node);
            break;
        default:
            throw new AssertionError("Unexpected node type: " + node);
        }
    }
    
    public void remove(INode node) {
        INode existing;
        
        switch (node.getType()) {
        case INode.TYPE_TOP_NODE:
            existing = topNodes.remove(node.getSpos());
            break;
        case INode.TYPE_KEY_NODE:
            existing = keyNodes.remove(node.getSpos());
            break;
        default:
            throw new AssertionError("Unexpected node type: " + node);
        }
        
        if (existing == null) {
            throw new AssertionError("No node with given spos, node: " + node.toString());
        }
    }
    
    /* (non-Javadoc)
     * @see bergdb.coreds.IDirtyNodes#getAndRemoveTooDirtyNodes(long, bergdb.coreds.DirtyNodes.TransactionNodesForMe)
     */
    public void getAndRemoveTooDirtyNodes(long dirtyLimit, TransactionNodesForMe list) {
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
    private void getTooDirtyNodes(long dirtyLimit, boolean remove, TransactionNodesForMe list) {
        
        // TopNodes
        
        Iterator<Map.Entry<Long, TopNode>> iter = topNodes.entrySet().iterator();
        while (iter.hasNext()) {
            Map.Entry<Long, TopNode> entry = iter.next();
            TopNode node = entry.getValue();
            long keyPos = entry.getKey().longValue();
            
            if (keyPos != node.getSpos()) {
                throw new AssertionError("should not happen");
                //iter.remove();
                //continue;
            }
            
            if (node.getSpos() < dirtyLimit) {
                if (node.isDirty) {   // XXX
                    list.addTopNode(node);
                }
                
                if (remove) iter.remove();
                
            } else {
                break;
                // keys are sorted, if keyPos >= dirtyLimit, the rest of the keys will also be
                // >= dirtyLimit, so we can break here.
            }
        }
        iter = null;
        
        // KeyNodes

        Iterator<Map.Entry<Long, KeyNode>> it = keyNodes.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<Long, KeyNode> entry = it.next();
            KeyNode node = entry.getValue();
            long keyPos = entry.getKey().longValue();
            
            if (keyPos != node.getSpos()) {
                throw new AssertionError("bad state, node: " + node);
                //it.remove();
                //continue;
            }
            
            if (node.getSpos() < dirtyLimit) {
                if (node.isDirty) {
                    list.addKeyNode(node);
                }
                
                if (remove) it.remove();
                
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
    
    public static interface TransactionNodesForMe {
        public void addTopNode(TopNode node);
        public void addKeyNode(KeyNode node);
    }
    
    
    // ======== Testing ========
    
    private static class TestTransactionNodes implements TransactionNodesForMe {
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
        DirtyNodes1 d = new DirtyNodes1();
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
        DirtyNodes1 d = new DirtyNodes1();
        d.add(testNode(10));
        d.add(testNode(20));
        d.add(testNode(30));
        Assert.assertEquals("tooDirtyCount", 3, d.tooDirtyCount(100));
        
        d = new DirtyNodes1();
        d.add(testNode(10));
        d.add(testNode(20));
        d.add(testNode(30));
        Assert.assertEquals("tooDirtyCount", 1, d.tooDirtyCount(20));
    }
    
    @T
    public static void testGetTooDirtyNodes1() {
        DirtyNodes1 d = new DirtyNodes1();
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
        DirtyNodes1 d = new DirtyNodes1();
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
        Assert.assertEquals(2, d.keyNodes.size());
    }
}