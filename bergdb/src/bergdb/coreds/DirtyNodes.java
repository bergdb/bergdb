package bergdb.coreds;

import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;

import bergdb.core.TransactionNodes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * Simple implementation of the dirty node set, nodes are
 * stored in one sorted spos-to-TopNode map and one sorted spos-to-KeyNode map.
 * Synch note: this class itself is not thread-safe.
 * Access is protected externally by Db.writeLock.
 * 
 * @author Frans Lundberg
 */
public class DirtyNodes {
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
    public DirtyNodes() {
        topNodes = new TreeMap<Long, TopNode>();
        keyNodes = new TreeMap<Long, KeyNode>();
    }
    
    /**
     * Returns the number of nodes in the collection.
     * Caller must hold DB.writeLock.
     * This method is only used for monitoring.
     */
    public int getSize() {
        return topNodes.size() + keyNodes.size();
    }
    
    /**
     * Adds 'node' to the node collection if: node.getSpos() != Spos.NULL.
     * Caller must hold DB.writeLock.
     */
    public void add(TopNode node) {
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
    public void add(KeyNode node) {
        assert node.isDirty == true;
        long pos = node.getSpos();
        if (pos != Spos.NULL) {   
            keyNodes.put(pos, node);
        }
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
    public void getTooDirtyNodes(long dirtyLimit, boolean remove, TransactionNodesForMe list) {
        
        // TopNodes
        
        Iterator<Map.Entry<Long, TopNode>> iter = topNodes.entrySet().iterator();
        while (iter.hasNext()) {
            Map.Entry<Long, TopNode> entry = iter.next();
            TopNode node = entry.getValue();
            long keyPos = entry.getKey().longValue();
            
            if (keyPos != node.getSpos()) {
                iter.remove();
                continue;
            }
            
            if (node.getSpos() < dirtyLimit) {
                list.addTopNode(node);
                if (remove) {
                    iter.remove();
                }
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
                it.remove();
                continue;
            }
            
            if (node.getSpos() < dirtyLimit) {
                list.addKeyNode(node);
                if (remove) {
                    it.remove();
                }
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
    
    @T
    public static void test1() {
        DirtyNodes d = new DirtyNodes();
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
        DirtyNodes d = new DirtyNodes();
        d.add(testNode(10));
        d.add(testNode(20));
        d.add(testNode(30));
        Assert.assertEquals("tooDirtyCount", 3, d.tooDirtyCount(100));
        
        d = new DirtyNodes();
        d.add(testNode(10));
        d.add(testNode(20));
        d.add(testNode(30));
        Assert.assertEquals("tooDirtyCount", 1, d.tooDirtyCount(20));
    }
    
    @T
    public static void testGetTooDirtyNodes1() {
        /* TODO D. Fix test.
        DirtyNodes d = new DirtyNodes();
        KeyNode n1 = testNode(10);
        KeyNode n2 = testNode(20);
        KeyNode n3 = testNode(30);
        d.add(n1);
        d.add(n2);
        d.add(n3);
        
        TransactionNodes list = new TransactionNodes();
        d.getTooDirtyNodes(100, false, list);
        Assert.assertEquals(n1, list.keyNodes[0]);
        Assert.assertEquals(n2, list.keyNodes[1]);
        Assert.assertEquals(n3, list.keyNodes[2]);*/
    }
    
    @T
    public static void testGetTooDirtyNodes2() {
        // TODO D. Fix test
        /*DirtyNodes d = new DirtyNodes();
        KeyNode n1 = testNode(10);
        KeyNode n2 = testNode(20);
        KeyNode n3 = testNode(30);
        d.add(n1);
        d.add(n2);
        d.add(n3);
        n2.setSpos(999);
        
        TransactionNodes list = new TransactionNodes();
        d.getTooDirtyNodes(100, false, list);
        Assert.assertEquals(n1, list.keyNodes[0]);
        Assert.assertEquals(n3, list.keyNodes[1]);
        Assert.assertEquals(2, d.keyNodes.size());*/
    }
}