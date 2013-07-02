package bergdb.core;

import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * Simple implementation of the dirty node set, nodes are
 * stored in a one sorted spos-to-TopNode map and a sorted spos-to-KeyNode map.
 * 
 * @author Frans Lundberg
 */
public class DirtyNodes2 {
    //
    // Synch note: this class itself is not thread-safe. 
    // Access is protected externally by DB.writeLock.
    //
    
    private TreeMap<Long, TopNode> topNodes;
    private TreeMap<Long, KeyNode> keyNodes;
    
    
    public DirtyNodes2() {
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
     * @param dirtyLimit A node with an spos less than this is
     * "too dirty".
     * @param remove If true, the read entries will be removed from
     * the collection; a get-and-remove operation.
     * @param list The list to add the too dirty nodes to.
     */
    public void getTooDirtyNodes(long dirtyLimit, boolean remove, TransactionNodes list) {
        
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
                list.add(node);
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
                list.add(node);
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
    
    // ======== Testing ========
    
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
        
        TransactionNodes list = new TransactionNodes();
        d.getTooDirtyNodes(100, false, list);
        Assert.assertEquals(n1, list.keyNodes[0]);
        Assert.assertEquals(n2, list.keyNodes[1]);
        Assert.assertEquals(n3, list.keyNodes[2]);
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
        
        TransactionNodes list = new TransactionNodes();
        d.getTooDirtyNodes(100, false, list);
        Assert.assertEquals(n1, list.keyNodes[0]);
        Assert.assertEquals(n3, list.keyNodes[1]);
        Assert.assertEquals(2, d.keyNodes.size());
    }
}