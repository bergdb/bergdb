package bergdb.coreds;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;
import java.util.TreeMap;

import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * Straight-forward implementation of the dirty node set.
 * 
 * @author Frans Lundberg
 */
public class DirtyNodes1 implements IDirtyNodes {
    //
    // Note, ordinary TreeMap used. There could be room for performance 
    // optimization here. We could have buckets, say 1M big. Put all there as if
    // they all had the same spos.
    // We could also allow non dirty nodes in the collection physically - avoid the 
    // remove operation - would allow more room for optimization.
    //
    
    private final TreeMap<Long, INode> nodes;
    
    /**
     * Creates a new collection of dirty nodes.
     */
    public DirtyNodes1() {
        nodes = new TreeMap<Long, INode>();
    }
    
    public final int getSize() {
        return nodes.size();
    }
    
    private void put(INode node) {
        put(node.getSpos(), node);
    }
    
    public void put(long spos, INode node) {
        if (spos != Spos.NULL) {
            nodes.put(spos, node);
        }
    }
    
    /**
     * Removes one mapping.
     * 
     * @param spos  The key of the mapping to remove.
     * @throws AssertionError  If no key 'spos' exists.
     */
    public void remove(long spos) {
        INode existing = nodes.remove(spos);
        
        if (existing == null) {
            //System.out.print("---- DirtyNodes1, unexpected, printing dirty nodes:");
            //print(System.out);
            //System.out.println("Done.");
            throw new AssertionError("No node with given spos: " + spos);
        }
    }
    
    @SuppressWarnings("unused")
    private void print(PrintStream out) {
        for (Map.Entry<Long, INode> entry : nodes.entrySet()) {
            out.println(entry.toString());
        }
        out.println();
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

        Iterator<Map.Entry<Long, INode>> iter = nodes.entrySet().iterator();
        while (iter.hasNext()) {
            Map.Entry<Long, INode> entry = iter.next();
            INode node = entry.getValue();
            long keyPos = entry.getKey().longValue();
            
            if (keyPos != node.getSpos()) {
                throw new AssertionError("should not happen");
            }
            
            if (node.getSpos() < dirtyLimit) {
                if (node.isDirty()) {
                    
                    if (remove) {
                        node.setIsDirty(false);
                    }
                    
                    switch (node.getType()) {
                    case INode.TYPE_TOP_NODE:
                        list.addTopNode((TopNode) node);
                        break;
                    case INode.TYPE_KEY_NODE:
                        list.addKeyNode((KeyNode) node);
                        break;
                    default:
                        throw new AssertionError("Bad node type, node: " + node);
                    }
                    
                } else {
                    throw new AssertionError("Non-dirty node in DirtyNodes collection, node: " + node);
                }
                
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
    }
    
    /**
     * Inefficient, for debug/test only.
     */
    private int tooDirtyCount(long dirtyLimit) {
        final int[] count = new int[1];
        
        TransactionNodesForMe nodes = new TransactionNodesForMe() {
            public void addTopNode(TopNode node) {
                count[0]++;
            }

            public void addKeyNode(KeyNode node) {
                count[0]++;
            }
        };
        
        getTooDirtyNodes(dirtyLimit, false, nodes);
        return count[0];
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
        d.put(k.spos, k);
        
        k = new KeyNode();
        k.setSpos(20);
        k.setIsDirty(true);
        d.put(k.spos, k);
        
        k = new KeyNode();
        k.setSpos(30);
        k.setIsDirty(true);
        d.put(k.spos, k);
        
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
        d.put(testNode(10));
        d.put(testNode(20));
        d.put(testNode(30));
        Assert.assertEquals("tooDirtyCount", 3, d.tooDirtyCount(100));
        
        d = new DirtyNodes1();
        d.put(testNode(10));
        d.put(testNode(20));
        d.put(testNode(30));
        Assert.assertEquals("tooDirtyCount", 1, d.tooDirtyCount(20));
    }
    
    @T
    public static void testGetTooDirtyNodes1() {
        DirtyNodes1 d = new DirtyNodes1();
        KeyNode n1 = testNode(10);
        KeyNode n2 = testNode(20);
        KeyNode n3 = testNode(30);
        d.put(n1);
        d.put(n2);
        d.put(n3);
        
        TestTransactionNodes list = new TestTransactionNodes();
        d.getTooDirtyNodes(100, false, list);
        Assert.assertEquals(n1, list.keyNodes.get(0));
        Assert.assertEquals(n2, list.keyNodes.get(1));
        Assert.assertEquals(n3, list.keyNodes.get(2));
    }
}