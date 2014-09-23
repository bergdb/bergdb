package bergdb.core;

import java.util.ArrayList;

import bergdb.dag.INode;
import bergdb.dag.KeyNode;
import bergdb.dag.TopNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;

/**
 * An in-memory data structure that keeps information about the transactions
 * that belongs to the startup section of the database stream.
 * The information is needed to be able to append dirty nodes to the current transaction
 * so they do not become too dirty.
 * 
 * @author Frans Lundberg
 */
public class KvTransSeq {
    private TransInfo first;     // Head of linked list, may be null.
    private TransInfo last;      // Last set of linked list, may be null.
    private int size;
    
    public boolean isEmpty() {
        return first == null;
    }
    
    public int getSize() {
        return size;
    }
    
    public void add(TransInfo info) {
        if (info == null) throw new IllegalArgumentException("info == null not allowed");
        
        if (isEmpty()) {
            first = info;
            last = info;
        } else {
            if (info.tpos <= last.tpos) {
                throw new IllegalArgumentException(
                        "info.tpos <= last.tpos, " + info.tpos + ", " + last.tpos);
            }
            last.next = info;
            last = info;
        }
        
        size += 1;
    }
    
    /**
     * Removes all TransInfos with a tpos < limit.
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
        
        if (first == null) {
            // To avoid possible memory leak, last is set to null.
            last = null;
        }
        
        return result;
    }

    /**
     * Adds index nodes with a tpos < limit to transNodes.
     */
    public void addToTransNodes(long limit, final TransNodesForMe transNodes) {
        visitGotDirtyNodes(limit, new Visitor() {
            public void node(INode node) {
                int type = node.getType();
                switch (type) {
                case INode.TYPE_TOP_NODE:
                    transNodes.addTopNode((TopNode) node);
                    break;
                case INode.TYPE_KEY_NODE:
                    transNodes.addKeyNode((KeyNode) node);
                    break;
                default:
                    throw new IllegalStateException("Unexpected node type in " 
                            + this.getClass().getSimpleName() + ", nodeType: " + node.getType());
                }
            }
        });
    }
    
    /**
     * Accepts a visitor which will visit all gotDirtyNodes with a tpos &lt; limit.
     */
    public void visitGotDirtyNodes(long limit, Visitor visitor) {
        if (isEmpty()) {
            return;
        }
        
        TransInfo info = first;
        while (info != null && info.tpos < limit) {
            for (INode node : info.gotDirtyNodes) {
                visitor.node(node);
            }
            info = info.next;
        }
    }
    
    /**
     * Information needed about one transaction and linked-list pointer.
     */
    public static class TransInfo {
        TransInfo next = null;
        
        /** Transaction stream position. */
        long tpos;
        
        /** Last stream position of the transaction. */
        long lastPos;
        
        /** Index nodes (top nodes, key nodes) that got dirty while the transaction executed. */
        ArrayList<INode> gotDirtyNodes = new ArrayList<INode>();
        
        TransInfo() {
        }
        
        TransInfo(long tpos, long lastPos) {
            this.tpos = tpos;
            this.lastPos = lastPos;
        }
    }
    
    /**
     * The method subset of core.TransactionNodes needed by this class.
     * This type is useful to minimize dependency, good for testing / mocks.
     */
    public static interface TransNodesForMe {
        public void addTopNode(TopNode node);
        public void addKeyNode(KeyNode node);
    }
    
    public static interface Visitor {
        public void node(INode node);
    }
    
    
    // ======== Tests ========
    
    @T
    public static void test0() {
        KvTransSeq s = new KvTransSeq();
        
        Assert.assertEquals(0, s.getSize());
        Assert.assertTrue(s.isEmpty());
    }
    
    @T
    public static void testAddOne() {
        KvTransSeq s = new KvTransSeq();
        TransInfo info = new TransInfo(120, 200);
        s.add(info);
        
        Assert.assertEquals(1, s.getSize());
        Assert.assertFalse(s.isEmpty());
    }

    @T
    public static void testAddThree() {
        // Test with no nodes at all.
        
        KvTransSeq s = new KvTransSeq();
        TransInfo ts1 = new TransInfo(100, 120);
        TransInfo ts2 = new TransInfo(200, 220);
        TransInfo ts3 = new TransInfo(300, 320);
        
        s.add(ts1);
        s.add(ts2);
        s.add(ts3);
        
        Assert.assertEquals(3, s.getSize());
    }
    
    @T
    public static void testRemoveBeforeSpos() {
        
        KvTransSeq s = new KvTransSeq();
        TransInfo info1 = new TransInfo(100, 120);
        TransInfo info2 = new TransInfo(200, 220);
        
        s.add(info1);
        s.add(info2);
        
        Assert.assertEquals(2, s.getSize());
        
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
}
