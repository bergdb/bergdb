package bergdb.core;

import java.util.ArrayList;

import bergdb.dag.INode;
import bergdb.dag.KeyNode;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.nanotest.Assert;
import static bergdb.nanotest.Assert.*;
import bergdb.nanotest.Nano;

/**
 * An in-memory data structure that keeps information about the transactions
 * that belongs to the startup section of the database stream.
 * The information is needed to be able to append dirty nodes to the end of the
 * stream before so they will not become too dirty.
 * 
 * @author Frans Lundberg
 */
public class TransSeq implements PosOfTransBeforeFunction {
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
     * Returns the stream position of the last transaction with 
     * tpos < limit or Spos.NULL if there is no such transaction.
     */
    public long posOfTransBefore(long limit) {
        long result = Spos.NULL;
        
        TransInfo t = first;
        while (t != null && t.tpos < limit) {
            result = t.tpos;
            t = t.next;
        }
        
        return result;
    }
    
    /**
     * Takes dirty index nodes from the trans seq and adds to trans nodes.
     * 
     * @param tposLimit  Takes all nodes of transactions with tpos LTE tposLimit.
     * @param transNodes  For output.
     */
    public void take(final long tposLimit, final TransNodesForMe transNodes) {
        if (isEmpty()) {
            return;
        }
        
        while (first != null && first.tpos <= tposLimit) {
            for (INode node : first.gotDirtyNodes) {
                int type = node.getType();
                switch (type) {
                case INode.TYPE_TOP_NODE:
                    //if (node.isDirty()) {   // TODO A. Use if here? could have been cleaned in advance due to addUnstoredDescendent
                        transNodes.addTopNode((TopNode) node);
                    //}
                    break;
                case INode.TYPE_KEY_NODE:
                    //if (node.isDirty()) {   // TODO A. Use if here? could have been cleaned in advance due to addUnstoredDescendent
                        transNodes.addKeyNode((KeyNode) node);
                    //}
                    break;
                }
                
                assert node.isIndexNode() : "non-index node in trans seq, " + node.toString();
            }
            
            first = first.next;
            size -= 1;
        }
        
        if (first == null) {
            // To avoid a potential memory leak
            last = null;
        }
    }
    
    /**
     * Accepts a visitor which will visit all gotDirtyNodes with a tpos <= limit.
     */
    public void visitGotDirtyNodes(long limit, NodeVisitor visitor) {
        if (isEmpty()) {
            return;
        }
        
        TransInfo info = first;
        while (info != null && info.tpos <= limit) {
            for (INode node : info.gotDirtyNodes) {
                visitor.node(node, info.tpos, info.lastPos);
            }
            info = info.next;
        }
    }
    
    /**
     * Information about a transaction and a linked-list pointer.
     */
    public static class TransInfo {
        TransInfo next = null;
        
        /** Transaction stream position. */
        long tpos;
        
        /** Last stream position of the transaction. */
        long lastPos;
        
        long tt;
        
        long startupPos;

        
        /** Index nodes (top nodes, key nodes) that got dirty while the transaction executed. */
        ArrayList<INode> gotDirtyNodes = new ArrayList<INode>();


        TransInfo() {}
        
        public String toString() {
            return "tt:" + tt + ", tpos:" + tpos + ", gotDirtyCount:" + gotDirtyNodes.size();
        }
        
        public String print() {
            StringBuilder b = new StringBuilder();
            b.append("tt:" + tt + ", tpos:" + tpos);
            if (gotDirtyNodes.size() == 0) {
                b.append(", no gotDirtyNodes");
            } else {
                b.append(", gotDirtyNodes:\n");
                for (INode n : gotDirtyNodes) {
                    b.append("  " + n.toString() + "\n");
                }
            }
            return b.toString();
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
    
    public static interface NodeVisitor {
        /**
         * @param tpos  Transaction pos, that is the first stream pos of the transaction.
         * @param lastPos  Last pos of the transaction.
         */
        public void node(INode node, long tpos, long lastTpos);
    }
    
    
    // ======== Tests ========
    
    private static TransInfo newTransInfo(long tpos, long lastPos) {
        return newTransInfo(tpos, lastPos, -1);
    }
    
    private static TransInfo newTransInfo(long tpos, long lastPos, long tt) {
        TransInfo info = new TransInfo();
        info.tpos = tpos;
        info.lastPos = lastPos;
        info.tt = tt;
        return info;
    }
    
    /** Test TransInfo object with one node. */
    private static TransInfo newTransInfo(long tpos, long lastPos, INode node) {
        TransInfo info = new TransInfo();
        info.tpos = tpos;
        info.lastPos = lastPos;
        info.tt = -1;
        info.gotDirtyNodes.add(node);
        return info;
    }
    
    @Nano
    public static void test0() {
        TransSeq s = new TransSeq();
        
        Assert.assertEquals(0, s.getSize());
        Assert.assertTrue(s.isEmpty());
    }
    
    @Nano
    public static void testAddOne() {
        TransSeq s = new TransSeq();
        TransInfo info = newTransInfo(120, 200);
        s.add(info);
        
        Assert.assertEquals(1, s.getSize());
        Assert.assertFalse(s.isEmpty());
    }

    @Nano
    public static void testAddThree() {
        // Test with no nodes at all.
        
        TransSeq s = new TransSeq();
        TransInfo ts1 = newTransInfo(100, 120);
        TransInfo ts2 = newTransInfo(200, 220);
        TransInfo ts3 = newTransInfo(300, 320);
        
        s.add(ts1);
        s.add(ts2);
        s.add(ts3);
        
        Assert.assertEquals(3, s.getSize());
    }
    
    @Nano
    private static void testPosOfTransBefore() {        
        TransSeq s = new TransSeq();
        TransInfo info1 = newTransInfo(100, 120);
        TransInfo info2 = newTransInfo(200, 220);
        
        s.add(info1);
        s.add(info2);
        
        assertEquals(-1, s.posOfTransBefore(0));
        assertEquals(-1, s.posOfTransBefore(99));
        assertEquals(-1, s.posOfTransBefore(100));
        assertEquals(100, s.posOfTransBefore(101));
        assertEquals(200, s.posOfTransBefore(9999999));
        assertEquals(100, s.posOfTransBefore(160));
    }
    
    @Nano
    private static void testPosOfTransBeforeWithEmptySeq() {
        TransSeq s = new TransSeq();
        assertEquals(-1, s.posOfTransBefore(0));
        assertEquals(-1, s.posOfTransBefore(99));
        assertEquals(-1, s.posOfTransBefore(Long.MAX_VALUE));
        assertEquals(-1, s.posOfTransBefore(Long.MIN_VALUE));
    }
    
    @Nano
    public static void testTake1() {
        TransSeq s = new TransSeq();
        
        KeyNode n1 = new KeyNode();
        n1.setDirty(true);
        KeyNode n2 = new KeyNode();
        n2.setDirty(true);
        
        TransInfo info1 = newTransInfo(100, 120, n1);
        TransInfo info2 = newTransInfo(200, 220, n2);
        
        s.add(info1);
        s.add(info2);
        
        final ArrayList<INode> nodes = new ArrayList<INode>();
        
        TransNodesForMe transNodes = new TransNodesForMe() {
            public void addTopNode(TopNode node) {
                nodes.add(node);
            }

            public void addKeyNode(KeyNode node) {
                nodes.add(node);
            }
        };
        
        s.take(99, transNodes);
        Assert.assertEquals(0, nodes.size());
        
        s.take(100, transNodes);
        Assert.assertEquals(1, nodes.size());
        Assert.assertTrue(nodes.contains(n1));
        
        s.take(200, transNodes);
        Assert.assertEquals(2, nodes.size());
        Assert.assertTrue(nodes.get(0) == n1);
        Assert.assertTrue(nodes.get(1) == n2);
        Assert.assertTrue(s.isEmpty());
    }
    
    @Nano
    public static void testTake2() {
        TransSeq s = new TransSeq();
        KeyNode n1 = new KeyNode();
        n1.setDirty(true);
        KeyNode n2 = new KeyNode();
        n2.setDirty(true);
        TransInfo info1 = newTransInfo(100, 120, n1);
        TransInfo info2 = newTransInfo(200, 220, n2);
        
        s.add(info1);
        s.add(info2);
        
        final ArrayList<INode> nodes = new ArrayList<INode>();
        
        TransNodesForMe transNodes = new TransNodesForMe() {
            public void addTopNode(TopNode node) {
                nodes.add(node);
            }

            public void addKeyNode(KeyNode node) {
                nodes.add(node);
            }
        };
        
        s.take(200, transNodes);
        Assert.assertEquals(2, nodes.size());
        Assert.assertTrue(nodes.get(0) == n1);
        Assert.assertTrue(nodes.get(1) == n2);
        Assert.assertTrue(s.isEmpty());
    }
}
