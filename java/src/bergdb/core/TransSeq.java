package bergdb.core;

import java.util.ArrayList;
import java.util.zip.CRC32;
import bergdb.common.MyChecksum;
import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.nanotest.Assert;
import static bergdb.nanotest.Assert.*;
import bergdb.nanotest.Nano;

/**
 * An in-memory data structure that keeps information about the transactions
 * of the startup section of the database stream.
 * In particular, it is a collection of all dirty nodes with information 
 * about for which transaction they got dirty.
 * 
 * The algorithm for updating startup pos is included in this.take().
 * 
 * One theory documents, the D data structure corresponds to TransSeq.
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
     * Also computes a new startup pos (sp).
     * 
     * @param currentSp  Current startup pos (sp).
     * @param maxSp  Maximum currently allowed startup pos (sp).
     * @param valueCount  Number of value nodes in the current transaction.
     * @param transNodes  Output parameters; nodes are added to transNodes.
     * @return The new startup pos (sp).
     */
    public long take(long currentSp, long maxSp, 
            final int valueCount, final long kvSize, 
            final TransNodesForMe transNodes) {
        return take(currentSp, maxSp, valueCount, kvSize, transNodes, Long.MAX_VALUE);
    }
    
    /**
     * As take() above, and takes nodes for at most 'maxBytes' bytes of the record (2026-10-21,
     * bergdb 005-17): a node counts its size in the stream and 16 bytes, for its entry in the
     * got-dirty list if it is still dirty. The transactions are taken whole; the first that
     * does not fit is not taken, also when fewer than two are. It matters for records near
     * the record limit only (StoredTrans.recordLimit).
     */
    public long take(long currentSp, long maxSp, 
            final int valueCount, final long kvSize, 
            final TransNodesForMe transNodes, final long maxBytes) {
        //
        // Takes nodes from TransSeq queue until 1. the queue is empty, or 2. the maxSp would be
        // exceed if we would continue, or 3. the index node limit has been reached.
        // The index node limit (nodeCountLimit) is used for some fairness. Large kv transactions
        // should include more index nodes that small kv transactions.
        // Since we always process 2 transaction before considering the limit, the startup
        // pos updates should never fall exceedingly behind.
        //
        // TODO D. Consider / test: increase nodeCountLimit by a factor (of 4.0 perhaps) 
        // if startup pos is falling behind (with more than 2.0 * startupDistance perhaps).
        //
        
        long newSp = currentSp;
        int nodeCount = 0;
        int transCount = 0;
        
        if (isEmpty()) {
            return newSp;
        }
        
        final int nodeCountLimit = nodeCountLimit(valueCount, kvSize);
        
        long bytes = 0;
        
        while (first != null 
                && first.tpos <= maxSp 
                && (nodeCount < nodeCountLimit || transCount < 2)) {
            
            if (maxBytes != Long.MAX_VALUE) {
                final long cost = recordBytes(first);
                if (bytes + cost > maxBytes) {
                    break;
                }
                bytes += cost;
            }
            
            newSp = first.tpos;
            
            for (Node node : first.gotDirtyNodes) {
                int type = node.getType();
                
                switch (type) {
                case Node.TYPE_TOP_NODE:
                    transNodes.addTopNode((TopNode) node);
                    nodeCount++;
                    break;
                case Node.TYPE_KEY_NODE:
                    transNodes.addKeyNode((KeyNode) node);
                    nodeCount++;
                    break;
                }
                
                assert node.isIndexNode() : "non-index node in trans seq, " + node.toString();
            }
            
            transCount++;
            
            first = first.next;
            size -= 1;
        }
        
        if (first == null) {
            // To avoid a potential memory leak
            last = null;
        }
        
        return newSp;
    }
    
    /**
     * The index nodes take() takes, after the first two transactions. In long (2026-10-21,
     * bergdb 005-21): valueCount * 4 was an int product.
     */
    static int nodeCountLimit(int valueCount, long kvSize) {
        final long limit = valueCount * 4L + kvSize / 1024;
        return limit > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) limit;
    }
    
    /** The bytes the got-dirty nodes of 'info' may add to a record; see take(). */
    private static long recordBytes(TransInfo info) {
        long bytes = 0;
        for (Node node : info.gotDirtyNodes) {
            switch (node.getType()) {
            case Node.TYPE_TOP_NODE:
                bytes += StoredTopNode.getByteSize((TopNode) node) + 16;
                break;
            case Node.TYPE_KEY_NODE:
                bytes += StoredKeyNode.getByteSize((KeyNode) node) + 16;
                break;
            }
        }
        return bytes;
    }
    
    /**
     * Computes and returns a checksum of the TransSeq state.
     */
    public long checksum() {
        MyChecksum sum = new MyChecksum(new CRC32());
        sum.updateWithLong(this.size);
        
        TransInfo info = first;
        while (info != null) {
            sum.updateWithLong(info.lastPos);
            sum.updateWithLong(info.tt);
            sum.updateWithLong(info.tpos);
            sum.updateWithLong(info.startupPos);
            
            for (Node node : info.gotDirtyNodes) {
                sum.update(node.getType());
                sum.updateWithLong(node.getId());
            }
            
            info = info.next;
        }
        
        return sum.getValue();
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
            for (Node node : info.gotDirtyNodes) {
                visitor.node(node, info.tpos, info.lastPos);
            }
            info = info.next;
        }
    }
    
    /**
     * Information about a transaction and a linked-list pointer.
     */
    public static class TransInfo implements NodeSink {
        TransInfo next = null;
        
        /** Transaction stream position. */
        public long tpos;
        
        /** Last stream position of the transaction. */
        public long lastPos;
        
        public long tt;
        
        public long startupPos;
        
        /** Index nodes that got dirty while the transaction executed. */
        public ArrayList<Node> gotDirtyNodes = new ArrayList<Node>();

        TransInfo() {}
        
        public void addGotDirtyNode(Node node) {
            gotDirtyNodes.add(node);
        }
        
        public String toString() {
            return "tt:" + tt + ", tpos:" + tpos + ", gotDirtyCount:" + gotDirtyNodes.size();
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
         * @param lastTpos  Last pos of the transaction.
         */
        public void node(Node node, long tpos, long lastTpos);
    }
    
    public static interface NodeSink {
        public void addGotDirtyNode(Node node);
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
    private static TransInfo newTransInfo(long tpos, long lastPos, Node node) {
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
        
        final ArrayList<Node> nodes = new ArrayList<Node>();
        
        TransNodesForMe transNodes = new TransNodesForMe() {
            public void addTopNode(TopNode node) {
                nodes.add(node);
            }

            public void addKeyNode(KeyNode node) {
                nodes.add(node);
            }
        };
        
        s.take(0, 99, Integer.MAX_VALUE, Integer.MAX_VALUE, transNodes);
        Assert.assertEquals(0, nodes.size());
        
        s.take(0, 100, Integer.MAX_VALUE, Integer.MAX_VALUE, transNodes);
        Assert.assertEquals(1, nodes.size());
        Assert.assertTrue(nodes.contains(n1));
        
        s.take(0, 200, Integer.MAX_VALUE, Integer.MAX_VALUE, transNodes);
        Assert.assertEquals(2, nodes.size());
        Assert.assertTrue(nodes.get(0) == n1);
        Assert.assertTrue(nodes.get(1) == n2);
        Assert.assertTrue(s.isEmpty());
    }
    
    /** bergdb 005-21: the node count limit does not wrap. */
    @Nano
    public static void testNodeCountLimit() {
        assertEquals(4 + 1, nodeCountLimit(1, 1024));
        assertEquals(Integer.MAX_VALUE, nodeCountLimit(Integer.MAX_VALUE, Integer.MAX_VALUE));
        assertEquals(Integer.MAX_VALUE, nodeCountLimit(600 * 1000 * 1000, 0));   // wrapped
    }
    
    /** take() with a byte budget (bergdb 005-17): whole transactions, as many as fit. */
    @Nano
    public static void testTakeWithBudget() {
        TransSeq s = new TransSeq();
        KeyNode n1 = new KeyNode();
        KeyNode n2 = new KeyNode();
        KeyNode n3 = new KeyNode();
        s.add(newTransInfo(100, 120, n1));
        s.add(newTransInfo(200, 220, n2));
        s.add(newTransInfo(300, 320, n3));
        final long cost = StoredKeyNode.getByteSize(n1) + 16;
        
        final ArrayList<Node> nodes = new ArrayList<Node>();
        TransNodesForMe transNodes = new TransNodesForMe() {
            public void addTopNode(TopNode node) { nodes.add(node); }
            public void addKeyNode(KeyNode node) { nodes.add(node); }
        };
        
        Assert.assertEquals(0, s.take(0, 300, 1, 0, transNodes, cost - 1));
        Assert.assertEquals(0, nodes.size());
        Assert.assertEquals(200, s.take(0, 300, 1, 0, transNodes, 2 * cost + 1));
        Assert.assertEquals(2, nodes.size());
        Assert.assertEquals(300, s.take(200, 300, 1, 0, transNodes, cost));
        Assert.assertEquals(3, nodes.size());
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
        
        final ArrayList<Node> nodes = new ArrayList<Node>();
        
        TransNodesForMe transNodes = new TransNodesForMe() {
            public void addTopNode(TopNode node) {
                nodes.add(node);
            }

            public void addKeyNode(KeyNode node) {
                nodes.add(node);
            }
        };
        
        s.take(0, 200, Integer.MAX_VALUE, Integer.MAX_VALUE, transNodes);
        Assert.assertEquals(2, nodes.size());
        Assert.assertTrue(nodes.get(0) == n1);
        Assert.assertTrue(nodes.get(1) == n2);
        Assert.assertTrue(s.isEmpty());
    }
}
