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
 * that belongs to the startup section of the database stream.
 * The information is needed to be able to append dirty nodes to the end of the
 * stream so they will not become too dirty.
 * 
 * The algorithm for updating startup pos is included in this.take().
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
        
        final long nodeCountLimitLong = valueCount * 4 + kvSize / 1024;
        final int nodeCountLimit = nodeCountLimitLong > Integer.MAX_VALUE ? 
                Integer.MAX_VALUE : (int) nodeCountLimitLong;
        
        while (first != null 
                && first.tpos <= maxSp 
                && (nodeCount < nodeCountLimit || transCount < 2)) {
            
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
    
    public String print() {
        StringBuilder b = new StringBuilder();
        b.append("======== TransSeq ========\n");
        b.append("size: " + this.size + "\n");
        
        TransInfo info = this.first;
        
        while (info != null) {
            b.append("---- TransInfo tt " + info.tt + " ----\n");
            b.append("tpos: " + info.tpos + "\n");
            b.append("startupPos: " + info.startupPos + "\n");
            printDirty(b, info);            
            info = info.next;
        }
        
        return b.toString();
    }
    
    private void printDirty(StringBuilder b, TransInfo info) {
        b.append("gotDirty: ");
        for (Node node : info.gotDirtyNodes) {
            b.append(node + "; ");
        }
        b.append("\n");
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
        
        public void addDirtyNode(Node node) {
            gotDirtyNodes.add(node);
        }
        
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
                for (Node n : gotDirtyNodes) {
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
         * @param lastTpos  Last pos of the transaction.
         */
        public void node(Node node, long tpos, long lastTpos);
    }
    
    public static interface NodeSink {
        public void addDirtyNode(Node node);
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
