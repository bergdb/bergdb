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
    private long dirtyCount;     // D: the got-dirty nodes of the transactions, for take()
    private long ownBytes;       // O: the own bytes of their records, ownBytes()
    
    public boolean isEmpty() {
        return first == null;
    }
    
    /** The last transaction, or null; for tests (bergdb 005-31). */
    TransInfo last() {
        return last;
    }
    
    /**
     * The span of the transactions: from the tpos of the oldest to that of the newest, or 0.
     * The deadline of take() is at least the span (bergdb 007-07).
     */
    long span() {
        return first == null ? 0 : last.tpos - first.tpos;
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
        dirtyCount += info.gotDirtyNodes.size();
        ownBytes += info.ownBytes;
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
     * Takes dirty index nodes from the trans seq and adds them to trans nodes: whole
     * transactions, oldest first, as many as the record's share and the deadline ask for
     * (2026-10-27, bergdb 005-49 and 007-03, step 3). Returns the new startup pos (sp), the
     * tpos of the last transaction taken.
     * 
     * <p>The share. The record takes its part of D, the got-dirty nodes of the transactions
     * of the startup section, in proportion to the stream it adds:</p>
     * 
     * <pre>
     *     share = D * (o / O) * (S / sd)
     * </pre>
     * 
     * <p>where o is the record's own bytes (ownBytes()), O the own bytes of the records of
     * the section's transactions, S the length of the section, from the current startup pos
     * to the end of the stream, and sd the startup distance's setting, the target size of
     * the section. o * S / O estimates the stream that the record adds before its index
     * nodes are known: a record that adds a thousandth of sd takes a thousandth of D, so the
     * index nodes a commit writes follow its own size, up to one transaction more (bergdb
     * 010, P4). D / O is the rate at which the section's commits made nodes dirty. At that
     * rate a commit writes as many nodes as it makes dirty while the section is sd long,
     * more while it is longer, fewer while it is shorter; so the actual startup distance,
     * such that the stream's length minus it is the startup pos, stays near the setting.</p>
     * 
     * <p>The transactions that fit in the share are taken. The next, of which only a part
     * fits, is taken if that part is larger than a number in [0, 1) hashed from the stream's
     * length (dither()), so that a record takes its share on average. Without the hash, a
     * record that takes about one transaction leaves a band of 0.7 to 1.5 sd where the
     * section does not move (005-49, section 5).</p>
     * 
     * <p>The deadline (D1 of bergdb 007-01, D4 of 007-03): a transaction that begins d or
     * more before the end of the stream is taken whatever the share, where d is the larger
     * of d_h = 2 * sd and the span of the section's transactions, from the tpos of the
     * oldest to that of the newest. While the span is below d_h, d = d_h, and the take keeps
     * up with d_h, as T3 asks (007-01, section 3), also where the pace falls behind. After a
     * decrease of the setting, the pace uses the new setting at once, but the deadline does
     * not jump to the new d_h, which would write most of D in one record (007-06, section
     * 3): d starts at the span and comes down with it. A record takes every transaction that
     * begins within the last record's length of the oldest, so the span shrinks with every
     * record until it is below d_h (2026-10-28, bergdb 007-07).</p>
     * 
     * <p>D, O and the span are taken from the transactions of the startup section, which a
     * start reruns (DbStarter), and the hash is a function of the stream, so the stream does
     * not depend on restarts (010, P2).</p>
     * 
     * <p>The taken nodes add at most 'maxBytes' bytes to the record (2026-10-21, bergdb
     * 005-17): a node counts its size in the stream and 16 bytes, for its entry in the
     * got-dirty list if it is still dirty. The first transaction that does not fit is not
     * taken, also after the deadline. It matters for records near the record limit only
     * (StoredTrans.recordLimit).</p>
     * 
     * @param currentSp  Current startup pos (sp).
     * @param streamLength  The length of the stream before the record.
     * @param startupDistance  The startup distance's setting, sd.
     * @param recordOwnBytes  The record's own bytes, ownBytes().
     * @param transNodes  Output parameters; nodes are added to transNodes.
     * @param maxBytes  The most bytes that the taken nodes may add to the record.
     * @return The new startup pos (sp).
     */
    public long take(long currentSp, long streamLength, int startupDistance, 
            long recordOwnBytes, final TransNodesForMe transNodes, final long maxBytes) {
        long newSp = currentSp;
        
        if (isEmpty()) {
            return newSp;
        }
        
        assert ownBytes > 0 : ownBytes;     // every record has own bytes, see ownBytes()
        // The deadline: d_h, or the span of the section's transactions while it is longer.
        final long hardSp = streamLength - Math.max(2L * startupDistance, span());
        final double share = (double) dirtyCount * recordOwnBytes / ownBytes 
                * (streamLength - currentSp) / startupDistance;
        final double u = dither(streamLength);
        
        long taken = 0;
        long bytes = 0;
        
        while (first != null) {
            final int count = first.gotDirtyNodes.size();
            
            // Before the deadline, a transaction that does not fit in what is left of the
            // share is taken if the part that fits is larger than u.
            if (first.tpos > hardSp && taken + count > share && share - taken <= u * count) {
                break;
            }
            
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
                    break;
                case Node.TYPE_KEY_NODE:
                    transNodes.addKeyNode((KeyNode) node);
                    break;
                }
                
                assert node.isIndexNode() : "non-index node in trans seq, " + node.toString();
            }
            
            taken += count;
            dirtyCount -= count;
            ownBytes -= first.ownBytes;
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
     * The own bytes of a record, which pace take() (bergdb 005-49): its value nodes, and
     * 48 bytes for its header, end marker, got-dirty count, last byte and alignment
     * (StoredTrans); not its index nodes and got-dirty list, which follow from the take.
     * A start computes the same from the record (DbStarter).
     */
    static long ownBytes(long valueBytes) {
        return 48 + valueBytes;
    }
    
    /**
     * A number in [0, 1) hashed from a stream position, for take() (bergdb 005-49): the
     * finalizer of SplitMix64. A product with a constant alone, as 005-49's prototype had,
     * turns a step of the stream into a fixed step of the number; since what a record takes
     * changes its size, records then took more than their share, up to 30 percent with
     * transactions of one put (bergdb 007-03, step 3).
     */
    static double dither(long pos) {
        long z = pos * 0x9E3779B97F4A7C15L;
        z = (z ^ (z >>> 30)) * 0xBF58476D1CE4E5B9L;
        z = (z ^ (z >>> 27)) * 0x94D049BB133111EBL;
        return ((z ^ (z >>> 31)) >>> 11) * 0x1.0p-53;
    }
    
    /** The bytes the got-dirty nodes of 'info' may add to a record; see take(). */
    static long recordBytes(TransInfo info) {
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
        sum.updateWithLong(this.dirtyCount);
        sum.updateWithLong(this.ownBytes);
        
        TransInfo info = first;
        while (info != null) {
            sum.updateWithLong(info.lastPos);
            sum.updateWithLong(info.tt);
            sum.updateWithLong(info.tpos);
            sum.updateWithLong(info.startupPos);
            sum.updateWithLong(info.ownBytes);
            
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
        
        /** The own bytes of its record, TransSeq.ownBytes() (bergdb 005-49). */
        public long ownBytes;
        
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
        info.ownBytes = ownBytes(0);
        return info;
    }
    
    /** Test TransInfo object with one node. */
    private static TransInfo newTransInfo(long tpos, long lastPos, Node node) {
        TransInfo info = new TransInfo();
        info.tpos = tpos;
        info.lastPos = lastPos;
        info.tt = -1;
        info.ownBytes = ownBytes(0);
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
        
        // The deadline alone: a record of no own bytes has no share. With sd 50, d_h = 100.
        s.take(0, 199, 50, 0, transNodes, Long.MAX_VALUE);
        Assert.assertEquals(0, nodes.size());
        
        s.take(0, 200, 50, 0, transNodes, Long.MAX_VALUE);
        Assert.assertEquals(1, nodes.size());
        Assert.assertTrue(nodes.contains(n1));
        
        s.take(0, 300, 50, 0, transNodes, Long.MAX_VALUE);
        Assert.assertEquals(2, nodes.size());
        Assert.assertTrue(nodes.get(0) == n1);
        Assert.assertTrue(nodes.get(1) == n2);
        Assert.assertTrue(s.isEmpty());
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
        
        // All three are past the deadline, d_h = 300, longer than their span, 200, and have
        // no share; the budget decides.
        Assert.assertEquals(0, s.take(0, 600, 150, 0, transNodes, cost - 1));
        Assert.assertEquals(0, nodes.size());
        Assert.assertEquals(200, s.take(0, 600, 150, 0, transNodes, 2 * cost + 1));
        Assert.assertEquals(2, nodes.size());
        Assert.assertEquals(300, s.take(200, 600, 150, 0, transNodes, cost));
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
        
        s.take(0, 300, 50, 0, transNodes, Long.MAX_VALUE);
        Assert.assertEquals(2, nodes.size());
        Assert.assertTrue(nodes.get(0) == n1);
        Assert.assertTrue(nodes.get(1) == n2);
        Assert.assertTrue(s.isEmpty());
    }
    
    /** A transaction with 'count' got-dirty key nodes and a record of 'ownBytes' (005-49). */
    private static TransInfo paceInfo(long tpos, int count, long ownBytes) {
        TransInfo info = newTransInfo(tpos, tpos + 99);
        info.ownBytes = ownBytes;
        for (int i = 0; i < count; i++) {
            KeyNode n = new KeyNode();
            n.setDirty(true);
            info.gotDirtyNodes.add(n);
        }
        return info;
    }
    
    private static final TransNodesForMe IGNORE = new TransNodesForMe() {
        public void addTopNode(TopNode node) {}
        public void addKeyNode(KeyNode node) {}
    };
    
    /** Ten transactions from 'tpos', 100 apart, of 10 got-dirty nodes and 100 own bytes. */
    private static TransSeq paceSeq(long tpos) {
        TransSeq s = new TransSeq();
        for (int i = 0; i < 10; i++) {
            s.add(paceInfo(tpos + 100 * i, 10, 100));
        }
        return s;
    }
    
    /**
     * The share (bergdb 005-49): the transactions that fit, and the next with the
     * probability of the part that fits.
     */
    @Nano
    public static void testShare() {
        // D = 100 nodes, O = 1000 bytes. A record of 100 own bytes, a section of 2000 and sd
        // 800: a share of 100 * 100 / 1000 * 2000 / 800 = 25 nodes, two transactions and
        // half of the third, which is taken if the hash of the stream's length is below 0.5.
        Assert.assertEquals(0.4056, dither(1300), 1e-4);
        Assert.assertEquals(0.9944, dither(1200), 1e-4);
        TransSeq s = paceSeq(0);
        Assert.assertEquals(200, s.take(1300 - 2000, 1300, 800, 100, IGNORE, Long.MAX_VALUE));
        Assert.assertEquals(7, s.getSize());
        s = paceSeq(0);
        Assert.assertEquals(100, s.take(1200 - 2000, 1200, 800, 100, IGNORE, Long.MAX_VALUE));
        Assert.assertEquals(8, s.getSize());
        
        // Half the section, half the share: 12.5 nodes, one transaction and a quarter of
        // the next, which the hash 0.41 does not take.
        s = paceSeq(0);
        Assert.assertEquals(0, s.take(1300 - 1000, 1300, 800, 100, IGNORE, Long.MAX_VALUE));
        Assert.assertEquals(9, s.getSize());
        
        // On average a record takes its share, 2.5 transactions, also when what it takes
        // decides the length of the stream, and so the hash, for the next record. Here a
        // record is 400 bytes and 104 for each transaction taken. With the hash of 005-49's
        // prototype, a product with a constant only, records took 2.85 transactions.
        long transactions = 0;
        long length = 8000000;
        for (int i = 0; i < 10000; i++) {
            s = paceSeq(length - 1500);
            s.take(length - 2000, length, 800, 100, IGNORE, Long.MAX_VALUE);
            final int taken = 10 - s.getSize();
            transactions += taken;
            length += 400 + 104 * taken;
        }
        Assert.assertEquals(2.5, transactions / 10000.0, 0.02);
    }
    
    /**
     * The deadline (bergdb 007-03, step 3): a transaction that begins d_h = 2 * sd or more
     * before the end of the stream is taken whatever the share; or, while the span of the
     * transactions is longer than d_h, one that begins the span or more before the end (D4,
     * bergdb 007-07).
     */
    @Nano
    public static void testDeadline() {
        TransSeq s = new TransSeq();
        for (int i = 0; i < 5; i++) {
            s.add(paceInfo(100 * i, 1000, 100));
        }
        // A record of 1 own byte: a share of 5000 * 1 / 500 * 801 / 250 = 32 nodes, less
        // than a transaction. With sd 250, d_h = 500, longer than the span, 400, takes the
        // transactions at 0 to 300, 800 to 500 before the end; the one at 400 waits.
        Assert.assertEquals(300, s.take(-1, 800, 250, 1, IGNORE, Long.MAX_VALUE));
        Assert.assertEquals(1, s.getSize());
        Assert.assertEquals(400, s.first.tpos);
        
        // With sd 100, d_h = 200 is shorter than the span: the deadline is at the span. It
        // takes the transactions at 0 and 100, 500 and 400 before the end, not those to 300.
        s = new TransSeq();
        for (int i = 0; i < 5; i++) {
            s.add(paceInfo(100 * i, 1000, 100));
        }
        Assert.assertEquals(100, s.take(-1, 500, 100, 1, IGNORE, Long.MAX_VALUE));
        Assert.assertEquals(3, s.getSize());
    }
    
    /**
     * The deadline after a decrease of the setting, alone (bergdb 007-07): records of no own
     * bytes have no share. Transactions 100 apart, from 0 to 1900, records of 100 bytes, and
     * sd 100, so d_h = 200. Each record takes the transactions that begin within the last
     * record's length of the oldest, two, not the 19 that begin d_h or more before the end;
     * so the span shrinks by a record each time until it is below d_h, and then the deadline
     * is at d_h.
     */
    @Nano
    public static void testDeadlineAfterDecrease() {
        TransSeq s = new TransSeq();
        for (int i = 0; i < 20; i++) {
            s.add(paceInfo(100 * i, 10, 100));
        }
        long length = 2000;
        long sp = -1;
        for (int i = 0; i < 40; i++) {
            final long span = s.span();
            final int size = s.getSize();
            sp = s.take(sp, length, 100, 0, IGNORE, Long.MAX_VALUE);
            if (span >= 200) {
                Assert.assertEquals("i=" + i, size - 2, s.getSize());
            }
            s.add(paceInfo(length, 10, 100));
            Assert.assertTrue("i=" + i, s.first.tpos > length - Math.max(200, span));
            if (span >= 200) {
                Assert.assertEquals("i=" + i, span - 100, s.span());
            }
            length += 100;
        }
        Assert.assertEquals(100, s.span());
        Assert.assertEquals(2, s.getSize());
    }
    
    /**
     * A decrease of the setting (bergdb 007-03, D4; 007-07): the pace uses the new setting
     * at once, and the deadline, at the span of the transactions while that is longer than
     * twice the new setting, takes no more than a record's length of the section. So no
     * record takes more than its share, and the span shrinks with every record until it is
     * below twice the setting. Records of 1000 own bytes and 100 bytes for each node taken,
     * each a transaction of 10 got-dirty nodes, at sd 100000 and then 25000. With the
     * deadline at twice the new setting at once, the record at the decrease took 250 nodes,
     * and the next three 130, 70 and 40.
     */
    @Nano
    public static void testDecrease() {
        final int[] taken = new int[1];
        final TransNodesForMe counter = new TransNodesForMe() {
            public void addTopNode(TopNode node) { taken[0]++; }
            public void addKeyNode(KeyNode node) { taken[0]++; }
        };
        TransSeq s = new TransSeq();
        long length = 0;
        long sp = -1;
        int sd = 100000;
        int below = -1;
        for (int i = 0; i < 1300; i++) {
            if (i == 1000) {
                sd = 25000;
            }
            final long span = s.span();
            taken[0] = 0;
            sp = s.take(sp, length, sd, 1000, counter, Long.MAX_VALUE);
            s.add(paceInfo(length, 10, 1000));
            
            // The deadline, at the span while that is longer than 2 * sd: the span shrinks.
            Assert.assertTrue("i=" + i, s.first.tpos > length - Math.max(2L * sd, span));
            if (span >= 2L * sd) {
                Assert.assertTrue("i=" + i, s.span() < span);
            }
            length += 1000 + 100 * taken[0];
            
            // At the decrease the section is 100000, so the share is 500 * 1000 / 50000 *
            // 100000 / 25000 = 40 nodes, and it shrinks with the section.
            if (i >= 1000) {
                Assert.assertTrue("i=" + i + ", " + taken[0], taken[0] <= 40);
                if (below < 0 && s.span() < 2L * sd) {
                    below = i - 1000;
                }
            }
        }
        Assert.assertTrue("below 2 sd after " + below, below >= 0 && below <= 20);
        Assert.assertEquals(25000, length - sp, 5000);
    }
    
    /**
     * The sums of the pace are those of the transactions left, so a start, which adds the
     * transactions of the startup section again, has the same sums and checksum (bergdb
     * 005-49; 010, P2).
     */
    @Nano
    public static void testSumsAfterTake() {
        TransSeq s = new TransSeq();
        for (int i = 0; i < 6; i++) {
            s.add(paceInfo(100 * i, i + 1, 50 + 10 * i));
        }
        // d_h = 520, longer than the span, 500, takes the transactions at 0 to 300.
        Assert.assertEquals(300, s.take(-1, 820, 260, 1, IGNORE, Long.MAX_VALUE));
        
        TransSeq r = new TransSeq();
        for (TransInfo a = s.first; a != null; a = a.next) {
            TransInfo b = newTransInfo(a.tpos, a.lastPos, a.tt);
            b.startupPos = a.startupPos;
            b.ownBytes = a.ownBytes;
            b.gotDirtyNodes = a.gotDirtyNodes;
            r.add(b);
        }
        Assert.assertEquals(2, r.getSize());
        Assert.assertEquals(5 + 6, r.dirtyCount);
        Assert.assertEquals(90 + 100, r.ownBytes);
        Assert.assertEquals(r.dirtyCount, s.dirtyCount);
        Assert.assertEquals(r.ownBytes, s.ownBytes);
        Assert.assertEquals(r.checksum(), s.checksum());
    }
}
