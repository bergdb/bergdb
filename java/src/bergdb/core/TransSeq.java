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
    
    /**
     * The cap c of the share's factor S / sd in take() (bergdb 024-31, 015-84): the share
     * counts the span of the section's transactions, from the tpos of the oldest to that of
     * the newest, as at most c * sd, so S is replaced by S - max(0, span - c * sd)
     * (shareSection()). After a decrease of the setting with one call, S is still the old
     * section, and S / sd starts at the old setting over the new one, 10 from 1000 to 100
     * MB: without the cap the commits of the catch-up wrote records of 13 to 15 MB at 50M
     * keys, 12 to 14 times the new mean (bergdb 007-07, section 11.2; OP4 of 024-05). With
     * it a record's share is at most about c times the one it would have with the section
     * at sd. With a constant setting the span is below 2 * sd (T3), so with c = 2 the cap
     * never binds and the stream is as without it; it binds only while the span is over
     * 2 * sd after a decrease, when the deadline is at the span. The deadline is unchanged:
     * it still takes every transaction that begins at the span or more before the end, so
     * the section shrinks with every record until it is below 2 * sd (bergdb 007-07, section
     * 10.4). T3 holds for every pace (bergdb 007-08).
     */
    static final int SHARE_FACTOR_CAP = 2;
    
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
     *     share = D * (o / O) * (S' / sd),   S' = S - max(0, span - c * sd)
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
     * such that the stream's length minus it is the startup pos, stays near the setting.
     * S' is S with the span of the section's transactions counted as at most c * sd, c =
     * SHARE_FACTOR_CAP (shareSection(), bergdb 024-31): after a decrease of the setting the
     * factor S' / sd is at most about c, not the old setting over the new one, so no commit
     * of the catch-up writes many times the share of a section at the setting. With a
     * constant setting the span is below 2 * sd and S' = S.</p>
     * 
     * <p>The share is computed in integers, once per take (bergdb 005-79; in doubles from
     * 2026-10-28, b8ac8a1, until then; 2026.1 had no pace): in units of 2^-16 of a node,
     * shareFp = floor(D o S 2^16 / (O sd)), at most D 2^16, with one rounding (shareFp()). Its
     * bounds: o is below 2^31 (the record limit, StoredTrans.valueLimit), sd from 10 to
     * 2^31 - 1, and O at least 48 when D has a transaction. Nothing in the code bounds D and S,
     * so shareFp() checks D < 2^32 and S < 2^47 (128 TB) itself; beyond them the share is all
     * of D, and the take takes every transaction before the deadline, as it does after it. T3
     * holds for every pace (bergdb 007-08), so this cannot break the bound. Within them D o
     * and S 2^16 are below 2^63, and their product is divided in 128 bits.</p>
     * 
     * <p>The transactions that fit in the share are taken. The next, of which only a part
     * fits, is taken if that part is larger than a number u in [0, 1) hashed from the
     * stream's length (ditherFp(), u = uFp / 2^16), so that a record takes its share on
     * average. Without the hash, a record that takes about one transaction leaves a band of
     * 0.7 to 1.5 sd where the section does not move (005-49, section 5). In integers, before
     * the deadline, the take stops at a transaction of count nodes, after taken nodes, if
     * ((taken + count) << 16) > shareFp and shareFp - (taken << 16) <= uFp * count. With
     * taken + count at most D < 2^32, shareFp at most D 2^16, uFp below 2^16 and count below
     * 2^31, no term reaches 2^49. Beyond the bounds shareFp is Long.MAX_VALUE, and the first
     * test is false.</p>
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
     * <p>The taken nodes also stay within the room of the record's got-dirty set, 'room', if
     * it is not null (bergdb 031-06, review-main, R2; SetRoom): every taken node counted as
     * one that the take keeps dirty, at its largest. The first transaction that does not fit
     * in it is not taken either, also after the deadline.</p>
     * 
     * @param currentSp  Current startup pos (sp).
     * @param streamLength  The length of the stream before the record.
     * @param startupDistance  The startup distance's setting, sd.
     * @param recordOwnBytes  The record's own bytes, ownBytes().
     * @param transNodes  Output parameters; nodes are added to transNodes.
     * @param maxBytes  The most bytes that the taken nodes may add to the record.
     * @param room  The room of the record's got-dirty set, which the take reduces; or null.
     * @return The new startup pos (sp).
     */
    long take(long currentSp, long streamLength, int startupDistance, 
            long recordOwnBytes, final TransNodesForMe transNodes, final long maxBytes,
            final SetRoom room) {
        long newSp = currentSp;
        
        if (isEmpty()) {
            return newSp;
        }
        
        assert ownBytes > 0 : ownBytes;     // every record has own bytes, see ownBytes()
        // The deadline: d_h, or the span of the section's transactions while it is longer.
        final long hardSp = streamLength - Math.max(2L * startupDistance, span());
        // The share and the dither in units of 2^-16 (bergdb 005-79).
        final long share = shareFp(dirtyCount, recordOwnBytes, ownBytes, 
                shareSection(streamLength - currentSp, span(), startupDistance), startupDistance);
        final long u = ditherFp(streamLength);
        
        long taken = 0;
        long bytes = 0;
        
        while (first != null) {
            final int count = first.gotDirtyNodes.size();
            
            // Before the deadline, a transaction that does not fit in what is left of the
            // share is taken if the part that fits is larger than u. In units of 2^-16.
            if (first.tpos > hardSp && ((taken + count) << 16) > share 
                    && share - (taken << 16) <= u * count) {
                break;
            }
            
            if (maxBytes != Long.MAX_VALUE) {
                final long cost = recordBytes(first);
                if (bytes + cost > maxBytes) {
                    break;
                }
                bytes += cost;
            }
            if (room != null && !room.take(first)) {
                break;
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
    
    /** take() with no room of the record's set: the tests' and the stress tests' take. */
    public long take(long currentSp, long streamLength, int startupDistance, 
            long recordOwnBytes, final TransNodesForMe transNodes, final long maxBytes) {
        return take(currentSp, streamLength, startupDistance, recordOwnBytes, transNodes,
                maxBytes, null);
    }
    
    /**
     * The take of the empty record of a call of Db.maintain() (bergdb 024-32, section 2.2,
     * M4), after its share (take()): the oldest transactions, whole, as take() takes them,
     * while the startup pos is below 'target', a position that reclaim waits for (an
     * iteration's pEnd or pSafe, each the tpos of a transaction of the section), until the
     * taken nodes reach 'budget' bytes; the first transaction is taken whatever its size,
     * so that each call moves the startup pos. A node counts as in take(). The first
     * transaction that does not fit in 'maxBytes', the room left in the record, or in 'room',
     * what the share's take left of the room of the record's got-dirty set (take(); bergdb
     * 031-06, review-main, R2), is not taken. A take beyond the share is allowed by the
     * model, whose take policy has the deadline and any pace (lean/SIS/Bound.lean,
     * takePolicy; T3 holds for every pace).
     * 
     * @return The new startup pos, the tpos of the last transaction taken, or currentSp if
     *      none is taken.
     */
    long takeTo(long currentSp, long target, long budget, final TransNodesForMe transNodes,
            long maxBytes, final SetRoom room) {
        long newSp = currentSp;
        long bytes = 0;
        
        while (first != null && newSp < target) {
            final long cost = recordBytes(first);
            if (newSp != currentSp && bytes + cost > budget || bytes + cost > maxBytes) {
                break;
            }
            if (room != null && !room.take(first)) {
                break;
            }
            bytes += cost;
            newSp = first.tpos;
            
            for (Node node : first.gotDirtyNodes) {
                if (node.getType() == Node.TYPE_TOP_NODE) {
                    transNodes.addTopNode((TopNode) node);
                } else if (node.getType() == Node.TYPE_KEY_NODE) {
                    transNodes.addKeyNode((KeyNode) node);
                }
                assert node.isIndexNode() : "non-index node in trans seq, " + node.toString();
            }
            
            dirtyCount -= first.gotDirtyNodes.size();
            ownBytes -= first.ownBytes;
            first = first.next;
            size -= 1;
        }
        
        if (first == null) {
            last = null;
        }
        
        return newSp;
    }
    
    /**
     * The section that take()'s share counts (bergdb 024-31): S - max(0, span - c * sd), c =
     * SHARE_FACTOR_CAP, where S is the section, from the startup pos to the end of the
     * stream, and span the span of the section's transactions, at most S. It is S while the
     * span is at most c * sd, so always with a constant setting (T3: the span is below
     * 2 * sd); after a decrease, (S - span) + c * sd, the records at the section's two ends
     * and c times the setting. The result is at most S, so shareFp()'s bounds hold.
     */
    static long shareSection(long S, long span, int sd) {
        return S - Math.max(0, span - SHARE_FACTOR_CAP * (long) sd);
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
     * A number from 0 to 65,535, in units of 2^-16 a number in [0, 1), hashed from a stream
     * position, for take() (bergdb 005-49): the top 16 bits of SplitMix64's finalizer. A
     * product with a constant alone, as 005-49's prototype had, turns a step of the stream
     * into a fixed step of the number; since what a record takes changes its size, records
     * then took more than their share, up to 30 percent with transactions of one put (bergdb
     * 007-03, step 3). From 2026-10-28 (b8ac8a1) until 005-79 it was a double, the top 53
     * bits times 2^-53; this is its floor times 2^16, exactly (bergdb 005-79).
     */
    static int ditherFp(long pos) {
        long z = pos * 0x9E3779B97F4A7C15L;
        z = (z ^ (z >>> 30)) * 0xBF58476D1CE4E5B9L;
        z = (z ^ (z >>> 27)) * 0x94D049BB133111EBL;
        return (int) ((z ^ (z >>> 31)) >>> 48);
    }
    
    /**
     * The share of take(), floor(D o S 2^16 / (O sd)) at most D 2^16, in units of 2^-16 of
     * a node (bergdb 005-79), in 64-bit integers with a 128-bit product and two divisions of
     * 128 by 64 bits:
     * 
     * <pre>
     *     p = D * o                  below 2^63, as D < 2^32 and o < 2^31
     *     q = S << 16                below 2^63, as S < 2^47
     *     X = p * q                  below 2^126: Math.multiplyHigh and the low product
     *     Y = floor(X / O)           128 by 64 bits
     *     Q = floor(Y / sd)          128 by 64 bits; floor(X / (O sd)) for positive integers
     *     result = min(Q, D << 16)
     * </pre>
     * 
     * <p>The min changes no decision of take(): taken + count is at most D, so its first
     * test is false at D << 16 as at any larger Q. Outside the bounds, D or S not below 2^32
     * and 2^47, o not below 2^31, or O or sd not positive, it returns Long.MAX_VALUE: the
     * share is all of D (see take()). None of these is reached with BergDB's limits.</p>
     * 
     * @param D  The got-dirty nodes of the section's transactions.
     * @param o  The record's own bytes.
     * @param O  The own bytes of the section's records.
     * @param S  The length of the section, from the startup pos to the end of the stream.
     * @param sd  The startup distance's setting.
     */
    static long shareFp(long D, long o, long O, long S, int sd) {
        if (D >>> 32 != 0 || o >>> 31 != 0 || S >>> 47 != 0 || O < 1 || sd < 1) {
            return Long.MAX_VALUE;
        }
        final long p = D * o;
        final long q = S << 16;
        final long xHi = Math.multiplyHigh(p, q);     // the unsigned high word, as p, q >= 0
        final long xLo = p * q;
        // Y = X / O: xHi is below 2^62, so its signed division is the unsigned one.
        final long yHi = xHi / O;
        final long yLo = divlu(xHi % O, xLo, O);
        final long qHi = yHi / sd;
        final long qLo = divlu(yHi % sd, yLo, sd);
        final long max = D << 16;
        return qHi != 0 || Long.compareUnsigned(qLo, max) > 0 ? max : qLo;
    }
    
    /**
     * The quotient of the 128-bit unsigned number u1 2^64 + u0 by v, where u1 < v, both
     * unsigned: below 2^64 then. Hacker's Delight, 2nd edition, section 9-4, divlu, with
     * 64-bit words in two 32-bit digits (bergdb 005-79): v is normalized, shifted left until
     * its top bit is set; each quotient digit is estimated from the top digits and corrected
     * at most twice. The comparisons are unsigned, as the words use all 64 bits.
     */
    private static long divlu(long u1, long u0, long v) {
        assert v != 0 && Long.compareUnsigned(u1, v) < 0 : u1 + ", " + v;
        final long b = 1L << 32;                    // the number base, 32-bit digits
        final int s = Long.numberOfLeadingZeros(v); // 0 to 63
        v <<= s;                                    // normalized
        final long vn1 = v >>> 32, vn0 = v & 0xFFFFFFFFL;
        final long un32 = (u1 << s) | (s == 0 ? 0 : u0 >>> (64 - s));
        final long un10 = u0 << s;
        final long un1 = un10 >>> 32, un0 = un10 & 0xFFFFFFFFL;
        
        long q1 = Long.divideUnsigned(un32, vn1);
        long rhat = Long.remainderUnsigned(un32, vn1);
        while (q1 >= b || Long.compareUnsigned(q1 * vn0, (rhat << 32) + un1) > 0) {
            q1--;
            rhat += vn1;
            if (rhat >= b) {
                break;
            }
        }
        
        final long un21 = (un32 << 32) + un1 - q1 * v;   // below v, modulo 2^64 as computed
        long q0 = Long.divideUnsigned(un21, vn1);
        rhat = Long.remainderUnsigned(un21, vn1);
        while (q0 >= b || Long.compareUnsigned(q0 * vn0, (rhat << 32) + un0) > 0) {
            q0--;
            rhat += vn1;
            if (rhat >= b) {
                break;
            }
        }
        return (q1 << 32) + q0;
    }
    
    /**
     * bergdb 031-06 (review-main, R2): the room of a record's got-dirty set for the nodes that
     * its take adds (Db.store()), so that the set stays within StoredTrans.takeRoom() by the
     * take itself and Db.checkTakeable() cannot fail by it. 'left' starts at takeRoom() less
     * the record's own got-dirty nodes; each transaction that take() or takeTo() takes
     * reduces it by its got-dirty nodes, every one counted as a node that the take keeps
     * dirty (Db.handleStillDirtyNodes), at its largest with its entry, as checkTakeable()
     * counts the set (largestBytes()). A transaction that does not fit is not taken. The
     * counts are of the record's own nodes and of the transactions of D, so the take is a
     * function of the stream and the action (010-01, P2). Until 2026-11-27 only the bytes
     * of the taken nodes at their sizes then bounded the take (maxBytes), and a take of many
     * nodes smaller than the largest, many of them kept dirty, gave a set over takeRoom() at
     * lowered record limits: the database failed at checkTakeable() (the review's
     * RmRoomProbe). At the release's limits takeRoom() is near 2 GB, about 3.9 million nodes
     * at node size 30, and no take comes near it.
     */
    static final class SetRoom {
        /** The bytes counted for a top node and for a key node, each with its entry. */
        final long topBytes, nodeBytes;
        
        /** The room left, in bytes at the largest node sizes; below 0, none. */
        long left;
        
        SetRoom(long left, long topBytes, long nodeBytes) {
            this.left = left;
            this.topBytes = topBytes;
            this.nodeBytes = nodeBytes;
        }
        
        /** Reduces the room by the transaction's got-dirty nodes and returns true, if they fit. */
        boolean take(TransInfo info) {
            final long bytes = largestBytes(info.gotDirtyNodes, topBytes, nodeBytes);
            if (bytes > left) {
                return false;
            }
            left -= bytes;
            return true;
        }
    }
    
    /**
     * The bytes of the index nodes 'nodes', each counted at its largest with its got-dirty
     * entry: 'topBytes' a top node, 'nodeBytes' any other (Db.checkTakeable(), SetRoom).
     */
    static long largestBytes(java.util.List<Node> nodes, long topBytes, long nodeBytes) {
        long top = 0;
        for (Node node : nodes) {
            if (node.getType() == Node.TYPE_TOP_NODE) {
                top++;
            }
        }
        return top * topBytes + (nodes.size() - top) * nodeBytes;
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
        // In units of 2^-16 (bergdb 005-79): the share 25 * 2^16, and the hashes 26,583 and
        // 65,167, 0.4056 and 0.9944.
        Assert.assertEquals(25L << 16, shareFp(100, 100, 1000, 2000, 800));
        Assert.assertEquals(26583, ditherFp(1300));
        Assert.assertEquals(65167, ditherFp(1200));
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
        
        // A tie, which the take stops at (<=; bergdb 005-79, the review of Part B): the part
        // that fits, all of the share, 297,636 / 2^16 nodes, equals u times the
        // transaction's 6 nodes, 49,606 * 6. It is l3-node14's one take where the double
        // rule of 2026-10-28 differs: that rule took the transaction. One transaction of 6
        // nodes at 500,000, the stream's length 531,776, sd 2^16, a section of u bytes, and
        // o = O = 1000 own bytes.
        final long tieLength = 531776;
        Assert.assertEquals(49606, ditherFp(tieLength));
        Assert.assertEquals(297636, shareFp(6, 1000, 1000, 49606, 65536));
        s = new TransSeq();
        s.add(paceInfo(500000, 6, 1000));
        Assert.assertEquals(tieLength - 49606, 
                s.take(tieLength - 49606, tieLength, 65536, 1000, IGNORE, Long.MAX_VALUE));
        Assert.assertEquals(1, s.getSize());
        
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
     * The cap of the share's factor (bergdb 024-31, 015-84). Right after a decrease of the
     * setting from 1000 to 100 MB the section is still about 1000 MB, its transactions'
     * span 999 MB; the share counts the section as 201 MB, c = SHARE_FACTOR_CAP times the
     * new setting and the 1 MB outside the span, not 1000 MB: 2.01 times the steady share,
     * that of a section of 100 MB with the same D, o and O, not ten times. While the span is
     * at most c * sd, as with a constant setting, the share is as without the cap.
     * D = 3,000,000 nodes, O = 10^9 own bytes, o = 10^6: the steady share is 3,000 nodes.
     */
    @Nano
    public static void testShareCap() {
        Assert.assertEquals(2, SHARE_FACTOR_CAP);
        final int sd = 100000000;
        final long D = 3000000, O = 1000000000L, o = 1000000;
        final long steady = shareFp(D, o, O, sd, sd);
        Assert.assertEquals(3000L << 16, steady);
        // The decrease: S 1000 MB, the span 999 MB.
        final long S = 1000000000L;
        Assert.assertEquals(201000000L, shareSection(S, S - 1000000, sd));
        Assert.assertEquals(6030L << 16, shareFp(D, o, O, shareSection(S, S - 1000000, sd), sd));
        // A span of at most 2 sd, as with a constant setting: the section as it is.
        Assert.assertEquals(250000000L, shareSection(250000000L, 2L * sd, sd));
        Assert.assertEquals(150000000L, shareSection(150000000L, 140000000L, sd));
        Assert.assertEquals(4500L << 16, shareFp(D, o, O, shareSection(3L * sd / 2, sd, sd), sd));
        // Just over: one byte less.
        Assert.assertEquals(250000000L - 1, shareSection(250000000L, 2L * sd + 1, sd));
    }
    
    /**
     * A decrease of the setting by ten, from 100,000 to 10,000, as from 1000 to 100 MB, with
     * the cap of the share's factor (bergdb 024-31). Records of 1000 own bytes and 100 bytes
     * for each node taken, each a transaction of 10 got-dirty nodes. In steady state a record
     * takes 10 nodes. After the decrease no record takes more than c + 1 transactions, (c +
     * 1) * 10 nodes, where without the cap the share was 100 nodes; and the section without
     * its last record, the span of the transactions after the take, shrinks with every
     * record while it is at least 2 sd (the deadline's ratchet, bergdb 007-07), and stays
     * below 2 sd once it is.
     */
    @Nano
    public static void testDecreaseCapped() {
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
        long lastSpan = 0;
        int most = 0;
        for (int i = 0; i < 2000; i++) {
            if (i == 1000) {
                sd = 10000;
                lastSpan = s.span();
            }
            taken[0] = 0;
            sp = s.take(sp, length, sd, 1000, counter, Long.MAX_VALUE);
            final long section = s.span();     // without this record's transaction
            s.add(paceInfo(length, 10, 1000));
            length += 1000 + 100 * taken[0];
            if (i < 1000) {
                continue;
            }
            most = Math.max(most, taken[0]);
            if (below < 0) {
                if (section < 2L * sd) {
                    below = i - 1000;
                } else {
                    Assert.assertTrue("i=" + i, i == 1000 || section < lastSpan);
                }
            } else {
                Assert.assertTrue("i=" + i + ", " + section, section < 2L * sd);
            }
            lastSpan = section;
        }
        Assert.assertTrue("most " + most, most <= 10 * (SHARE_FACTOR_CAP + 1));
        Assert.assertTrue("below 2 sd after " + below, below > 0 && below <= 200);
        Assert.assertEquals(10000, length - sp, 3000);
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
    
    // ======== The take in integers, bergdb 005-79 ========
    
    /** A number below 2^k, with k uniform from 0 to maxBits: spread over the bit lengths. */
    private static long spread(java.util.SplittableRandom r, int maxBits) {
        final int k = r.nextInt(maxBits + 1);
        return k == 0 ? 0 : r.nextLong() >>> (64 - k);
    }
    
    private static java.math.BigInteger unsigned(long x) {
        java.math.BigInteger b = java.math.BigInteger.valueOf(x);
        return x >= 0 ? b : b.add(java.math.BigInteger.ONE.shiftLeft(64));
    }
    
    /** shareFp as BigInteger computes it: floor(D o S 2^16 / (O sd)), at most D 2^16. */
    private static long shareExact(long D, long o, long O, long S, int sd) {
        java.math.BigInteger x = java.math.BigInteger.valueOf(D).multiply(java.math.BigInteger.valueOf(o))
                .multiply(java.math.BigInteger.valueOf(S)).shiftLeft(16);
        java.math.BigInteger q = x.divide(java.math.BigInteger.valueOf(O)
                .multiply(java.math.BigInteger.valueOf(sd)));
        return q.min(java.math.BigInteger.valueOf(D << 16)).longValueExact();
    }
    
    private static void checkShareFp(long D, long o, long O, long S, int sd) {
        final long expected = shareExact(D, o, O, S, sd);
        final long actual = shareFp(D, o, O, S, sd);
        if (actual != expected) {
            Assert.assertEquals("shareFp(" + D + ", " + o + ", " + O + ", " + S + ", " + sd + ")",
                    expected, actual);
        }
    }
    
    private static void checkDivlu(long u1, long u0, long v) {
        java.math.BigInteger x = unsigned(u1).shiftLeft(64).add(unsigned(u0));
        final long expected = x.divide(unsigned(v)).longValue();
        final long actual = divlu(u1, u0, v);
        if (actual != expected) {
            Assert.assertEquals("divlu(" + Long.toUnsignedString(u1) + ", " 
                    + Long.toUnsignedString(u0) + ", " + Long.toUnsignedString(v) + ")",
                    expected, actual);
        }
    }
    
    /**
     * divlu, the 128 by 64-bit division of shareFp, against BigInteger: unsigned words that
     * use all 64 bits, divisors of every bit length, the quotient below 2^64 (u1 < v), and
     * the edges, where the estimated quotient digits are corrected.
     */
    @Nano
    public static void testDivluExact() {
        final long m = -1L;                                 // 2^64 - 1
        final long[] vs = {1, 2, 3, 10, 0xFFFFFFFFL, 1L << 32, (1L << 32) + 1, Long.MAX_VALUE,
                Long.MIN_VALUE, Long.MIN_VALUE + 1, m - 1, m, 0x8000000080000000L, 
                0xFFFFFFFF00000000L, 0x80000000FFFFFFFFL};
        for (long v : vs) {
            for (long u1 : new long[] {0, 1, v - 1, (v - 1) >>> 1, Long.divideUnsigned(v, 3)}) {
                if (Long.compareUnsigned(u1, v) >= 0) {
                    continue;
                }
                for (long u0 : new long[] {0, 1, m, Long.MIN_VALUE, Long.MAX_VALUE, 0xFFFFFFFFL,
                        0xFFFFFFFF00000000L, v, v - 1}) {
                    checkDivlu(u1, u0, v);
                }
            }
        }
        java.util.SplittableRandom r = new java.util.SplittableRandom(7905);
        for (int i = 0; i < 100000; i++) {
            long v = spread(r, 64);
            if (v == 0) {
                v = 1;
            }
            long u1 = Long.remainderUnsigned(spread(r, 64), v);
            if (i % 4 == 0) {
                u1 = v - 1 - (u1 & 0xFF);                   // near v: corrections
                if (Long.compareUnsigned(u1, v) >= 0) {
                    u1 = v - 1;
                }
            }
            checkDivlu(u1, r.nextLong(), v);
        }
    }
    
    /**
     * shareFp against BigInteger's floor, clamped at D 2^16 (bergdb 005-79), on 10^5 cases
     * from SplitMix64: half spread over the bit lengths within the bounds (D to 2^32 - 1, o
     * to 2^31 - 1, S to 2^47 - 1, O from 1 to S + 1 or to 2^63 - 1, sd from 10 to
     * 2^31 - 1), which mostly clamp; half as BergDB has them, a section near sd and o at most
     * O, where the share is a few nodes; and on the edges, each bound at its largest, O = 1,
     * sd = 10, o = 0 and D = 0.
     */
    @Nano
    public static void testShareFpExact() {
        final long dMax = (1L << 32) - 1, oMax = (1L << 31) - 1, sMax = (1L << 47) - 1;
        final int sdMax = Integer.MAX_VALUE;
        for (long D : new long[] {0, 1, 1000, dMax}) {
            for (long o : new long[] {0, 1, 48, oMax}) {
                for (long S : new long[] {0, 1, 10, 1L << 31, sMax}) {
                    for (long O : new long[] {1, 48, oMax, sMax + 1, Long.MAX_VALUE}) {
                        for (int sd : new int[] {10, 1 << 20, sdMax}) {
                            checkShareFp(D, o, O, S, sd);
                        }
                    }
                }
            }
        }
        java.util.SplittableRandom r = new java.util.SplittableRandom(79);
        for (int i = 0; i < 50000; i++) {
            final long D = spread(r, 32), o = spread(r, 31), S = spread(r, 47);
            final long O = i % 2 == 0 ? 1 + Long.remainderUnsigned(spread(r, 48), S + 1)
                    : 1 + spread(r, 62) + spread(r, 62);
            final int sd = 10 + (int) Long.remainderUnsigned(spread(r, 31), sdMax - 9L);
            checkShareFp(D, o, O, S, sd);
        }
        for (int i = 0; i < 50000; i++) {
            final int sd = 10 + (int) Long.remainderUnsigned(spread(r, 31), sdMax - 9L);
            final long S = r.nextLong(4L * sd + 1);
            final long O = 48 + r.nextLong(S + 1);
            final long o = 48 + r.nextLong(Math.min(O, (1L << 31) - 48));
            final long D = r.nextLong(1 + Math.min(dMax, O / 40));
            checkShareFp(D, o, O, S, sd);
        }
    }
    
    /**
     * Outside the bounds the share is all of D, Long.MAX_VALUE, and every transaction before
     * the deadline is taken (bergdb 005-79): D = 2^32, S = 2^47, o = 2^31, O or sd not
     * positive. At the bounds' largest values the share is D 2^16 here, the min.
     */
    @Nano
    public static void testShareFpClamp() {
        Assert.assertEquals(Long.MAX_VALUE, shareFp(1L << 32, 48, 1000, 2000, 800));
        Assert.assertEquals(Long.MAX_VALUE, shareFp(100, 48, 1000, 1L << 47, 800));
        Assert.assertEquals(Long.MAX_VALUE, shareFp(100, 1L << 31, 1000, 2000, 800));
        Assert.assertEquals(Long.MAX_VALUE, shareFp(100, 48, 0, 2000, 800));
        Assert.assertEquals(Long.MAX_VALUE, shareFp(100, 48, 1000, 2000, 0));
        Assert.assertEquals(Long.MAX_VALUE, shareFp(-1, 48, 1000, 2000, 800));
        final long dMax = (1L << 32) - 1;
        Assert.assertEquals(dMax << 16, shareFp(dMax, (1L << 31) - 1, 1, (1L << 47) - 1, 10));
        
        // Beyond the bounds a record takes every transaction before the deadline.
        TransSeq s = new TransSeq();
        for (int i = 0; i < 10; i++) {
            s.add(paceInfo((1L << 48) + 100 * i, 10, 100));
        }
        final long length = (1L << 48) + 2000;
        Assert.assertEquals((1L << 48) + 900, s.take(0, length, 800, 100, IGNORE, Long.MAX_VALUE));
        Assert.assertTrue(s.isEmpty());
    }
    
    /** ditherFp is the floor of the double dither of 005-49 times 2^16 (bergdb 005-79). */
    @Nano
    public static void testDitherFp() {
        java.util.SplittableRandom r = new java.util.SplittableRandom(79);
        for (int i = 0; i < 1000; i++) {
            final long pos = i < 500 ? i : r.nextLong();
            long z = pos * 0x9E3779B97F4A7C15L;
            z = (z ^ (z >>> 30)) * 0xBF58476D1CE4E5B9L;
            z = (z ^ (z >>> 27)) * 0x94D049BB133111EBL;
            final long top53 = (z ^ (z >>> 31)) >>> 11;     // 005-49's u is top53 2^-53
            final int u = ditherFp(pos);
            Assert.assertTrue("pos " + pos, u >= 0 && u < 65536 && u == top53 >>> 37);
        }
    }
}
