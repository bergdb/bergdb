package bergdb.core;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.zip.CRC32C;
import bergdb.common.AssertStatus;
import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.dag.AccessData;
import bergdb.dag.Node;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Pointer;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import static bergdb.nanotest.Assert.assertEquals;
import static bergdb.nanotest.Assert.assertArrayEquals;
import static bergdb.nanotest.Assert.assertFalse;
import bergdb.nanotest.Nano;
import bergdb.pub.util.DbException;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;
import bergdb.storage.VersioningStreamException;

/**
 * This class and its inner classes are responsible serializing transactions to bytes
 * and to parse transactions from raw bytes.
 * For this class, performance is important enough to sometimes take precedence 
 * over pretty code.
 * 
 * @author Frans Lundberg
 */
public class StoredTrans {
    /**
     * The format byte of a stored transaction, written by Serializer and checked by Parser.
     * 9 since 2026-11-27 (bergdb 031-06), for release 2026.7, which does not open a database
     * of 2026.6 (Frans, 2026-11-27: a new format, refused with a clear message, no upgrade
     * path): one record an action, a commit's record and a part's of maintain() hold
     * reclaim's copies, row and table beside the action's KVs, and a copy's value node has the
     * copy mark (StoredValueNode, byte 6), which format 8 had as zero; a stream of format 8 is
     * of release 2026.6, refused at the start with a message that names it (formatRefused()).
     * No release has written format 9: its meaning may still change before 2026.7. It
     * changed on 2026-11-27 (bergdb 028-67, C3): bytes 5 to 7 of the header, written zero and
     * not read before, hold the header's check (headerCheck()), which every parse compares; a
     * stream of a build of 2026.7 before that has meta blocks of version 155, which a start
     * refuses first, so the number stays.
     * 8 since 2026-11-19 (bergdb 026-25), for release 2026.6: format 7's layout, and a
     * record's KVs are rerun as one batch by the writer PE, "plan, then emit" (Dag.putKvs,
     * PeWriter; bergdb 030-21 proves it in the model), which writes each node once, so a
     * record means another tree than in format 7, and its nodes have other ids; a stream of
     * format 7 is of release 2026.5, whose meta block's version (154) 2026.6 refuses first
     * (bergdb 028-15), or of a build of 2026.6 before 026-25, refused here.
     * 7 since 2026-11-11 (bergdb 024-21), for release 2026.5: format 6's layout, and a
     * record's deletes are rerun with the merges of underfull key nodes (Dag.mergeAfterDelete;
     * 024-11, section 5), so a record of deletes means another tree than in format 6;
     * databases of format 6, written by release 2026.4, are refused at the start, with a
     * message that names that release. Also in format 7 (bergdb 024-25): the node checksum
     * is CRC32C, 4 bytes, in a node header of 12 bytes (NodeChecksum), so the node formats
     * are 3 (top and key nodes) and 5 (value and delete nodes).
     * 6 since 2026-11-10 (bergdb 023-07, section 5.8; 023-09), for release 2026.4: a record's
     * deletes are rerun with the upward unlink, the empty key first, root collapse and the
     * take-back (Dag.deleteUpward), and a space split in place of a segment root made by the
     * transaction repoints the segment leaf's klong (Dag.spaceSplitInPlace), so a record
     * means another tree than in format 5; databases of format 5, written by release 2026.3
     * and earlier, are refused (023-02, F9 (a)).
     * 5 since 2026-10-15: the header holds topPos (bergdb 011-11, M18). Before, 2,
     * also through two incompatible changes, of 2015-12-29 and of 2016-05-11 (both id and
     * spos in the got-dirty list): they changed CURRENT_FORMAT_VERSION, to 3 and then 4,
     * which was never the stored byte, and is gone since 2026-10-25. A stream of another
     * format is refused: new databases only (F1-008-11's Q5).
     *
     * <p>A change of what a record holds, its header or its nodes, changes this number, so
     * that a start refuses a stream of another format: startup parses at least the record
     * that the last valid meta block names. A node's own format byte changes with its
     * layout too. A change of RecoverableStream's framing (a record's size field or last
     * byte, the meta blocks) changes MetaBlock's version instead, which recovery checks
     * before it writes; the zero fill of a torn record uses only the framing (2026-10-25,
     * bergdb 005-40), and since bergdb 028-67 comes after the record's header is checked
     * (RECORD_CHECK). MetaBlock's version is 156 since 2026-11-27 (bergdb 028-67: a block
     * holds its own position), 155 from 2026-11-18, when the startup distance left the meta
     * block (bergdb 028-15): each a change that an older release cannot read, so that the
     * older release refuses the stream before it writes (the rule proposed in bergdb 026-12,
     * SF3); a stream of version 154, of
     * release 2026.5 or earlier, is refused by its meta block, before a record is read.</p>
     */
    public final static byte RECORD_FORMAT = 9;

    /** The size of a record's header: the size, the format, the check, tt, startupPos, topPos. */
    static final int HEADER_SIZE = 32;

    /** The smallest record the writer writes: an empty one, 41 bytes and 7 of padding. */
    static final int MIN_RECORD_SIZE = 48;

    /**
     * The record header's check (bergdb 028-67, C3; Frans, 2026-11-27; 031-07, W24): the low
     * 24 bits of CRC-32C over the database's ID 'id' (16 bytes), the record's own stream
     * position 'tpos' (8 bytes, little-endian) and the header's other fields as stored, its
     * bytes 0 to 4 (the size and the format) and 8 to 31 (tt, startupPos, topPos): 53 bytes.
     * The header at 'offset' of 'header' holds it in bytes 5 to 7, little-endian, which were
     * written zero and not read until then. It ties a record to its place and its database,
     * so that a record of another file or position, as an older stream file's bytes in the
     * last file after a kill, is not taken as one (bergdb 035-02), and it covers the header,
     * which had no checksum (027-03, G12): every error of 1 to 3 bits in the header's 32
     * bytes changes it (031-07, section 5.3), and other bytes pass it once in 2^24.
     */
    static int headerCheck(byte[] id, long tpos, byte[] header, int offset) {
        return headerCheck(new CRC32C(), new byte[53], id, tpos, header, offset);
    }

    /** headerCheck() with the caller's CRC-32C and 53 bytes of scratch (the serializer's). */
    private static int headerCheck(CRC32C crc, byte[] scratch, byte[] id, long tpos,
            byte[] header, int offset) {
        System.arraycopy(id, 0, scratch, 0, 16);
        Bytes.longToBytesLE(tpos, scratch, 16);
        System.arraycopy(header, offset, scratch, 24, 5);
        System.arraycopy(header, offset + 8, scratch, 29, 24);
        crc.reset();
        crc.update(scratch, 0, 53);
        return (int) crc.getValue() & 0xffffff;
    }

    /** Whether the header at 'offset' of 'header' holds its check (headerCheck()). */
    static boolean headerChecks(byte[] id, long tpos, byte[] header, int offset) {
        final int stored = (header[offset + 5] & 0xff) | (header[offset + 6] & 0xff) << 8
                | (header[offset + 7] & 0xff) << 16;
        return stored == headerCheck(id, tpos, header, offset);
    }

    /**
     * Sets bytes 5 to 7 of the header at 'offset' of 'header' to its check (headerCheck()),
     * for the record at 'tpos' of the database of ID 'id'. For the serializer, and for tests
     * and tools that make or change a record's header.
     */
    static void setHeaderCheck(byte[] id, long tpos, byte[] header, int offset) {
        setCheckBytes(headerCheck(id, tpos, header, offset), header, offset);
    }

    private static void setCheckBytes(int check, byte[] header, int offset) {
        header[offset + 5] = (byte) check;
        header[offset + 6] = (byte) (check >>> 8);
        header[offset + 7] = (byte) (check >>> 16);
    }

    /**
     * The Core's check of a record for the start's recovery (RecoverableStream.recover(),
     * bergdb 028-67, C1), which knows a record's size and last byte only: a whole header is
     * one if it holds its check (headerCheck()) for its position and the database's ID; a
     * header that the end of the stream cuts (fewer than 32 bytes) is one as far as it goes
     * if its size is one the writer writes (48 or more, a multiple of 8, at most
     * MAX_RECORD_SIZE) and its format byte, if there, is RECORD_FORMAT; the first record of
     * the walk is refused for another format as NodeStream refuses it (formatRefused()); and a
     * whole record is one if it parses.
     */
    static final RecoverableStream.RecordCheck RECORD_CHECK = new RecoverableStream.RecordCheck() {
        public int headerSize() {
            return HEADER_SIZE;
        }

        public boolean headerChecks(long pos, byte[] header, byte[] id) {
            return StoredTrans.headerChecks(id, pos, header, 0);
        }

        public boolean tornHeaderFits(long pos, byte[] bytes, int length) {
            final int size = Bytes.bytesToIntLE(bytes, 0);
            return size >= MIN_RECORD_SIZE && size <= MAX_RECORD_SIZE
                    && size % RecoverableStream.TRANS_ALIGNMENT == 0
                    && (length < 5 || bytes[4] == RECORD_FORMAT);
        }

        public void checkFormat(long pos, byte[] header) {
            if (header.length > 4 && header[4] != RECORD_FORMAT) {
                throw new VersioningStreamException(formatRefused(header[4]));
            }
        }

        public String recordProblem(long pos, byte[] record, byte[] id) {
            try {
                parse(pos, record, id);
                return null;
            } catch (RuntimeException e) {
                return e.getMessage() != null ? e.getMessage() : e.toString();
            }
        }
    };
    
    /**
     * The largest record, in bytes (2026-10-21, bergdb 005-17): the record's size field is an
     * int (RecoverableStream), and the record is serialized to one array, at most about
     * Integer.MAX_VALUE long.
     */
    public static final long MAX_RECORD_SIZE = Integer.MAX_VALUE - 8;
    
    /** The record limit in force: MAX_RECORD_SIZE; tests lower it. */
    static volatile long recordLimit = MAX_RECORD_SIZE;
    
    /**
     * The most bytes the value nodes of a transaction may take: 7/8 of the record limit, so
     * that its last eighth, 256 MB, is left for the index nodes and the got-dirty list
     * (Db.checkSize).
     */
    static long valueLimit() {
        return recordLimit / 8 * 7;
    }
    
    /**
     * The most bytes the index nodes that one record makes dirty or creates may take, by Db's
     * bound at the largest node size (2026-10-24, bergdb 005-31): 15/16 of the record limit.
     * TransSeq.take writes them in the record of a later transaction, all in one; a
     * transaction whose record leaves less than 1/16 of the limit for them waits for the next.
     * Since bergdb 031-06 (review F5) it bounds a record, its action's KVs and its
     * maintenance's together (Db.recordDirtyFits, before the go point); an action alone is
     * admitted within actionDirtyLimit().
     */
    static long dirtyLimit() {
        return recordLimit - recordLimit / 16;
    }
    
    /**
     * bergdb 031-06 (review F5): the share of dirtyLimit() that every action leaves the step
     * that its record may carry, a sixteenth of the record limit, so that a run of the largest
     * actions leaves each step that room (Codex's E5).
     */
    static long stepDirtyRoom() {
        return recordLimit / 16;
    }
    
    /**
     * bergdb 031-06 (review F5): the most bytes the index nodes of an action alone may take,
     * dirtyLimit() less stepDirtyRoom(), 7/8 of the record limit (Db.checkDirtyNodes). Until
     * 031-06 an action had dirtyLimit() and its record carried nothing else.
     */
    static long actionDirtyLimit() {
        return dirtyLimit() - stepDirtyRoom();
    }
    
    /**
     * The bytes counted for a record's two top nodes, each at its largest (StoredTopNode, a
     * height of at most 48, TopNode.MAX_HEIGHT) with its got-dirty entry of 16 (Db's counts of
     * index nodes; bergdb 024-25).
     */
    static final long TOP_BYTES = 2 * (48 + 16L * 48 + 16);
    
    /**
     * bergdb 031-06 (review F5): the most bytes of a record's got-dirty set, its nodes counted
     * at their largest with their entries, that a later record with no KVs of an action can
     * take whole: an empty commit with nothing due, whose limit is recordLimit, and the part
     * of maintain() that takes D, M4 (Reclaim.planPart), whose limit is recordCap() and which
     * holds the table: the smaller of the two limits, M4's less TABLE_ROOM, less the record's
     * header (TransSeq.ownBytes(0)) and TOP_BYTES. Db.store() fails the database before it
     * appends a record whose set is over it, as no later take could take the set and the
     * startup pos would stay before it for good. The set is the record's own nodes, within
     * dirtyLimit() by the counts before the go point, and the nodes that its take keeps dirty
     * (Db.handleStillDirtyNodes), which the take keeps within the rest (TransSeq.SetRoom;
     * bergdb 031-06, review-main, R2). Until 2026-11-27 M4's table was not counted (review-main,
     * R5): at the release's limits, where recordCap() is recordLimit, a set within the table's
     * bytes of the room was taken by an empty commit only. At a lowered limit recordCap() is
     * recordLimit + stepRoom(), and stepRoom() holds TABLE_ROOM, so the room is as before.
     */
    static long takeRoom() {
        return Math.min(recordLimit, recordCap() - TABLE_ROOM) - TransSeq.ownBytes(0)
                - TOP_BYTES;
    }
    
    /**
     * bergdb 031-06: the room of the step that a record carries besides its transaction's,
     * for the row, the table and the scan's KVs but the last (Reclaim.MAX_STEP_SIZE).
     */
    static final long STEP_FIXED_ROOM = 256 * 1024L;
    
    /**
     * bergdb 031-06 (review-main, R5): the bytes that the record of M4 holds besides those of
     * a record with no KVs, which takeRoom() leaves it: the table's value node and the
     * got-dirty entries of the index nodes on its key's path. STEP_FIXED_ROOM, where
     * stepRoom() holds the row and the table: a table of a few rows and a path of a few
     * hundred nodes, some kB, unless the rows' keys are among the longest the Core accepts.
     * Assumed, not checked: a table over it leaves M4 less room than takeRoom(), and a set in
     * D within the difference is taken by a later commit, not by M4 (a part then appends the
     * table and does not move the startup pos).
     */
    static final long TABLE_ROOM = STEP_FIXED_ROOM;
    
    /**
     * bergdb 031-06: the largest value node that a user transaction can store, a value of
     * Db.MAX_VALUE_BYTES (L4) at a key of Db.MAX_TRANS_KEY_BYTES (L3), within valueLimit().
     */
    static long maxValueNode() {
        final long node = 12 + 8 + 4 + 4 + Db.MAX_VALUE_BYTES + 4
                + 8L * (Db.MAX_TRANS_KEY_BYTES / 7 + 1);
        return Math.min(valueLimit(), node + 3);
    }
    
    /**
     * bergdb 031-06: the room that the maintenance a record carries (Maintenance.Plan) has on
     * top of its transaction's limits (valueLimit(), dirtyLimit()), so that the user's
     * transaction never leaves the step too little (031-06, rule 4): its value nodes, at most
     * one value node of the largest size and STEP_FIXED_ROOM; and a sixteenth of the record
     * limit for the got-dirty entries of its index nodes. The index nodes themselves are within
     * dirtyLimit(), with the action's (stepDirtyRoom(); review F5).
     */
    static long stepRoom() {
        return maxValueNode() + STEP_FIXED_ROOM + recordLimit / 16;
    }
    
    /**
     * bergdb 031-06: the most bytes of a record that carries maintenance: recordLimit and the
     * step's room on top, at most MAX_RECORD_SIZE. At the release's limits it is
     * MAX_RECORD_SIZE, as before; a transaction within L1 to L5 and its step stay below it
     * by 024-17, section 5.3, with the step counted as a transaction of its KVs (5.5).
     */
    static long recordCap() {
        return Math.min(MAX_RECORD_SIZE, recordLimit + stepRoom());
    }
    
    /** Transaction time. */
    public final long tt;

    /** First spos of transaction (tpos). */
    public final long tpos;

    /** The spos of the last byte of the transaction. */
    public final long lastPos;
    
    /** The nodes of the transaction. */
    public StoredNode[] nodes;
    
    public final long startupPos;
    
    /**
     * The position of the latest version of the newest written top node: the super root at
     * the startup time of this record (bergdb 011-11, 8.3). Spos.NULL if none.
     * Startup starts from the last record's topPos; before 2026-10-15, it scanned the startup
     * section for the newest top node, which the section need not hold (M18).
     */
    public final long topPos;
    
    public long[] gotDirtyIdsAndSpos;

    
    private StoredTrans() {
        // for testing
        tt = 0;
        tpos = 0;
        lastPos = 99;
        startupPos = 0;
        topPos = Spos.NULL;
    }
    
    StoredTrans(Parser d) {
        tt = d.transactionTime;
        tpos = d.tpos;
        lastPos = d.lastPos;
        nodes = d.nodes;
        startupPos = d.startupPos;
        topPos = d.topPos;
        gotDirtyIdsAndSpos = d.gotDirtyIdsAndSpos;
    }
    
    /**
     * Returns a value node matching the given key, or null if no
     * match is found. Linear search is used.
     * 
     * @deprecated
     */
    public ValueNode getValueNode(long[] key) {
        // NOTE is this really OK? What is value written multiple times
        // in the startup interval? We would have multiple matches.
        
        ValueNode result = null;
        
        for (int i = 0; i < nodes.length; i++) {
            StoredNode stored = nodes[i];
            if (stored instanceof StoredValueNode) {
                StoredValueNode storedValueNode = (StoredValueNode) stored;
                long[] storedKey = storedValueNode.getKey();
                if (Keys.areEqual(key, storedKey)) {
                    result = storedValueNode.getNode();
                }
            }
        }
        
        return result;
    }
    
    /**
     * Returns the node with the given id, or null if such a node
     * does not exist; the first of the nodes, in their order, if several have it.
     * 
     * <p>A scan of the nodes, as before bergdb 021-16, when they are at most
     * FIND_NODE_SCAN_LIMIT, as in most records; otherwise a lookup in a map from id to node,
     * made at the first call for the current array 'nodes' (021-16, Q2). The start's rerun
     * calls it for every node it makes, a key node per 7 bytes of a new key, and with a scan
     * only, a database with a key of 100,000 bytes and then one of 1,000,000 with the same
     * start took 5 s to start, its rerun in this scan.</p>
     */
    public Node findNode(long id) {
        if (nodes.length <= FIND_NODE_SCAN_LIMIT) {
            for (StoredNode stored : nodes) {
                if (stored.getNode().getId() == id) {
                    return stored.getNode();
                }
            }
            return null;
        }
        
        if (nodesById == null || nodesIndexed != nodes) {
            final java.util.HashMap<Long, Node> map =
                    new java.util.HashMap<Long, Node>(2 * nodes.length + 1);
            for (StoredNode stored : nodes) {
                map.putIfAbsent(stored.getNode().getId(), stored.getNode());
            }
            nodesById = map;
            nodesIndexed = nodes;
        }
        
        return nodesById.get(id);
    }
    
    /** The most nodes that findNode() scans; above, it makes a map. */
    static final int FIND_NODE_SCAN_LIMIT = 64;
    
    /** findNode()'s map, and the array 'nodes' it was made from. */
    private java.util.HashMap<Long, Node> nodesById = null;
    private StoredNode[] nodesIndexed = null;

    /**
     * Creates and returns a list of the value nodes of the transaction: its puts and
     * deletes, one for each key it put or deleted, with the key (getKey()). A delete of a
     * key that had no value stores nothing and is not in the list; a step of reclaim lists
     * the values it copied and reclaim's own keys (Db.getTrans(); bergdb 020-24-09, U9-9).
     */
    public List<StoredValueNode> getValueNodes() {
        List<StoredValueNode> storedValueNodes = new ArrayList<StoredValueNode>();
        
        for (StoredNode n : nodes) {
            byte type = n.getNode().getType();
            if (type == Node.TYPE_VALUE || type == Node.TYPE_DELETE) {
                storedValueNodes.add((StoredValueNode) n);
            }
        }
        return storedValueNodes;
    }

    /**
     * Creates a StoredTrans by parsing the data in a the byte buffer: the record at
     * 'transPos' of the database of ID 'id', whose header must hold its check (bergdb 028-67,
     * headerCheck(); NodeStream.databaseId() gives a stream's ID).
     * 
     * @throws IllegalArgumentException
     * @throws StreamFormatException
     */
    public static StoredTrans parse(long transPos, byte[] buffer, byte[] id) {
        Parser p = new Parser();
        p.parse(transPos, buffer, id);
        return new StoredTrans(p);
    }

    /**
     * The message of a VersioningStreamException for a record whose format byte is not
     * RECORD_FORMAT: it says whether the stream was written by an older or a newer BergDB
     * (2026-10-25, bergdb 005-40). Before, every other format got the message of format 2.
     * Format 8 names release 2026.6, which wrote it, and that this version does not read it
     * (bergdb 031-06).
     */
    static String formatRefused(byte version) {
        int v = version & 0xff;
        String s = "Cannot parse stored transaction of format version " + v + "; this version "
                + "of BergDB reads format " + RECORD_FORMAT + " only. ";
        if (v > RECORD_FORMAT) {
            return s + "A larger number is a database written by a newer version of BergDB.";
        }
        if (v == 8) {
            return s + "Format 8 is a database written by release 2026.6, an older version of "
                    + "BergDB, which this version does not open: there is no upgrade path, and "
                    + "release 2026.6 still opens it (bergdb 031-06). It is also a database of "
                    + "a development build of 2026.7 before one record an action.";
        }
        return s + "A smaller number is a database written by an older version of BergDB, "
                + "which this version cannot open; or the stream is damaged, as the meta "
                + "block's version of a database of release 2026.5 or earlier refuses it "
                + "before (bergdb 028-15). Format 7 is also a database of a development "
                + "build of 2026.6 before its writer PE (bergdb 026-25).";
    }
    
    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append("tt:" + tt + ", tpos:" + tpos + ", lastPos:" + lastPos + ", startupPos:" + this.startupPos
                + ", topPos:" + this.topPos);
        b.append(", nodeCount:" + this.nodes.length);
        
        if (gotDirtyIdsAndSpos.length > 0) {
            b.append("\ngot dirty: ");
            for (int i = 0; i < gotDirtyIdsAndSpos.length; i++) {
                b.append(gotDirtyIdsAndSpos[i] + " ");
            }
        }
        
        return b.toString();
    }
    
    public String print() {
        StringBuilder b = new StringBuilder();
        b.append(toString() + "\n");
        for (StoredNode n : this.nodes) {
            b.append("* " + n.toString() + "\n");
        }
        return b.toString();
    }
    
    /** Returns number of zero bytes to add to provided transaction size. */
    private static int computeZeroCount(long transSizeBefore) {
        final int N = NodeStream.TRANS_ALIGNMENT;
        int result = (int) (N - transSizeBefore % N);
        result = (result == 8) ? 0 : result;
        assert result >= 0 && result < 8 : "result:" + result;
        return result;
    }

    /**
     * Struct class; key-value pair with raw data as read from the stored transaction.
     */
    public static class Kv {
        public final byte[] key;
        public final byte[] value;
        
        public Kv(byte[] key, byte[] value) {
            this.key = key;
            this.value = value;
        }
    }

    /**
     * Parses stream bytes to StoredNode objects.
     */
    static class Parser {
        long transactionTime;
        long tpos;
        long lastPos;
        long startupPos;
        long topPos;
        StoredNode[] nodes;
        long[] gotDirtyIdsAndSpos;

        int offset = 0;
        int byteSize;

        /**
         * Parses a transaction starting at buffer[0]: the record at 'tpos' of the database of
         * ID 'id', 16 bytes, whose header must hold its check (bergdb 028-67, C3).
         * buffer.length may be longer than required to store the transaction.
         */
        void parse(long tpos, byte[] buffer, byte[] id) {
            if (buffer == null) {
                throw new IllegalArgumentException("buffer == null not allowed");
            }

            if (id == null || id.length != 16) {
                throw new IllegalArgumentException("a database ID of 16 bytes is required");
            }

            if (buffer.length < 16 + 1) {
                throw new StreamFormatException("buffer too short, " + buffer.length);
            }

            if (tpos < 0) {
                throw new IllegalArgumentException("transPos < 0, " + tpos);
            }
            
            if (tpos % RecoverableStream.TRANS_ALIGNMENT != 0) {
                throw new IllegalArgumentException("bad transPos, " + tpos);
            }

            this.tpos = tpos;
            offset = 0;
            byteSize = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;

            // Header, node end marker, got-dirty count and last byte (bergdb 005-74,
            // option A). The serializer may have supplied an array longer than the record.
            if (byteSize < 32 + 4 + 4 + 1 || buffer.length < byteSize) {
                throw new StreamFormatException("Bad transaction size in header: "
                        + byteSize + ", buffer size: " + buffer.length + ".");
            }
            
            byte version = buffer[offset];
            offset++;
            
            if (version != RECORD_FORMAT) {
                throw new VersioningStreamException(formatRefused(version));
            }

            // Bytes 5 to 7, the header's check (bergdb 028-67, C3), after the format: a
            // stream of another format is refused as that (VersioningStreamException).
            if (!headerChecks(id, tpos, buffer, 0)) {
                throw new StreamFormatException("The header of the record at " + tpos
                        + " does not hold its check (bergdb 028-67, C3): the record was "
                        + "written at another position or by another database, or its header "
                        + "is damaged.");
            }
            offset += 3;
            
            transactionTime = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
            
            startupPos = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
            
            topPos = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
            
            // Parse nodes

            ArrayList<StoredNode> nodeList = new ArrayList<StoredNode>();
            while (true) {
                StoredNode stored = next(buffer);
                if (stored == null) {
                    break;
                }

                nodeList.add(stored);
            }
            
            // Parse got-dirty node ids

            if (offset > byteSize - 5) {
                throw new StreamFormatException("No room for gotDirtyCount and last byte.");
            }
            
            int gotDirtyCount = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;
            
            if (gotDirtyCount < 0 || gotDirtyCount > (byteSize - offset - 1) / 16) {
                throw new StreamFormatException("bad gotDirtyCount, " + gotDirtyCount);
            }
            
            this.gotDirtyIdsAndSpos = new long[gotDirtyCount * 2];
            
            for (int i = 0; i < gotDirtyCount * 2; i++) {
                gotDirtyIdsAndSpos[i] = Bytes.bytesToLongLE(buffer, offset);
                offset += 8;
            }

            nodes = nodeList.toArray(new StoredNode[nodeList.size()]);
            
            // Room for RecoverableStream.LAST_BYTE.
            offset += 1;     
            
            int transSizeBefore = offset;
            int count = computeZeroCount(transSizeBefore);
            if (count > byteSize - transSizeBefore) {
                throw new StreamFormatException("No room for transaction padding, size "
                        + byteSize + ", required " + ((long) transSizeBefore + count) + ".");
            }
            int transSize = transSizeBefore + count;
            
            // The content fills the record exactly, as the serializer writes it (bergdb
            // 015-72): a size field larger than the content would make the iterator skip the
            // records it covers.
            if (transSize != byteSize) {
                throw new StreamFormatException("The record at " + tpos + " ends at offset "
                        + transSize + " by its content, and its size says " + byteSize + ".");
            }
            lastPos = RecoverableStream.getSpos(tpos, transSize - 1);
            
            assert lastPos % NodeStream.TRANS_ALIGNMENT == (NodeStream.TRANS_ALIGNMENT - 1) 
                    : "Bad lastPos: " + lastPos + ", transSize:" + transSize + ", transPos: " + tpos;
        }
        
        boolean hasNewStartupPos() {
            return startupPos != -1;
        }

        private StoredNode next(byte[] buffer) {
            if (offset > byteSize - 4) {
                throw new StreamFormatException("Missing node end marker at offset " + offset
                        + ", transaction size " + byteSize + ".");
            }

            int nodeSize = Bytes.bytesToIntLE(buffer, offset);
            if (nodeSize == 0) {
                offset += 4;
                return null;
            }

            // The common node header is 12 bytes (bergdb 024-25; 8 before). Check before
            // parsing or advancing: a negative size used to move backwards and loop until the
            // heap ran out.
            if (nodeSize < NodeChecksum.HEADER_SIZE || nodeSize > byteSize - offset) {
                throw new StreamFormatException("Bad node size, " + nodeSize + ", at offset "
                        + offset + " of transaction at " + tpos + ", size " + byteSize + ".");
            }

            long spos = RecoverableStream.getSpos(tpos, offset);
            StoredNode stored = NodeStream.bytesToNode(spos, buffer, offset, nodeSize);

            offset += nodeSize;
            return stored;
        }
    }
    
    /**
     * Class used to serialize a transaction to bytes. For performance reasons, an object of this
     * class can be reused to serialize multiple transactions. It has internal buffers that may be
     * large and would be expensive to allocate each time a transaction is serialized. This class is
     * not thread-safe.
     * 
     * @author Frans Lundberg
     */
    public static class Serializer {
        private static final int INIT_SIZE_OF_BYTE_BUFFER = 100 * 1000;
        private static final int INIT_SIZE_OF_LONG_BUFFER = 10 * 1000;
        private static final int INIT_SIZE_OF_PREV_POS = 100;

        private long[] longBuffer;
        private byte[] byteBuffer;
        private int totalSize;
        private int topAndKeySize;
        private long[] prevPos;
        private int extraZeros;
        
        private TransNodes transNodes;
        private long transStartPos;
        private long transTime;
        private long startupPos;
        private TopNode topNode;
        private long topPos;
        
        private long transNextSpos;
        private long transLastSpos;

        /** Number of times serialize() has been called. */
        private long counter;
        
        /** bergdb 031-06: the record's limit, Trans.recordCap, set before serialize(); 0: recordLimit. */
        long recordCap;

        /**
         * The database's ID, for the header's check (bergdb 028-67, C3): NodeStream sets it
         * before serialize(); 16 zero bytes until then, as in tests that use a Serializer
         * alone.
         */
        final byte[] databaseId = new byte[16];
        private final CRC32C crc = new CRC32C();
        private final byte[] checkScratch = new byte[53];
        private ArrayList<Node> gotDirtyNodes;
        
        /**
         * Allocates memory for the serialization.
         */
        public Serializer() {
            longBuffer = new long[INIT_SIZE_OF_LONG_BUFFER];
            byteBuffer = new byte[INIT_SIZE_OF_BYTE_BUFFER];
            prevPos = new long[INIT_SIZE_OF_PREV_POS];
            counter = 0;
        }

        /**
         * Serializes the transaction given the nodes in TransNodes. Use the getOutputX() methods to
         * get the result.
         * 
         * @param transTime
         *            The transaction time.
         * @param transStartPos
         *            The spos of the first byte of the transaction.
         * @param startupPos
         */
        public void serialize(TransNodes transNodes, long transTime, long transStartPos, 
                long startupPos, ArrayList<Node> gotDirtyNodes) {
            serialize(transNodes, transTime, transStartPos, startupPos, gotDirtyNodes, null);
        }

        /**
         * As serialize() above, with the newest written top node, whose position after this
         * transaction is stored as topPos (null: Spos.NULL). It may be one of the transaction's
         * top nodes; its position in this transaction is then stored.
         */
        public void serialize(TransNodes transNodes, long transTime, long transStartPos, 
                long startupPos, ArrayList<Node> gotDirtyNodes, TopNode topNode) {
            assert transNodes != null;
            assert transTime >= 0;
            assert transStartPos >= 0;

            this.transNodes = transNodes;
            this.transStartPos = transStartPos;
            this.transTime = transTime;
            this.startupPos = startupPos;
            this.gotDirtyNodes = gotDirtyNodes;
            this.topNode = topNode;

            prepareToSerialize();
            
            // After prepareToSerialize(): a top node of this transaction has its new position.
            this.topPos = topNode == null ? Spos.NULL : topNode.getSpos();
            assert topNode == null || (Spos.isValid(topPos) && !Spos.isVpos(topPos))
                    : "the newest written top node has no stream position: " + topPos;
            
            if (AssertStatus.enabled()) {
                checkStreamPointersOfKeyNodes();
                checkStreamPointers();
            }
            
            serializeToBuffer();
            
            counter++;
        }
        
        /**
         * Checks that stream pointers of key nodes are not Spos.NULL.
         * They should be valid after prepareToSerialized has been run.
         * Call this method, only if assertions are enabled (-ea) since it may
         * degrade performance.
         * 
         * @throws AssertionError
         */
        private void checkStreamPointersOfKeyNodes() {
            Pointer pointer = new Pointer();
            for (int i = 0; i < transNodes.keyCount; i++) {
                KeyNode keyNode = transNodes.keyNodes[i];
                int size = keyNode.size;
                
                for (int j = 0; j < size; j++) {
                    long klong = keyNode.klongs[j];
                    if (Klong.getType(klong) == Klong.TYPE_KEY) {
                        keyNode.getPointer(j, pointer);     // A coherent pair.
                        Node pointee = pointer.node;
                        long spos = keyNode.getSerializedRef(j);
                        
                        if (!Spos.isValid(spos)) {
                            String message = "Bad stream pointer of KeyNode, index " + j + ", spos: " + spos 
                                    + ", trans at t=" + transTime + " tpos=" + transStartPos 
                                    + ", node:\n" + keyNode.print();
                                    
                            if (pointee != null) {
                                message += "pointee node:\n" + pointee.print();
                            }
                            
                            throw new AssertionError(message);
                        }
                    }
                }
            }
        }
        
        /**
         * Checks that stream pointers are not Spos.NULL or vpos.
         * They should be valid after prepareToSerialized has been run.
         * Call this method, only if assertions are enabled (-ea) since it
         * degrades performance.
         * 
         * @throws AssertionError
         */
        private void checkStreamPointers() {
            Iterator<Node> iter = transNodes.indexNodeIterator();
            Pointer p = new Pointer();

            while (iter.hasNext()) {
                Node node = iter.next();
                
                long spos = node.getSpos();
                if (Spos.isNull(spos)) {
                    throw new AssertionError("Spos of node is NULL, node: " + node.toString());
                }
                
                if (Spos.isVpos(spos)) {
                    throw new AssertionError("Spos of index node (" + spos 
                            + ") is vpos, node: " + node.toString());
                }
                
                int count = node.getSize();
                for (int i = 0; i < count; i++) {
                    node.getPointer(i, p);
                    // A stream pointer, as written (with handles, bergdb item 009: its
                    // serialized reference). A memory pointer to a node not written yet is
                    // written with its vpos, as before (its long field was access data, which
                    // this check passed).
                    if (!p.isNull() && p.node == null) {
                        spos = node.getSerializedRef(i);
                        if (Spos.isNull(spos)) {
                            throw new AssertionError("spos of node pointer is NULL, index: " + i + ", node: " + node.toString());
                        }
                        
                        if (Spos.isVpos(spos)) {
                            throw new AssertionError("spos of index node pointer (" + spos 
                                    + ") is vpos, index: " + i + ", node: " + node.toString());
                        }
                    }
                }
            }
        }

        /** Returns the transaction buffer with the serialized transaction. */
        public final byte[] getTransBuffer() {
            return this.byteBuffer;
        }

        /** Returns the byte size of the buffer returned by getTransBuffer(). */
        public final int getOutputTransSize() {
            return this.totalSize;
        }

        public final long getOutputNextSpos() {
            return this.transNextSpos;
        }

        public final long getOutputLastSpos() {
            return this.transLastSpos;
        }

        /**
         * Prepares for serialization by computing sizes; sets totalSize, transLastSpos,
         * transNextSpos, sets spos of nodes! This solves the inter-transaction stream
         * pointer issue. Inter-transaction stream pointers will work, even when stream pointers 
         * point forward within the transaction.
         */
        private void prepareToSerialize() {
            // The three node loops sets new stream pos of nodes, sets ID if needed,
            // Also computes totalSize and sets prevPos array for KeyNodes.
            // This is performance-sensitive; pretty code has lower-than-usual prio here.
            // 2026-10-21 (bergdb 005-17): the size is added up in a long, and a record above
            // the record limit is refused; the int sum wrapped for transactions of 2 GB.

            long size = 32; // Header size, 32 = trans size (4), format (4), trans time (8),
                            // startupPos (8), topPos (8)
            long currentPos = RecoverableStream.getSpos(transStartPos, size);

            resizePrevPosIfNeeded();

            // Prepares topNodes.
            for (int i = 0; i < transNodes.topCount; i++) {
                TopNode node = transNodes.topNodes[i];
                node.spos = currentPos;
                size += StoredTopNode.getByteSize(node);
                currentPos = RecoverableStream.getSpos(transStartPos, size);
            }

            // Prepares keyNodes.
            {
                int prevPosIndex = 0;
                for (int i = 0; i < transNodes.keyCount; i++) {
                    KeyNode node = transNodes.keyNodes[i];
                    prevPos[prevPosIndex++] = node.spos;
                    node.spos = currentPos;
                    size += StoredKeyNode.getByteSize(node);
                    currentPos = RecoverableStream.getSpos(transStartPos, size);
                }
            }

            final long topAndKey = size;

            // Prepares valueNodes. The offset from the transaction, in the stream, before the
            // spos (a volatile field), so that a reader that sees the new spos sees the offset
            // of the same write (2026-10-24, bergdb 005-34).
            for (int i = 0; i < transNodes.valueCount; i++) {
                ValueNode node = transNodes.valueNodes[i];
                long[] key = transNodes.keys[i];
                node.offsetFromTrans = (int) (currentPos - transStartPos);
                node.setSpos(currentPos);
                size += StoredValueNode.getByteSizeLong(node.value, key);
                currentPos = RecoverableStream.getSpos(transStartPos, size);
            }

            // Marker for end of nodes
            size += 4;
            
            // Number of got dirty node ids
            size += 4;
            
            // Got-dirty node ids
            size += 16L * gotDirtyNodes.size();

            // Room for RecoverableStream.LAST_BYTE.
            size += 1;

            // For totalSize to be a multiple of TRANS_ALIGNMENT.
            extraZeros = computeZeroCount(size);
            size += extraZeros;
            
            final long limit = recordCap > 0 ? recordCap : recordLimit;   // bergdb 031-06
            if (size > limit) {
                throw new DbException("The record of the transaction would take " + size 
                        + " bytes, more than the limit, " + limit + " (bergdb 005-17).");
            }
            
            totalSize = (int) size;
            topAndKeySize = (int) topAndKey;
            
            assert totalSize % NodeStream.TRANS_ALIGNMENT == 0 : totalSize + ", " + extraZeros;

            transLastSpos = RecoverableStream.getSpos(transStartPos, totalSize - 1);
            transNextSpos = RecoverableStream.getSpos(transStartPos, totalSize);
            
            resizeBuffersIfNeeded();
        }

        private void serializeToBuffer() {
            //
            // Note, code to serialize causes significant execution time (30-40%) for PUT operations.
            // We could possibly return quickly and let another thread serialize nodes.
            // Possibly the thread that handles flushing the buffer could be used, or a separate
            // one. KeyNode.size and order of transactions would need to be handled.
            // Low complexity vs performance.
            //

            int longOffset = 0;
            int byteOffset;

            longOffset = serializeHeader(longOffset);
            byteOffset = serializeNodes(longOffset);
            byteOffset = serializeEnd(byteOffset);

            // The header's check, over its bytes as copied (bergdb 028-67, C3).
            setCheckBytes(headerCheck(crc, checkScratch, databaseId, transStartPos, byteBuffer,
                    0), byteBuffer, 0);

            assert byteOffset == totalSize;
            assert totalSize % 8 == 0;
        }

        private int serializeHeader(int longOffset) {
            long int0 = totalSize;
            long int1 = RECORD_FORMAT;
            
            longBuffer[longOffset] = int0 | (int1 << 32);
            longOffset += 1;
            longBuffer[longOffset] = transTime;
            longOffset += 1;
            longBuffer[longOffset] = startupPos;
            longOffset += 1;
            longBuffer[longOffset] = topPos;
            longOffset += 1;
            
            return longOffset;
        }

        private int serializeNodes(int longOffset) {
            int offset = 0;
            int prevPosIndex = 0;

            for (int i = 0; i < transNodes.topCount; i++) {
                TopNode topNode = transNodes.topNodes[i];
                longOffset += StoredTopNode.toLongs(topNode, longBuffer, longOffset);
            }

            for (int i = 0; i < transNodes.keyCount; i++) {
                KeyNode keyNode = transNodes.keyNodes[i];
                longOffset += StoredKeyNode.toLongs(keyNode, longBuffer, longOffset,
                        prevPos[prevPosIndex++]);
            }

            // Copies from longBuffer to byteBuffer, top nodes and value nodes.
            offset = copyLongBufferToByteBuffer(longOffset, offset);

            // The checksums of the top and key nodes, on their bytes (bergdb 024-25): toLongs
            // leaves them zero. A value node's toBytes sets its own.
            int nodeOffset = 32;
            for (int i = 0; i < transNodes.topCount; i++) {
                int size = StoredTopNode.getByteSize(transNodes.topNodes[i]);
                NodeChecksum.set(byteBuffer, nodeOffset, size);
                nodeOffset += size;
            }
            for (int i = 0; i < transNodes.keyCount; i++) {
                int size = StoredKeyNode.getByteSize(transNodes.keyNodes[i]);
                NodeChecksum.set(byteBuffer, nodeOffset, size);
                nodeOffset += size;
            }
            assert nodeOffset == offset : nodeOffset + ", " + offset;

            for (int i = 0; i < transNodes.valueCount; i++) {
                ValueNode n = transNodes.valueNodes[i];
                long[] skey = transNodes.keys[i];
                offset += StoredValueNode.toBytes(n, skey, byteBuffer, offset,
                        transNodes.isCopy(skey));       // the copy mark, bergdb 031-06
            }
            return offset;
        }

        private int serializeEnd(int offset) {
            // Zero to indicate end of nodes.
            Bytes.intToBytesLE(0, byteBuffer, offset);
            offset += 4;
            
            Bytes.intToBytesLE(gotDirtyNodes.size(), byteBuffer, offset);
            offset += 4;
            
            for (int i = 0; i < gotDirtyNodes.size(); i++) {
                Node node = gotDirtyNodes.get(i);
                Bytes.longToBytesLE(node.getId(), byteBuffer, offset);
                offset += 8;
                Bytes.longToBytesLE(node.getSpos(), byteBuffer, offset);
                offset += 8;
            }

            System.arraycopy(NodeStream.ZEROS64, 0, byteBuffer, offset, extraZeros);
            offset += extraZeros;

            // End of buffer (LAST_BYTE indicates a valid transaction).

            byteBuffer[offset] = RecoverableStream.LAST_BYTE;
            offset += 1;
            return offset;
        }

        private int copyLongBufferToByteBuffer(int longOffset, int offset) {
            for (int j = 0; j < longOffset; j++) {
                long value = longBuffer[j];
                byteBuffer[offset++] = (byte) value;
                byteBuffer[offset++] = (byte) (value >>> 8);
                byteBuffer[offset++] = (byte) (value >>> 16);
                byteBuffer[offset++] = (byte) (value >>> 24);
                byteBuffer[offset++] = (byte) (value >>> 32);
                byteBuffer[offset++] = (byte) (value >>> 40);
                byteBuffer[offset++] = (byte) (value >>> 48);
                byteBuffer[offset++] = (byte) (value >>> 56);
            }
            return offset;
        }
        
        

        private void resizePrevPosIfNeeded() {
            // Increases prevPos length if needed.
            // Decreases it every PRIME'th time if possible to avoid memory leak
            // after a large transaction.
            
            final int PRIME = 97;
            final int PRIME_MINUS_ONE = 96;

            if (counter % PRIME == PRIME_MINUS_ONE) {
                int newSize = Math.max(INIT_SIZE_OF_PREV_POS, transNodes.keyCount);
                if (prevPos.length != newSize) {
                    prevPos = new long[newSize];
                }
            }

            if (this.prevPos.length < transNodes.keyCount) {
                // floor(1.2 keyCount), in integers (bergdb 005-79); keyCount is far below
                // 2^31 / 1.2, as each key node takes bytes of a record below 2^31.
                this.prevPos = new long[transNodes.keyCount + transNodes.keyCount / 5];
            }
        }

        private void resizeBuffersIfNeeded() {
            // Increases buffer sizes of byteBuffer and longBuffer if required.
            // Decreases buffer sizes every PRIME'th transaction if possible.
            
            final int PRIME = 97;
            final int PRIME_MINUS_ONE = 96;
            
            if (counter % PRIME == PRIME_MINUS_ONE) {
                int newByteSize = Math.max(INIT_SIZE_OF_BYTE_BUFFER, totalSize);
                if (byteBuffer.length != newByteSize) {
                    try {
                        byteBuffer = new byte[newByteSize];
                    } catch (OutOfMemoryError e) {
                        throw new OutOfMemoryError(e.getMessage() 
                                + ", tried to allocate " + newByteSize 
                                + " bytes for byte[], counter is " + counter);
                    }
                }

                int newLongSize = Math.max(INIT_SIZE_OF_LONG_BUFFER, topAndKeySize / 8);
                if (longBuffer.length != newLongSize) {
                    try {
                        longBuffer = new long[newLongSize];
                    } catch (OutOfMemoryError e) {
                        throw new OutOfMemoryError(e.getMessage() 
                                + ", tried to allocate " + (newLongSize*8) 
                                + " bytes for long[], counter is " + counter);
                    }
                }
            }

            if (byteBuffer.length < totalSize) {
                // At most the record limit (2026-10-21, bergdb 005-17): the int cast gave
                // Integer.MAX_VALUE, more than the largest array, from 1.79 GB.
                // floor(1.2 totalSize) in long integers (bergdb 005-79).
                int newSize = (int) Math.max(totalSize, 
                        Math.min(totalSize + totalSize / 5L, MAX_RECORD_SIZE));
                
                try {
                    byteBuffer = new byte[newSize];
                } catch (OutOfMemoryError e) {
                    throw new OutOfMemoryError(e.getMessage() 
                            + ", tried to allocate " + newSize + " bytes (byte[])");
                }
            }

            if (longBuffer.length < (topAndKeySize / 8) + 8) {
                int newSize = (int) (topAndKeySize / 8 + 8);
                
                try {
                    longBuffer = new long[newSize];
                } catch (OutOfMemoryError e) {
                    throw new OutOfMemoryError(e.getMessage() 
                            + ", tried to allocate " + (newSize * 8) + " bytes (long[])");
                }
            }
        }
    }
    
    
    // ======== Testing ========

    /** The database ID of a Serializer that no NodeStream gave one: 16 zero bytes. */
    private static final byte[] TEST_ID = new byte[16];
    
    /** bergdb 005-74, F2: this record used to loop between its two delete nodes. */
    @Nano
    private static void testNegativeNodeSize() {
        byte[] buffer = recordWithBadNodeSize(-32);
        try {
            parse(128, buffer, TEST_ID);
            throw new AssertionError("negative node size was accepted");
        } catch (StreamFormatException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("node size"));
        }
    }

    /**
     * bergdb 005-74, option A: a node must fit inside its declared record; and since bergdb
     * 024-25 hold its 12-byte header (sizes 8 and 11).
     */
    @Nano
    private static void testNodeSizeOutsideRecord() {
        for (int size : new int[] {1, 6, 7, 8, 11, Integer.MAX_VALUE}) {
            try {
                parse(128, recordWithBadNodeSize(size), TEST_ID);
                throw new AssertionError("bad node size was accepted: " + size);
            } catch (StreamFormatException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("node size"));
            }
        }
        byte[] buffer = recordWithBadNodeSize(36);
        Bytes.intToBytesLE(80, buffer, 0);    // The array is longer than the record.
        setHeaderCheck(TEST_ID, 128, buffer, 0);
        try {
            parse(128, buffer, TEST_ID);
            throw new AssertionError("node beyond the declared record was accepted");
        } catch (StreamFormatException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("node size"));
        }
    }

    private static byte[] recordWithBadNodeSize(int size) {
        // Two delete nodes of 36 bytes, at 32 and 68 (of 32 bytes, at 32 and 64, and a record
        // of 112 bytes, until the node header's 12 bytes, bergdb 024-25); the second's size
        // is 'size'.
        byte[] buffer = new byte[120];
        Bytes.intToBytesLE(buffer.length, buffer, 0);
        buffer[4] = RECORD_FORMAT;
        Bytes.longToBytesLE(1, buffer, 8);
        for (int offset : new int[] {32, 68}) {
            Bytes.intToBytesLE(offset == 32 ? 36 : size, buffer, offset);
            buffer[offset + 4] = Node.TYPE_DELETE;
            buffer[offset + 5] = 5;
            Bytes.intToBytesLE(offset, buffer, offset + 20);
            Bytes.intToBytesLE(8, buffer, offset + 24);
        }
        NodeChecksum.set(buffer, 32, 36);
        buffer[buffer.length - 1] = RecoverableStream.LAST_BYTE;
        setHeaderCheck(TEST_ID, 128, buffer, 0);        // bergdb 028-67
        return buffer;
    }

    /** A reused serializer buffer must not make bytes beyond the record readable. */
    @Nano
    private static void testCorruptRecordSize() {
        Serializer serializer = new Serializer();
        serializer.serialize(new TransNodes(), 100, 200, -1, new ArrayList<Node>());
        for (int size : new int[] {Integer.MIN_VALUE, -1, 0, 16, 32, 40, 41, 47}) {
            byte[] buffer = serializer.getTransBuffer().clone();
            Bytes.intToBytesLE(size, buffer, 0);
            try {
                parse(200, buffer, TEST_ID);
                throw new AssertionError("bad record size was accepted: " + size);
            } catch (StreamFormatException e) {
                // Refused before a header, node or list is read outside the record.
            }
        }
    }

    @Nano
    private static void testGotDirtyCountOutsideRecord() {
        Serializer serializer = new Serializer();
        serializer.serialize(new TransNodes(), 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer().clone();
        Bytes.intToBytesLE(1, buffer, 36);
        try {
            parse(200, buffer, TEST_ID);
            throw new AssertionError("got-dirty list beyond the record was accepted");
        } catch (StreamFormatException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("gotDirtyCount"));
        }
    }
    
    @Nano
    private static void testKvSanity() {
        byte[] key = new byte[]{1};
        byte[] value = new byte[]{1, 2};
        
        Kv kv = new Kv(key, value);
        Assert.assertArrayEquals(new byte[]{1}, kv.key);
        Assert.assertArrayEquals(new byte[]{1, 2}, kv.value);
    }
    
    /** bergdb 005-21: a corrupt got-dirty count is a StreamFormatException. */
    @Nano
    private static void testCorruptGotDirtyCount() {
        Serializer serializer = new Serializer();
        serializer.serialize(new TransNodes(), 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer().clone();
        Bytes.intToBytesLE(Integer.MAX_VALUE, buffer, 36);     // after the header and the end marker
        try {
            new Parser().parse(200, buffer, TEST_ID);
            throw new AssertionError("no exception");
        } catch (StreamFormatException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("gotDirtyCount"));
        }
    }
    
    /** bergdb 005-17: a record above the record limit is refused by the serializer. */
    @Nano
    private static void testRecordAboveLimit() {
        final long saved = recordLimit;
        recordLimit = 100 * 1000;
        try {
            Serializer serializer = new Serializer();
            serializer.serialize(transWithValue(new byte[90 * 1000]), 100, 200, -1, 
                    new ArrayList<Node>());
            try {
                serializer.serialize(transWithValue(new byte[100 * 1000]), 100, 200, -1, 
                        new ArrayList<Node>());
                throw new AssertionError("a record above the limit was serialized");
            } catch (DbException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("limit"));
            }
        } finally {
            recordLimit = saved;
        }
    }
    
    @Nano
    private static void testSerialize1() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        serializer.serialize(transNodes, 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(200, buffer, TEST_ID);
        
        assertEquals(0, parser.nodes.length);
        assertEquals(100, parser.transactionTime);
        assertEquals(200, parser.tpos);
    }
    
    @Nano
    private static void testSerialize2() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        ValueNode v0 = new ValueNode(new byte[]{});
        ValueNode v1 = new ValueNode(new byte[]{12});
        ValueNode v2 = new ValueNode(new byte[]{13, 14});
        
        KeyNode n = new KeyNode();
        n.setId(101);
        n.addKlong(10, Klong.createKey(StringUtil.toBytes("a")), v0, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.createKey(StringUtil.toBytes("b")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.createKey(StringUtil.toBytes("c")), v2, AccessData.DEFAULT_ACCESS_DATA);
        
        transNodes.addValueNode(v0, Keys.toSegments("a"));
        transNodes.addValueNode(v1, Keys.toSegments("b"));
        transNodes.addValueNode(v2, Keys.toSegments("c"));
        transNodes.addKeyNode(n);
        
        serializer.serialize(transNodes, 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(200, buffer, TEST_ID);
        
        assertEquals(4, parser.nodes.length);
        assertEquals(100, parser.transactionTime);
        assertEquals(200, parser.tpos);
        assertEquals(Node.TYPE_KEY_NODE, parser.nodes[0].getNode().getType());
        assertEquals(Node.TYPE_VALUE, parser.nodes[1].getNode().getType());
        assertEquals(Node.TYPE_VALUE, parser.nodes[2].getNode().getType());
        assertEquals(Node.TYPE_VALUE, parser.nodes[3].getNode().getType());
        
        byte[] value1 = ((ValueNode) parser.nodes[2].getNode()).value.clone();
        Assert.assertArrayEquals(new byte[]{12}, value1);
        
        byte[] value2 = ((ValueNode) parser.nodes[3].getNode()).value.clone();
        Assert.assertArrayEquals(new byte[]{13, 14}, value2);
    }
    
    /** topPos names the new position of a top node written in the same transaction. */
    @Nano
    private static void testTopPosOfTopNodeInTransaction() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        TopNode top = TopNode.createDummy(7);
        transNodes.addTopNode(top);
        serializer.serialize(transNodes, 100, 200, -1, new ArrayList<Node>(), top);
        
        Parser parser = new Parser();
        parser.parse(200, serializer.getTransBuffer(), TEST_ID);
        
        assertEquals(top.getSpos(), parser.topPos);
        assertEquals(parser.nodes[0].getNode().getSpos(), parser.topPos);
    }
    
    /** topPos names the position of a top node written earlier. */
    @Nano
    private static void testTopPosOfEarlierTopNode() {
        Serializer serializer = new Serializer();
        TopNode top = TopNode.createDummy(7);
        top.spos = 128;
        serializer.serialize(new TransNodes(), 100, 200, -1, new ArrayList<Node>(), top);
        
        Parser parser = new Parser();
        parser.parse(200, serializer.getTransBuffer(), TEST_ID);
        
        assertEquals(128, parser.topPos);
        assertEquals(0, parser.nodes.length);
    }
    
    /**
     * A transaction of the format before 2026-10-15 (2), or of release 2026.3 and earlier (5),
     * is refused with a clear message, as a VersioningStreamException since 2026-10-25
     * (bergdb 005-40); the message named release 2026.3 from format 6 (bergdb 023-07,
     * section 5.8), and since bergdb 028-15 the meta block's version that refuses a database
     * of release 2026.5 or earlier first.
     */
    @Nano
    private static void testRefusesOldFormat() {
        Serializer serializer = new Serializer();
        serializer.serialize(new TransNodes(), 100, 200, -1, new ArrayList<Node>());
        for (int format : new int[] {2, 5}) {
            byte[] buffer = serializer.getTransBuffer().clone();
            assertEquals(RECORD_FORMAT, buffer[4]);
            buffer[4] = (byte) format;
            
            try {
                new Parser().parse(200, buffer, TEST_ID);
                throw new AssertionError("no exception for format " + format);
            } catch (VersioningStreamException e) {
                String m = e.getMessage();
                Assert.assertTrue(m, m.contains("format version " + format + ";"));
                Assert.assertTrue(m, m.contains("older version"));
                Assert.assertTrue(m, m.contains("release 2026.5 or earlier"));
            }
        }
    }
    
    /**
     * Transactions of formats 6 and 7 are refused as ones of an older BergDB (bergdb 024-21:
     * format 7's deletes merge underfull key nodes, so a record of format 6 means another
     * tree; bergdb 026-25: format 8's KVs are rerun as one batch by the writer PE, so a record
     * of format 7 means another tree). The message named release 2026.4 until bergdb 028-15:
     * a database of a release before 2026.6 is refused by its meta block's version, before a
     * record is read.
     */
    @Nano
    private static void testRefusesFormat6() {
        Serializer serializer = new Serializer();
        serializer.serialize(new TransNodes(), 100, 200, -1, new ArrayList<Node>());
        for (int format : new int[] {6, 7, 8}) {
            byte[] buffer = serializer.getTransBuffer().clone();
            assertEquals(RECORD_FORMAT, buffer[4]);
            buffer[4] = (byte) format;
            try {
                new Parser().parse(200, buffer, TEST_ID);
                throw new AssertionError("no exception for format " + format);
            } catch (VersioningStreamException e) {
                String m = e.getMessage();
                Assert.assertTrue(m, m.contains("format version " + format + ";"));
                Assert.assertTrue(m, m.contains("older version"));
            }
        }
    }
    
    /**
     * A transaction of a larger format is refused as one of a newer BergDB (2026-10-25, bergdb
     * 005-40). Until then its message named format 2, written until 2026-10-15, as the cause.
     */
    @Nano
    private static void testRefusesNewerFormat() {
        Serializer serializer = new Serializer();
        serializer.serialize(new TransNodes(), 100, 200, -1, new ArrayList<Node>());
        for (int format : new int[] {RECORD_FORMAT + 1, 200}) {
            byte[] buffer = serializer.getTransBuffer().clone();
            buffer[4] = (byte) format;
            try {
                new Parser().parse(200, buffer, TEST_ID);
                throw new AssertionError("no exception for format " + format);
            } catch (VersioningStreamException e) {
                String m = e.getMessage();
                Assert.assertTrue(m, m.contains("format version " + format + ";"));
                Assert.assertTrue(m, m.contains("newer version"));
                Assert.assertFalse(m, m.contains("format 2"));
            }
        }
    }
    
    @Nano
    private static void testSerializeWithGotDirtyIds() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        ArrayList<Node> gotDirty = new ArrayList<Node>();
        
        KeyNode n1 = new KeyNode();
        n1.setId(1000L);
        KeyNode n2 = new KeyNode();
        n2.setId(2000L);
        
        gotDirty.add(n1);
        gotDirty.add(n2);
        
        serializer.serialize(transNodes, 100, 200, -1, gotDirty);
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(200, buffer, TEST_ID);
        
        assertEquals(4, parser.gotDirtyIdsAndSpos.length);
        assertEquals(1000L, parser.gotDirtyIdsAndSpos[0]);
        assertEquals(2000L, parser.gotDirtyIdsAndSpos[2]);
    }
    
    @Nano
    static void testSerializeTransWithDelete() {
        Serializer s = new Serializer();
        TransNodes transNodes = new TransNodes();
        transNodes.addValueNode(ValueNode.createDelete(), Keys.toSegments("key1"));
        s.serialize(transNodes, 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = s.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(200, buffer, TEST_ID);
        
        StoredNode[] stored = parser.nodes;
        assertEquals(1, stored.length);
        assertEquals(Node.TYPE_DELETE, stored[0].getNode().getType());   
    }

    @Nano
    private static void testSerializeWithNewStartupPos1() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        serializer.serialize(transNodes, 100, 200, 12345, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(200, buffer, TEST_ID);
        
        assertEquals(12345, parser.startupPos);
    }
    
    @Nano
    private static void testSerializeWithNewStartupPos2() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        serializer.serialize(transNodes, 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(200, buffer, TEST_ID);
        
        assertEquals(-1, parser.startupPos);
        assertFalse(parser.hasNewStartupPos());
    }
    
    @Nano
    private static void testSerializeAndCheckKey() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        ValueNode v0 = new ValueNode(new byte[]{});
        KeyNode n = new KeyNode();
        n.setId(101);
        n.addKlong(10, Klong.createKey(StringUtil.toBytes("a")), v0, AccessData.DEFAULT_ACCESS_DATA);
        
        transNodes.addValueNode(v0, Keys.toSegments("a"));
        transNodes.addKeyNode(n);
        
        serializer.serialize(transNodes, 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer();
        Parser parser = new Parser();
        parser.parse(200, buffer, TEST_ID);
        
        assertEquals(2, parser.nodes.length);
        assertEquals(Node.TYPE_VALUE, parser.nodes[1].getNode().getType());
        assertArrayEquals(Keys.toSegments("a"), ((StoredValueNode) parser.nodes[1]).getKey());
    }
    
    @Nano
    private static void testSerializeAndCheckKey2() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        ValueNode v0 = new ValueNode(new byte[]{});
        transNodes.addValueNode(v0, Keys.toSegments("a"));
        
        long time = 120;
        long transPos = RecoverableStream.META_BLOCK_SIZE;  // was 0, in the first meta block,
                // where no transaction starts and no value node is (bergdb 005-34)
        serializer.serialize(transNodes, time, transPos, -1, new ArrayList<Node>());
        Parser parser = new Parser();
        parser.parse(transPos, serializer.getTransBuffer(), TEST_ID);
        
        assertEquals(1, parser.nodes.length);
        assertEquals(Node.TYPE_VALUE, parser.nodes[0].getNode().getType());
        StoredValueNode node = (StoredValueNode) parser.nodes[0];
        assertArrayEquals(Keys.toSegments("a"), node.getKey());
    }
    
    /**
     * The same transaction must give the same bytes, whatever the serializer serialized
     * before. Needed for streams that are the same byte for byte with and without
     * restarts (T2 in bergdb 027-01, sis-model.md). Regression test for a bug found 2026-10-12
     * (level 2): the alignment padding of value nodes was not
     * written, so a reused buffer gave other padding bytes and checksums.
     */
    @Nano
    private static void testSameBytesFromReusedSerializer() {
        Serializer fresh = new Serializer();
        Serializer reused = new Serializer();

        byte[] earlier = new byte[64];
        java.util.Arrays.fill(earlier, (byte) 99);
        reused.serialize(transWithValue(earlier), 10, 1024, 128, new ArrayList<Node>());

        // A value of 1 byte and a key of 1 segment: 3 bytes of padding.
        reused.serialize(transWithValue(new byte[]{42}), 20, 2048, 128, new ArrayList<Node>());
        fresh.serialize(transWithValue(new byte[]{42}), 20, 2048, 128, new ArrayList<Node>());

        assertEquals(fresh.getOutputTransSize(), reused.getOutputTransSize());
        byte[] a = java.util.Arrays.copyOf(fresh.getTransBuffer(), fresh.getOutputTransSize());
        byte[] b = java.util.Arrays.copyOf(reused.getTransBuffer(), reused.getOutputTransSize());
        assertArrayEquals(a, b);
    }

    /**
     * Bergdb 028-67, C3: bytes 5 to 7 of a record's header hold the low 24 bits of CRC-32C
     * over the database's ID, the record's position and the header's bytes 0 to 4 and 8 to
     * 31, little-endian; a parse refuses the record at another position or of another
     * database, and with any one bit of its header flipped (a flip of the format byte as
     * another format, VersioningStreamException, as before).
     */
    @Nano
    private static void testHeaderCheck() {
        final byte[] id = new byte[16];
        for (int i = 0; i < id.length; i++) {
            id[i] = (byte) (31 * i + 7);
        }
        Serializer serializer = new Serializer();
        System.arraycopy(id, 0, serializer.databaseId, 0, 16);
        serializer.serialize(transWithValue(new byte[] {1, 2, 3}), 100, 2048, 128,
                new ArrayList<Node>());
        final byte[] buffer = java.util.Arrays.copyOf(serializer.getTransBuffer(),
                serializer.getOutputTransSize());
        
        CRC32C crc = new CRC32C();
        crc.update(id, 0, 16);
        byte[] pos = new byte[8];
        Bytes.longToBytesLE(2048, pos, 0);
        crc.update(pos, 0, 8);
        crc.update(buffer, 0, 5);
        crc.update(buffer, 8, 24);
        assertEquals((int) crc.getValue() & 0xffffff, (buffer[5] & 0xff)
                | (buffer[6] & 0xff) << 8 | (buffer[7] & 0xff) << 16);
        assertEquals(100, parse(2048, buffer, id).tt);
        
        byte[] otherId = id.clone();
        otherId[15] ^= 1;
        for (Object[] c : new Object[][] {{2040L, id}, {2056L, id}, {2048L + 200000, id},
                {2048L, otherId}, {2048L, TEST_ID}}) {
            try {
                parse((Long) c[0], buffer, (byte[]) c[1]);
                throw new AssertionError("parsed at " + c[0]);
            } catch (StreamFormatException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("does not hold its "
                        + "check (bergdb 028-67, C3)"));
            }
        }
        
        for (int i = 0; i < HEADER_SIZE; i++) {
            for (int bit = 0; bit < 8; bit++) {
                byte[] b = buffer.clone();
                b[i] ^= (byte) (1 << bit);
                try {
                    parse(2048, b, id);
                    throw new AssertionError("parsed with bit " + bit + " of byte " + i
                            + " flipped");
                } catch (VersioningStreamException e) {
                    assertEquals(4, i);
                } catch (StreamFormatException e) {
                    Assert.assertTrue("byte " + i, i != 4);
                }
            }
        }
    }
    
    /**
     * Bergdb 028-67, C1: RECORD_CHECK, the Core's check of a header for the start's
     * recovery. A whole header checks for its own position and ID only; a header that the end
     * of the stream cuts fits if its size is one the writer writes (48 or more, a multiple of
     * 8, at most MAX_RECORD_SIZE) and its format byte, if there, is RECORD_FORMAT; another
     * format is refused (checkFormat()) as NodeStream refuses it.
     */
    @Nano
    private static void testRecordCheck() {
        final RecoverableStream.RecordCheck c = RECORD_CHECK;
        assertEquals(32, c.headerSize());
        Serializer serializer = new Serializer();
        serializer.serialize(transWithValue(new byte[] {1}), 100, 4096, 128,
                new ArrayList<Node>());
        final byte[] record = java.util.Arrays.copyOf(serializer.getTransBuffer(),
                serializer.getOutputTransSize());
        final byte[] header = java.util.Arrays.copyOf(record, 32);
        Assert.assertTrue(c.headerChecks(4096, header, TEST_ID));
        assertFalse(c.headerChecks(4104, header, TEST_ID));
        Assert.assertTrue(c.recordProblem(4096, record, TEST_ID) == null);
        Assert.assertTrue(c.recordProblem(4104, record, TEST_ID) != null);
        
        for (int length = 4; length < 32; length++) {
            Assert.assertTrue("length " + length, c.tornHeaderFits(4096, header, length));
        }
        for (int size : new int[] {-8, 0, 40, 49, 52, Integer.MAX_VALUE}) {
            byte[] h = header.clone();
            Bytes.intToBytesLE(size, h, 0);
            assertFalse("size " + size, c.tornHeaderFits(4096, h, 20));
        }
        byte[] h = header.clone();
        h[4] = 8;
        assertFalse(c.tornHeaderFits(4096, h, 5));
        Assert.assertTrue(c.tornHeaderFits(4096, h, 4));
        try {
            c.checkFormat(4096, h);
            throw new AssertionError("format 8 passed");
        } catch (VersioningStreamException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("format version 8;"));
        }
        c.checkFormat(4096, header);
    }
    
    private static TransNodes transWithValue(byte[] value) {
        ValueNode node = new ValueNode(value);
        node.setId(1001);
        TransNodes transNodes = new TransNodes();
        transNodes.addValueNode(node, Keys.toSegments("a"));
        return transNodes;
    }

    /**
     * findNode() (bergdb 021-16, Q2): the node of an id, the first of two nodes with one id,
     * null for an id that no node has, and the nodes of a new array after one is set; in
     * time linear in the count of nodes, as the start's rerun calls it for each node it
     * makes. It scanned the nodes at each call: 200,000 lookups among 100,001 nodes took
     * seconds.
     */
    @Nano
    private static void testFindNode() {
        final int n = 100 * 1000;
        final StoredTrans s = new StoredTrans();
        final ValueNode[] values = new ValueNode[n];
        s.nodes = new StoredNode[n + 1];
        for (int i = 0; i < n; i++) {
            values[i] = new ValueNode(new byte[] {(byte) i});
            values[i].setId(1000 + 2L * i);
            s.nodes[i] = StoredValueNode.create(values[i], Keys.toSegments("k" + i));
        }
        final ValueNode twin = new ValueNode(new byte[] {7});
        twin.setId(1000);
        s.nodes[n] = StoredValueNode.create(twin, Keys.toSegments("twin"));
        
        final long t0 = System.nanoTime();
        for (int i = 0; i < n; i++) {
            Assert.assertTrue("the node of id " + (1000 + 2L * i),
                    s.findNode(1000 + 2L * i) == values[i]);
            Assert.assertTrue("no node of id " + (1001 + 2L * i),
                    s.findNode(1001 + 2L * i) == null);
        }
        final long ms = (System.nanoTime() - t0) / 1000000;
        // A scan of the 100,000 nodes a lookup takes minutes; 20 s leaves room for load
        // (bergdb 028-23; 2 s until then).
        Assert.assertTrue("200,000 lookups took " + ms + " ms", ms < 20000);
        
        s.nodes = new StoredNode[] {StoredValueNode.create(twin, Keys.toSegments("twin"))};
        Assert.assertTrue("the new array's node", s.findNode(1000) == twin);
        Assert.assertTrue("not in the new array", s.findNode(1002) == null);
        
        // A scan, up to FIND_NODE_SCAN_LIMIT nodes, and a map above it: the same answers.
        for (int size : new int[] {2, FIND_NODE_SCAN_LIMIT, FIND_NODE_SCAN_LIMIT + 1}) {
            s.nodes = new StoredNode[size];
            for (int i = 0; i < size - 1; i++) {
                s.nodes[i] = StoredValueNode.create(values[i], Keys.toSegments("k" + i));
            }
            s.nodes[size - 1] = StoredValueNode.create(twin, Keys.toSegments("twin"));
            Assert.assertTrue(size + " nodes: the first of id 1000",
                    s.findNode(1000) == values[0]);
            Assert.assertTrue(size + " nodes: the last",
                    s.findNode(1000 + 2L * (size - 2)) == values[size - 2]);
            Assert.assertTrue(size + " nodes: none", s.findNode(999) == null);
        }
    }
    
    @Nano
    private static void testGetValueNode() {
        StoredTrans s = new StoredTrans();
        
        s.nodes = new StoredNode[2];
        s.nodes[0] = StoredValueNode.create(new ValueNode(new byte[1]), Keys.toSegments("adam"));
        s.nodes[1] = StoredValueNode.create(new ValueNode(new byte[2]), Keys.toSegments("eve"));
        
        ValueNode v = s.getValueNode(Keys.toSegments("kalle"));
        Assert.assertNull(v);
        
        v = s.getValueNode(Keys.toSegments("adam"));
        Assert.assertEquals(1, v.getValue().length);
        
        v = s.getValueNode(Keys.toSegments("eve"));
        Assert.assertEquals(2, v.getValue().length);
    }
}
