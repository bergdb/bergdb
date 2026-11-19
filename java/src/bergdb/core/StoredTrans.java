package bergdb.core;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
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
     * before it writes; the zero fill of a torn record, before its format is read, uses
     * only the framing (2026-10-25, bergdb 005-40). MetaBlock's version is 155 since
     * 2026-11-18, when the startup distance left the meta block (bergdb 028-15): a change
     * that an older release cannot read, so that the older release refuses the stream before
     * it writes (the rule proposed in bergdb 026-12, SF3); a stream of version 154, of
     * release 2026.5 or earlier, is refused by its meta block, before a record is read.</p>
     */
    public final static byte RECORD_FORMAT = 8;
    
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
     * The most bytes the index nodes that one transaction makes dirty or creates may take,
     * by Db's bound at the largest node size (2026-10-24, bergdb 005-31): 15/16 of the record
     * limit. TransSeq.take writes them in the record of a later transaction, all in one; a
     * transaction whose record leaves less than 1/16 of the limit for them waits for the next.
     */
    static long dirtyLimit() {
        return recordLimit - recordLimit / 16;
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
     * Creates a StoredTrans by parsing the data in a the byte buffer.
     * 
     * @throws IllegalArgumentException
     * @throws StreamFormatException
     */
    public static StoredTrans parse(long transPos, byte[] buffer) {
        Parser p = new Parser();
        p.parse(transPos, buffer);
        return new StoredTrans(p);
    }

    /**
     * The message of a VersioningStreamException for a record whose format byte is not
     * RECORD_FORMAT: it says whether the stream was written by an older or a newer BergDB
     * (2026-10-25, bergdb 005-40). Before, every other format got the message of format 2.
     */
    static String formatRefused(byte version) {
        int v = version & 0xff;
        String s = "Cannot parse stored transaction of format version " + v + "; this version "
                + "of BergDB reads format " + RECORD_FORMAT + " only. ";
        if (v > RECORD_FORMAT) {
            return s + "A larger number is a database written by a newer version of BergDB.";
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
         * Parses a transaction starting at buffer[0].
         * buffer.length may be longer than required to store the transaction.
         */
        void parse(long tpos, byte[] buffer) {
            if (buffer == null) {
                throw new IllegalArgumentException("buffer == null not allowed");
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

            offset += 3;     // three unused bytes
            
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
            
            if (size > recordLimit) {
                throw new DbException("The record of the transaction would take " + size 
                        + " bytes, more than the limit, " + recordLimit + " (bergdb 005-17).");
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
                offset += StoredValueNode.toBytes(n, skey, byteBuffer, offset);
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

    /** bergdb 005-74, F2: this record used to loop between its two delete nodes. */
    @Nano
    private static void testNegativeNodeSize() {
        byte[] buffer = recordWithBadNodeSize(-32);
        try {
            parse(128, buffer);
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
                parse(128, recordWithBadNodeSize(size));
                throw new AssertionError("bad node size was accepted: " + size);
            } catch (StreamFormatException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("node size"));
            }
        }
        byte[] buffer = recordWithBadNodeSize(36);
        Bytes.intToBytesLE(80, buffer, 0);    // The array is longer than the record.
        try {
            parse(128, buffer);
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
                parse(200, buffer);
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
            parse(200, buffer);
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
            new Parser().parse(200, buffer);
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
        parser.parse(200, buffer);
        
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
        parser.parse(200, buffer);
        
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
        parser.parse(200, serializer.getTransBuffer());
        
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
        parser.parse(200, serializer.getTransBuffer());
        
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
                new Parser().parse(200, buffer);
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
        for (int format : new int[] {6, 7}) {
            byte[] buffer = serializer.getTransBuffer().clone();
            assertEquals(8, buffer[4]);
            buffer[4] = (byte) format;
            try {
                new Parser().parse(200, buffer);
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
                new Parser().parse(200, buffer);
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
        parser.parse(200, buffer);
        
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
        parser.parse(200, buffer);
        
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
        parser.parse(200, buffer);
        
        assertEquals(12345, parser.startupPos);
    }
    
    @Nano
    private static void testSerializeWithNewStartupPos2() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        serializer.serialize(transNodes, 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(200, buffer);
        
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
        parser.parse(200, buffer);
        
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
        parser.parse(transPos, serializer.getTransBuffer());
        
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
