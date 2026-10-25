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
     * 5 since 2026-10-15: the header holds topPos (docs/level2-alignment.md, M18). Before, 2,
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
     * only the framing (2026-10-25, bergdb 005-40).</p>
     */
    public final static byte RECORD_FORMAT = 5;
    
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
     * the startup time of this record (docs/level2-alignment.md, 8.3). Spos.NULL if none.
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
     * does not exist.
     */
    public Node findNode(long id) {
        for (StoredNode stored : nodes) {
            if (stored.getNode().getId() == id) {
                return stored.getNode();
            }
        }
        
        return null;
    }

    /**
     * Creates and returns a list of the value nodes of the transaction.
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
                + "which cannot be opened: format 2 was written until 2026-10-15 "
                + "(docs/level2-alignment.md, M18).";
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
            int byteSize = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;

            if (buffer.length < byteSize) {
                throw new StreamFormatException("buffer too small, size in header: " 
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
            
            int gotDirtyCount = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;
            
            if (gotDirtyCount < 0 || gotDirtyCount > (buffer.length - offset) / 16) {
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
            int transSize = transSizeBefore + count;
            lastPos = RecoverableStream.getSpos(tpos, transSize - 1);
            
            assert lastPos % NodeStream.TRANS_ALIGNMENT == (NodeStream.TRANS_ALIGNMENT - 1) 
                    : "Bad lastPos: " + lastPos + ", transSize:" + transSize + ", transPos: " + tpos;
        }
        
        boolean hasNewStartupPos() {
            return startupPos != -1;
        }

        private StoredNode next(byte[] buffer) {
            if (offset + 4 >= buffer.length) {
                return null;
            }

            int nodeSize = Bytes.bytesToIntLE(buffer, offset);
            if (nodeSize == 0) {
                offset += 4;
                return null;
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
                this.prevPos = new long[(int) (transNodes.keyCount * 1.20)];
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
                int newSize = (int) Math.max(totalSize, 
                        Math.min((long) (totalSize * 1.20), MAX_RECORD_SIZE));
                
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
     * A transaction of the format before 2026-10-15 (2) is refused with a clear message, as a
     * VersioningStreamException since 2026-10-25 (bergdb 005-40).
     */
    @Nano
    private static void testRefusesOldFormat() {
        Serializer serializer = new Serializer();
        serializer.serialize(new TransNodes(), 100, 200, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer().clone();
        assertEquals(RECORD_FORMAT, buffer[4]);
        buffer[4] = 2;
        
        try {
            new Parser().parse(200, buffer);
            throw new AssertionError("no exception for format 2");
        } catch (VersioningStreamException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("format version 2;"));
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("older version"));
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
        for (int format : new int[] {6, 200}) {
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
    public static void testSerializeTransWithDelete() {
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
     * restarts (T2 in docs/sis-model.md). Regression test for a bug found 2026-10-12
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
