package bergdb.core;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import bergdb.common.AssertStatus;
import bergdb.common.Bytes;
import bergdb.common.Util;
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
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;

/**
 * This class and its inner classes are responsible serializing transactions to bytes
 * and to parse transactions from raw bytes.
 * For this class, performance is important enough to take precedence over pretty code.
 * 
 * @author Frans Lundberg
 */
public class StoredTrans {
    public final static byte CURRENT_FORMAT_VERSION = 3;    // serial format version (one byte).
        // 151229 - changed from 2 to 3
    
    /** Transaction time. */
    public final long tt;

    /** First spos of transaction (tpos). */
    public final long tpos;

    /** The spos of the last byte of the transaction. */
    public final long lastPos;
    
    /** The nodes of the transaction. */
    public StoredNode[] nodes;
    
    public final long startupPos;
    
    public long[] gotDirtyIds;

    
    private StoredTrans() {
        // for testing
        tt = 0;
        tpos = 0;
        lastPos = 99;
        startupPos = 0;
    }
    
    StoredTrans(Parser d) {
        tt = d.transactionTime;
        tpos = d.tpos;
        lastPos = d.lastPos;
        nodes = d.nodes;
        startupPos = d.startupPos;
        gotDirtyIds = d.gotDirtyIds;
    }
    
    public boolean isPrimordial() {
        return tpos == RecoverableStream.META_BLOCK_SIZE;
    }
    
    public boolean hasNewStartupPos() {
        return startupPos != -1;
    }
    
    public Trans createRerunTransaction(Trans.Builder b) {        
        List<StoredValueNode> storedValueNodes = extractValueNodes();
        
        for (StoredValueNode n : storedValueNodes) {
            assert n.getKey() != null : "key is null, " + n;
            assert n.getKey().length > 0 : "Bad key, zero-length";
            
            ValueNode node = n.getValueNode();
            long[] key = n.getKey();
            
            if (node.isDelete()) {
                b.delete(key);
            } else {
                b.put(key, node.getValue());
            }
        }
        
        Trans trans = b.build();
        trans.isInternal = true;
        trans.tpos = tpos;
        trans.lastPos = lastPos;
        trans.tt = tt;
        trans.isStartupRerun = true;
        trans.startupPos = startupPos;
        
        return trans;
    }
    
    public boolean isIndexTransaction() {
        boolean result = true;
        for (StoredNode stored : nodes) {
            if (!stored.getNode().isIndexNode()) {
                result = false;
                break;
            }
        }
        return result;
    }
    
    /**
     * Returns a value node matching the given key, or null if no
     * match is found. Linear search is used.
     */
    public ValueNode getValueNode(long[] key) {
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

    private List<StoredValueNode> extractValueNodes() {
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

    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append("tt:" + tt + ", tpos:" + tpos + ", lastPos:" + lastPos + ", startupPos:" + this.startupPos);
        b.append(", nodeCount:" + this.nodes.length);
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
        StoredNode[] nodes;
        long[] gotDirtyIds;

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
            
            if (version != 2) {
                throw new StreamFormatException("Cannot parse stored transaction of "
                        + "format version " + version + ".");
            }

            offset += 3;     // three unused bytes
            
            transactionTime = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
            
            startupPos = Bytes.bytesToLongLE(buffer, offset);
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
            
            if (gotDirtyCount < 0) {
                throw new StreamFormatException("bad gotDirtyCount, " + gotDirtyCount);
            }
            
            this.gotDirtyIds = new long[gotDirtyCount];
            
            for (int i = 0; i < gotDirtyCount; i++) {
                gotDirtyIds[i] = Bytes.bytesToLongLE(buffer, offset);
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
            assert transNodes != null;
            assert transTime >= 0;
            assert transStartPos >= 0;

            this.transNodes = transNodes;
            this.transStartPos = transStartPos;
            this.transTime = transTime;
            this.startupPos = startupPos;
            this.gotDirtyNodes = gotDirtyNodes;

            prepareToSerialize();
            
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
            for (int i = 0; i < transNodes.keyCount; i++) {
                KeyNode keyNode = transNodes.keyNodes[i];
                int size = keyNode.size;
                
                for (int j = 0; j < size; j++) {
                    long klong = keyNode.klongs[j];
                    if (Klong.getType(klong) == Klong.TYPE_KEY) {
                        long pos = keyNode.pos[j];
                        Node pointee = keyNode.pointers[j];
                        long spos = pointee == null ? pos : pointee.getSpos();
                        
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
                    if (!p.isNull()) {
                        spos = p.pos;
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

            totalSize = 24; // Header size, 24 = trans size (4), empty (4), trans time (8), startupPos (8)
            long currentPos = RecoverableStream.getSpos(transStartPos, totalSize);

            resizePrevPosIfNeeded();

            // Prepares topNodes.
            for (int i = 0; i < transNodes.topCount; i++) {
                TopNode node = transNodes.topNodes[i];
                node.spos = currentPos;
                node.id = (node.id == Spos.NULL) ? currentPos : node.id;
                totalSize += StoredTopNode.getByteSize(node);
                currentPos = RecoverableStream.getSpos(transStartPos, totalSize);
            }

            // Prepares keyNodes.
            {
                int prevPosIndex = 0;
                for (int i = 0; i < transNodes.keyCount; i++) {
                    KeyNode node = transNodes.keyNodes[i];
                    prevPos[prevPosIndex++] = node.spos;
                    node.spos = currentPos;
                    node.id = (node.id == Spos.NULL) ? currentPos : node.id;
                    totalSize += StoredKeyNode.getByteSize(node);
                    currentPos = RecoverableStream.getSpos(transStartPos, totalSize);
                }
            }

            topAndKeySize = totalSize;

            // Prepares valueNodes.
            for (int i = 0; i < transNodes.valueCount; i++) {
                ValueNode node = transNodes.valueNodes[i];
                long[] key = transNodes.keys[i];
                node.setSpos(currentPos);
                totalSize += StoredValueNode.getByteSize(node, key);
                currentPos = RecoverableStream.getSpos(transStartPos, totalSize);
            }

            // Marker for end of nodes
            totalSize += 4;
            
            // Number of got dirty node ids
            totalSize += 4;
            
            // Got-dirty node ids
            totalSize += 8 * gotDirtyNodes.size();

            // Room for RecoverableStream.LAST_BYTE.
            totalSize += 1;

            // For totalSize to be a multiple of TRANS_ALIGNMENT.
            extraZeros = computeZeroCount(totalSize);
            totalSize += extraZeros;
            
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
            final long FORMAT_VERSION = 2L;    // current serial format version (one byte).
            long int0 = totalSize;
            long int1 = FORMAT_VERSION;
            
            longBuffer[longOffset] = int0 | (int1 << 32);
            longOffset += 1;
            longBuffer[longOffset] = transTime;
            longOffset += 1;
            longBuffer[longOffset] = startupPos;
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
                long id = gotDirtyNodes.get(i).getId();
                Bytes.longToBytesLE(id, byteBuffer, offset);
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
                int newSize = (int) (totalSize * 1.20);
                
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
        n.addKlong(10, Klong.createKey(Util.toBytes("a")), v0, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.createKey(Util.toBytes("b")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.createKey(Util.toBytes("c")), v2, AccessData.DEFAULT_ACCESS_DATA);
        
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
        
        assertEquals(2, parser.gotDirtyIds.length);
        assertEquals(1000L, parser.gotDirtyIds[0]);
        assertEquals(2000L, parser.gotDirtyIds[1]);
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
        n.addKlong(10, Klong.createKey(Util.toBytes("a")), v0, AccessData.DEFAULT_ACCESS_DATA);
        
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
        long transPos = 0;
        serializer.serialize(transNodes, time, transPos, -1, new ArrayList<Node>());
        Parser parser = new Parser();
        parser.parse(transPos, serializer.getTransBuffer());
        
        assertEquals(1, parser.nodes.length);
        assertEquals(Node.TYPE_VALUE, parser.nodes[0].getNode().getType());
        StoredValueNode node = (StoredValueNode) parser.nodes[0];
        assertArrayEquals(Keys.toSegments("a"), node.getKey());
    }
    
    @Nano
    private static void testCreateRerunTransaction() {
        Serializer serializer = new Serializer();
        TransNodes nodes = new TransNodes();
        nodes.addValueNode(new ValueNode(new byte[]{1, 2, 3}), Keys.toSegments("key1"));
        serializer.serialize(nodes, 101, 0, -1, new ArrayList<Node>());
        byte[] buffer = serializer.getTransBuffer();
        
        StoredTrans stored = StoredTrans.parse(0, buffer);
        Trans trans = stored.createRerunTransaction(Trans.Builder.ForDb.create());
        
        assertEquals(1, trans.kvs.length);
        assertArrayEquals(new byte[]{1, 2, 3}, trans.kvs[0].getValue());
        assertArrayEquals(Keys.toSegments("key1"), trans.kvs[0].getKey());
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
