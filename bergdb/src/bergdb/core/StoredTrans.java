package bergdb.core;

import java.util.ArrayList;
import java.util.List;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.dag.AccessData;
import bergdb.dag.INode;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import static bergdb.nanotest.Assert.assertEquals;
import static bergdb.nanotest.Assert.assertArrayEquals;
import bergdb.nanotest.T;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;

/**
 * This class and its inner classes are responsible serializing transactions to bytes
 * and to parse transactions from raw bytes.
 * Performance is important enough here that is may take precedence over
 * pretty code.
 * 
 * @author Frans Lundberg
 */
public class StoredTrans {
    /** Transaction time. */
    public final long tt;

    /** First spos of transaction (tpos). */
    public final long pos;

    /** The spos of the last byte of the transaction. */
    public final long lastPos;

    /** The nodes of the transaction. */
    public final StoredNode[] nodes;

    private StoredTrans(Parser d) {
        tt = d.transactionTime;
        pos = d.pos;
        lastPos = d.lastPos;
        nodes = d.nodes;
    }
    
    public Trans createRerunTransaction() {
        // NOTE needs to handle DELETE ops later.
        
        List<StoredValueNode> storedValueNodes = extractValueNodes();
        
        Trans.Builder b = Trans.builder();
        for (StoredValueNode n : storedValueNodes) {
            assert n.getKey() != null : "key is null, " + n;
            assert n.getKey().length > 0 : "Bad key, zero-length";
            b.put(n.getKey(), n.getNode().getValue());
        }
        
        Trans trans = b.build();
        trans.isInternal = true;
        trans.pos = pos;
        trans.lastPos = lastPos;
        trans.time = tt;
        
        return b.build();
    }

    private List<StoredValueNode> extractValueNodes() {
        List<StoredValueNode> storedValueNodes = new ArrayList<StoredValueNode>();
        
        for (StoredNode n : nodes) {
            if (n.getNode().getType() == INode.TYPE_VALUE) {
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
        b.append("tt:" + tt + ", transPos:" + pos);
        b.append(", nodeCount:" + this.nodes.length);
        return b.toString();
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
    private static class Parser {
        long transactionTime;
        long pos;
        long lastPos;
        StoredNode[] nodes;

        int offset = 0;

        /**
         * Parses a transaction starting at buffer[0].
         * buffer.length may be longer than required to store the transaction.
         */
        void parse(long transPos, byte[] buffer) {
            if (buffer == null) {
                throw new IllegalArgumentException("buffer == null not allowed");
            }

            if (buffer.length < 16 + 1) {
                throw new StreamFormatException("buffer too short, " + buffer.length);
            }

            if (transPos < 0) {
                throw new IllegalArgumentException("transPos < 0, " + transPos);
            }

            this.pos = transPos;
            offset = 0;
            int byteSize = Bytes.bytesToIntLE(buffer, offset);
            offset += 4;

            if (buffer.length < byteSize) {
                throw new StreamFormatException("buffer too small, size in header: " 
                        + byteSize + ", buffer size: " + buffer.length + ".");
            }

            offset += 4; // 4 unused bytes
            transactionTime = Bytes.bytesToLongLE(buffer, offset);
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

            nodes = nodeList.toArray(new StoredNode[nodeList.size()]);
            lastPos = RecoverableStream.getSpos(transPos, offset - 1);
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

            long spos = RecoverableStream.getSpos(pos, offset);
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
        private long transTime;
        private long transStartPos;
        private long transNextSpos;
        private long transLastSpos;

        /** Number of times serialize() has been called. */
        private long counter;

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
         */
        public void serialize(TransNodes transNodes, long transTime, long transStartPos) {
            assert transNodes != null;
            assert transTime >= 0;
            assert transStartPos >= 0;

            this.transNodes = transNodes;
            this.transStartPos = transStartPos;
            this.transTime = transTime;

            prepareToSerialize();
            serializeToBuffer();
        }

        /** Returns the transaction buffer with the serialized transaction. */
        public final byte[] getOutputTransBuffer() {
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
         * Prepare for serialization by computing sizes; sets totalSize, transLastSpos,
         * transNextSpos.
         */
        private void prepareToSerialize() {
            // The three node loops sets new stream pos of nodes, sets ID if needed,
            // Also computes totalSize and sets prevPos array for KeyNodes.

            totalSize = 16; // Header size, trans size, 4 empty, trans time
            long currentPos = RecoverableStream.getSpos(transStartPos, totalSize);

            resizePrevPosIfNeeded();

            // Prepares topNodes.
            for (int i = 0; i < transNodes.topSize; i++) {
                TopNode node = transNodes.topNodes[i];
                node.spos = currentPos;
                node.id = (node.id == Spos.NULL) ? currentPos : node.id;
                totalSize += StoredTopNode.getByteSize(node);
                currentPos = RecoverableStream.getSpos(transStartPos, totalSize);
            }

            // Prepares keyNodes.
            {
                int prevPosIndex = 0;
                for (int i = 0; i < transNodes.keySize; i++) {
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
            for (int i = 0; i < transNodes.valueSize; i++) {
                ValueNode node = transNodes.valueNodes[i];
                long[] key = transNodes.keys[i];
                node.spos = currentPos;
                totalSize += StoredValueNode.getByteSize(node, key);
                currentPos = RecoverableStream.getSpos(transStartPos, totalSize);
            }

            totalSize += 4;

            totalSize = totalSize + 1;
            // Adds room for RecoverableStream.LAST_BYTE.

            // For totalSize to be a multiple of TRANS_ALIGNMENT.

            extraZeros = NodeStream.TRANS_ALIGNMENT - totalSize % NodeStream.TRANS_ALIGNMENT;
            totalSize += extraZeros;
            assert totalSize % NodeStream.TRANS_ALIGNMENT == 0 : totalSize + ", " + extraZeros;

            transLastSpos = RecoverableStream.getSpos(transStartPos, totalSize - 1);
            transNextSpos = RecoverableStream.getSpos(transStartPos, totalSize);
        }

        private void serializeToBuffer() {
            //
            // Code to serialize causes significant execution time (30-40%) for PUT operations.
            // We could possibly return quickly and let another thread serialize nodes.
            // Possibly the thread that handles flushing the buffer could be used, or a separate
            // one. KeyNode.size and order of transactions would need to be handled.
            //

            int longOffset = 0;
            int byteOffset;

            resizeBuffersIfNeeded();
            longOffset = serializeHeader(longOffset);
            byteOffset = serializeNodes(longOffset);
            byteOffset = serializeEnd(byteOffset);

            assert byteOffset == totalSize;
            assert totalSize % 8 == 0;
        }

        private int serializeHeader(int longOffset) {
            longBuffer[longOffset] = totalSize; // Note, 4 bytes available, int-to-long conversion.
            longOffset += 1;
            longBuffer[longOffset] = transTime;
            longOffset += 1;
            return longOffset;
        }

        private int serializeNodes(int longOffset) {
            int offset = 0;
            int prevPosIndex = 0;

            for (int i = 0; i < transNodes.topSize; i++) {
                TopNode topNode = transNodes.topNodes[i];
                longOffset += StoredTopNode.toLongs(topNode, longBuffer, longOffset);
            }

            for (int i = 0; i < transNodes.keySize; i++) {
                KeyNode keyNode = transNodes.keyNodes[i];
                longOffset += StoredKeyNode.toLongs(keyNode, longBuffer, longOffset,
                        prevPos[prevPosIndex++]);
            }

            // Copies from longBuffer to byteBuffer, top nodes and value nodes.
            offset = copyLongBufferToByteBuffer(longOffset, offset);

            for (int i = 0; i < transNodes.valueSize; i++) {
                ValueNode n = transNodes.valueNodes[i];
                long[] skey = transNodes.keys[i];
                offset += StoredValueNode.toBytes(n, skey, byteBuffer, offset);
            }
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

        private int serializeEnd(int offset) {
            // Zero to indicate end of nodes.
            Bytes.intToBytesLE(0, byteBuffer, offset);
            offset += 4;

            System.arraycopy(NodeStream.ZEROS64, 0, byteBuffer, offset, extraZeros);
            offset += extraZeros;

            // End of buffer (LAST_BYTE indicates a valid transaction).

            byteBuffer[offset] = RecoverableStream.LAST_BYTE;
            offset += 1;
            return offset;
        }

        private void resizePrevPosIfNeeded() {
            // 10007 is a prime.

            if (counter % 10007 == 0) {
                int newSize = Math.max(INIT_SIZE_OF_PREV_POS, transNodes.keySize);
                if (prevPos.length != newSize) {
                    prevPos = new long[newSize];
                }
            }

            if (this.prevPos.length < transNodes.keySize) {
                this.prevPos = new long[(int) (transNodes.keySize * 1.20)];
            }
        }

        private void resizeBuffersIfNeeded() {
            if (counter % 10007 == 0) {
                int newSize = Math.max(INIT_SIZE_OF_BYTE_BUFFER, totalSize);
                if (byteBuffer.length != newSize) {
                    byteBuffer = new byte[newSize];
                }

                newSize = Math.max(INIT_SIZE_OF_LONG_BUFFER, topAndKeySize / 8);
                if (longBuffer.length != newSize) {
                    longBuffer = new long[newSize];
                }
            }

            if (this.byteBuffer.length < totalSize) {
                this.byteBuffer = new byte[(int) (totalSize * 1.10)];
            }

            if (this.longBuffer.length < (topAndKeySize / 8) + 8) {
                this.longBuffer = new long[(int) (topAndKeySize / 8 + 8)];
            }
        }
    }
    
    
    // ======== Tests ========
    
    @T
    private static void testKvSanity() {
        byte[] key = new byte[]{1};
        byte[] value = new byte[]{1, 2};
        
        Kv kv = new Kv(key, value);
        Assert.assertArrayEquals(new byte[]{1}, kv.key);
        Assert.assertArrayEquals(new byte[]{1, 2}, kv.value);
    }
    
    @T
    private static void testSerialize1() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        serializer.serialize(transNodes, 100, 200);
        byte[] buffer = serializer.getOutputTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(200, buffer);
        
        assertEquals(0, parser.nodes.length);
        assertEquals(100, parser.transactionTime);
        assertEquals(200, parser.pos);
    }
    
    @T
    private static void testSerialize2() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        ValueNode v0 = new ValueNode(new byte[]{});
        ValueNode v1 = new ValueNode(new byte[]{12});
        ValueNode v2 = new ValueNode(new byte[]{13, 14});
        
        KeyNode n = new KeyNode();
        n.addKlong(10, Klong.create(Util.toBytes("a")), v0, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(20, Klong.create(Util.toBytes("b")), v1, AccessData.DEFAULT_ACCESS_DATA);
        n.addKlong(30, Klong.create(Util.toBytes("c")), v2, AccessData.DEFAULT_ACCESS_DATA);
        
        transNodes.addValueNode(v0, Keys.toSegments("a"));
        transNodes.addValueNode(v1, Keys.toSegments("b"));
        transNodes.addValueNode(v2, Keys.toSegments("c"));
        transNodes.addKeyNode(n);
        
        serializer.serialize(transNodes, 100, 200);
        byte[] buffer = serializer.getOutputTransBuffer();
        
        Parser parser = new Parser();
        parser.parse(200, buffer);
        
        assertEquals(4, parser.nodes.length);
        assertEquals(100, parser.transactionTime);
        assertEquals(200, parser.pos);
        assertEquals(INode.TYPE_KEY_NODE, parser.nodes[0].getNode().getType());
        assertEquals(INode.TYPE_VALUE, parser.nodes[1].getNode().getType());
        assertEquals(INode.TYPE_VALUE, parser.nodes[2].getNode().getType());
        assertEquals(INode.TYPE_VALUE, parser.nodes[3].getNode().getType());
        
        byte[] value1 = ((ValueNode) parser.nodes[2].getNode()).value.clone();
        Assert.assertArrayEquals(new byte[]{12}, value1);
        
        byte[] value2 = ((ValueNode) parser.nodes[3].getNode()).value.clone();
        Assert.assertArrayEquals(new byte[]{13, 14}, value2);
    }
    
    @T
    private static void testSerializeAndCheckKey() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        ValueNode v0 = new ValueNode(new byte[]{});
        KeyNode n = new KeyNode();
        n.addKlong(10, Klong.create(Util.toBytes("a")), v0, AccessData.DEFAULT_ACCESS_DATA);
        
        transNodes.addValueNode(v0, Keys.toSegments("a"));
        transNodes.addKeyNode(n);
        
        serializer.serialize(transNodes, 100, 200);
        byte[] buffer = serializer.getOutputTransBuffer();
        Parser parser = new Parser();
        parser.parse(200, buffer);
        
        assertEquals(2, parser.nodes.length);
        assertEquals(INode.TYPE_VALUE, parser.nodes[1].getNode().getType());
        assertArrayEquals(Keys.toSegments("a"), ((StoredValueNode) parser.nodes[1]).getKey());
    }
    
    @T
    private static void testSerializeAndCheckKey2() {
        Serializer serializer = new Serializer();
        TransNodes transNodes = new TransNodes();
        
        ValueNode v0 = new ValueNode(new byte[]{});
        transNodes.addValueNode(v0, Keys.toSegments("a"));
        
        long time = 120;
        long transPos = 0;
        serializer.serialize(transNodes, time, transPos);
        Parser parser = new Parser();
        parser.parse(transPos, serializer.getOutputTransBuffer());
        
        assertEquals(1, parser.nodes.length);
        assertEquals(INode.TYPE_VALUE, parser.nodes[0].getNode().getType());
        StoredValueNode node = (StoredValueNode) parser.nodes[0];
        assertArrayEquals(Keys.toSegments("a"), node.getKey());
    }
    
    @T
    private static void testCreateRerunTransaction() {
        Serializer serializer = new Serializer();
        TransNodes nodes = new TransNodes();
        nodes.addValueNode(new ValueNode(new byte[]{1, 2, 3}), Keys.toSegments("key1"));
        serializer.serialize(nodes, 101, 0);
        byte[] buffer = serializer.getOutputTransBuffer();
        
        StoredTrans stored = StoredTrans.parse(0, buffer);
        Trans trans = stored.createRerunTransaction();
        
        assertEquals(1, trans.kvs.length);
        assertArrayEquals(new byte[]{1, 2, 3}, trans.kvs[0].getValue());
        assertArrayEquals(Keys.toSegments("key1"), trans.kvs[0].getKey());
    }
}
