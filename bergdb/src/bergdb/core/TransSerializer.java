package bergdb.core;

import bergdb.common.Bytes;
import bergdb.dag.KeyNode;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.TransNodes;
import bergdb.dag.ValueNode;
import bergdb.storage.RecoverableStream;

/**
 * Class used to serialize a transaction to bytes. For performance reasons, an object of this class
 * can be reused to serialize multiple transactions. It has internal buffers that may be large and
 * would be expensive to allocate each time a transaction is serialized. This class is not
 * thread-safe.
 * 
 * @author Frans Lundberg
 */
public class TransSerializer {
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
    public TransSerializer() {
        longBuffer = new long[INIT_SIZE_OF_LONG_BUFFER];
        byteBuffer = new byte[INIT_SIZE_OF_BYTE_BUFFER];
        prevPos = new long[INIT_SIZE_OF_PREV_POS];
        counter = 0;
    }

    /**
     * Serializes the transaction given the transactions nodes. Use the getOutputX() methods to get
     * the result.
     * 
     * @param transTime
     *            The transaction time.
     * @param transStartPos
     *            The spos of the first byte of the transaction.
     */
    public void serialize(TransNodes transNodes, long transTime, long transStartPos) {
        assert transNodes != null;
        assert transTime >= 0;
        assert transStartPos > 0;

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
     * Prepare for serialization by computing sizes, needed to 
     * get totalSize and 
     */
    private void prepareToSerialize() {
        // Below three loops sets new stream pos of nodes, sets ID if needed,
        // Also computes totalSize and sets prevPos array for KeyNodes.

        int prevPosIndex = 0;

        totalSize = 16; // Header size, trans size, 4 empty, trans time
        long pos = RecoverableStream.getSpos(transStartPos, totalSize);

        resizePrevPosIfNeeded();

        // Loop topNodes.
        for (int i = 0; i < transNodes.topSize; i++) {
            TopNode node = transNodes.topNodes[i];
            node.spos = pos;
            node.id = (node.id == Spos.NULL) ? pos : node.id;
            totalSize += StoredTopNode.getByteSize(node);
            pos = RecoverableStream.getSpos(transStartPos, totalSize);
        }

        // Loop keyNodes.
        for (int i = 0; i < transNodes.keySize; i++) {
            KeyNode node = transNodes.keyNodes[i];
            prevPos[prevPosIndex++] = node.spos;
            node.spos = pos;
            node.id = (node.id == Spos.NULL) ? pos : node.id;
            //totalSize += node.getByteSize();
            totalSize += StoredKeyNode.getByteSize(node);
            pos = RecoverableStream.getSpos(transStartPos, totalSize);
        }

        topAndKeySize = totalSize;

        // Loop valueNodes.
        for (int i = 0; i < transNodes.valueSize; i++) {
            ValueNode node = transNodes.valueNodes[i];
            node.spos = pos;
            totalSize += StoredValueNode.getByteSize(node, transNodes.choices[i].size);
            pos = RecoverableStream.getSpos(transStartPos, totalSize);
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
        // Possibly the thread that handles flushing the buffer could be used, or a separate one.
        // KeyNode.size and order of transactions would need to be stored.
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
            offset += StoredValueNode.toBytes(n, transNodes.choices[i], byteBuffer, offset);
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
