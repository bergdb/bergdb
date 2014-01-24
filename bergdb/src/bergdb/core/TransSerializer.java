package bergdb.core;

import bergdb.common.Bytes;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.TransNodes;
import bergdb.dag.ValueNode;
import bergdb.storage.RecoverableStream;

/**
 * Class used to serialize a transaction to the stream.
 * For performance reasons, an object of this class can be reused to
 * serialize multiple transactions. This class is not thread-safe.
 * 
 * @author Frans Lundberg
 */
public class TransSerializer {
    // NOTE We current have no checksum for keys.
    
    private static final int INIT_SIZE_OF_BYTE_BUFFER = 100*1000;
    private static final int INIT_SIZE_OF_LONG_BUFFER = 10*1000;
    private static final int INIT_SIZE_OF_PREV_POS = 100;
    
    private long[] longBuffer;
    private byte[] byteBuffer;
    private int totalSize;
    private int topAndKeySize;
    private long[] prevPos;
    private int extraZeros;
    private TransNodes transNodes;
    private Trans trans;
    private boolean writeMetaBlock = false;
    private long appendNodesCounter;
    
    
    public TransSerializer() {
        longBuffer = new long[INIT_SIZE_OF_LONG_BUFFER];
        byteBuffer = new byte[INIT_SIZE_OF_BYTE_BUFFER];
        prevPos = new long[INIT_SIZE_OF_PREV_POS];
    }
    
    /**
     * Prepares for serialization.
     * 
     * @param trans
     * @param transNodes
     * @param transStartPos
     * @param appendNodesCounter  
     *  A counter that increases with 1 for each transaction that is appended to the stream.
     * 
     */
    public void prepare(Trans trans, TransNodes transNodes, 
            long transStartPos, long appendNodesCounter) {
        // Below three loops sets new stream pos of nodes, sets ID if needed, and sets isDirty = false.
        // Also computes totalSize and sets prevPos array for KeyNodes.
        
        assert trans != null;
        assert transNodes != null;
        
        this.appendNodesCounter = appendNodesCounter;
        this.trans = trans;
        this.transNodes = transNodes;
        int prevPosIndex = 0;
        
        totalSize = 16;        // Header size, trans size, 4 empty, trans time
        long pos = RecoverableStream.getSpos(transStartPos, totalSize);
        
        resizePrevPosIfNeeded();
        
        // Loop topNodes.
        for (int i = 0; i < transNodes.topSize; i++) {
            final TopNode n1 = transNodes.topNodes[i];
            n1.spos = pos;
            n1.id = (n1.id == Spos.NULL) ? pos : n1.id;
            totalSize += n1.getByteSize();
            pos = RecoverableStream.getSpos(transStartPos, totalSize);
        }
        
        // Loop keyNodes.
        for (int i = 0; i < transNodes.keySize; i++) {
            final KeyNode n = transNodes.keyNodes[i];
            prevPos[prevPosIndex++] = n.spos;
            n.spos = pos;
            n.id = (n.id == Spos.NULL) ? pos : n.id;
            totalSize += n.getByteSize();
            pos = RecoverableStream.getSpos(transStartPos, totalSize);
        }
        
        topAndKeySize = totalSize;
        
        // Loop valueNodes.
        for (int i = 0; i < transNodes.valueSize; i++) {
            final ValueNode n = transNodes.valueNodes[i];
            n.spos = pos;
            totalSize += n.getByteSize(transNodes.choices[i].size);
            pos = RecoverableStream.getSpos(transStartPos, totalSize);
        }
        
        totalSize += 4;
        totalSize += 4;
        
        for (int i = 0; i < trans.kvs.length; i++) {
            totalSize += 4 + Keys.getByteSize(trans.kvs[i].keySegments);
        }
        
        totalSize = totalSize + 1;
            // Adds room for RecoverableStream.LAST_BYTE.
       
        // For totalSize to be a multiple of TRANS_ALIGNMENT.
        extraZeros = NodeStream.TRANS_ALIGNMENT - totalSize % NodeStream.TRANS_ALIGNMENT;
        totalSize += extraZeros;
        assert totalSize % NodeStream.TRANS_ALIGNMENT == 0 : totalSize + ", " + extraZeros;
        
        // Sets fields of trans.
        
        trans.tpos = transStartPos;
        trans.lastSpos = RecoverableStream.getSpos(transStartPos, totalSize - 1);
        trans.nextSpos = RecoverableStream.getSpos(transStartPos, totalSize);
        
        // Determines whether metablock(s) will be written.
        // Assumes meta blocks are written eagerly.
        
        long tSize = trans.lastSpos - trans.tpos + 1;
        if (tSize > RecoverableStream.META_BLOCK_SIZE) {
            if (tSize >= RecoverableStream.META_BLOCK_DISTANCE) {
                writeMetaBlock = true;
            } else {
                long blockIndex1 = trans.tpos / RecoverableStream.META_BLOCK_DISTANCE;
                long blockIndex2 = trans.lastSpos / RecoverableStream.META_BLOCK_DISTANCE;                
                writeMetaBlock = (blockIndex1 != blockIndex2) || trans.tpos == 0;
            }
        }
    }
    

    public void serialize() {
        //
        // Code to serialize causes significant exe time (30-40%) for Set operations.
        // We could possibly return quickly and let another thread serialize nodes.
        // Possibly the thread that handles flushing the buffer could be used, or a separate one.
        // KeyNode.size and order of transactions would need to be stored.
        //
        
        resizeBuffersIfNeeded(appendNodesCounter);
        
        int offset = 0;
        int longOffset = 0;
        int prevPosIndex = 0;
        
        // 130502 Frans: Transaction header now 4+4+8 = 16 (size, free, transTime).
        
        longBuffer[longOffset] = totalSize;      // Note, 4 bytes available, int-to-long conversion.
        longOffset += 1;
        longBuffer[longOffset] = trans.transTime;
        longOffset += 1;
        
        for (int i = 0; i < transNodes.topSize; i++) {
            TopNode n1 = transNodes.topNodes[i];
            int longSize = n1.toLongs(longBuffer, longOffset);
            longOffset += longSize;
        }
        
        for (int i = 0; i < transNodes.keySize; i++) {
            KeyNode n1 = transNodes.keyNodes[i];
            int longSize = n1.toLongs(longBuffer, longOffset, prevPos[prevPosIndex++]);
            longOffset += longSize;
        }
        
        // TopNodes and KeyNodes have been serialized to longBuffer[]
        // Code here will set byteBuffer from longBuffer.
        
        for (int j = 0; j < longOffset; j++) {
            long value = longBuffer[j];
            byteBuffer[offset++] = (byte) value;
            byteBuffer[offset++] = (byte) (value >>>  8);
            byteBuffer[offset++] = (byte) (value >>> 16);
            byteBuffer[offset++] = (byte) (value >>> 24);
            byteBuffer[offset++] = (byte) (value >>> 32);
            byteBuffer[offset++] = (byte) (value >>> 40);
            byteBuffer[offset++] = (byte) (value >>> 48);
            byteBuffer[offset++] = (byte) (value >>> 56);
        }
        
        for (int i = 0; i < transNodes.valueSize; i++) {
            ValueNode n = transNodes.valueNodes[i];
            int byteSize = n.toBytes(transNodes.choices[i], byteBuffer, offset);
            offset += byteSize;
        }
        
        // Zero to indicate end of nodes.
        Bytes.intToBytesLE(0, byteBuffer, offset);
        offset += 4;
        
        final int kvCount = trans.kvs.length;
        Bytes.intToBytesLE(kvCount, byteBuffer, offset);
        offset += 4;
        
        // Adding the keys
        
        for (int i = 0; i < kvCount; i++) {
            // TODO C. Add method to Keys to serialize to existing byte array
            // to avoid memory allocation here.
            byte[] key = Keys.toBytes(trans.kvs[i].keySegments);
            Bytes.intToBytesLE(key.length, byteBuffer, offset);
            offset += 4;
            System.arraycopy(key, 0, byteBuffer, offset, key.length);
            offset += key.length;
        }
        
        System.arraycopy(NodeStream.ZEROS64, 0, byteBuffer, offset, extraZeros);
        offset += extraZeros;
        
        // End of buffer (LAST_BYTE indicates a valid transaction).
        
        byteBuffer[offset] = RecoverableStream.LAST_BYTE;
        offset += 1;
        
        assert offset == totalSize : "offset = " + offset + ", but totalSize = " + totalSize;
        assert totalSize % 8 == 0 : "totalSize = " + totalSize;
    }
    
    private void resizePrevPosIfNeeded() {
        // 10007 is a prime.
        
        if (appendNodesCounter % 10007 == 0) {    
            int newSize = Math.max(INIT_SIZE_OF_PREV_POS, transNodes.keySize);
            if (prevPos.length != newSize) {
                prevPos = new long[newSize];
            }
        }
        
        if (this.prevPos.length < transNodes.keySize) {
            this.prevPos = new long[(int) (transNodes.keySize * 1.20)];
        }
    }
    
    private void resizeBuffersIfNeeded(long addNodesCounter) {
        if (addNodesCounter % 10007 == 0) {
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
    
    /** Returns the transaction buffer that contains the serialized transaction. */
    public final byte[] getTransBuffer() {
        return this.byteBuffer;
    }
    
    /** Returns the byte size of the buffer returned by getTransBuffer(). */
    public final int getTransSize() {
        return this.totalSize;
    }
    
    public final boolean wroteMetaBlock() {
        return this.writeMetaBlock;
    }
}
