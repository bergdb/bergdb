package bergdb.core;

import java.io.PrintStream;

import bergdb.common.Bytes;
import bergdb.common.Pair;
import bergdb.graph.INode;
import bergdb.graph.KeyNode;
import bergdb.graph.Spos;
import bergdb.graph.StreamChecksumException;
import bergdb.graph.TopNode;
import bergdb.graph.TransactionNodes;
import bergdb.graph.ValueNode;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;

/**
 * NodeStream is the input/output for DB. DB appends nodes with addNodes() and reads nodes
 * with readNode().
 * Concurrency. This class is not thread safe; synchronize externally. 
 * One writer (calling addNodes() and multiple readers (calling readNode()) is assumed.
 * 
 * @author Frans Lundberg
 */
public class NodeStream implements bergdb.graph.Graph.NodeReader {
    private static final int initSizeOfByteBuffer = 100*1000;
    private static final int initSizeOfLongBuffer = 10*1000;
    
    /** Transaction start position is always divisable by TRANS_ALIGNMENT. */
    private static final int TRANS_ALIGNMENT = 8;
    
    private final RecoverableStream rstream;
    private final MetaBlock metaBlock;
            // Shortcut reference.
    private final boolean writeEnabled;
            // Set to false to test performance without serialization of nodes and without writing
            // anything to the DB stream.
    private final Object writeLock;
            // For asserting that caller of some methods holds the required DB.writeLock.
    
    /** Buffer with serialized nodes for the current transaction. */
    private byte[] byteBuffer;
    
    /** Buffer with serialized top and key nodes for current transaction. */
    private long[] longBuffer;
    
    private int addNodesCounter;
    
    /** Byte array with zero bytes, useful for zero-fill of transaction buffer. */
    private static final byte[] zeros64 = new byte[64];
    
    /**
     * Creates a new NodeStream given a RecoverableStream.
     * 
     * @param rstream  The underlying stream.
     * @param writeEnabled  True for normal usage, false for performance testing
     * (will disable writes to the underlying stream and INode serialization).
     */
    public NodeStream(RecoverableStream rstream, boolean writeEnabled, Object writeLock) {
        if (rstream == null) {
            throw new IllegalArgumentException("rstream == null not allowed.");
        }
        
        if (writeLock == null) {
            throw new IllegalArgumentException("writeLock == null not allowed");
        }
        
        this.rstream = rstream;
        this.metaBlock = rstream.getMetaBlock();
        this.writeEnabled = writeEnabled;
        this.byteBuffer = new byte[initSizeOfByteBuffer];
        this.longBuffer = new long[initSizeOfLongBuffer];
        this.addNodesCounter = 0;
        this.writeLock = writeLock;
    }
    
    /**
     * Calls method with same name in RecoverableStream. Same exceptions.
     * 
     * @see RecoverableStream#recover()
     * @throws StreamIoException
     * @throws StreamFormatException
     */
    public void recover() {
        assert Thread.holdsLock(writeLock);
        this.rstream.recover();
    }

    /**
     * Returns the length of the underlying stream.
     * The caller must hold DB.writeLock.
     */
    final long getLength() {
        assert Thread.holdsLock(writeLock);
        return rstream.getLength();
    }
    
    /**
     * Returns the MetaBlock of the underlying RecoverableStream.
     */
    public MetaBlock getMetaBlock() {
        // Note, we could add a short-cut reference to MetaBlock in this class to improve
        // performance since it is a final field in rstream. But probably no measurable 
        // performance improvement.
        return rstream.getMetaBlock();
    }
    
    public final long getPosOfLastValidMetaBlock() {
        return rstream.getPosOfLastValidMetaBlock();
    }
    
    /**
     * Adds nodes to the stream as one single transaction.
     * Caller must hold Db.writeLock.
     * 
     * @param trans Optional parameter for output. If non-null, this method sets trans.spos, 
     *              trans.byteSize.
     * @throws StreamIoException
     */
    public boolean appendNodes(long transactionTime, TransactionNodes nodes, Trans trans) {
        //
        // 130430: Changed to use new version of TransactionNodes (separates node types).
        // 130409: boolean return instead of void.
        // 121009: We now allow noop operation, that is, nodesToAdd.size() == 0.
        // 
        
        assert nodes.assertNoDuplicates();
        
        int totalSize = 0;
        int topAndKeySize = 0;     // Bytesize of TopNode + KeyNodes for transaction.
        int prevPosIndex = 0;
        boolean wroteMetaBlock = false;     // the result
        final long[] prevPos = new long[nodes.keySize];    
            // 1305 Frans: Note, this allocation seems to be done on the stack.
            // On my computer, it is faster than a member field that is reused.
        
        addNodesCounter++;
        metaBlock.setTime(transactionTime);
        totalSize = 16;        // Header size, trans size, 4 empty, trans time
        final long transStartPos = rstream.getNextSpos();
        long pos = rstream.getSpos(transStartPos, totalSize);
        
        // Below three loops sets new stream pos of nodes, sets ID if needed, and sets isDirty = false.
        // Also computes totalSize and sets prevPos array for KeyNodes.
        
        // Loop topNodes.
        for (int i = 0; i < nodes.topSize; i++) {
            final TopNode n1 = nodes.topNodes[i];
            n1.spos = pos;
            n1.id = (n1.id == Spos.NULL) ? pos : n1.id;
            totalSize += n1.getByteSize();
            pos = rstream.getSpos(transStartPos, totalSize);
        }
        
        // Loop keyNodes.
        for (int i = 0; i < nodes.keySize; i++) {
            final KeyNode n = nodes.keyNodes[i];
            prevPos[prevPosIndex++] = n.spos;
            n.spos = pos;
            n.id = (n.id == Spos.NULL) ? pos : n.id;
            totalSize += n.getByteSize();
            pos = rstream.getSpos(transStartPos, totalSize);
        }
        
        topAndKeySize = totalSize;
        
        // Loop valueNodes.
        for (int i = 0; i < nodes.valueSize; i++) {
            final ValueNode n = nodes.valueNodes[i];
            n.spos = pos;
            totalSize += n.getByteSize(nodes.choices[i].size);
            pos = rstream.getSpos(transStartPos, totalSize);
        }
        
        // Below code creates a transaction byte buffer to be written to database stream.
        
        totalSize = totalSize + 1;
                // Adds room for RecoverableStream.LAST_BYTE.
        
        // For totalSize to be a multiple of TRANS_ALIGNMENT.
        int extraZeros = TRANS_ALIGNMENT - totalSize % TRANS_ALIGNMENT;
        totalSize += extraZeros;
        assert totalSize % TRANS_ALIGNMENT == 0 : totalSize + ", " + extraZeros;
        
        trans.spos = transStartPos;
        trans.lastSpos = rstream.getSpos(transStartPos, totalSize - 1);
        trans.nextSpos = rstream.getSpos(transStartPos, totalSize);
        
        // Determines whether a metablock was written.
        // Assumes meta blocks are written eagerly.
        
        long tSize = trans.lastSpos - trans.spos + 1;
        if (tSize > RecoverableStream.META_BLOCK_SIZE) {
            if (tSize >= RecoverableStream.META_BLOCK_DISTANCE) {
                wroteMetaBlock = true;
            } else {
                long blockIndex1 = trans.spos / RecoverableStream.META_BLOCK_DISTANCE;
                long blockIndex2 = trans.lastSpos / RecoverableStream.META_BLOCK_DISTANCE;                
                wroteMetaBlock = (blockIndex1 != blockIndex2) || trans.spos == 0;
            }
        }
        
        if (!this.writeEnabled && addNodesCounter > 2) {
            // Special DEV if-clause. Useful for performance testing.
            // With/without stream + serialization of nodes.
            // The condition with addNodesCount is required when 
            // the stream is empty and initialized with internal transaction.
            // This is an ugly hack and only used for performance testing.
            return wroteMetaBlock;
        }
        
        // ----
        // Code for rest of method causes significant exe time (30-40%) for Set operations.
        // We could possibly return quickly and let other thread serialize nodes. 
        // KeyNode.size would need to be stored.
        // ----
        
        resizeBuffersIfNeeded(totalSize, topAndKeySize);
        
        int offset = 0;
        int longOffset = 0;
        prevPosIndex = 0;
        
        // 130502 Frans: Transaction header now 4+4+8 = 16 (size, free, transTime).
        
        longBuffer[longOffset++] = totalSize;      // Note, 4 bytes available.
        longBuffer[longOffset++] = transactionTime;
        
        for (int i = 0; i < nodes.topSize; i++) {
            TopNode n1 = nodes.topNodes[i];
            int longSize = n1.toLongs(longBuffer, longOffset);
            longOffset += longSize;
        }
        
        for (int i = 0; i < nodes.keySize; i++) {
            KeyNode n1 = nodes.keyNodes[i];
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
        
        for (int i = 0; i < nodes.valueSize; i++) {
            ValueNode n = nodes.valueNodes[i];
            int byteSize = n.toBytes(nodes.choices[i], byteBuffer, offset);
            offset += byteSize;
        }
        
        System.arraycopy(zeros64, 0, byteBuffer, offset, extraZeros);
        offset += extraZeros;
        
        // End of buffer (LAST_BYTE indicates a valid transaction).
        
        byteBuffer[offset] = RecoverableStream.LAST_BYTE;
        offset += 1;
        
        assert offset == totalSize : "offset = " + offset + ", but totalSize = " + totalSize;
        assert totalSize % 8 == 0 : "totalSize = " + totalSize;

        //System.out.println("==== NodeStream.addNodes ====\n" + nodes.print());
        
        // Stores buffer to stream.
        rstream.append(byteBuffer, 0, totalSize, true, transactionTime);
        
        // Sets the start pos to the meta block.
        rstream.getMetaBlock().setLastTransSpos(transStartPos);
        return wroteMetaBlock;
    }
    
    public long getLastTransSpos() {
        return rstream.getMetaBlock().getLastTransSpos();
    }

    private void resizeBuffersIfNeeded(int totalSize, int topAndKeySize) {
        if (addNodesCounter % 5013 == 0) {
            int newSize = Math.max(initSizeOfByteBuffer, totalSize);
            if (byteBuffer.length != newSize) {
                byteBuffer = new byte[newSize];
            }
            
            newSize = Math.max(initSizeOfLongBuffer, topAndKeySize / 8);
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
    
    /**
     * Gets a stream item. Assumes the item exists at the location and that it 
     * is valid.
     * 
     * @param tempBuffer A buffer to read to. Avoids some mem alloc. If non-null it must be at
     * least 4 bytes long. If long enough to read the node into it, it will save some 
     * memory allocation.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    public final INode readNode(long spos, byte[] tempBuffer) {
        if (tempBuffer == null || tempBuffer.length < 4) {
            tempBuffer = new byte[1024];
        }
        return readNode(rstream, spos, tempBuffer);
    }
    
    /**
     * Reads a StoredNode (stream item) from the stream.
     * 
     * @param stream
     * @param spos
     * @param buffer Buffer for temporary storage only, will be modified. Can be anything at input.
     * Should be larger than most stream items and must be at least 4 bytes long.
     * @return The INode that was read.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    private static INode readNode(RecoverableStream stream, long spos, byte[] buffer) {
        assert buffer != null;
        assert buffer.length >= 4 : "Bad buffer.length, " + buffer.length + ".";
        
        stream.read(spos, buffer, 0, 4);
        
        int size = Bytes.bytesToIntLE(buffer, 0);
        if (size <= 6) {
            throw new StreamFormatException("Bad node byte size, " + size 
                    + ". At spos " + spos + ".");
        }
        if (buffer.length < size) {
            buffer = new byte[size];
        }
        
        stream.read(spos, buffer, 0, size);
        
        INode node = bytesToNode(spos, buffer, 0, size, null);
        return node;
    }

    /**
     * Reads a stream item (StoredNode) from the bytes in 'buffer'.
     * 
     * @param spos  The spos of the stream item.
     * @param offset  The stream item should be read starting at this offset
     *   in 'buffer'. Position should be given so it includes item size field and
     *   previous spos and other headers.
     * @param size  Byte size of the serialized node.
     * @param stored  If this parameter is non-null, the node and addition data from the stream
     * (previous spos) is set to it. If only the INode is wanted, this parameter should be 'null'.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    private static INode bytesToNode(long spos, byte[] buffer, int offset, int size, StoredNode stored) {
        assert buffer.length > offset + 5 : "offset=" + offset + ", buffer.length=" + buffer.length;        
        byte nodeType = buffer[offset + 4];      
            // Node type byte always has this location for all node types.
        
        {
            // Checksum computation. Same for all node types.
            
            if (buffer[offset + 7] != 0) {
                throw new StreamChecksumException("spos: " + spos + ", buffer[7]: " 
                        + ((int)buffer[7]) + ", nodeType: " + nodeType);
            }
            int sumInData = (buffer[offset + 6]) & 0x000000ff;
            
            if (sumInData != 0) {
                buffer[offset + 6] = 0;
                int computedSum = 0;
                for (int i = 0; i < size; i++) {
                    computedSum ^= buffer[offset + i];
                    // This works, lowest 8 bits do not change for byte-to-int conversion.
                }
                computedSum = computedSum & 0x000000ff;
                computedSum = computedSum == 0 ? 1 : computedSum;
                
                if (computedSum != sumInData) {
                    throw new StreamChecksumException("spos: " + spos 
                            + ", sumInData: " + ((int)sumInData) 
                            + ", computedSum: " + ((int) computedSum) + ", nodeType: " + nodeType);
                }
            }
        }
        
        long sposPrevious = Spos.NULL;
        
        if (nodeType == INode.TYPE_KEY_NODE) {
            sposPrevious = KeyNode.prevPosFromBytes(buffer, offset);
        }
        
        INode node = null;
        byte[] choices = null;
        
        switch (nodeType) {
        case INode.TYPE_KEY_NODE:
            node = KeyNode.fromBytes(buffer, offset, spos);
            break;
        case INode.TYPE_TOP_NODE:
            node = TopNode.fromBytes(buffer, offset, spos);
            break;
        case INode.TYPE_VALUE:
        case INode.TYPE_DELETE:
            if (stored == null) {
                node = ValueNode.fromBytes(buffer, offset, spos);
            } else {
                Pair<ValueNode, byte[]> pair = ValueNode.fromBytesIncludingChoices(buffer, offset, spos);
                node = pair.getValue0();
                choices = pair.getValue1();
            }
            break;
        default:
            throw new StreamFormatException("Bad node type in stream, " 
                    + ((int)nodeType) + ", for stream item at spos = " + spos + ". "
                    + "sposPrevious=" + sposPrevious
                    + ", buffer.length=" + buffer.length + ".");
        }
        
        //assert node.isDirty() == false;
        assert node.getSpos() == spos;
        
        if (stored != null) {
            stored.node = node;
            stored.sposPrevious = sposPrevious;
            stored.choices = choices;
        }
        
        return node;
    }
    
    public void printStream(PrintStream out) {
        printStream(out, 0);
    }
    
    public void printStream(PrintStream out, long startSSPos) {
        TransIterator titer = new TransIterator(startSSPos);
        
        while (titer.next()) {
            out.println("==== Trans at " + titer.transPos + " ====");
            NodeIterator niter = titer.getNodeIterator();
            while (niter.next()) {
                INode inode = niter.node;
                out.println("-- " + inode.getClass().getSimpleName() 
                        + " prev:" + niter.sposPrevious + " --");
                out.println(inode.toString());
            }
        }
    }
    
    /**
     * Returns the spos of the last valid transaction that was completely 
     * written before stream position 'spos'.
     * If there is no such transaction, the spos of the very first valid 
     * transaction is returned instead. If there is no valid transaction at all in 
     * the stream, Spos.NULL is returned. Caller must hold DB.writeLock.
     */
    public long getPosOfLastCompletedTrans() {
        assert Thread.holdsLock(writeLock);
        return rstream.getPosOfTransCompletedBefore(rstream.getNextSpos());
    }
    
    /**
     * Iterator that iterates through the successful transactions in the stream from a given 
     * start pos.
     */
    public class TransIterator {
        long startPos;
        long transPos;
        long nextTransPos;
        long transCount;
        boolean transOk;
        byte[] transBuffer;
        long transactionTime;
        
        public TransIterator() {
            this(0);
        }
        
        public TransIterator(long startPos) {
            this.startPos = startPos;
        }
        
        /**
         * Advances iterator to next transaction.
         * Returns true if there was an item, false if not.
         * 
         * Caller must hold DB.writeLock.
         */
        public boolean next() {
            
            start: while (true) {    // Dummy while-loop just to be able to do "continue start;".
                if (transCount == 0) {
                    long p = rstream.getPosOfTransCompletedBefore(startPos);
                    if (p == Spos.NULL) {
                        // No valid transactions in stream.
                        return false;
                    }
                    transPos = p;
                } else {
                    transPos = nextTransPos;
                }
                
                if (transPos >= rstream.getLength()) {
                    return false;
                }
                
                byte[] buffer = new byte[4];
                rstream.read(transPos, buffer, 0, 4);
                int size = Bytes.bytesToIntLE(buffer, 0);
                if (size < 16 + 0 + 1) {
                    String message = "Bad transaction size, " + size 
                            + ", transPos=" + transPos + ", stream size: " + rstream.getLength()
                            + ", transCount=" + transCount;
                    throw new StreamFormatException(message);
                }
                
                buffer = new byte[size];
                rstream.read(transPos, buffer, 0, size);
                byte lastByte = buffer[buffer.length - 1];
                if (lastByte != 0 && lastByte != RecoverableStream.LAST_BYTE) {
                    throw new StreamFormatException("Bad lastByte: " + ((int) lastByte));
                }
                transOk = lastByte == 0 ? false : true;
                transBuffer = buffer;
                nextTransPos = rstream.getSpos(transPos, size);
                
                if (!transOk) {
                    continue start;
                }
                
                transCount++;    // We do not include non-committed transactions in count.
                transactionTime = Bytes.bytesToLongLE(transBuffer, 8);
                
                break;    // always break at end of while loop
            }
            return true;
        }
        
        public final long getTransactionTime() {
            return transactionTime;
        }
        
        public final long getTransPos() {
            return transPos;
        }
        
        public NodeIterator getNodeIterator() {
            return new NodeIterator(transPos, transBuffer);
        }
    }
    
    /**
     * Class that can iterate through the nodes (stream items) of a transaction given the 
     * transaction bytes.
     */
    public class NodeIterator {
        byte[] buffer;
        int count = 0;
        int offset = 0;
        long transPos;
        long sposPrevious;
        byte[] choices;       // non-null for value nodes (including deletes)
        INode node;
        private StoredNode storedNode;
        private long transactionTime;
        
        public NodeIterator(long transPos, byte[] buffer) throws StreamFormatException {
            if (buffer == null) {
                throw new IllegalArgumentException("buffer == null not allowed");
            }
            if (buffer.length < 16 + 0 + 1) {
                throw new IllegalArgumentException("buffer too small, " + buffer.length);
            }
            this.buffer = buffer;
            this.transPos = transPos;
            this.storedNode = new StoredNode();
            int size = Bytes.bytesToIntLE(buffer, offset);
            if (size != buffer.length) {
                throw new StreamFormatException("Bad size, " + size + ", " + buffer.length);
            }
            offset += 8;
            transactionTime = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
        }
        
        public long getTransactionTime() {
            return transactionTime;
        }
        
        /**
         * Advances iterator to next stream item.
         * Sets fields: node, sposPrevious, count, offset.
         */
        public boolean next() {
            // 130424 Frans: modified to handle zero-fill.
            
            if (offset + 4 >= buffer.length) {
                return false;
            }
            
            int nodeSize = Bytes.bytesToIntLE(buffer, offset);
            if (nodeSize == 0) {
                return false;
            }
            
            long spos = rstream.getSpos(transPos, offset);
            NodeStream.bytesToNode(spos, buffer, offset, nodeSize, storedNode);
            
            this.node = storedNode.node;
            this.sposPrevious = storedNode.sposPrevious;
            this.choices = storedNode.choices;
            
            offset += nodeSize;
            count++;
            return true;
        }
    }
}
