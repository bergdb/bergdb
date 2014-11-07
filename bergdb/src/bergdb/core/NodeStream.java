package bergdb.core;

import java.io.PrintStream;

import bergdb.common.Bug;
import bergdb.common.Bytes;
import bergdb.dag.INode;
import bergdb.dag.Spos;
import bergdb.dag.StreamChecksumException;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;

/**
 * Db uses a NodeStream object as its interface to the database stream. Db appends nodes with
 * appendNodes() and reads nodes with readNode(). 
 * Concurrency: One write thread (holding writeLock) calling appendNodes(), getLength(), recover(), 
 * getPosOfLastCompletedTrans() and multiple concurrent reader threads calling
 * readNode() is the assumption.
 * 
 * @author Frans Lundberg
 */
public class NodeStream implements bergdb.dag.Dag.NodeReader {
    /** Transaction start position is always divisable by TRANS_ALIGNMENT. */
    static final int TRANS_ALIGNMENT = 8;

    private final RecoverableStream rstream;
    private final Object writeLock;
        // For asserting that caller of some methods holds the required DB.writeLock.
    
    private final StoredTrans.Serializer serializer;

    /** Byte array with 64 zero bytes, useful for zero-fill of transaction buffer. */
    public static final byte[] ZEROS64 = new byte[64];

    /**
     * Creates a new NodeStream given a RecoverableStream.
     * 
     * @param rstream
     *            The underlying stream.
     */
    public NodeStream(RecoverableStream rstream, Object writeLock) {
        if (rstream == null) {
            throw new IllegalArgumentException("rstream == null not allowed.");
        }

        if (writeLock == null) {
            throw new IllegalArgumentException("writeLock == null not allowed");
        }

        this.serializer = new StoredTrans.Serializer();
        this.rstream = rstream;
        this.writeLock = writeLock;
    }

    /**
     * Recovers the stream by adding zero bytes at end if needed
     * and reads the last valid meta block.
     * 
     * @see RecoverableStream#recover()
     * @throws StreamIoException
     * @throws StreamFormatException
     */
    public void recover() {
        assert Thread.holdsLock(writeLock);
        
        long length = rstream.getLength();
        if (length < RecoverableStream.META_BLOCK_SIZE) {
            throw new StreamFormatException("Cannot recover stream without complete first "
                    + "meta block, length: " + length);
        }
        
        rstream.recover();
    }

    /**
     * Returns the length of the underlying stream. The caller must hold DB.writeLock.
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

    void appendNodes(TransNodes nodes, Trans trans) {                
        long pos = rstream.getNextSpos();
        serializer.serialize(nodes, trans.time, pos, trans.startupPos);

        trans.pos = pos;
        trans.lastPos = serializer.getOutputLastSpos();
        trans.nextPos = serializer.getOutputNextSpos();

        byte[] buffer = serializer.getTransBuffer();
        int bufferSize = serializer.getOutputTransSize();

        rstream.append(buffer, 0, bufferSize, true, trans.time);
        rstream.getMetaBlock().setLastTransSpos(pos);
    }
    
    /**
     * Similar to appendNodes(), but does not actually write to 
     * db stream, instead it serializes and checks that the serialized transaction bytes
     * matches what is in the stream already. Used when re-running transactions.
     * trans.pos/lastPos/nextPos should be set correctly already.
     */
    void doDummyAppend(TransNodes nodes, Trans trans) {        
        assert nodes.assertNoDuplicates();
        
        if (trans.pos < 1) {
            throw new Bug("trans.pos not set, was " + trans.pos + ", trans: " + trans);
        }
        
        serializer.serialize(nodes, trans.time, trans.pos, trans.startupPos);

        long lastPos = serializer.getOutputLastSpos();
        long nextPos = serializer.getOutputNextSpos();
        
        trans.lastPos = lastPos;
        trans.nextPos = nextPos;
        
        byte[] buffer = serializer.getTransBuffer();
        int bufferSize = serializer.getOutputTransSize();
        
        //checkEqualBytes(trans.pos, buffer, bufferSize);
        
        rstream.getMetaBlock().setLastTransSpos(trans.pos);
    }

    private void checkEqualBytes(long transPos, byte[] transBytes, int transBytesSize) {
        boolean equal = true;
        int diffIndex = -1;
        
        byte[] streamBytes = readTransBytes(transPos);
        
        if (transBytesSize != streamBytes.length) {
            equal = false;
        } else {
            for (int i = 0; i < transBytesSize; i++) {
                if (transBytes[i] != streamBytes[i]) {
                    equal = false;
                    diffIndex = i;
                    break;
                }
            }
        }
        
        if (!equal) {
            String diff = printDiff(transPos, transBytes, streamBytes);
            throw new IllegalStateException(
                    "transBytes and streamBytes are not equal. " + diffIndex + ", diff:\n" + diff);
        }
    }

    private String printDiff(long transPos, byte[] transBytes, byte[] streamBytes) {
        String s1 = printTransGivenBuffer(transPos, transBytes);
        String s2 = printTransGivenBuffer(transPos, streamBytes);
        return "From transBytes:\n  " + s1 + "\nFrom streamBytes:\n  " + s2;
    }
    
    private String printTransGivenBuffer(long tpos, byte[] buffer) {
        String s;
        try {
            StoredTrans t = StoredTrans.parse(tpos, buffer);
            s = t.print();
        } catch (StreamFormatException e) {
            s = "format exception: " + e.getMessage();
        }
        return s;
    }

    public long getLastTransSpos() {
        return rstream.getMetaBlock().getLastTransSpos();
    }

    /**
     * Reads a node from the stream given is spos.
     * 
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    public INode readNode(long spos) {
        byte[] buffer = new byte[1024];        
        rstream.read(spos, buffer, 0, 4);
        
        int size = Bytes.bytesToIntLE(buffer, 0);
        if (size <= 6) {
            throw new StreamFormatException("Bad node byte size, " + size + ". At spos " + spos
                    + ".");
        }
        
        if (buffer.length < size) {
            buffer = new byte[size];
        }
        
        rstream.read(spos, buffer, 0, size);
        
        INode node = bytesToNode(spos, buffer, 0, size).getNode();
        return node;
    }
    
    public byte[] readTransBytes(long tpos) {
        byte[] buffer = new byte[4];
        rstream.read(tpos, buffer, 0, 4);
        
        int size = Bytes.bytesToIntLE(buffer, 0);
        if (size <= 6) {
            throw new StreamFormatException("Bad transaction byte size, " + size + ". At spos " + tpos
                    + ".");
        }
        
        buffer = new byte[size];
        rstream.read(tpos, buffer, 0, size);
        return buffer;
    }

    /**
     * Reads a stream item (StoredNode) from the bytes in 'buffer'.
     * 
     * @param spos
     *            The spos of the stream item.
     * @param offset
     *            The stream item should be read starting at this offset in 'buffer'. Position
     *            should be given so it includes item size field and previous spos and other
     *            headers.
     * @param size
     *            Byte size of the serialized node.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    static StoredNode bytesToNode(long spos, byte[] buffer, int offset, int size) {
        assert buffer.length > offset + 5 : "offset=" + offset + ", buffer.length=" + buffer.length;
        byte nodeType = buffer[offset + 4];
        // Node type byte always has this location for all node types.

        {
            // Checksum computation. Same for all node types.

            if (buffer[offset + 7] != 0) {
                throw new StreamChecksumException("spos: " + spos + ", buffer[7]: "
                        + ((int) buffer[7]) + ", nodeType: " + nodeType);
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
                    throw new StreamChecksumException("spos: " + spos + ", sumInData: "
                            + ((int) sumInData) + ", computedSum: " + ((int) computedSum)
                            + ", nodeType: " + nodeType);
                }
            }
        }
        
        StoredNode stored;

        switch (nodeType) {
        case INode.TYPE_KEY_NODE:
            stored = StoredKeyNode.parse(buffer, offset, spos);
            break;
        case INode.TYPE_TOP_NODE:
            stored = StoredTopNode.parse(buffer, offset, spos);
            break;
        case INode.TYPE_VALUE:
        case INode.TYPE_DELETE:
            stored = StoredValueNode.parse(buffer, offset, spos, true);
            // NOTE Key always read currently. Not always needed. Check if we can increase performance.
            break;
        default:
            throw new StreamFormatException("Bad node type in stream, " + ((int) nodeType)
                    + ", for stream item at spos = " + spos + ". " 
                    + ", buffer.length=" + buffer.length + ".");
        }

        return stored;
    }
    

    public void print(PrintStream out) {
        print(out, 0);
    }

    public void print(PrintStream out, long startPos) {
        TransIterator titer = createTransIterator(startPos);

        while (titer.next()) {
            out.println("==== Trans @" + titer.tpos + " ====");
            
            StoredTrans storedTrans = titer.getStoredTrans();
            out.println(storedTrans.toString());
            
            for (StoredNode s : storedTrans.nodes) {
                out.println("* p:" + s.getPrevPos());
                out.println(s.getNode().print().replace("\n", "\n  "));
                /*
                INode node = s.getNode();
                out.println("-- " + node.getClass().getSimpleName() + " prev:"
                        + s.getPrevPos() + " --");
                out.println(node.toString());*/
            }
        }
    }

    /**
     * Returns the spos of the last valid transaction that was completely written before stream
     * position 'spos'. If there is no such transaction, the spos of the very first valid
     * transaction is returned instead. If there is no valid transaction at all in the stream,
     * Spos.NULL is returned. Caller must hold DB.writeLock.
     */
    public long getPosOfLastCompletedTrans() {
        assert Thread.holdsLock(writeLock);
        return rstream.getPosOfTransCompletedBefore(rstream.getNextSpos());
    }
    
    public TransIterator createTransIterator(long startPos) {
        return new TransIterator(startPos, false);
    }
    
    public TransIterator createTransIteratorFromExactStartupPos(long startPos) {
        return new TransIterator(startPos, true);
    }

    /**
     * Iterator that iterates through the successful transactions in the stream 
     * from a given start pos.
     */
    public class TransIterator {
        long startPos;
        long tpos; // stream pos of first byte of current transaction
        long lastPos; // stream pos of last byte of current transaction
        long nextTransPos;
        long transCount;
        boolean transOk;
        byte[] transBuffer;
        long transTime;
        boolean exactStartPos;

        private TransIterator(long startPos, boolean exactStartPos) {
            this.startPos = startPos;
            this.exactStartPos = exactStartPos;
        }

        /**
         * Advances iterator to next transaction. Returns true if there was an item, false if not.
         * 
         * Caller must hold DB.writeLock.
         */
        public boolean next() {

            start: while (true) { // Dummy while-loop just to be able to do "continue start;".
                if (transCount == 0) {
                    if (exactStartPos) {
                        tpos = startPos;
                    } else {
                        long p = rstream.getPosOfTransCompletedBefore(startPos);
                        if (p == Spos.NULL) {
                            // No valid transactions in stream.
                            return false;
                        }
                        tpos = p;
                    }
                } else {
                    tpos = nextTransPos;
                }

                if (tpos >= rstream.getLength()) {
                    return false;
                }

                byte[] buffer = new byte[4];
                rstream.read(tpos, buffer, 0, 4);
                int size = Bytes.bytesToIntLE(buffer, 0);
                if (size < 16 + 0 + 1) {
                    String message = "Bad transaction size, " + size + ", transPos=" + tpos
                            + ", stream size: " + rstream.getLength() + ", transCount="
                            + transCount;
                    throw new StreamFormatException(message);
                }

                buffer = new byte[size];
                rstream.read(tpos, buffer, 0, size);
                byte lastByte = buffer[buffer.length - 1];
                if (lastByte != 0 && lastByte != RecoverableStream.LAST_BYTE) {
                    throw new StreamFormatException("Bad lastByte: " + ((int) lastByte));
                }
                transOk = lastByte == 0 ? false : true;
                transBuffer = buffer;

                lastPos = RecoverableStream.getSpos(tpos, size - 1);
                nextTransPos = RecoverableStream.getSpos(tpos, size);

                if (!transOk) {
                    continue start;
                }

                transCount++; // We do not include non-committed transactions in count.
                transTime = Bytes.bytesToLongLE(transBuffer, 8);

                break; // always break at end of while loop
            }
            return true;
        }

        public final long getTransTime() {
            return transTime;
        }

        /** Returns the stream pos of the first byte of the transaction. */
        public final long getTpos() {
            return tpos;
        }

        /** Returns the stream pos of the last byte of the transaction. */
        public final long getLastPos() {
            return lastPos;
        }
        
        public StoredTrans getStoredTrans() {
            return StoredTrans.parse(tpos, transBuffer);
        }
    }
}
