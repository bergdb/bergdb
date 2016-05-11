package bergdb.core;

import java.io.PrintStream;
import java.util.ArrayList;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.dag.Node;
import bergdb.dag.Spos;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;

/**
 * Db uses a NodeStream object as its interface to the database stream. Db appends nodes with
 * appendNodes() and reads nodes with readNode(). 
 * Concurrency assumption: one write thread holding writeLock and calling appendNodes(), 
 * getLength(), recover(), getPosOfLastCompletedTrans() and multiple concurrent 
 * threads calling readNode().
 * 
 * @author Frans Lundberg
 */
public class NodeStream implements bergdb.dag.Dag.NodeReader {
    /** Transaction start position is always divisable by TRANS_ALIGNMENT. */
    static final int TRANS_ALIGNMENT = 8;

    private final RecoverableStream rstream;
    private final Object writeLock;
        // For asserting that caller of some methods holds the required Db.writeLock.
    
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

    public final long getNextPos() {
        return rstream.getNextSpos();
    }

    /**
     * Appends a transaction to the node stream.
     */
    void appendNodes(TransNodes nodes, Trans trans, ArrayList<Node> gotDirtyNodes) {
        long pos = getNextPos();
        serializer.serialize(nodes, trans.tt, pos, trans.startupPos, gotDirtyNodes);
        
        trans.tpos = pos;
        trans.lastPos = serializer.getOutputLastSpos();
        trans.nextPos = serializer.getOutputNextSpos();

        byte[] buffer = serializer.getTransBuffer();
        int bufferSize = serializer.getOutputTransSize();

        rstream.append(buffer, 0, bufferSize, true, trans.tt);
        rstream.getMetaBlock().setLastTransSpos(pos);
    }
    
    @SuppressWarnings("unused")
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
        return "---- Trans@" + transPos + " ----\n" + "From transBytes:\n  " + s1 + "From streamBytes:\n  " + s2;
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
    
    public NodeHeader readNodeHeader(long spos) {
        // Assumes: node type at offset 4.
        // Assumes: id at offset 16 for TYPE_TOP_NODE.
        // Assumes: id at offset 24 for TYPE_KEY_NODE.
        // Assumes: length of key node >= 32.
        
        byte[] buffer = new byte[32];
        rstream.read(spos, buffer, 0, 8);
        
        byte type = buffer[4];   // assumed same for all node types
        long id;
        
        if (type == Node.TYPE_TOP_NODE || type == Node.TYPE_KEY_NODE) {
            rstream.read(spos + 8, buffer, 8, 32-8);
            
            if (type == Node.TYPE_TOP_NODE) {
                id = Bytes.bytesToLongLE(buffer, 16);
            } else {
                id = Bytes.bytesToLongLE(buffer, 24);
            }
        } else if (type == Node.TYPE_VALUE || type == Node.TYPE_DELETE) {
            id = spos;
        } else {
            throw new StreamFormatException("unknown node type, " + ((int) type) 
                    + ", spos: " + spos + ", node header bytes: " + Util.toHex(buffer, 0, 8));
        }
        
        return new NodeHeader(type, id);
    }

    /**
     * Reads a node from the stream given its spos.
     * 
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    public Node readNode(long spos) {
        assert spos >= RecoverableStream.META_BLOCK_SIZE : "bad spos, " + spos;

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
        Node node = bytesToNode(spos, buffer, 0, size).getNode();
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
        //
        // * Assumption: node type byte always stored at same location 
        //   (for all versions, all node types)
        // * Assumption: Checksums always computed the same way for all node types
        //   and version.
        //
        
        assert buffer.length > offset + 5 : "offset=" + offset + ", buffer.length=" + buffer.length;
        byte nodeType = buffer[offset + 4];
        
        checkChecksum(spos, buffer, offset, size, nodeType);
        
        StoredNode stored;

        switch (nodeType) {
        case Node.TYPE_KEY_NODE:
            stored = StoredKeyNode.parse(buffer, offset, spos);
            break;
        case Node.TYPE_TOP_NODE:
            stored = StoredTopNode.parse(buffer, offset, spos);
            break;
        case Node.TYPE_VALUE:
        case Node.TYPE_DELETE:
            stored = StoredValueNode.parse(buffer, offset, spos);
            break;
        default:
            throw new StreamFormatException("Bad node type in stream, " + ((int) nodeType)
                    + ", for stream item at spos = " + spos + ". " 
                    + ", buffer.length=" + buffer.length + ".");
        }

        return stored;
    }

    private static void checkChecksum(long spos, byte[] buffer, int offset, int size, byte nodeType) {
        int computedSum = NodeChecksum.sumWithZeroReplace(buffer, offset, size, offset + 6);
        int storedSum = Bytes.bytesToUShortLE(buffer, offset + 6);
        
        if (computedSum != storedSum) {
            throw new StreamChecksumException("spos: " + spos + ", storedSum: "
                    + storedSum + ", computedSum: " + computedSum + ", nodeType: " + nodeType);
        }
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
                Node node = s.getNode();
                out.println("-- " + node.getClass().getSimpleName() + " prev:"
                        + s.getPrevPos() + " --");
                out.print(node.print());
            }
        }
    }
    
    public void printGotDirtyLine(PrintStream out, StoredTrans storedTrans) {
        if (storedTrans.gotDirtyIdsAndSpos.length > 0) {
            out.print("got dirty: ");
            long[] d = storedTrans.gotDirtyIdsAndSpos;
            for (int i = 0; i < d.length; i++) {
                out.print(d[i] + " ");
            }
            out.println();
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
         * Advances iterator to next transaction. Returns true if there was a transaction, false if not.
         * 
         * Caller must hold Db.writeLock.
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
