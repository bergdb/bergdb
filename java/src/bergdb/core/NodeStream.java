package bergdb.core;

import java.io.PrintStream;
import java.util.ArrayList;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.dag.Spos;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;
import bergdb.storage.VersioningStreamException;

/**
 * Db uses a NodeStream object as its interface to the database stream. Db appends nodes with
 * appendNodes() and reads nodes with readNode(). 
 * Concurrency assumption: one write thread holding writeLock and calling appendNodes(), 
 * getLength(), recover(), getPosOfLastCompletedTrans() and multiple concurrent 
 * threads calling readNode() and getAppendedEnd().
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

    private volatile long appendedEnd;
        // The end of the records appended in whole (bergdb 021-13): see getAppendedEnd().
        // Written by the writer, after the append; read by any thread.

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
        
        rstream.recover();
        appendedEnd = rstream.getLength();      // Whole records only, after the recovery.
    }
    
    /**
     * The end of the records appended in whole (bergdb 021-13): the position after the last
     * record that appendNodes() has appended, or, after recover(), the stream's length; 0
     * before either. A record that starts before it is in the stream in whole. One at or
     * after it may be in part, or not at all, while its nodes' positions are set already:
     * appendNodes() sets them before it appends the record (StoredTrans.Serializer), and
     * a reader can see them (ValueNode.getTpos(), a get's tpos). Any thread may call it.
     */
    public long getAppendedEnd() {
        return appendedEnd;
    }

    /**
     * Whether the stream holds a creation that did not complete, and no committed transaction
     * (bergdb 005-33); see RecoverableStream.isIncompleteCreation(). The caller must hold
     * DB.writeLock.
     */
    boolean isIncompleteCreation(long creationLength) {
        assert Thread.holdsLock(writeLock);
        return rstream.isIncompleteCreation(creationLength);
    }

    /**
     * Returns the length of the underlying stream. The caller must hold DB.writeLock.
     */
    final long getLength() {
        assert Thread.holdsLock(writeLock);
        return rstream.getLength();
    }
    
    /** The first position that can be read; larger than 0 after reclaim cut the stream. */
    public long getFirstPos() {
        return rstream.getFirstPos();
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

    public final long getLastTransPosOfLastValidMetaBlock() {
        return rstream.getLastTransSposOfLastValidMetaBlock();
    }
    
    /**
     * The stream's last valid meta block, which recovery starts from, or null if there is
     * none. It reads the stream and writes nothing (bergdb 005-50).
     */
    public MetaBlock readLastValidMetaBlock() {
        return rstream.readLastValidMetaBlock();
    }

    public final long getNextPos() {
        return rstream.getNextSpos();
    }

    /**
     * Appends a transaction to the node stream.
     */
    void appendNodes(TransNodes nodes, Trans trans, ArrayList<Node> gotDirtyNodes) {
        appendNodes(nodes, trans, gotDirtyNodes, null);
    }
    
    /**
     * As appendNodes() above; the transaction stores the position of the latest version of
     * topNode, the newest written top node (StoredTrans.topPos).
     */
    void appendNodes(TransNodes nodes, Trans trans, ArrayList<Node> gotDirtyNodes, TopNode topNode) {
        long pos = getNextPos();
        serializer.serialize(nodes, trans.tt, pos, trans.startupPos, gotDirtyNodes, topNode);
        
        trans.tpos = pos;
        trans.lastPos = serializer.getOutputLastSpos();
        trans.nextPos = serializer.getOutputNextSpos();

        byte[] buffer = serializer.getTransBuffer();
        int bufferSize = serializer.getOutputTransSize();

        rstream.append(buffer, 0, bufferSize, true, trans.tt);
        rstream.getMetaBlock().setLastTransSpos(pos);
        appendedEnd = trans.nextPos;        // After the append (bergdb 021-13).
    }
    
    public NodeHeader readNodeHeader(long spos) {
        // Assumes: node type at buffer[4]
        // Assumes: id at offset StoredTopNode.ID_OFFSET for TYPE_TOP_NODE.
        // Assumes: id at offset StoredKeyNode.ID_OFFSET for TYPE_KEY_NODE.
        // Assumes: id at offset StoredValueNode.ID_OFFSET for TYPE_VALUE/TYPE_DELETE.
        // Assumes: byte size of node >= 32.
        
        byte[] buffer = new byte[32];
        rstream.read(spos, buffer, 0, 32);
        
        byte type = buffer[4];
        long id;
        
        if (type == Node.TYPE_TOP_NODE) {
            id = Bytes.bytesToLongLE(buffer, StoredTopNode.ID_OFFSET);
        } else if (type == Node.TYPE_KEY_NODE) {
            id = Bytes.bytesToLongLE(buffer, StoredKeyNode.ID_OFFSET);
        } else if (type == Node.TYPE_VALUE || type == Node.TYPE_DELETE) {
            id = Bytes.bytesToLongLE(buffer, StoredValueNode.ID_OFFSET);
        } else {
            throw new StreamFormatException("unknown node type, " + ((int) type) 
                    + ", spos: " + spos + ", node header bytes: " + StringUtil.toHex(buffer, 0, 8));
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
        // A check, not an assert (2026-11-06, bergdb 019-32): a pointer of a damaged node
        // reaches here.
        if (spos < RecoverableStream.META_BLOCK_SIZE) {
            throw new StreamFormatException("Bad node position, " + spos + ".");
        }

        byte[] buffer = new byte[1024];      
        rstream.read(spos, buffer, 0, 4);
        
        int size = Bytes.bytesToIntLE(buffer, 0);
        if (size <= 6) {
            throw new StreamFormatException("Bad node byte size, " + size + ". At spos " + spos
                    + ".");
        }
        checkReadSize(spos, size);
        
        if (buffer.length < size) {
            buffer = new byte[size];
        }
        
        rstream.read(spos, buffer, 0, size);
        Node node = bytesToNode(spos, buffer, 0, size).getNode();
        return node;
    }
    
    public byte[] readTransBytes(long tpos) {
        int size = readRecordHeader(tpos, 7);
        
        byte[] buffer = new byte[size];
        rstream.read(tpos, buffer, 0, size);
        return buffer;
    }

    /**
     * Reads the header of the record at 'tpos', its size and its format byte, before the
     * record (bergdb 024-17, QL7 and 6.5; 024-24), and returns its size. A size of at most
     * 'min', or over the record limit StoredTrans.MAX_RECORD_SIZE (L7), is corrupt; so is one
     * beyond the stream (checkReadSize). A record of another format is refused with
     * VersioningStreamException before its bytes are read: until 2026.5 the whole record was
     * read into one array first, so that a start on an older stream whose last record was
     * 1.5 GB needed 1.5 GB of heap to refuse it.
     *
     * @throws StreamFormatException
     * @throws VersioningStreamException
     */
    private int readRecordHeader(long tpos, int min) {
        byte[] header = new byte[4];
        rstream.read(tpos, header, 0, 4);
        int size = Bytes.bytesToIntLE(header, 0);
        if (size <= min) {
            throw new StreamFormatException("Bad transaction size, " + size + ", transPos="
                    + tpos + ", stream size: " + rstream.getLength() + ".");
        }
        if (size > StoredTrans.MAX_RECORD_SIZE) {
            throw new StreamFormatException("Bad transaction size, " + size + ", transPos="
                    + tpos + ": more than the record limit, " + StoredTrans.MAX_RECORD_SIZE
                    + " (bergdb 024-17, L7).");
        }
        checkReadSize(tpos, size);
        // The format byte of a committed record (its last byte set, RecoverableStream): an
        // uncommitted one, a crash's tail, is skipped by the iterator, as before.
        byte[] b = new byte[1];
        rstream.read(RecoverableStream.getSpos(tpos, size - 1), b, 0, 1);
        if (b[0] == RecoverableStream.LAST_BYTE) {
            header = new byte[5];
            rstream.read(tpos, header, 0, 5);
            if (header[4] != StoredTrans.RECORD_FORMAT) {
                throw new VersioningStreamException(StoredTrans.formatRefused(header[4]));
            }
        }
        return size;
    }
    
    /** Check untrusted sizes before allocating, excluding meta blocks (bergdb 005-74, A). */
    private void checkReadSize(long pos, int size) {
        checkReadSize(pos, size, rstream.getLength());
    }

    /** checkReadSize() above, for the stream's length 'length'. */
    static void checkReadSize(long pos, int size, long length) {
        // Check the last byte, not the next position: a record may end just before a meta
        // block that a crash has not written. Recovery handles that incomplete block.
        // 'pos >= length' first (2026-11-09, bergdb 021-14): getSpos() overflows for a pos
        // near Long.MAX_VALUE, and the check passed; for a pos below the length it cannot.
        if (size < 8 || pos >= length
                || RecoverableStream.getSpos(pos, (long) size - 1) >= length) {
            throw new StreamFormatException("Bad item byte size, " + size + ", at spos " + pos
                    + ": beyond the stream's record bytes, length " + length + ".");
        }
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
        // A node holds at least its header, with the checksum (bergdb 024-25).
        if (size < NodeChecksum.HEADER_SIZE) {
            throw new StreamFormatException("Bad node size, " + size + ", at spos " + spos
                    + ": less than a node's header.");
        }
        int computedSum = NodeChecksum.sum(buffer, offset, size);
        int storedSum = NodeChecksum.stored(buffer, offset);
        
        if (computedSum != storedSum) {
            throw new StreamChecksumException("spos: " + spos + ", storedSum: "
                    + Integer.toUnsignedString(storedSum) + ", computedSum: "
                    + Integer.toUnsignedString(computedSum) + ", nodeType: " + nodeType);
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
    
    /**
     * An iterator from the transaction RecoverableStream.getPosOfTransCompletedBefore()
     * gives for 'startPos': one completed before it, in general not the last one, or the
     * first one found if there is none (bergdb 005-39).
     */
    public TransIterator createTransIterator(long startPos) {
        return new TransIterator(startPos, false);
    }
    
    public TransIterator createTransIteratorFromExactStartupPos(long startPos) {
        return new TransIterator(startPos, true);
    }

    /**
     * Iterator that iterates through the successful transactions in the stream 
     * from a given start pos.
     * From an exact start pos, such as a startup pos, the transaction there must be
     * committed, or next() throws a StreamFormatException (bergdb 005-28).
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
        boolean started; // a transaction has been read, committed or not

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
                if (!started) {
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

                // The header first (bergdb 024-17, QL7): a size over the record limit is
                // corrupt, another format refused, before the record is read.
                int size = readRecordHeader(tpos, 16);

                byte[] buffer = new byte[size];
                rstream.read(tpos, buffer, 0, size);
                byte lastByte = buffer[buffer.length - 1];
                if (lastByte != 0 && lastByte != RecoverableStream.LAST_BYTE) {
                    throw new StreamFormatException("Bad lastByte: " + ((int) lastByte));
                }
                transOk = lastByte == 0 ? false : true;
                transBuffer = buffer;

                lastPos = RecoverableStream.getSpos(tpos, size - 1);
                nextTransPos = RecoverableStream.getSpos(tpos, size);
                started = true;

                if (!transOk) {
                    if (exactStartPos && tpos == startPos) {
                        // An exact start pos must name a committed transaction (bergdb
                        // 005-28). Before, next() went back to it and read it again, for ever.
                        throw new StreamFormatException("Transaction at start pos " + tpos
                                + " is not committed (its last byte is 0).");
                    }
                    continue start;
                }

                transCount++; // We do not include non-committed transactions in count.
                transTime = Bytes.bytesToLongLE(transBuffer, 8);

                break; // always break at end of while loop
            }
            return true;
        }

        public StoredTrans getStoredTrans() {
            return StoredTrans.parse(tpos, transBuffer);
        }
    }
}
