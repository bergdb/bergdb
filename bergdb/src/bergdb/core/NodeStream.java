package bergdb.core;

import java.io.PrintStream;

import bergdb.common.Bytes;
import bergdb.dag.INode;
import bergdb.dag.Spos;
import bergdb.dag.StreamChecksumException;
import bergdb.dag.TransNodes;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;

/**
 * Db uses a NodeStream object as its interface to the database stream. Db appends nodes with
 * appendNodes() and reads nodes with readNode(). Concurrency: One writer thread calling addNodes(),
 * getLength(), recover(), getPosOfLastCompletedTrans() and multiple reader threads calling
 * readNode() is the concurrency situation that is assumed.
 * 
 * @author Frans Lundberg
 */
public class NodeStream implements bergdb.dag.Dag.NodeReader {
    /** Transaction start position is always divisable by TRANS_ALIGNMENT. */
    static final int TRANS_ALIGNMENT = 8;

    private final RecoverableStream rstream;
    private final Object writeLock;
    // For asserting that caller of some methods holds the required DB.writeLock.
    private final TransSerializer transSerializer;

    /** Byte array with 64 zero bytes, useful for zero-fill of transaction buffer. */
    public static final byte[] ZEROS64 = new byte[64];

    /**
     * Creates a new NodeStream given a RecoverableStream.
     * 
     * @param rstream
     *            The underlying stream.
     * @param writeEnabled
     *            True for normal usage, false for performance testing (will disable writes to the
     *            underlying stream and INode serialization).
     */
    public NodeStream(RecoverableStream rstream, Object writeLock) {
        if (rstream == null) {
            throw new IllegalArgumentException("rstream == null not allowed.");
        }

        if (writeLock == null) {
            throw new IllegalArgumentException("writeLock == null not allowed");
        }

        this.transSerializer = new TransSerializer();
        this.rstream = rstream;
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

    /**
     * Adds nodes to the stream as one single transaction. Caller must hold Db.writeLock.
     * 
     * @param trans
     *            Parameter for input/output, this method sets trans.tpos/lastSpos/nextSpos.
     *            trans.transTime used as input.
     * @throws StreamIoException
     */
    public void appendNodes(TransNodes nodes, Trans trans) {
        assert nodes.assertNoDuplicates();

        long transTpos = rstream.getNextSpos();
        transSerializer.serialize(nodes, trans.time, transTpos);

        trans.pos = transTpos;
        trans.lastPos = transSerializer.getOutputLastSpos();
        trans.nextPos = transSerializer.getOutputNextSpos();

        byte[] buffer = transSerializer.getOutputTransBuffer();
        int bufferSize = transSerializer.getOutputTransSize();

        rstream.append(buffer, 0, bufferSize, true, trans.time);
        rstream.getMetaBlock().setLastTransSpos(transTpos);
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
    public final INode readNode(long spos) {
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
        
        INode node = bytesToNode(spos, buffer, 0, size, null);
        return node;
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
     * @param stored
     *            If this parameter is non-null, the node and addition data from the stream
     *            (previous spos) is set to it. If only the INode is wanted, this parameter should
     *            be 'null'.
     * @throws StreamFormatException
     * @throws StreamIoException
     */
    static INode bytesToNode(long spos, byte[] buffer, int offset, int size,
            StoredNode stored) {

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

        long sposPrevious = Spos.NULL;
        INode node = null;
        byte[] choices = null;

        switch (nodeType) {
        case INode.TYPE_KEY_NODE:
            StoredKeyNode storedKeyNode = StoredKeyNode.createFromBytes(buffer, offset, spos);
            node = storedKeyNode.getNode();
            sposPrevious = storedKeyNode.getPrevPos();
            break;
        case INode.TYPE_TOP_NODE:
            node = StoredTopNode.fromBytes(buffer, offset, spos);
            break;
        case INode.TYPE_VALUE:
        case INode.TYPE_DELETE:
            StoredValueNode storedValueNode = StoredValueNode.create(buffer, offset, spos);
            node = storedValueNode.getNode();
            choices = storedValueNode.getChoices();
            break;
        default:
            throw new StreamFormatException("Bad node type in stream, " + ((int) nodeType)
                    + ", for stream item at spos = " + spos + ". " + "sposPrevious=" + sposPrevious
                    + ", buffer.length=" + buffer.length + ".");
        }

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
            out.println("==== Trans at " + titer.tpos + " ====");
            NodeIterator niter = titer.getNodeIterator();
            while (niter.next()) {
                INode inode = niter.node;
                out.println("-- " + inode.getClass().getSimpleName() + " prev:"
                        + niter.sposPrevious + " --");
                out.println(inode.toString());
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

    /**
     * Iterator that iterates through the successful transactions in the stream from a given start
     * pos.
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

        public TransIterator() {
            this(0);
        }

        public TransIterator(long startPos) {
            this.startPos = startPos;
        }

        /**
         * Advances iterator to next transaction. Returns true if there was an item, false if not.
         * 
         * Caller must hold DB.writeLock.
         */
        public boolean next() {

            start: while (true) { // Dummy while-loop just to be able to do "continue start;".
                if (transCount == 0) {
                    long p = rstream.getPosOfTransCompletedBefore(startPos);
                    if (p == Spos.NULL) {
                        // No valid transactions in stream.
                        return false;
                    }
                    tpos = p;
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

        public NodeIterator getNodeIterator() {
            return new NodeIterator(tpos, transBuffer);
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
        byte[] choices; // non-null for value nodes (including deletes)
        INode node;
        private StoredNode storedNode;
        private long transTime;

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
            transTime = Bytes.bytesToLongLE(buffer, offset);
            offset += 8;
        }

        public long getTransTime() {
            return transTime;
        }

        /**
         * Advances iterator to next stream item. Sets fields: node, sposPrevious, count, offset.
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

            long spos = RecoverableStream.getSpos(transPos, offset);
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
