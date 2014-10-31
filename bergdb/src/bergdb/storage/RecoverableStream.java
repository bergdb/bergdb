package bergdb.storage;

import java.io.IOException;

import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

/**
 * <p>This class adds transactional support to an underlying AppendOnlyStream.
 * An instance of the class can be used to recover a stream that crashed at any point in the stream.
 * Recovery is done without parsing through the whole stream. This is possible because of 
 * the meta block occurring in the stream at predetermined fixed positions.
 * This class throws DBStreamException when there is an error with the underlying AppendOnlyStream.
 * </p>
 * 
 * <pre>
 * RECOVERABLE STREAM FORMAT
 * The stream format provides one layer on top of an AppendOnlyStream.
 * It has no knowledge of upper layers. For this class, a transaction is simple an array of 
 * bytes. The recoverable stream format is partly defined by the ABNF below. 
 * The ABNF rules below describes the non-meta-block bytes of the stream. 
 * 
 * Transactions = Transaction*
 * Transaction = Header TransactionBytes LastByte
 * Header = 
 *        // 4 bytes. The transaction header consists of the size - the total number of bytes of 
 *        // the Transaction including Header itself (4 bytes) and LastByte (1 byte). The size is 
 *        // stored as a 4-byte little-endian integer. Maximum Size is 2^31-1 (Integer.MAX_VALUE).
 * TransactionBytes = 
 *        // The transaction bytes. For this class (layer), contents can be anything and is 
 *        // unknown.
 * LastByte =
 *        // One byte equal to 10 (decimal) for a successful transaction and 0 otherwise.
 * 
 * The Transactions bytes are interspersed with MetaBlock:s at regular, fixed stream locations.
 * The i'th meta block (first is 0'th) starts at stream position i * META_BLOCK_DISTANCE and is 
 * META_BLOCK_SIZE long. The exact format for the meta blocks is defined by the class 
 * MetaBlock. The Transaction bytes are never written to the locations of the meta blocks.
 * If an ongoing Transaction being written "hits" the meta block area in the stream, it will skip 
 * those bytes and continue writing the transaction data right after it.
 * MetaBlocks are written *eagerly*. If the transaction size == distance to meta block, then the 
 * meta block will be written too. It will be the last part of the stream.
 * </pre>
 * 
 * @see AppendOnlyStream
 * @see MetaBlock
 * @author Frans Lundberg
 */
public class RecoverableStream {
    
    /** The byte size of a meta block in the stream. */
    public static final int META_BLOCK_SIZE = 128;
    
    /** The distance between two consecutive meta blocks in the stream. */
    public static final int META_BLOCK_DISTANCE = 200*1000;
    
    /** Byte size of transaction header. */
    public static final int TRANS_HEADER_SIZE = 4;
    
    /** If check enabled, append sizes must be a multiple of this value. */
    public static final int TRANS_ALIGNMENT = 8;
    
    private static final byte[] zeros = new byte[10*1000];
    private static final int MAX_TRANS_SIZE = Integer.MAX_VALUE;
    public static final byte LAST_BYTE = 10;    
    private final AppendOnlyStream aos;
    private final MetaBlock metaBlock;
    private long posOfLastValidMetaBlock;
    
    /**
     * Creates a new instance from an append-only stream.
     * 
     * @param aos The stream, must not be null.
     * @throws IllegalArgumentException if 'stream' if null.
     */
    public RecoverableStream(AppendOnlyStream aos, MetaBlock metaBlock) {
        if (aos == null) {
            throw new IllegalArgumentException("aos == null not allowed.");
        }
        
        if (metaBlock == null) {
            throw new IllegalArgumentException("metaBlock == null not allowed");
        }
        
        assert zeros.length > META_BLOCK_SIZE : zeros.length + ", too short.";
        
        this.aos = aos;
        this.metaBlock = metaBlock;
        this.posOfLastValidMetaBlock = -1;   // inited later
    }
    
    /**
     * Recovers the stream; adds zero bytes at end if needed, reads the last valid meta block.
     * This method must be called before any data is appended to an existing
     * underlying stream.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException
     */
    public void recover() {
        fixMetaBlockIfNeeded();
        
        MetaBlock lastBlock = readLastValidMetaBlock();
        if (lastBlock == null) {
            throw new StreamFormatException("Could not find *any* valid meta block. "
                    + "At least the very first meta block must be valid in a db stream.");
        }
        
        this.metaBlock.setFromOtherMetaBlock(lastBlock);
        
        long spos;
        if (lastBlock.getLastTransSpos() == Constants.SposNULL) {
            spos = RecoverableStream.META_BLOCK_SIZE;
        } else {
            spos = lastBlock.getLastTransSpos();
        }
        
        fixLastTransactionIfNeeded(spos);
    }
    
    /**
     * Returns the stream position of the last valid meta block, or
     * -1 if unknown.
     */
    public long getPosOfLastValidMetaBlock() {
        return this.posOfLastValidMetaBlock;
    }

    /**
     * Handles the case when the stream crashed while writing the last transaction.
     * The last transaction needs to be "filled out" with zero bytes.
     * 
     * @param spos  The stream position of a transaction in the stream.
     */
    private void fixLastTransactionIfNeeded(long spos) {
        
        while (true) {
            long remaining = getRemainingTransBytes(spos, aos.getLength());
            if (remaining == 0) {
                break;  // We are done!
            }
            
            assert remaining > 0 : "remaining = " + remaining;
            
            if (remaining < 4) {
                // Special case, transaction size not completely written.
                // Add zero bytes to complete 4-byte size.
                appendZeros(4 - remaining);
                remaining = getRemainingTransBytes(spos, aos.getLength());
            }
            
            byte[] buffer = new byte[4];
            read(spos, buffer, 0, 4);
            int transSize = Bytes.bytesToIntLE(buffer, 0);
            if (transSize < (4 + 1) || transSize > MAX_TRANS_SIZE) {
                throw new StreamFormatException("Bad transaction size in db stream, " 
                        + transSize + ", spos " + spos + ". Stream length: " + aos.getLength());
            }
            
            if (remaining < transSize) {
                // Bad last transaction, not enough stream space for it, zero fill to correct.
                appendZeros(transSize - remaining);
                break;   // We are done!
            }
            
            spos = getSpos(spos, transSize);
        }
    }

    private void appendZeros(long zeroCount) {
        while (zeroCount > 0) {
            assert this.metaBlock != null;
            
            int len = (int) (zeroCount > zeros.length ? zeros.length : zeroCount);
            append(zeros, 0, len, false, -1);
            zeroCount -= len;
        }
    }
    
    /**
     * Returns the spos given a start spos and 
     * a size where 'size' is counted in transaction bytes only.
     * 'sposStart' is in the spos coordinate system, while 'size' 
     * is in the transaction pos coordinate system.
     * 
     * @param sposStart  Start spos, cannot be an spos for a byte in a meta-block.
     * @throws IllegalArgumentException  if sposStart is in a meta-block.
     */
    public final static long getSpos(final long sposStart, final int size) {
        final long startOffset = sposStart % META_BLOCK_DISTANCE;
        final long transBytesPerBlock = META_BLOCK_DISTANCE - META_BLOCK_SIZE;
        long blockCount = size / transBytesPerBlock;
        final long left = size - blockCount * transBytesPerBlock;
        
        if (startOffset + left >= META_BLOCK_DISTANCE) {
            blockCount++;
        }
        
        return sposStart + size + blockCount * META_BLOCK_SIZE;
    }
    
    /**
     * The start Spos of the next transaction that will be appended.
     * The caller must hold DB.writeLock since method calls aos.getLength().
     */
    public final long getNextSpos() {
        long pos = aos.getLength();
        int blockPos = (int) (aos.getLength() % META_BLOCK_DISTANCE);
        assert blockPos >= 0 && blockPos < META_BLOCK_DISTANCE : "Bad blockPos, " + blockPos;
        return blockPos < RecoverableStream.META_BLOCK_SIZE ? pos + (RecoverableStream.META_BLOCK_SIZE - blockPos) : pos;
            // If in meta block, position right after it.
    }
    
    /**
     * Number of transaction bytes (non-meta-block bytes) since beginning of stream at a 
     * certain stream position. A concept that is useful internally.
     */
    private static long getTransPos(long spos) {
        final long blockCount = spos / META_BLOCK_DISTANCE;
        final long blockOffset = spos % META_BLOCK_DISTANCE;
        long result = blockCount * (META_BLOCK_DISTANCE - META_BLOCK_SIZE);
        result += blockOffset > META_BLOCK_SIZE ? blockOffset - META_BLOCK_SIZE : 0;
        return result;
    }
    
    
    
    /**
     * Returns the maximum number of bytes a transaction can have that starts at 'spos' given 
     * the current size of the stream (aos.getSize()).
     */
    private static long getRemainingTransBytes(long spos, long streamSize) {
        if (spos > streamSize) {
            throw new IllegalArgumentException("spos >= streamSize, " + spos + ", " + streamSize);
        }
        
        long transPos1 = getTransPos(spos);
        long transPos2 = getTransPos(streamSize);
        long diff = transPos2 - transPos1;
        assert diff >= 0 : transPos1 + ", " + transPos2;
        return transPos2 - transPos1;
    }
    
    

    private void fixMetaBlockIfNeeded() {
        long size = aos.getLength();
        
        assert META_BLOCK_DISTANCE < Integer.MAX_VALUE;
        int blockPos = (int) (size % META_BLOCK_DISTANCE);
        
        if (blockPos > 0 && blockPos < RecoverableStream.META_BLOCK_SIZE) {
            // If in the middle of writing a meta block.
            int zeroByteCount = RecoverableStream.META_BLOCK_SIZE - blockPos;
            try {
                aos.append(zeros, 0, zeroByteCount);
            } catch (IOException e) {
                throw new StreamIoException(e);
            }
        }
    }
     
    /**
     * Reads transaction bytes from the WriteOnceStream into 'buffer'.
     * 
     * @throws StreamIoException
     */
    public void read(long pos, byte[] buffer, int offset, int size) {
        int blockPos = (int) (pos % META_BLOCK_DISTANCE);
        
        if (blockPos >= 0 && blockPos < RecoverableStream.META_BLOCK_SIZE) {
            // If in meta block, position right after it.
            pos += RecoverableStream.META_BLOCK_SIZE - blockPos;
        }
        
        blockPos = (int) (pos % META_BLOCK_DISTANCE);
        int distanceToMeta = META_BLOCK_DISTANCE - blockPos;
        
        while (size >= distanceToMeta) {
            try {
                aos.read(pos, buffer, offset, distanceToMeta);
            } catch (IOException e) {
                throw new StreamIoException(e);
            }
            
            size -= distanceToMeta;
            offset += distanceToMeta;
            pos += distanceToMeta + RecoverableStream.META_BLOCK_SIZE;
            distanceToMeta = META_BLOCK_DISTANCE - RecoverableStream.META_BLOCK_SIZE;
        }
        
        if (size > 0) {
            try {
                aos.read(pos, buffer, offset, size);
            } catch (IOException e) {
                throw new StreamIoException(e);
            }
        }
    }
    
    /**
     * Appends transaction bytes to the stream.
     * The last byte in 'buffer' must equal LAST_BYTE.
     * The first 4 bytes must be the total byte size of the transaction; 
     * that is, it has to equal 'size'.
     *  
     * @param useChecks Normally checks should be run. They are fast.
     * @param transTime Transaction time of the transaction that caused the append or -1
     * if unknown.
     * @throws StreamIoException
     * @throws StreamFormatException
     */
    public void append(byte[] buffer, int offset, int size, boolean useChecks, long transTime) {
        //
        // We could also write the last byte in this method. However, it would
        // give us one more write to AppendOnlyStream or allocation of
        // another buffer. That is why we require the last byte marker to 
        // be included in 'buffer'.
        //
        // Note that the meta block is written *eagerly*. 
        // If 'size' == distanceToMeta, the transaction data *and* the meta
        // block will be written together.
        //
        
        if (useChecks) {            
            if (buffer[offset + size - 1] != LAST_BYTE) {
                throw new IllegalArgumentException("Last byte of transaction " +
                        "must be " + ((int) LAST_BYTE));
            }
            
            int transactionSize = Bytes.bytesToIntLE(buffer, 0);
            if (transactionSize != size) {
                throw new IllegalArgumentException("Bad transactionSize in " +
                		"byte buffer, was " + transactionSize 
                		+ ", expected " + size);
            }
            
        }
        
        long aosSize = aos.getLength();
        
        assert META_BLOCK_DISTANCE < Integer.MAX_VALUE;
        int blockPos = (int) (aosSize % META_BLOCK_DISTANCE);

        if (useChecks && blockPos > 0 && blockPos < RecoverableStream.META_BLOCK_SIZE) {
            // If in the middle of writing a meta block, bad state.
            throw new StreamFormatException("Bad state, in the middle of a " +
            		"meta block, " + blockPos + ", " + aosSize + ".");
        }
        
        int distanceToMeta = META_BLOCK_DISTANCE - blockPos;
        if (blockPos == 0) {
            distanceToMeta = 0;   // Special case
        }
        
        while (size >= distanceToMeta) {
            try {
                aos.append(buffer, offset, distanceToMeta);
                writeMetaBlock();
            } catch (IOException e) {
                throw new StreamIoException(e);
            }
            size -= distanceToMeta;
            offset += distanceToMeta;
            distanceToMeta = META_BLOCK_DISTANCE - RecoverableStream.META_BLOCK_SIZE;
        }
        
        if (size > 0) {
            try {
                aos.append(buffer, offset, size);
            } catch (IOException e) {
                throw new StreamIoException(e);
            }
            offset += size;
        }
    }

    private void writeMetaBlock() throws IOException {
        long metaPos = aos.getLength();
        aos.append(metaBlock.getBlock(), 0, RecoverableStream.META_BLOCK_SIZE);
        this.posOfLastValidMetaBlock = metaPos;
        
        //System.out.println("RecoverableStream, wrote MetaBlock, pos: " + metaPos 
        //        + ", startupPos: " + metaBlock.getStartupPos());
    }
    
    /**
     * Returns the last valid meta block, or null if no such block exists.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException
     */
    public MetaBlock readLastValidMetaBlock() {
        long length = aos.getLength();
        long spos = length - META_BLOCK_SIZE;
        spos = spos < 0 ? 0 : spos;        
        MetaBlock block = readValidMetaBlock(aos, spos);
        if (block == null) {
            return null;
        }
        this.posOfLastValidMetaBlock = block.getPos();
        
        return block;
    }
    
    public MetaBlock getMetaBlock() {
        return metaBlock;
    }
    
    /**
     * Returns the length of the underlying append-only stream.
     * Caller must hold DB.writeLock.
     */
    public long getLength() {
        assert aos != null;
        return aos.getLength();
    }
    
    /**
     * Returns the last valid transaction that was completely written before 
     * stream position 'spos'.
     * If there is no such transaction, the spos of the very first valid 
     * transaction is returned instead. If there is no valid transaction at all in 
     * the stream, Spos.NULL is returned. Caller must hold DB.writeLock.
     * 
     * @throws StreamIoException
     */
    public long getPosOfTransCompletedBefore(long spos) {
        // TODO LATER. This doc is not true, or we have a bug. This method does not iterate to find
        // last valid transaction, just any recent transaction completely written before
        // stream position 'spos'.
        
        MetaBlock meta = readValidMetaBlock(aos, spos);
        long result = meta.getLastTransSpos();
        if (result == Constants.SposNULL) {
            if (aos.getLength() > RecoverableStream.META_BLOCK_SIZE) {
                result = RecoverableStream.META_BLOCK_SIZE;     // spos of very first transaction
            }
        }
        return result;
    }
    
    /**
     * Reads and returns the last valid meta block that starts before or at
     * 'spos'. If no such meta block exists, null is returned.
     * 
     * @throws StreamIoException
     */
    static MetaBlock readValidMetaBlock(AppendOnlyStream aos, long spos) {
        long metaIndex;
        byte[] metaBytes = new byte[RecoverableStream.META_BLOCK_SIZE];
        MetaBlock result = null;
        long blockPos;
        
        metaIndex = spos / META_BLOCK_DISTANCE;
        for (long i = metaIndex; i >= 0; i--) {
            try {
                blockPos = i * META_BLOCK_DISTANCE;
                aos.read(blockPos, metaBytes, 0, metaBytes.length);
            } catch (IOException e) {
                throw new StreamIoException(e);
            }
            
            result = new MetaBlock(metaBytes, blockPos);
            if (result.isValid()) {
                result.checkFormat();
                break;
            } else {
                result = null;
            }
        }
        
        return result;
    }
    
    /**
     * Returns true if the spos is an allowed position, that is, one that is not negative,
     * or within a meta block.
     */
    static void assertAllowedPos(long spos) {
        if (spos != Constants.SposNULL) {
            if (spos < 0) {
                throw new AssertionError("Bad spos (negative), " + spos + ".");
            }
            
            if ((spos % META_BLOCK_DISTANCE) < RecoverableStream.META_BLOCK_SIZE) {
                throw new AssertionError("Bad spos (in metablock), " + spos + ".");
            }
        }
    }

    /**
     * Iterates through the transactions starting at a certain spos.
     * The first transaction is the last transaction that completed before
     * 'spos' or if there is no such transaction, the very first transaction
     * in the stream is the first returned by the iterator.
     */
    public static class Iterator {
        RecoverableStream stream;
        long spos;
        byte[] bytes;
        long transSSPos;
        boolean first = true;
        
        private Iterator(RecoverableStream stream, long spos) {
            this.stream = stream;
            this.spos = spos;
        }
        
        /**
         * Gets the next valid transaction and returns true if there is one.
         * Otherwise, this method returns false.
         * Use getBytes() to get the actual transaction bytes.
         * 
         * @throws StreamIoException
         * @throws StreamFormatException
         */
        public boolean next() {
            if (first) {
                spos = stream.getPosOfTransCompletedBefore(spos);
                first = false;
            }
            
            if (spos == Constants.SposNULL) {
                return false;
            }
            
            boolean result = false;
            
            while (true) {
                byte[] sizeBytes = new byte[4];
                stream.read(spos, sizeBytes, 0, sizeBytes.length);
                int size = Bytes.bytesToIntLE(sizeBytes, 0);
                if (size <= 5 || size > MAX_TRANS_SIZE) {
                    throw new StreamFormatException("Bad transaction byte " +
                    		"size in db stream, " + size + ".");
                }
                
                bytes = new byte[size];
                stream.read(spos, bytes, 0, bytes.length);
                transSSPos = spos;
                
                spos = RecoverableStream.getSpos(spos, size);
                if (spos >= stream.getLength()) {
                    spos = Constants.SposNULL;
                }
                
                if (bytes[bytes.length - 1] == LAST_BYTE) {
                    result = true;
                    break;
                }
                
                if (spos == Constants.SposNULL) {
                    result = false;
                    break;
                }
            }
            
            return result;
        }
        
        public byte[] getBytes() {
            return bytes;
        }
        
        /**
         * Only valid if next() returned true.
         */
        public long getSSPos() {
            return transSSPos;
        }
    }
    
    public static class Tester {
        private Tester() {}
        
        @T
        public static void testGetRemainingTransBytes1() {
            Assert.assertEquals(300 - META_BLOCK_SIZE, getRemainingTransBytes(100, 300));
        }
        
        @T
        public static void testGetRemainingTransBytes3() {
            // Extends over two meta blocks.
            long res = getRemainingTransBytes(0, META_BLOCK_DISTANCE+1000);
            Assert.assertEquals(META_BLOCK_DISTANCE+1000 - 2 * META_BLOCK_SIZE, res);
        }
        
        @T
        public static void testGetRemainingTransBytes4() {
            // Exactly after a meta block
            long res = getRemainingTransBytes(0, META_BLOCK_DISTANCE + META_BLOCK_SIZE);
            Assert.assertEquals(META_BLOCK_DISTANCE - META_BLOCK_SIZE, res);
        }
        
        @SuppressWarnings("all")
        @T
        public static void testThatConstantsMatch() {
            Assert.assertTrue(META_BLOCK_SIZE % TRANS_ALIGNMENT == 0);
            Assert.assertTrue(META_BLOCK_DISTANCE % TRANS_ALIGNMENT == 0);
        }
        
        @T
        private static void testGetTransPos() {
            Assert.assertEquals(0, getTransPos(0));
            Assert.assertEquals(0, getTransPos(1));
            Assert.assertEquals(0, getTransPos(META_BLOCK_SIZE));
            Assert.assertEquals(1, getTransPos(META_BLOCK_SIZE + 1));
            Assert.assertEquals(META_BLOCK_DISTANCE - META_BLOCK_SIZE, getTransPos(META_BLOCK_DISTANCE));
            Assert.assertEquals(META_BLOCK_DISTANCE - META_BLOCK_SIZE - 1, getTransPos(META_BLOCK_DISTANCE - 1));
            Assert.assertEquals(2 * (META_BLOCK_DISTANCE - META_BLOCK_SIZE) + 1, 
                    getTransPos(2 * META_BLOCK_DISTANCE + META_BLOCK_SIZE + 1));
        }
        
        @T
        public static void test1() {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r = new RecoverableStream(mstream, new MetaBlock());
            
            byte[] transBytes = new byte[20];
            Bytes.intToBytesLE(20, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            
            r.append(transBytes, 0, transBytes.length, true, -1);
            
            Assert.assertEquals(RecoverableStream.META_BLOCK_SIZE + 20, mstream.getLength());
        }
        
        @T
        public static void testGetPos1() {
            final int s = META_BLOCK_SIZE;
            final int d = META_BLOCK_DISTANCE;
            
            Assert.assertTrue(RecoverableStream.getSpos(s, d) == d + s + s);
            Assert.assertTrue(RecoverableStream.getSpos(s, 0) == s);
            Assert.assertTrue(RecoverableStream.getSpos(s + 18, 3) == s + 21);
        }
        
        @T
        public static void testGetPos2() {
            final int s = META_BLOCK_SIZE;
            final int d = META_BLOCK_DISTANCE;
            
            Assert.assertTrue(RecoverableStream.getSpos(10*d + s, 38) == 10*d + s + 38);
            Assert.assertEquals(11*d + s + 10, RecoverableStream.getSpos(10*d + (d-10), 20));
            Assert.assertEquals(15*d + (d-s-10), RecoverableStream.getSpos(10*d + (d-s-10), 5*(d-s)));
        }
        
        @T
        public static void crashInFirstTransaction() throws Exception {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            
            byte[] transBytes = new byte[20];
            Bytes.intToBytesLE(20, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            r1.append(transBytes, 0, 10, false, -1);     // Only first 10 bytes of trans
            
            RecoverableStream r2 = new RecoverableStream(mstream, new MetaBlock());
            r2.recover();
            
            Assert.assertEquals(RecoverableStream.META_BLOCK_SIZE + 20, mstream.getLength());
            
            byte[] buffer = new byte[1];
            mstream.read(RecoverableStream.META_BLOCK_SIZE + 20 - 1, buffer, 0, 1);
                    // Reads last byte
            
            Assert.assertEquals(0, buffer[0]);
        }
        
        @T
        public static void crashInTransactionSize() throws IOException {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            
            byte[] transBytes = new byte[20];
            Bytes.intToBytesLE(20, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            r1.append(transBytes, 0, 2, false, -1);
                // Only first 2 bytes of trans (trans byte size incomplete).
            
            RecoverableStream r2 = new RecoverableStream(mstream, new MetaBlock());
            r2.recover();
            
            Assert.assertEquals(RecoverableStream.META_BLOCK_SIZE + 20, mstream.getLength());
            
            byte[] buffer = new byte[1];
            mstream.read(RecoverableStream.META_BLOCK_SIZE + 20 - 1, buffer, 0, 1);
                    // Reads last byte
            
            Assert.assertEquals(0, buffer[0]);
        }
        
        @T
        public static void crashInThirdTransaction() throws Exception {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            
            byte[] transBytes = new byte[20];
            Bytes.intToBytesLE(20, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            r1.append(transBytes, 0, 20, true, -1);
            r1.append(transBytes, 0, 20, true, -1);
            r1.append(transBytes, 0, 10, false, -1);
            
            Assert.assertEquals(RecoverableStream.META_BLOCK_SIZE + 20 + 20 + 10, mstream.getLength());
            
            RecoverableStream r2 = new RecoverableStream(mstream, new MetaBlock());
            r2.recover();
            
            Assert.assertEquals(RecoverableStream.META_BLOCK_SIZE + 20 + 20 + 20, mstream.getLength());
            
            byte[] buffer = new byte[1];
            mstream.read(RecoverableStream.META_BLOCK_SIZE + 60 - 1, buffer, 0, 1);
                    // Reads last byte
            Assert.assertEquals(0, buffer[0]);
        }
        
        @T
        public static void largeTransaction() throws IOException {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            
            byte[] transBytes = new byte[3 * RecoverableStream.META_BLOCK_DISTANCE + 20];
            Bytes.intToBytesLE(transBytes.length, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            r1.append(transBytes, 0, transBytes.length, true, -1);
            
            long expectedSize = 3 * RecoverableStream.META_BLOCK_DISTANCE + 20 + 4 * RecoverableStream.META_BLOCK_SIZE;
            Assert.assertEquals(expectedSize, mstream.getLength());
            
            RecoverableStream r2 = new RecoverableStream(mstream, new MetaBlock());
            r2.recover();
            
            Assert.assertEquals(expectedSize, mstream.getLength());
        }
        
        @T
        public static void crashInlargeTransaction() throws IOException {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            
            byte[] transBytes = new byte[3 * RecoverableStream.META_BLOCK_DISTANCE + 20];
            Bytes.intToBytesLE(transBytes.length, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            r1.append(transBytes, 0, transBytes.length - 10, false, 1);   
                // last 10 bytes missing
            
            long expectedSize = 3 * RecoverableStream.META_BLOCK_DISTANCE + 20 + 4 * RecoverableStream.META_BLOCK_SIZE - 10;
            Assert.assertEquals(expectedSize, mstream.getLength());
            
            RecoverableStream r2 = new RecoverableStream(mstream, new MetaBlock());
            r2.recover();
            
            Assert.assertEquals(expectedSize + 10, mstream.getLength());
        }
        
        @T
        public static void recoverFromMiddleOfStream() {
            //
            // A recovery that is not done from the beginning of the stream.
            //
            
            long spos = 0;
            
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            
            //System.out.println("---- RecoverableStream.Tester.recoverFromMiddleOfStream ----");
            
            byte[] transBytes = new byte[3 * RecoverableStream.META_BLOCK_DISTANCE + 20];
            Bytes.intToBytesLE(transBytes.length, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            
            r1.append(transBytes, 0, transBytes.length, true, -1);
            spos = r1.getNextSpos();
            
            //System.out.format("spos = %d\n", spos);
            
            r1.getMetaBlock().setLastTransSpos(spos);
            long expectedSize = 3 * RecoverableStream.META_BLOCK_DISTANCE + 20 + 4 * RecoverableStream.META_BLOCK_SIZE;
            Assert.assertEquals(expectedSize, mstream.getLength());
            
            spos = r1.getNextSpos();
            r1.append(transBytes, 0, transBytes.length, true, -1);
            r1.getMetaBlock().setLastTransSpos(spos);
            
            Assert.assertEquals(true, mstream.getLength() > transBytes.length * 2);
            long size = mstream.getLength();
            
            RecoverableStream r2 = new RecoverableStream(mstream, new MetaBlock());
            r2.recover();
            
            Assert.assertEquals(size, mstream.getLength());
                    // Checks for no append during recovery.
        }
        
        @T
        public static void testIterator() throws Exception {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            
            byte[] transBytes = new byte[20];
            Bytes.intToBytesLE(20, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            
            transBytes[5] = 1;
            r1.append(transBytes, 0, 20, true, -1);
            transBytes[5] = 2;
            r1.append(transBytes, 0, 20, true, -1);
            transBytes[5] = 3;
            r1.append(transBytes, 0, 20, true, -1);
            
            Assert.assertEquals(RecoverableStream.META_BLOCK_SIZE + 20 + 20 + 20, mstream.getLength());
            
            RecoverableStream r2 = new RecoverableStream(mstream, new MetaBlock());
            r2.recover();
            
            Assert.assertEquals(RecoverableStream.META_BLOCK_SIZE + 20 + 20 + 20, mstream.getLength());
            
            Iterator iter = new Iterator(r2, 0);
            
            Assert.assertEquals(true, iter.next());
            transBytes = iter.getBytes();
            Assert.assertEquals(1, transBytes[5]);
            
            Assert.assertEquals(true, iter.next());
            transBytes = iter.getBytes();
            Assert.assertEquals(2, transBytes[5]);
            
            Assert.assertEquals(true, iter.next());
            transBytes = iter.getBytes();
            Assert.assertEquals(3, transBytes[5]);
            
            Assert.assertEquals(false, iter.next());
        }
        
        @T
        public static void testConstantInFileStream() {
            Assert.assertTrue(FileStream.getSmallestFileSize() % META_BLOCK_DISTANCE == 0);
        }
    }
}
