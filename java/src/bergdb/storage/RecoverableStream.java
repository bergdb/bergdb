package bergdb.storage;

import java.io.IOException;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.common.Util;
import bergdb.core.StoredTrans;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

// TODO D. Remove reference to core.StoredTrans, ref storage -> core not allowed.

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
    
    /** 
     * Smallest size of a transaction that the layer above reads (NodeStream: a 16-byte 
     * header and the last byte). A transaction header fixed at recovery must give at 
     * least this size.
     */
    public static final int MIN_TRANS_SIZE = 16 + 1;
    
    /** If check enabled, append sizes must be a multiple of this value. */
    public static final int TRANS_ALIGNMENT = 8;
    
    private static final byte[] zeros = new byte[10*1000];
    private static final int MAX_TRANS_SIZE = Integer.MAX_VALUE;
    public static final byte LAST_BYTE = 10;    
    private final AppendOnlyStream aos;
    private final MetaBlock metaBlock;
    private long posOfLastValidMetaBlock;
    private long lastTransSposOfLastValidMetaBlock = -1;
        // The transaction that recovery starts from (2026-10-13).
    
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
        
        metaBlock.setFromOtherMetaBlock(lastBlock);
        
        long spos;
        if (lastBlock.getLastTransSpos() == Constants.SposNULL) {
            spos = RecoverableStream.META_BLOCK_SIZE;
        } else {
            spos = lastBlock.getLastTransSpos();
        }
        
        fixLastTransactionIfNeeded(spos);
    }
    
    /**
     * Returns the position of the transaction named by the last valid meta block, where
     * recovery starts, or -1 if unknown or none. The stream must not be cut after it.
     */
    public long getLastTransSposOfLastValidMetaBlock() {
        return this.lastTransSposOfLastValidMetaBlock;
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
            
            if (remaining < 5) {
                // Special case, transaction header not completely written.
                
                byte[] existingBytes = new byte[(int) remaining];
                read(spos, existingBytes, 0, existingBytes.length);
                
                byte[] bytesToAppend = transHeaderFixBytes(existingBytes);
                append(bytesToAppend, 0, bytesToAppend.length, false, -1);
                
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

    private static byte[] transHeaderFixBytes(byte[] existingBytes) {
        // If existing bytes (zero-filled) is large enough, zero-fill it.
        // If not, add 1 and then zeros.
        // 2026-10-13 (CrashTest): "large enough" was 6, so a cut after one size
        // byte of 6 to 16 gave a transaction that NodeStream rejected at startup
        // ("Bad transaction size"). Now it is MIN_TRANS_SIZE.
        
        byte[] fixBytes;
        int bytesToAdd = 5 - existingBytes.length;
        
        if (existingBytes.length < 1 || existingBytes.length >= 5) {
            throw new IllegalArgumentException("existingBytes: " + StringUtil.toHex(existingBytes));
        }
        
        byte[] buffer = new byte[5];
        System.arraycopy(existingBytes, 0, buffer, 0, existingBytes.length);
        
        int sizeFromBuffer = Bytes.bytesToIntLE(buffer, 0);
        
        boolean existingSizeTooSmall = sizeFromBuffer < MIN_TRANS_SIZE;
        
        fixBytes = new byte[bytesToAdd];
        fixBytes[fixBytes.length - 1] = StoredTrans.CURRENT_FORMAT_VERSION;
        
        for (int i = 0; i < bytesToAdd - 1; i++) {
            if (existingSizeTooSmall) {
                fixBytes[i] = (i == 0) ? (byte) 1 :  (byte) 0;
            } else {
                fixBytes[i] = 0;
            }
        }
        
        return fixBytes;
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
    public final static long getSpos(final long sposStart, final long size) {
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
     * The inverse of getSpos() (2026-10-24, bergdb 005-34): the start spos of a transaction
     * whose byte at offset 'size', counted in transaction bytes only, is at 'spos'. A value
     * node stores its offset in its record's bytes, which a meta block in the record makes
     * shorter than the distance in the stream.
     * 
     * @param spos  The spos of a byte of the transaction, not an spos in a meta block.
     * @throws IllegalArgumentException  if 'spos' is in a meta block, or the transaction
     *      would start before the first transaction byte of the stream.
     */
    public final static long getStartSpos(final long spos, final long size) {
        final long transBytesPerBlock = META_BLOCK_DISTANCE - META_BLOCK_SIZE;
        final long transPos = getTransPos(spos) - size;
        if (spos < 0 || spos % META_BLOCK_DISTANCE < META_BLOCK_SIZE || transPos < 0 
                || size < 0) {
            throw new IllegalArgumentException("No transaction start " + size 
                    + " transaction bytes before spos " + spos + ".");
        }
        return (transPos / transBytesPerBlock) * META_BLOCK_DISTANCE + META_BLOCK_SIZE 
                + transPos % transBytesPerBlock;
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
        
        if (size > 0 && blockPos < RecoverableStream.META_BLOCK_SIZE) {
            // If in the middle of writing a meta block, or at the position of one not begun.
            // 2026-10-23 (bergdb 005-27): a stream that ended at a meta block's position, after a
            // transaction that ended there, was left as it was. append() writes such a
            // transaction and its meta block in two appends, and a flush can come between them.
            // Recovery then stepped past the meta block, beyond the end of the stream, and the
            // database did not start. The block filled out is invalid, as a partly written one
            // is; recovery takes the valid one before it.
            
            int byteCount = RecoverableStream.META_BLOCK_SIZE - blockPos;
            try {
                aos.append(MetaBlock.FILL_OUT_TEMPLATE, blockPos, byteCount);
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
        this.lastTransSposOfLastValidMetaBlock = metaBlock.getLastTransSpos();
        
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
        MetaBlock block = readAValidMetaBlock(aos, spos);
        if (block == null) {
            return null;
        }
        this.posOfLastValidMetaBlock = block.getPos();
        this.lastTransSposOfLastValidMetaBlock = block.getLastTransSpos();
        
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
    
    /** The first position that can be read; larger than 0 after a pretruncate. */
    public long getFirstPos() {
        return aos.getFirstPos();
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
        
        MetaBlock meta = readAValidMetaBlock(aos, spos);
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
    static MetaBlock readAValidMetaBlock(AppendOnlyStream aos, long spos) {
        long metaIndex;
        MetaBlock result = null;
        
        metaIndex = spos / META_BLOCK_DISTANCE;
        
        // 2026-10-13: the search went down to block 0, also when the front of the
        // stream had been cut (pretruncate), and then failed reading the cut part. Blocks
        // before the first position of the stream are not searched.
        final long firstIndex = (aos.getFirstPos() + META_BLOCK_DISTANCE - 1) / META_BLOCK_DISTANCE;
        
        for (long i = metaIndex; i >= firstIndex; i--) {
        	long blockPos = i * META_BLOCK_DISTANCE;
            result = readMetaBlock(aos, blockPos);
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
     * Returns the MetaBlock at the given stream position.
     * The block may be invalid, caller should check it.
     * 
     * @throws StreamFormatException
     * @thrown StreamIoException
     * @throws VersioningStreamException
     */
    private static MetaBlock readMetaBlock(AppendOnlyStream aos, long blockPos) {
        byte[] header = new byte[6];
        
        try {
            aos.read(blockPos, header, 0, header.length);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
        
        byte[] expectedMagic = MetaBlock.MAGIC;
        byte[] actualMagic = Util.subarray(header, 0, 4);
        
        if (!Util.areEqual(expectedMagic, actualMagic)) {
            throw new BadMagicBytes("Expected magic bytes: " 
                    + StringUtil.toHex(expectedMagic) + ", got: " + StringUtil.toHex(actualMagic));
        }
        
        int version = Bytes.bytesToUShortLE(header, 4);
        
        if (version != MetaBlock.VERSION_154) {
            throw new VersioningStreamException("Cannot read meta block with version " 
                    + version + ". Version supported: " + MetaBlock.VERSION_154);
        }
        
        byte[] metaBytes = new byte[RecoverableStream.META_BLOCK_SIZE];
        
        try {
            aos.read(blockPos, metaBytes, 0, metaBytes.length);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
        
        return new MetaBlock(metaBytes, blockPos);
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
    }
    
    public static class Tester {
        private Tester() {}
        
        @Nano
        public static void testGetRemainingTransBytes1() {
            Assert.assertEquals(300 - META_BLOCK_SIZE, getRemainingTransBytes(100, 300));
        }
        
        @Nano
        public static void testGetRemainingTransBytes3() {
            // Extends over two meta blocks.
            long res = getRemainingTransBytes(0, META_BLOCK_DISTANCE+1000);
            Assert.assertEquals(META_BLOCK_DISTANCE+1000 - 2 * META_BLOCK_SIZE, res);
        }
        
        @Nano
        public static void testGetRemainingTransBytes4() {
            // Exactly after a meta block
            long res = getRemainingTransBytes(0, META_BLOCK_DISTANCE + META_BLOCK_SIZE);
            Assert.assertEquals(META_BLOCK_DISTANCE - META_BLOCK_SIZE, res);
        }
        
        @SuppressWarnings("all")
        @Nano
        public static void testThatConstantsMatch() {
            Assert.assertTrue(META_BLOCK_SIZE % TRANS_ALIGNMENT == 0);
            Assert.assertTrue(META_BLOCK_DISTANCE % TRANS_ALIGNMENT == 0);
        }
        
        @Nano
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
        
        @Nano
        public static void test1() {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r = new RecoverableStream(mstream, new MetaBlock());
            
            byte[] transBytes = new byte[20];
            Bytes.intToBytesLE(20, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            
            r.append(transBytes, 0, transBytes.length, true, -1);
            
            Assert.assertEquals(RecoverableStream.META_BLOCK_SIZE + 20, mstream.getLength());
        }
        
        @Nano
        public static void testGetPos1() {
            final int s = META_BLOCK_SIZE;
            final int d = META_BLOCK_DISTANCE;
            
            Assert.assertTrue(RecoverableStream.getSpos(s, d) == d + s + s);
            Assert.assertTrue(RecoverableStream.getSpos(s, 0) == s);
            Assert.assertTrue(RecoverableStream.getSpos(s + 18, 3) == s + 21);
        }
        
        @Nano
        public static void testGetPos2() {
            final int s = META_BLOCK_SIZE;
            final int d = META_BLOCK_DISTANCE;
            
            Assert.assertTrue(RecoverableStream.getSpos(10*d + s, 38) == 10*d + s + 38);
            Assert.assertEquals(11*d + s + 10, RecoverableStream.getSpos(10*d + (d-10), 20));
            Assert.assertEquals(15*d + (d-s-10), RecoverableStream.getSpos(10*d + (d-s-10), 5*(d-s)));
        }
        
        /** getStartSpos() is the inverse of getSpos() (bergdb 005-34). */
        @Nano
        public static void testGetStartSpos() {
            final int s = META_BLOCK_SIZE;
            final int d = META_BLOCK_DISTANCE;
            Assert.assertEquals(s, getStartSpos(s + 32, 32));
            Assert.assertEquals(d - 1000, getStartSpos(d + s + 1000, 2000));    // across one
            Assert.assertEquals(d - 1000, getStartSpos(d + s, 1000));    // just after one
            Assert.assertEquals(10*d + (d-s-10), getStartSpos(15*d + (d-s-10), 5*(d-s)));
            
            java.util.Random random = new java.util.Random(34);
            for (int i = 0; i < 100000; i++) {
                long start = (long) random.nextInt(1000) * d + s + random.nextInt(d - s);
                long size;
                switch (i % 4) {
                case 0: size = random.nextInt(3 * d); break;
                case 1: size = random.nextInt(100); break;
                case 2: size = Math.max(0, d - start % d - random.nextInt(3)); break;  // block end
                default: size = (long) random.nextInt(20000) * (d - s) + random.nextInt(2); break;
                }
                long spos = getSpos(start, size);
                Assert.assertEquals("start " + start + ", size " + size, start, 
                        getStartSpos(spos, size));
            }
            
            long[][] bad = {{s + 10, 11}, {d + 5, 0}, {d, 100}, {-1, 0}};    // spos, size
            for (long[] b : bad) {
                try {
                    getStartSpos(b[0], b[1]);
                    throw new AssertionError("taken, " + b[0] + ", " + b[1]);
                } catch (IllegalArgumentException e) {
                    // Expected.
                }
            }
        }
        
        @Nano
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
        
        @Nano
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
        
        @Nano
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
        
        @Nano
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
        
        @Nano
        public static void crashInLargeTransaction() throws IOException {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            
            byte[] transBytes = new byte[3 * RecoverableStream.META_BLOCK_DISTANCE + 20];
            Bytes.intToBytesLE(transBytes.length, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            r1.append(transBytes, 0, transBytes.length - 10, false, 1);   
                // last 10 bytes missing
            
            long expectedSize = 3 * RecoverableStream.META_BLOCK_DISTANCE + 20 
                    + 4 * RecoverableStream.META_BLOCK_SIZE - 10;
            Assert.assertEquals(expectedSize, mstream.getLength());
            
            RecoverableStream r2 = new RecoverableStream(mstream, new MetaBlock());
            r2.recover();
            
            Assert.assertEquals(expectedSize + 10, mstream.getLength());
        }
        
        @Nano
        public static void crashInMetaBlockHeader() {
            MemoryStream stream = new MemoryStream();
            MetaBlock metaBlock = new MetaBlock();
            RecoverableStream r1 = new RecoverableStream(stream, metaBlock);
            byte[] transBytes = new byte[200001];
            transBytes[transBytes.length - 1] = RecoverableStream.LAST_BYTE;
            Bytes.intToBytesLE(transBytes.length, transBytes, 0);
            
            r1.append(transBytes, 0, transBytes.length, true, 1000);
            stream.truncate(200003);
            
            RecoverableStream r2 = new RecoverableStream(stream, metaBlock);
            r2.recover();
        }
        
        @Nano
        public static void crashAtMetaBlockPosition() {
            // bergdb 005-27: a transaction ends exactly at the second meta block's position,
            // and a crash ends the stream there, before the meta block. Recovery fills it out,
            // as a partly written one; it is invalid, and recovery takes the first one. Until
            // 2026-10-23, recover() threw ("spos >= streamSize").
            
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            byte[] transBytes = new byte[META_BLOCK_DISTANCE - META_BLOCK_SIZE];
            Bytes.intToBytesLE(transBytes.length, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            r1.append(transBytes, 0, transBytes.length, true, -1);
            Assert.assertEquals(META_BLOCK_DISTANCE + META_BLOCK_SIZE, mstream.getLength());
                    // The meta block is written with the transaction.
            mstream.truncate(META_BLOCK_DISTANCE);
            
            RecoverableStream r2 = new RecoverableStream(mstream, new MetaBlock());
            r2.recover();
            
            Assert.assertEquals(META_BLOCK_DISTANCE + META_BLOCK_SIZE, mstream.getLength());
            Assert.assertEquals(0, r2.readLastValidMetaBlock().getPos());
            
            byte[] transBytes2 = new byte[20];
            Bytes.intToBytesLE(20, transBytes2, 0);
            transBytes2[transBytes2.length - 1] = LAST_BYTE;
            r2.append(transBytes2, 0, 20, true, -1);
            
            RecoverableStream r3 = new RecoverableStream(mstream, new MetaBlock());
            r3.recover();
            
            Assert.assertEquals(META_BLOCK_DISTANCE + META_BLOCK_SIZE + 20, mstream.getLength());
            Iterator iter = new Iterator(r3, 0);
            Assert.assertEquals(true, iter.next());
            Assert.assertEquals(transBytes.length, iter.getBytes().length);
            Assert.assertEquals(true, iter.next());
            Assert.assertEquals(20, iter.getBytes().length);
            Assert.assertEquals(false, iter.next());
        }
        
        @Nano
        public static void crashInTransHeader1() {
            // Crash in trans header when just one byte of size has been
            // written. This bytes is 1, so size would not work if filling out
            // with zeros only.
            
            MemoryStream stream = new MemoryStream();
            MetaBlock metaBlock = new MetaBlock();
            RecoverableStream r1 = new RecoverableStream(stream, metaBlock);
            byte[] transBytes = new byte[1025];    // 0x00000401
            
            Bytes.intToBytesLE(transBytes.length, transBytes, 0);
            transBytes[4] = StoredTrans.CURRENT_FORMAT_VERSION;
            transBytes[transBytes.length - 1] = RecoverableStream.LAST_BYTE;
            
            r1.append(transBytes, 0, transBytes.length, true, 10);
            
            stream.truncate(META_BLOCK_SIZE + 1);
            
            RecoverableStream r2 = new RecoverableStream(stream, metaBlock);
            r2.recover();
        }
        
        @Nano
        public static void crashInTransHeader2() {
            // Crash in trans header when just two bytes of the trans size field
            // has been written. These bytes are 1 and 0, so the size would not 
            // work if filling out with zeros only. The trans size must be large
            // enough to fit trans header + last byte. It must be at least 6 bytes.
            
            MemoryStream stream = new MemoryStream();
            MetaBlock metaBlock = new MetaBlock();
            RecoverableStream r1 = new RecoverableStream(stream, metaBlock);
            byte[] transBytes = new byte[0x00010002];    // 65536 + 2
            
            Bytes.intToBytesLE(transBytes.length, transBytes, 0);
            transBytes[4] = StoredTrans.CURRENT_FORMAT_VERSION;
            transBytes[transBytes.length - 1] = RecoverableStream.LAST_BYTE;
            
            r1.append(transBytes, 0, transBytes.length, true, 10);
            
            stream.truncate(META_BLOCK_SIZE + 2);
            
            RecoverableStream r2 = new RecoverableStream(stream, metaBlock);
            r2.recover();
        }
        
        @Nano
        public static void testTransHeaderFixBytes1() {
            // Test with one existing byte that is 0.
            
            byte[] existing = new byte[]{0};
            byte[] fix = transHeaderFixBytes(existing);
            
            byte[] total = Util.concat(existing, fix);
            int size = Bytes.bytesToIntLE(total, 0);
            
            Assert.assertEquals(256, size);
        }
        
        @Nano
        public static void testTransHeaderFixBytes2() {
            // Test with one existing byte that is large enough.
            
            byte[] existing = new byte[]{40};
            byte[] fix = transHeaderFixBytes(existing);
            
            byte[] total = Util.concat(existing, fix);
            int size = Bytes.bytesToIntLE(total, 0);
            
            Assert.assertEquals(40, size);
        }
        
        @Nano
        public static void testTransHeaderFixBytesBelowMin() {
            // One existing byte, 10, below MIN_TRANS_SIZE. Until 2026-10-13, the size
            // became 10, which NodeStream rejects.
            
            byte[] existing = new byte[]{10};
            byte[] fix = transHeaderFixBytes(existing);
            
            byte[] total = Util.concat(existing, fix);
            int size = Bytes.bytesToIntLE(total, 0);
            
            Assert.assertEquals(256 + 10, size);
        }
        
        @Nano
        public static void testTransHeaderFixBytes3() {
            // Test with two existing bytes. Size large enough as is.
            
            byte[] existing = new byte[]{2, 1};
            byte[] fix = transHeaderFixBytes(existing);
            
            byte[] total = Util.concat(existing, fix);
            int size = Bytes.bytesToIntLE(total, 0);
            
            Assert.assertEquals(256 + 2, size);
        }
        
        
        @Nano
        public static void testTransHeaderFixBytes4() {
            // Test with two existing bytes. Size large too small (3).
            
            byte[] existing = new byte[]{3, 0};
            byte[] fix = transHeaderFixBytes(existing);
            
            byte[] total = Util.concat(existing, fix);
            int size = Bytes.bytesToIntLE(total, 0);
            
            Assert.assertEquals(3*1 + 0*256 + 1*(256*256), size);
        }
        
        
        @Nano
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
        
        @Nano
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
        
        @Nano
        public static void testConstantInFileStream() {
            Assert.assertTrue(FileStream.getSmallestFileSize() % META_BLOCK_DISTANCE == 0);
        }
        
        @Nano
        public static void testConstantMetaBlockDistance() {
            // META_BLOCK_DISTANCE cannot be changed without serious stream data
            // compatibility issues.
            
            Assert.assertEquals(200*1000, META_BLOCK_DISTANCE);
        }
        
        @Nano
        public static void testConstantLastByte() {
            // RecoverableStream.LAST_BYTE cannot easily be changed.
            Assert.assertEquals(10, RecoverableStream.LAST_BYTE);
        }
        
        @Nano
        public static void testReadMetaBlock1() {
            MemoryStream mstream = new MemoryStream();
            MetaBlock meta1 = new MetaBlock();
            meta1.setLastTransSpos(1234L);
            RecoverableStream r1 = new RecoverableStream(mstream, meta1);
            
            byte[] bytes = new byte[1000];
            r1.append(bytes, 0, bytes.length, false, 1234L);
            mstream.close();
            
            MetaBlock meta2 = RecoverableStream.readMetaBlock(mstream.copy(), 0);
            
            meta2.checkFormat();
            Assert.assertTrue(meta2.isValid());
            Assert.assertEquals(1234L, meta2.getLastTransSpos());
        }
        
        @Nano
        public static void testReadMetaBlock2() throws IOException {
            // Version 22 should result in VersioningStreamException.
            
            MemoryStream mstream = new MemoryStream();
            MetaBlock meta = new MetaBlock();            
            RecoverableStream r1 = new RecoverableStream(mstream, meta);
            
            byte[] bytes = new byte[1000];
            r1.append(bytes, 0, bytes.length, false, 1234L);
            mstream.close();
            
            MemoryStream m = mstream.copy();
            MemoryStream.TestAccess.write(m, new byte[]{22, 0}, 4);
            
            VersioningStreamException ex = null;
            try {
                RecoverableStream.readMetaBlock(m, 0);
            } catch (VersioningStreamException e) {
                ex = e;
            }
            
            Assert.assertTrue(ex != null);
            Assert.assertTrue(ex.getMessage().contains("22"));
        }
        
        @Nano
        public static void testReadMetaBlock3() throws IOException {
            // Version 154 should work.
            
            MemoryStream mstream = new MemoryStream();
            MetaBlock meta = new MetaBlock();            
            RecoverableStream r1 = new RecoverableStream(mstream, meta);
            
            byte[] bytes = new byte[1000];
            r1.append(bytes, 0, bytes.length, false, 1234L);
            mstream.close();
            
            MemoryStream m = mstream.copy();
            MemoryStream.TestAccess.write(m, new byte[]{(byte) 154, 0}, 4);
            
            RecoverableStream.readMetaBlock(m, 0);
        }
    }
}
