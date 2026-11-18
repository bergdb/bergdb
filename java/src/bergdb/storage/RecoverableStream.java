package bergdb.storage;

import java.io.IOException;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.SalsaStream;

/**
 * <p>This class adds transactional support to an underlying AppendOnlyStream.
 * An instance of the class can be used to recover a stream that crashed at any point in the stream.
 * Recovery is done without parsing through the whole stream. This is possible because of 
 * the meta block occurring in the stream at predetermined fixed positions.
 * This class throws StreamIoException when there is an error with the underlying AppendOnlyStream,
 * or StreamFormatException when the stream's bytes are not as the format says.
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
     * The least record size that recovery's completion of a torn transaction header gives
     * (transHeaderFixBytes), retained from the 16-byte header format: the start's walk
     * refuses 16 and below (NodeStream.readRecordHeader); recovery's own walk refuses sizes
     * below 5 only. The current record header is 32 bytes; recovery does not parse it.
     */
    public static final int MIN_TRANS_SIZE = 16 + 1;
    
    /** If check enabled, append sizes must be a multiple of this value. */
    public static final int TRANS_ALIGNMENT = 8;
    
    /**
     * The byte that recovery writes at offset 4 of a torn transaction header, which it
     * completes (transHeaderFixBytes): 4, as since 2016. Any value would do: the transaction
     * is failed, and the layer above parses no failed transaction. Until 2026-10-25 (bergdb
     * 005-40) it was StoredTrans.CURRENT_FORMAT_VERSION, which was never the format of a
     * stored transaction, and this package's only reference to bergdb.core.
     */
    static final byte TORN_HEADER_FILLER = 4;
    
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
     * Recovers the stream: reads the last valid meta block, then fills out a meta block and
     * a last transaction that a crash has cut. This method must be called before any data
     * is appended to an existing underlying stream.
     *
     * <p>It reads before it writes (2026-10-25, bergdb 005-40): a stream whose meta blocks
     * it cannot read, as their magic bytes or their version are not this code's (a wrong
     * crypto key, or a stream of another version of BergDB), is refused as it is.</p>
     * 
     * @throws StreamIoException
     * @throws StreamFormatException  among them BadMagicBytes and VersioningStreamException,
     *      thrown before anything is written
     */
    public void recover() {
        // 2026-10-25 (bergdb 005-40): fixMetaBlockIfNeeded() came first. With a wrong crypto
        // key, or none, it filled out a meta block that a crash had cut, through that key,
        // and only then did readLastValidMetaBlock() find the magic bytes wrong; the right key
        // then read garbage in that block, and no start succeeded again. The same for a
        // stream of another version. readLastValidMetaBlock() reads only the meta blocks that
        // are complete in the stream, and the block that the fill makes is invalid, so it
        // finds the same block before the fill as after it.
        MetaBlock lastBlock = readLastValidMetaBlock();
        if (lastBlock == null) {
            throw new StreamFormatException("Could not find *any* valid meta block. "
                    + "At least the very first meta block must be valid in a db stream.");
        }
        checkLastTransSpos(lastBlock);
        
        fixMetaBlockIfNeeded();
        
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
     * Refuses a meta block whose last transaction's position cannot be one: not SposNULL and
     * before the first transaction byte, or not inside the stream (2026-11-06, bergdb 019-34).
     * Since bergdb 019-40 the invariant itself: a valid meta block names a transaction written
     * before it, and a cut never removes the one that the last valid block names
     * (getPosOfTransCompletedBefore()); so the position is from the first transaction byte
     * and the stream's first position up to the block.
     * This layer does not require aligned records (TRANS_ALIGNMENT is the caller's check), so
     * an unaligned position is taken. Before, a position past the stream's end made
     * fixLastTransactionIfNeeded throw an IllegalArgumentException. Called before recovery
     * writes anything.
     * 
     * @throws StreamFormatException
     */
    private void checkLastTransSpos(MetaBlock block) {
        final long spos = block.getLastTransSpos();
        if (spos == Constants.SposNULL) {
            return;
        }
        if (spos < Math.max(META_BLOCK_SIZE, aos.getFirstPos()) || spos >= block.getPos()) {
            throw new StreamFormatException("The meta block at " + block.getPos()
                    + " names the last transaction at " + spos + ", which cannot be one in a "
                    + "stream from " + aos.getFirstPos() + ": not before the block.");
        }
    }
    
    /**
     * Whether the stream holds a creation that did not complete, and no committed
     * transaction (2026-10-25, bergdb 005-33). A crash, as a power loss, while a database is
     * created can leave a part of its first meta block, the block, or the block and a part of
     * its first transaction; recovery's zero fill, before this check, made the last one the
     * whole creation with that transaction failed. That is: the stream is not empty and no
     * longer than 'creationLength'; its bytes begin as a meta block of this version as far
     * as they go, and a complete block is valid and names no transaction; and the
     * transaction after the block, if begun, is cut by the end of the stream, or failed (its
     * last byte 0) and ends the stream. A longer stream is not one, whatever its first
     * transaction's size says: it may hold data. This method only reads. Caller must hold
     * DB.writeLock.
     *
     * @param creationLength  The length of a new database's stream: the first meta block
     *      and the first transaction.
     * @throws StreamIoException
     */
    public boolean isIncompleteCreation(long creationLength) {
        final long length = aos.getLength();
        if (length == 0 || length > creationLength || aos.getFirstPos() > 0) {
            return false;
        }
        
        byte[] block = new byte[(int) Math.min(length, META_BLOCK_SIZE)];
        readRaw(0, block);
        if (!MetaBlock.beginsAsBlock(block)) {
            return false;   // Not a BergDB stream, a wrong crypto key, or another version.
        }
        if (length < META_BLOCK_SIZE) {
            return true;
        }
        MetaBlock first = new MetaBlock(block, 0);
        if (!first.isValid() || first.getLastTransSpos() != Constants.SposNULL) {
            return false;
        }
        
        final long transBytes = length - META_BLOCK_SIZE;
        if (transBytes < 4) {
            return true;    // No transaction, or a part of its size.
        }
        byte[] sizeBytes = new byte[4];
        readRaw(META_BLOCK_SIZE, sizeBytes);
        int transSize = Bytes.bytesToIntLE(sizeBytes, 0);
        if (transBytes != transSize) {
            return transBytes < transSize;      // Cut; else more bytes follow it.
        }
        byte[] lastByte = new byte[1];
        readRaw(length - 1, lastByte);
        return lastByte[0] == 0;
    }
    
    /** Reads bytes of the underlying stream, meta blocks included. */
    private void readRaw(long pos, byte[] buffer) {
        try {
            aos.read(pos, buffer, 0, buffer.length);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
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
        fixBytes[fixBytes.length - 1] = TORN_HEADER_FILLER;
        
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
     * The byte at offset + size - 1 must equal LAST_BYTE.
     * The first 4 bytes at offset must be the total byte size of the transaction;
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
            
            int transactionSize = Bytes.bytesToIntLE(buffer, offset);
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
     * Returns the position of a transaction to read the stream from, in order, to reach
     * stream position 'spos': the one named by the last valid meta block at or before
     * 'spos', which is the last transaction completely written before that meta block,
     * so before 'spos'. In general it is not the last one completed before 'spos': those
     * written between the meta block and 'spos' come after it. If the meta block names
     * none, the first transaction of the stream is returned, committed or not (the
     * iterators skip one that is not), or Spos.NULL if the stream has none.
     * 
     * In a stream whose front is cut (pretruncate), the meta block can name a transaction
     * that starts before the first position, and an 'spos' before the first meta block
     * after that position has no meta block at or before it. Then the result is the
     * transaction named by the next valid meta block that names one at or after the first
     * position. It can come after 'spos', and the transactions between the first position
     * and it are not found. Caller must hold DB.writeLock.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException  if no valid meta block names a transaction at or after
     *      the first position. A stream is not cut after the transaction its last valid meta
     *      block names (Reclaim).
     */
    public long getPosOfTransCompletedBefore(long spos) {
        // 2026-10-25 (bergdb 005-39): the Javadoc promised "the last valid transaction that
        // was completely written before stream position 'spos'", which was never searched
        // for, as a TODO here said. In a cut stream, an 'spos' before the first meta block
        // after the cut gave NullPointerException, and one after it could give a transaction
        // that starts before the cut, which cannot be read. Now the meta blocks after it are
        // searched for one that names a transaction after the cut.
        
        final long firstPos = aos.getFirstPos();
        MetaBlock meta = readAValidMetaBlock(aos, spos);
        long blockPos = meta != null ? meta.getPos()
                : (firstPos + META_BLOCK_DISTANCE - 1) / META_BLOCK_DISTANCE * META_BLOCK_DISTANCE;
        
        for (; blockPos + META_BLOCK_SIZE <= aos.getLength(); blockPos += META_BLOCK_DISTANCE) {
            meta = readMetaBlock(aos, blockPos);
            if (!meta.isValid()) {
                continue;
            }
            meta.checkFormat();
            long result = meta.getLastTransSpos();
            if (result == Constants.SposNULL) {
                if (aos.getLength() <= RecoverableStream.META_BLOCK_SIZE) {
                    return Constants.SposNULL;
                }
                result = RecoverableStream.META_BLOCK_SIZE;     // spos of very first transaction
            }
            if (result >= firstPos) {
                return result;
            }
        }
        
        throw new StreamFormatException("No valid meta block names a transaction at or after "
                + "the first position of the stream, " + firstPos + ".");
    }
    
    /**
     * A record's start at or before 'spos', to walk the records forward from by their sizes
     * (2026-11-12, bergdb 021-27, Q27-1; NodeStream.recordHolding()): the transaction that
     * the last valid meta block at or before 'spos' names, if there is one at or after the
     * first position; otherwise the first record after the first position. That is a
     * record's start: the first record, after meta block 0, in a stream not cut; reclaim
     * cuts at a record's start (Reclaim: pCut is a transaction's nextPos). Unlike
     * getPosOfTransCompletedBefore(), it does not search after 'spos' in a cut stream. A walk
     * from it reads the headers of the records between that meta block and 'spos' and of the
     * one that reaches over the block; more only if meta blocks are not valid. 'spos' must
     * not be in a meta block. Any thread may call it.
     *
     * @throws StreamIoException
     * @throws StreamFormatException  if a meta block is malformed
     */
    public long getRecordStartBefore(long spos) {
        final long firstPos = aos.getFirstPos();
        final long inBlock = firstPos % META_BLOCK_DISTANCE;
        long result = inBlock < META_BLOCK_SIZE ? firstPos - inBlock + META_BLOCK_SIZE : firstPos;
        MetaBlock meta = readAValidMetaBlock(aos, spos);
        if (meta != null) {
            long named = meta.getLastTransSpos();
            if (named != Constants.SposNULL && named >= firstPos) {
                result = named;
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
        byte[] header = new byte[8];
        
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
        
        int version = Bytes.bytesToIntLE(header, 4);    // An int, bergdb 019-01.
        
        if (version != MetaBlock.CURRENT_VERSION) {
            throw new VersioningStreamException(versionRefused(version));
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
     * The message of a VersioningStreamException for a meta block whose version is not
     * MetaBlock.CURRENT_VERSION (bergdb 028-15; 026-12, SF4 (a)): it names the release that
     * wrote an older one, and what a user does.
     */
    static String versionRefused(int version) {
        String s = "Cannot read meta block with version " + version + ". Version supported: "
                + MetaBlock.CURRENT_VERSION + ". ";
        if (version == MetaBlock.VERSION_154) {
            return s + "Version 154 is a database written by BergDB release 2026.5 or earlier, "
                    + "which this release does not open: its format is older than the stable "
                    + "format of release 2026.6 (bergdb 026-12, SF4). To keep its data, make "
                    + "the database again: read it with release 2026.5 and put the data into a "
                    + "new database with this release. The start has written nothing.";
        }
        if (version > MetaBlock.CURRENT_VERSION) {
            return s + "A larger number is a database written by a newer version of BergDB. "
                    + "The start has written nothing.";
        }
        return s + "The stream is damaged, or it was written by a version of BergDB "
                + "before 2015. The start has written nothing.";
    }
    
    /**
     * Iterates through the committed transactions, from the one that
     * getPosOfTransCompletedBefore(spos) gives to the end of the stream: from one
     * completed before 'spos', in general not the last one, or from the first one
     * found if there is none (bergdb 005-39).
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

        /** Checks and writes the supplied slice, even when the prefix looks like a record. */
        @Nano
        public static void testAppendOffset() throws IOException {
            MemoryStream stream = new MemoryStream();
            RecoverableStream r = new RecoverableStream(stream, new MetaBlock());
            int offset = 8;
            int size = 24;
            byte[] buffer = new byte[offset + size + 8];
            Bytes.intToBytesLE(size + 1, buffer, 0);
            Bytes.intToBytesLE(size, buffer, offset);
            buffer[offset + size - 1] = LAST_BYTE;
            r.append(buffer, offset, size, true, -1);
            byte[] stored = new byte[size];
            stream.read(META_BLOCK_SIZE, stored, 0, size);
            Assert.assertArrayEquals(java.util.Arrays.copyOfRange(buffer, offset, offset + size),
                    stored);
            long length = stream.getLength();
            Bytes.intToBytesLE(size, buffer, 0);
            Bytes.intToBytesLE(size + 1, buffer, offset);
            try {
                r.append(buffer, offset, size, true, -1);
                throw new AssertionError("accepted wrong record size at offset");
            } catch (IllegalArgumentException expected) {
                Assert.assertTrue(expected.getMessage(),
                        expected.getMessage().contains("Bad transactionSize"));
            }
            Assert.assertEquals(length, stream.getLength());
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
        
        /**
         * Regression test for bergdb 005-40: a recovery that cannot read the meta blocks, with
         * a wrong crypto key, with none on an encrypted stream, or with one on a stream that is
         * not encrypted, writes nothing, also when a crash has cut the stream at or in a meta
         * block. Until 2026-10-25 it filled out that meta block through the key first, and
         * the right key then read garbage there (at 0, 3 and 5 bytes into the block, its magic
         * bytes or its version), so that no recovery succeeded again.
         */
        @Nano
        public static void testRecoverWithWrongKeyWritesNothing() throws IOException {
            byte[] keyA = new byte[32];
            byte[] keyB = new byte[32];
            java.util.Arrays.fill(keyA, (byte) 1);
            java.util.Arrays.fill(keyB, (byte) 2);
            MemoryStream plain = new MemoryStream();
            long[] starts = appendNamedTransactions(new RecoverableStream(plain, new MetaBlock()), 
                    250);
            MemoryStream encrypted = new MemoryStream();
            new SalsaStream(encrypted, new byte[8], keyA).append(bytesOf(plain), 0, 
                    (int) plain.getLength());
            int complete = 0;           // Those that end before the meta block at 200,000.
            for (long start : starts) {
                complete += getSpos(start, 1000) <= META_BLOCK_DISTANCE ? 1 : 0;
            }
            
            // The stream, the key of the wrong recovery, the key of the right one.
            Object[][] cases = {{encrypted, keyB, keyA}, {encrypted, null, keyA}, 
                    {plain, keyA, null}};
            for (int x : new int[] {0, 3, 5, 50}) {
                for (int c = 0; c < cases.length; c++) {
                    MemoryStream m = ((MemoryStream) cases[c][0]).copy();
                    m.truncate(META_BLOCK_DISTANCE + x);
                    String what = "case " + c + ", cut " + x + " bytes into the meta block";
                    AppendOnlyStream wrong = cases[c][1] == null ? m 
                            : new SalsaStream(m, new byte[8], (byte[]) cases[c][1]);
                    try {
                        new RecoverableStream(wrong, new MetaBlock()).recover();
                        throw new AssertionError(what + ": recovered with the wrong key");
                    } catch (BadMagicBytes e) {
                        // Expected.
                    }
                    Assert.assertEquals(what, META_BLOCK_DISTANCE + x, m.getLength());
                    
                    // The stream as the right key reads it recovers as before the cut.
                    MemoryStream right = new MemoryStream();
                    byte[] bytes = bytesOf(m);
                    if (cases[c][2] != null) {
                        new SalsaStream(m, new byte[8], (byte[]) cases[c][2]).read(0, bytes, 0, 
                                bytes.length);
                    }
                    right.append(bytes, 0, bytes.length);
                    RecoverableStream r = new RecoverableStream(right, new MetaBlock());
                    r.recover();
                    Assert.assertEquals(what, 0, r.readLastValidMetaBlock().getPos());
                    Iterator iter = new Iterator(r, 0);
                    int n = 0;
                    while (iter.next()) {
                        n++;
                    }
                    Assert.assertEquals(what, complete, n);
                }
            }
        }
        
        private static byte[] bytesOf(MemoryStream m) throws IOException {
            byte[] bytes = new byte[(int) m.getLength()];
            m.read(0, bytes, 0, bytes.length);
            return bytes;
        }
        
        /**
         * Regression test for bergdb 005-40: a recovery writes nothing to a stream whose meta
         * blocks are of another version, also when a crash has cut one of them. Until
         * 2026-10-25 it filled out the cut one first.
         */
        @Nano
        public static void testRecoverOtherVersionWritesNothing() throws IOException {
            MemoryStream mstream = new MemoryStream();
            appendNamedTransactions(new RecoverableStream(mstream, new MetaBlock()), 250);
            for (long pos = 0; pos + META_BLOCK_SIZE <= mstream.getLength();
                    pos += META_BLOCK_DISTANCE) {
                MemoryStream.TestAccess.write(mstream, new byte[]{(byte) 156, 0}, pos + 4);
            }
            
            for (int x : new int[] {0, 3, 50}) {
                MemoryStream m = mstream.copy();
                m.truncate(META_BLOCK_DISTANCE + x);
                try {
                    new RecoverableStream(m, new MetaBlock()).recover();
                    throw new AssertionError("recovered, " + x + " bytes into the meta block");
                } catch (VersioningStreamException e) {
                    Assert.assertTrue(e.getMessage(), e.getMessage().contains("156"));
                }
                Assert.assertEquals("cut " + x + " bytes into the meta block",
                        META_BLOCK_DISTANCE + x, m.getLength());
            }
        }
        
        /**
         * Bergdb 005-33: isIncompleteCreation(), which a start checks before recovery. The
         * creation here is the first meta block and a first transaction of 136 bytes, as Db
         * writes. Every cut of it from 1 byte on is one, and so is the whole of it with that
         * transaction failed; the whole of it committed is not, nor an empty or a longer
         * stream, a stream that does not begin as a meta block of this version, a complete
         * block that is invalid or names a transaction, or a first transaction that more bytes
         * follow. The method only reads.
         */
        @Nano
        public static void testIsIncompleteCreation() throws IOException {
            final int creation = META_BLOCK_SIZE + 136;
            MemoryStream created = new MemoryStream();
            new RecoverableStream(created, new MetaBlock()).append(transBytes(136, LAST_BYTE), 0,
                    136, true, -1);
            Assert.assertEquals(creation, created.getLength());
            for (int cut = 0; cut <= creation; cut++) {
                MemoryStream m = created.copy();
                m.truncate(cut);
                Assert.assertEquals("cut at " + cut, cut > 0 && cut < creation,
                        isIncompleteCreation(m, creation));
            }
            
            MemoryStream failed = created.copy();
            MemoryStream.TestAccess.write(failed, new byte[] {0}, creation - 1);
            Assert.assertTrue("failed", isIncompleteCreation(failed, creation));
            
            // Longer than a creation: a transaction after it, committed or not; a first
            // transaction cut after the creation's length, whatever its size says.
            for (MemoryStream m : new MemoryStream[] {created.copy(), failed.copy()}) {
                new RecoverableStream(m, new MetaBlock()).append(transBytes(24, LAST_BYTE), 0,
                        24, true, -1);
                Assert.assertFalse("longer", isIncompleteCreation(m, creation));
            }
            MemoryStream large = new MemoryStream();
            new RecoverableStream(large, new MetaBlock()).append(transBytes(1000, LAST_BYTE), 0,
                    300 - META_BLOCK_SIZE, false, -1);
            Assert.assertFalse("cut at 300", isIncompleteCreation(large, creation));
            large.truncate(200);
            Assert.assertTrue("cut at 200", isIncompleteCreation(large, creation));
            
            // Not the beginning of a meta block of this version.
            for (int n : new int[] {1, 100, META_BLOCK_SIZE, creation}) {
                MemoryStream zeros = new MemoryStream();
                zeros.append(new byte[n], 0, n);
                Assert.assertFalse(n + " zero bytes", isIncompleteCreation(zeros, creation));
            }
            MemoryStream version = created.copy();
            MemoryStream.TestAccess.write(version, new byte[] {(byte) 154}, 4);
            version.truncate(10);
            Assert.assertFalse("version 154", isIncompleteCreation(version, creation));
            version.truncate(4);
            Assert.assertTrue("the magic bytes only", isIncompleteCreation(version, creation));
            for (int offset : new int[] {6, 7}) {     // Bergdb 019-01: the version is an int.
                MemoryStream high = created.copy();
                MemoryStream.TestAccess.write(high, new byte[] {1}, offset);
                high.truncate(10);
                Assert.assertFalse("byte " + offset + " of the version",
                        isIncompleteCreation(high, creation));
            }
            
            // A complete block that is invalid, or that names a transaction.
            MemoryStream invalid = created.copy();
            MemoryStream.TestAccess.write(invalid, new byte[] {0}, META_BLOCK_SIZE - 1);
            invalid.truncate(200);
            Assert.assertFalse("invalid block", isIncompleteCreation(invalid, creation));
            MemoryStream names = created.copy();
            byte[] pos = new byte[8];
            Bytes.longToBytesLE(META_BLOCK_SIZE, pos, 0);
            MemoryStream.TestAccess.write(names, pos, 16);
            names.truncate(200);
            Assert.assertFalse("a block that names a transaction",
                    isIncompleteCreation(names, creation));
            
            // A short first transaction, committed or failed, with more bytes after it.
            for (byte last : new byte[] {LAST_BYTE, 0}) {
                MemoryStream m = new MemoryStream();
                RecoverableStream r = new RecoverableStream(m, new MetaBlock());
                r.append(transBytes(24, last), 0, 24, false, -1);
                r.append(transBytes(100, LAST_BYTE), 0, 50, false, -1);
                Assert.assertFalse("last byte " + last, isIncompleteCreation(m, creation));
            }
        }
        
        /** The bytes of a transaction of 'size' bytes: its size, zeros, and its last byte. */
        private static byte[] transBytes(int size, byte last) {
            byte[] bytes = new byte[size];
            Bytes.intToBytesLE(size, bytes, 0);
            bytes[size - 1] = last;
            return bytes;
        }
        
        /** isIncompleteCreation() on the stream m, which it must leave as it was. */
        private static boolean isIncompleteCreation(MemoryStream m, long creationLength)
                throws IOException {
            byte[] before = bytesOf(m);
            boolean result = new RecoverableStream(m, new MetaBlock())
                    .isIncompleteCreation(creationLength);
            Assert.assertArrayEquals("unchanged", before, bytesOf(m));
            return result;
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
        
        /**
         * getPosOfTransCompletedBefore() gives the transaction named by the last valid meta
         * block at or before the position, which is in general not the last one completed
         * before it (bergdb 005-39; until 2026-10-25, its Javadoc said it was).
         */
        @Nano
        public static void testPosOfTransCompletedBefore() {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r = new RecoverableStream(mstream, new MetaBlock());
            long[] starts = appendNamedTransactions(r, 1300);
            
            for (long spos = 0; spos < mstream.getLength(); spos += 997) {
                long blockPos = spos / META_BLOCK_DISTANCE * META_BLOCK_DISTANCE;
                long expected = META_BLOCK_SIZE;    // The first, if the meta block names none.
                for (long start : starts) {
                    if (getSpos(start, 1000) < blockPos) {
                        expected = start;
                    }
                }
                Assert.assertEquals("spos " + spos, expected, r.getPosOfTransCompletedBefore(spos));
            }
            
            // 199 transactions after it were completed before 399,000, the last at 397,256.
            Assert.assertEquals(198128, r.getPosOfTransCompletedBefore(399000));
        }
        
        /**
         * In a stream whose front is cut, the meta blocks up to the first one after the cut
         * name a transaction before it. Until 2026-10-25 (bergdb 005-39), a position before
         * that meta block gave NullPointerException, and one in the META_BLOCK_DISTANCE bytes
         * after it gave a transaction that cannot be read.
         */
        @Nano
        public static void testPosOfTransCompletedBeforeAfterCut() {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r = new RecoverableStream(mstream, new MetaBlock());
            long[] starts = appendNamedTransactions(r, 1300);
            mstream.pretruncate(5 * META_BLOCK_DISTANCE);     // At one of its 1 MB arrays.
            Assert.assertEquals(5 * META_BLOCK_DISTANCE, mstream.getFirstPos());
            
            // The one the meta block at 1,200,000 names, as before the cut.
            long first = r.getPosOfTransCompletedBefore(6 * META_BLOCK_DISTANCE);
            Assert.assertTrue("" + first, first >= 5 * META_BLOCK_DISTANCE
                    && getSpos(first, 1000) < 6 * META_BLOCK_DISTANCE);
            long[] before = {0, 500, 5 * META_BLOCK_DISTANCE, 5 * META_BLOCK_DISTANCE + 50000,
                    6 * META_BLOCK_DISTANCE - 1};
            for (long spos : before) {
                Assert.assertEquals("spos " + spos, first, r.getPosOfTransCompletedBefore(spos));
            }
            
            Iterator iter = new Iterator(r, 0);
            int count = 0;
            while (iter.next()) {
                count++;
            }
            int expected = 0;
            for (long start : starts) {
                expected += start >= first ? 1 : 0;
            }
            Assert.assertEquals(expected, count);
            
            // Cut after the transaction its last meta block names: none can be found.
            MemoryStream mstream2 = new MemoryStream();
            RecoverableStream r2 = new RecoverableStream(mstream2, new MetaBlock());
            appendNamedTransactions(r2, 1100);
            mstream2.pretruncate(5 * META_BLOCK_DISTANCE);
            for (long spos : new long[] {0, 5 * META_BLOCK_DISTANCE + 50000}) {
                try {
                    r2.getPosOfTransCompletedBefore(spos);
                    throw new AssertionError("taken, spos " + spos);
                } catch (StreamFormatException e) {
                    // Expected.
                }
            }
        }
        
        /**
         * Appends 'count' committed transactions of 1000 bytes, each named by the meta
         * blocks after it, as NodeStream.appendNodes() does; returns their positions.
         */
        private static long[] appendNamedTransactions(RecoverableStream r, int count) {
            byte[] transBytes = new byte[1000];
            Bytes.intToBytesLE(transBytes.length, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            long[] result = new long[count];
            for (int i = 0; i < count; i++) {
                result[i] = r.getNextSpos();
                r.append(transBytes, 0, transBytes.length, true, -1);
                r.getMetaBlock().setLastTransSpos(result[i]);
            }
            return result;
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
            // Version 155 should work (154 until bergdb 028-15).
            
            MemoryStream mstream = new MemoryStream();
            MetaBlock meta = new MetaBlock();            
            RecoverableStream r1 = new RecoverableStream(mstream, meta);
            
            byte[] bytes = new byte[1000];
            r1.append(bytes, 0, bytes.length, false, 1234L);
            mstream.close();
            
            MemoryStream m = mstream.copy();
            MemoryStream.TestAccess.write(m, new byte[]{(byte) 155, 0}, 4);
            
            RecoverableStream.readMetaBlock(m, 0);
        }
        
        /**
         * Bergdb 028-15 (026-12, SF4 (a)): a meta block of version 154, as every release until
         * 2026.5 wrote, is refused with a message that names release 2026.5 and what a user
         * does; a newer version with one that says so.
         */
        @Nano
        public static void testReadMetaBlockVersion154Refused() throws IOException {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            byte[] bytes = new byte[1000];
            r1.append(bytes, 0, bytes.length, false, 1234L);
            mstream.close();
            
            for (int version : new int[] {154, 156}) {
                MemoryStream m = mstream.copy();
                MemoryStream.TestAccess.write(m, new byte[]{(byte) version, 0}, 4);
                try {
                    RecoverableStream.readMetaBlock(m, 0);
                    throw new AssertionError("version " + version + " read");
                } catch (VersioningStreamException e) {
                    String s = e.getMessage();
                    Assert.assertTrue(s, s.contains("version " + version));
                    Assert.assertTrue(s, s.contains(version == 154 ? "release 2026.5" : "newer"));
                }
            }
        }
    }
}
