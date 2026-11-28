package bergdb.storage;

import java.io.EOFException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.function.LongSupplier;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.ReadBelowFirstPosException;

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
 * Each meta block holds its own stream position and the database ID (bergdb 028-67, C3): a
 * block that holds another position than the one it is read at, or another ID than the
 * stream's first valid block, is not valid, as a block that a crash cut is not.
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
     * The least record size that recovery's completion of a size field that the end of the
     * stream cuts gives (transHeaderFixBytes): 48 since 2026-11-28, the least record that the
     * Core writes (StoredTrans.MIN_RECORD_SIZE), so that every size that the completion
     * writes is one that the Core's check takes at a later start (RecordCheck.tornHeaderFits;
     * bergdb 028-67, T1); 17 until then, retained from the 16-byte header format. The start's
     * walk refuses 16 and below (NodeStream.readRecordHeader); recovery's own walk refuses
     * sizes below 5 only. The current record header is 32 bytes; recovery does not parse
     * it, but checks it through the layer above's RecordCheck before it fills (bergdb 028-67).
     */
    public static final int MIN_TRANS_SIZE = 48;
    
    /** If check enabled, append sizes must be a multiple of this value. */
    public static final int TRANS_ALIGNMENT = 8;
    
    private static final byte[] zeros = new byte[10*1000];
    private static final int MAX_TRANS_SIZE = Integer.MAX_VALUE;
    public static final byte LAST_BYTE = 10;    
    private final Hold aos;
        // The storage, with the recovery's writes held in memory until writeRecovery()
        // (bergdb 028-70): every read, append and length of this class goes through it.
    private final MetaBlock metaBlock;
    private long posOfLastValidMetaBlock;
    private long lastTransSposOfLastValidMetaBlock = -1;
        // The transaction that recovery starts from (2026-10-13).
    private volatile byte[] streamId;
        // The database ID of the stream's first meta block, set by recover() (bergdb 028-67).
    private long zerosFrom = -1;
    private long zerosTo = -1;
        // The walk's last range of record bytes found zero (zerosAfterBlock(); bergdb 028-79).
    
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
        
        this.aos = new Hold(aos);
        this.metaBlock = metaBlock;
        this.posOfLastValidMetaBlock = -1;   // inited later
    }
    
    /**
     * As recover(RecordCheck) with no check of the records' headers: this layer's own
     * checks only, the records' sizes and last bytes.
     *
     * @throws StreamIoException
     * @throws StreamFormatException  among them BadMagicBytes, VersioningStreamException and
     *      BadTailException, thrown before anything is written
     */
    public void recover() {
        recover(null);
    }

    /**
     * Recovers the stream: reads the last valid meta block, then fills out a meta block and
     * a last transaction that a crash has cut. This method must be called before any data
     * is appended to an existing underlying stream.
     *
     * <p>It reads before it writes (2026-10-25, bergdb 005-40): a stream whose meta blocks
     * it cannot read, as their magic bytes or their version are not this code's (a stream
     * that an earlier release encrypted, or a stream of another version of BergDB), is
     * refused as it is.</p>
     *
     * <p>A tail of zeros within the stream's length, as a kill of the process during an
     * append can leave (bergdb 028-60; 031-02, F1), is a cut tail where its zeros begin
     * inside the last record: that record's size, read before them, says how far it reaches,
     * and the record is completed as an aborted one, its zeros not read; blocks of zeros among
     * them are not valid (readMetaBlock()). Zeros that cover a whole size field at a
     * record's start, where they begin or past the end of the record they begin in, give the
     * size 0 there, refused: "Bad transaction size in db stream, 0, spos P" (Database's
     * Javadoc says how to start). A meta block that the end of the stream cuts was completed
     * before the sizes were read, so the refusal could append its missing bytes, until
     * bergdb 028-67 (below). A size field that the end cuts (1 to 3 zero bytes) is completed
     * as a torn record's is, and that record recovered as an aborted one. Zeros that begin
     * inside the header of the last record, which the end cuts, are taken as its bytes not
     * written, as the zeros of the recovery's own completion are (walkTail(), since 2026-11-28,
     * bergdb 028-67, T1).</p>
     * 
     * <p>Since 2026-11-27 (bergdb 028-67, C1 and C3): a meta block is valid only if it holds
     * the position it is read at and the database ID of the stream's first valid block
     * (readLastValidMetaBlock()); a block of another place or database, as an older stream
     * file's bytes at the same offsets in a new file leave it, or of other bytes, is passed
     * over as a block of zeros is. Before it writes anything, the recovery walks the records
     * from the one that the last valid block names to the end, reading only (walkTail()):
     * each record's size and last byte, and with 'check', the layer above's, each record's
     * header, so that it completes a torn last record with zeros only after its header is
     * found to be one, or the begin of one followed by zeros (a partial append, or a part of
     * an earlier start's completion of one). A tail that is not the stream's own records,
     * zeros past a record's end or other bytes, is refused with a BadTailException that names
     * P, the end of the last record that is one, and the way out, a cut of the stream at P: a
     * size from such bytes no longer makes the recovery append up to 2 GB of zeros first.</p>
     *
     * <p>Since 2026-11-27 (Frans; bergdb 028-66): before the walk, the bytes that the storage
     * holds before its first position and deletes at the next cut, FileStream's files before
     * a gap, are checked (checkLeftovers()): each piece's first meta block must be this
     * database's, by 028-67's check, else the start is refused, before anything is written
     * or deleted.</p>
     *
     * @param check  The layer above's check of a record's header, or null.
     * @throws StreamIoException  among them one whose cause is the storage's refusal of the
     *      bytes before its first position (checkLeftovers()), thrown before anything is
     *      written
     * @throws StreamFormatException  among them BadMagicBytes, VersioningStreamException and
     *      BadTailException, thrown before anything is written
     */
    public void recover(RecordCheck check) {
        recover(check, false);
    }

    /**
     * As recover(RecordCheck), and with 'hold' the recovery's writes, the completion of a
     * meta block and of a torn last record, are held in memory, not written (2026-11-28,
     * bergdb 028-70): until writeRecovery(), or the next append, which writes them first,
     * the storage is as it was before the call, and this stream's reads and length are those
     * of the stream with the writes made. A database's start holds them until it has made
     * its last check of what it reads (Db.startInner), so that a start refused by any check,
     * of a record, of the section, of the startup distance or of reclaim's state, has written
     * nothing; until then the start refused after the recovery had written. The bytes written
     * are those that recover() without 'hold' writes, in the same order.
     *
     * @throws StreamIoException
     * @throws StreamFormatException  as recover(RecordCheck)
     */
    public void recover(RecordCheck check, boolean hold) {
        // 2026-10-25 (bergdb 005-40): fixMetaBlockIfNeeded() came first. With a wrong crypto
        // key, or none, it filled out a meta block that a crash had cut, through that key,
        // and only then did readLastValidMetaBlock() find the magic bytes wrong; the right key
        // then read garbage in that block, and no start succeeded again. The same for a
        // stream of another version. readLastValidMetaBlock() reads only the meta blocks that
        // are complete in the stream, and the block that the fill makes is invalid, so it
        // finds the same block before the fill as after it.
        MetaBlock lastBlock = readLastValidMetaBlock();
        if (lastBlock == null) {
            final long first = aos.getFirstPos();
            throw new StreamFormatException("Could not find *any* valid meta block. "
                    + "At least the very first meta block must be valid in a db stream."
                    + (first == 0 ? "" : " The stream begins at " + first + ", and the bytes"
                    + " before it are not there: it may lack bytes that the database needs"
                    + " (bergdb 028-66). The start has written nothing." + frontAccount()));
        }
        checkLastTransSpos(lastBlock);
        final byte[] id = lastBlock.getId();
        checkLeftovers(id);
        
        long spos;
        if (lastBlock.getLastTransSpos() == Constants.SposNULL) {
            spos = RecoverableStream.META_BLOCK_SIZE;
        } else {
            spos = lastBlock.getLastTransSpos();
        }
        
        // 2026-11-27 (bergdb 028-67, C1): the walk reads before anything is written; until
        // then fixMetaBlockIfNeeded() came first, and the walk zero-filled a size read from
        // any bytes, up to 2 GB, before a later check refused the stream.
        final long torn = walkTail(spos, check, lastBlock);

        aos.holding = hold;     // bergdb 028-70
        try {
            complete(lastBlock, id, torn);
        } finally {
            aos.holding = false;
        }
    }

    /**
     * recover()'s writes, after its walk: the meta block that the end of the stream cuts, and
     * the torn record at 'torn', if 0 or more; and the meta block in memory set from
     * 'lastBlock', the last valid one, of the stream's ID 'id'.
     */
    private void complete(MetaBlock lastBlock, byte[] id, long torn) {
        fixMetaBlockIfNeeded();

        metaBlock.setFromOtherMetaBlock(lastBlock);
        streamId = id;

        if (torn >= 0) {
            fixLastTransactionIfNeeded(torn);
        }
    }

    /**
     * Writes the recovery's writes that recover(RecordCheck, true) holds, if any, to the
     * storage, in the order made (bergdb 028-70); else returns. The caller must hold
     * DB.writeLock.
     *
     * @throws StreamIoException
     */
    public void writeRecovery() {
        try {
            aos.writeHeld();
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
    }

    /**
     * The storage as this class reads and appends it (bergdb 028-70): 'storage', and the
     * bytes appended while 'holding', which recover() sets for its writes when asked to hold
     * them. Those bytes are kept in memory, a run of zeros as its length only, at the end of
     * the stream, after the storage's bytes: getLength() and read() give the stream with them,
     * and writeHeld(), or the first append after 'holding', appends them to the storage.
     * Nothing is held but during a start, under the write lock, before any reader (the
     * fields are set only then); after it, every call passes on to the storage. 'pieces' is
     * volatile, so that a reader that comes later sees it null, as the interface asks of
     * the writer's changes (AppendOnlyStream, "CONCURRENCY").
     */
    private static final class Hold implements AppendOnlyStream {
        private final AppendOnlyStream storage;
        boolean holding;
        /** The pieces held, in order: each's offset from 'base', length and bytes. */
        private volatile ArrayList<long[]> pieces;     // null when nothing is held
        private ArrayList<byte[]> bytes;       // a piece's bytes, or null for zeros
        private long base;                     // the storage's length when held began
        private long held;                     // the bytes held

        Hold(AppendOnlyStream storage) {
            this.storage = storage;
        }

        public long getLength() {
            return pieces == null ? storage.getLength() : base + held;
        }

        public long getFirstPos() {
            return storage.getFirstPos();
        }

        public void read(long position, byte[] dest, int destOffset, int length)
                throws IOException {
            if (pieces == null || position + length <= base) {
                storage.read(position, dest, destOffset, length);
                return;
            }
            if (destOffset < 0 || length < 0 || destOffset + length > dest.length) {
                throw new IllegalArgumentException("destOffset " + destOffset + ", length "
                        + length + ", dest.length " + dest.length);
            }
            if (position < 0 || position + length > base + held) {
                throw new EOFException("Read of " + length + " bytes at " + position
                        + ", the stream's length " + (base + held) + ".");
            }
            final int below = position < base ? (int) (base - position) : 0;
            if (below > 0) {
                storage.read(position, dest, destOffset, below);
            }
            long p = position + below - base;
            int o = destOffset + below;
            int n = length - below;
            int i = pieceAt(p);
            while (n > 0) {
                final long[] piece = pieces.get(i);
                final int k = (int) Math.min(n, piece[0] + piece[1] - p);
                final byte[] b = bytes.get(i);
                if (b == null) {
                    Arrays.fill(dest, o, o + k, (byte) 0);
                } else {
                    System.arraycopy(b, (int) (p - piece[0]), dest, o, k);
                }
                p += k;
                o += k;
                n -= k;
                i++;
            }
        }

        /** The index of the piece that holds offset 'p' from 'base', 0 <= p < held. */
        private int pieceAt(long p) {
            int lo = 0;
            int hi = pieces.size() - 1;
            while (lo < hi) {
                final int mid = (lo + hi + 1) >>> 1;
                if (pieces.get(mid)[0] <= p) {
                    lo = mid;
                } else {
                    hi = mid - 1;
                }
            }
            return lo;
        }

        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            if (!holding) {
                writeHeld();
                storage.append(source, sourceOffset, length);
                return;
            }
            if (sourceOffset < 0 || length < 0 || sourceOffset + length > source.length) {
                throw new IllegalArgumentException("sourceOffset " + sourceOffset + ", length "
                        + length + ", source.length " + source.length);
            }
            if (pieces == null) {
                bytes = new ArrayList<byte[]>();
                base = storage.getLength();
                held = 0;
                pieces = new ArrayList<long[]>();
            }
            if (length == 0) {
                return;
            }
            boolean zero = true;
            for (int i = sourceOffset; i < sourceOffset + length && zero; i++) {
                zero = source[i] == 0;
            }
            final int last = pieces.size() - 1;
            if (zero && last >= 0 && bytes.get(last) == null) {
                pieces.get(last)[1] += length;
            } else {
                pieces.add(new long[] {held, length});
                bytes.add(zero ? null : Arrays.copyOfRange(source, sourceOffset,
                        sourceOffset + length));
            }
            held += length;
        }

        /** Appends the bytes held to the storage, in order, and holds nothing after it. */
        void writeHeld() throws IOException {
            final ArrayList<long[]> p = pieces;
            if (p == null) {
                return;
            }
            final ArrayList<byte[]> b = bytes;
            pieces = null;      // none is written twice if an append throws
            bytes = null;
            assert storage.getLength() == base : storage.getLength() + ", " + base;
            for (int i = 0; i < p.size(); i++) {
                long n = p.get(i)[1];
                if (b.get(i) != null) {
                    storage.append(b.get(i), 0, (int) n);
                }
                while (b.get(i) == null && n > 0) {
                    final int k = (int) Math.min(n, zeros.length);
                    storage.append(zeros, 0, k);
                    n -= k;
                }
            }
        }

        public void pretruncate(long position) throws IOException {
            storage.pretruncate(position);
        }

        public void checkLeftovers(LeftoverCheck check) throws IOException {
            storage.checkLeftovers(check);
        }

        public void close() throws IOException {
            storage.close();
        }
    }

    /**
     * The layer above's check of a record, which recover(RecordCheck) uses before it writes
     * (bergdb 028-67, C1): this layer knows a record's size field and last byte only. The
     * Core's is StoredTrans.RECORD_CHECK.
     */
    public interface RecordCheck {
        /** The size of a record's header: the bytes at its start that headerChecks() reads. */
        int headerSize();

        /**
         * Whether 'header', the first headerSize() bytes of the record at 'pos', is the header
         * of a record that the database of ID 'id' wrote at 'pos'.
         */
        boolean headerChecks(long pos, byte[] header, byte[] id);

        /**
         * Whether 'bytes', the first 'length' bytes of the record at 'pos', 1 or more and
         * fewer than headerSize(), after which the record holds zeros only to the end of the
         * stream, which cuts it, can begin a record's header, as far as they go. Every size
         * that transHeaderFixBytes() completes from bytes that fit must fit (since 2026-11-28,
         * bergdb 028-67, T1): a later start can find the completion cut again.
         */
        boolean tornHeaderFits(long pos, byte[] bytes, int length);

        /**
         * Throws a VersioningStreamException if 'header', the first headerSize() bytes of a
         * committed record at 'pos', or fewer if the record is shorter, is of another record
         * format than the layer above reads; else returns.
         */
        void checkFormat(long pos, byte[] header);

        /**
         * null if 'record', the whole committed record at 'pos', is a record of the database of
         * ID 'id' at 'pos', as a start parses it; else what is wrong.
         */
        String recordProblem(long pos, byte[] record, byte[] id);
    }

    /**
     * Walks the records from 'start', the record that the last valid meta block names, to
     * the end of the stream, reading only (bergdb 028-67, C1), and returns the position of
     * the record that the end of the stream cuts, which recover() completes, or -1 if the
     * last record ends at the end. Each record's size must be 5 or more, and a whole record's
     * last byte 0 or LAST_BYTE. With 'check', also each record's header, 'id' the stream's
     * database ID: a committed record's header must check; so must the header of the record
     * that the end cuts, before recover() fills it, or be the begin of one as far as the
     * stream holds bytes of it that are not zero (tornRecordIsOwn()); an aborted record's
     * that does not check, as the recovery of a record that a crash cut in its header leaves
     * it, is walked over, not taken as one. The first record, if committed, is
     * refused first for another record format (check.checkFormat()), as a start refused it
     * before (bergdb 005-40): a valid block names a record that this database wrote. Since
     * 2026-11-28 (bergdb 028-70) so is every later committed record whose header holds its
     * check, as a record of a newer release would.
     *
     * <p>Since 2026-11-28 (bergdb 028-79; 033's review of the start, F2), with or without
     * 'check', each meta block position after 'last', the last valid block, in a record whose
     * content the walk does not read, the record that the end of the stream cuts and an
     * aborted one, or right after the end of a whole record, must hold this database's
     * bytes as far as the stream holds them (foreignBlock()): zeros, or the begin of the
     * block that this database writes there followed by zeros, as recovery's fill and its
     * completion of a cut block are. Other bytes there, as a kill can leave another file's
     * in the last file, are refused: in such a record with P before it; after a whole record
     * that ends at the block's position with P there, not 128 bytes after it. Before, the
     * walk took a cut record without reading its content, and the cut at P kept the block:
     * such bytes stayed in the stream, and a later start refused the stream when reclaim's
     * cut had made their file the first, as readFirstMetaBlock() and leftoverProblem() read a
     * file's first block. A block inside a whole committed record is not read: the record is
     * the database's, parsed where another file's bytes can begin in it.</p>
     *
     * @param last  The last valid meta block: its position, its database ID, which the
     *      records' headers must hold, and the bytes of this database's blocks.
     * @throws BadTailException  for a tail that is not the stream's records, with P, the end of
     *      the last record found to be one; or that record's start, if it is a committed
     *      record that does not parse (check.recordProblem()), as when the tail's other bytes
     *      begin inside it; so also for the stream's last record, if committed, which is
     *      parsed whole for that (it is read twice at a start: the start parses it again);
     *      or the position of a meta block of other bytes after a whole record that ends there
     * @throws VersioningStreamException  as check.checkFormat() throws it
     * @throws StreamIoException
     */
    private long walkTail(final long start, RecordCheck check, MetaBlock last) {
        final byte[] id = last.getId();
        final long length = aos.getLength();
        final int headerSize = check == null ? 4 : check.headerSize();
        long spos = start;
        long verified = start;      // P: the end of the last record found to be one
        long committed = -1;        // the committed record that ends at 'verified', if any
        int committedSize = 0;
        zerosFrom = -1;
        zerosTo = -1;

        while (true) {
            // The end is at or in the meta block after a record's end (spos >= length), or
            // at a record's end.
            final long remaining = spos >= length ? 0 : getRemainingTransBytes(spos, length);
            if (remaining == 0) {
                // The last record, if committed, is parsed whole: the tail's other bytes can
                // begin inside it, after its header, and no record after it is there to be
                // refused; until 028-67 a start refused such a record after its recovery.
                if (check != null && committed >= 0 && verified == spos) {
                    final String problem = recordProblem(check, committed, committedSize, id);
                    if (problem != null) {
                        throw tailRefusal("The record at " + committed + ", the last of the "
                                + "stream, is not one of this database's records: " + problem,
                                committed, length);
                    }
                }
                return -1;
            }
            final byte[] header = new byte[(int) Math.min(remaining, headerSize)];
            read(spos, header, 0, header.length);
            if (remaining < 4) {
                // A torn size field, completed by transHeaderFixBytes().
                if (check != null && !tornRecordIsOwn(check, spos, header, remaining, id)) {
                    throw badTail("The record at " + spos + ", whose size field the end of "
                            + "the stream cuts, begins with a byte that does not begin the "
                            + "size of one of this database's records (bergdb 028-67, C1).",
                            verified, committed, committedSize, check, id, length);
                }
                refuseForeignBlock(spos, length, length, length, last, "the record at "
                        + spos + ", which the end of the stream cuts,", verified, committed,
                        committedSize, check);
                return spos;
            }
            final int size = Bytes.bytesToIntLE(header, 0);
            if (size < (4 + 1)) {
                throw badTail("Bad transaction size in db stream, " + size + ", spos " + spos
                        + ". Stream length: " + length + ".", verified, committed,
                        committedSize, check, id, length);
            }

            if (remaining < size) {
                if (check != null && !tornRecordIsOwn(check, spos, header, remaining, id)) {
                    throw badTail("The record at " + spos + ", of size " + size + ", which the "
                            + "end of the stream cuts, has a header that is not one of this "
                            + "database's records at its place (bergdb 028-67, C3).", verified,
                            committed, committedSize, check, id, length);
                }
                refuseForeignBlock(spos, length, length, length, last, "the record at "
                        + spos + ", of size " + size + ", which the end of the stream cuts,",
                        verified, committed, committedSize, check);
                return spos;
            }

            final long lastPos = getSpos(spos, size - 1);
            final byte[] lastByte = new byte[1];
            read(lastPos, lastByte, 0, 1);
            if (lastByte[0] != 0 && lastByte[0] != LAST_BYTE) {
                throw badTail("Bad lastByte, " + lastByte[0] + ", of the record at " + spos
                        + ", of size " + size + ".", verified, committed, committedSize, check,
                        id, length);
            }
            final long next = getSpos(spos, size);
            final long before = verified;       // P before this record
            final long beforeCommitted = committed;
            final int beforeSize = committedSize;
            if (check == null) {
                verified = next;
            } else {
                if (spos == start && lastByte[0] == LAST_BYTE) {
                    check.checkFormat(spos, header);
                }
                final boolean checks = size >= headerSize && header.length == headerSize
                        && check.headerChecks(spos, header, id);
                if (lastByte[0] == LAST_BYTE) {
                    if (!checks) {
                        throw badTail("The header of the record at " + spos + " is not one of "
                                + "this database's records at its place (bergdb 028-67, C3).",
                                verified, committed, committedSize, check, id, length);
                    }
                    // Another format, under a header that holds its check, as a newer
                    // release's record after this one's, is refused as such (2026-11-28,
                    // bergdb 028-70): before, it was refused after the recovery had written,
                    // or, the last of the stream, as a tail to cut (recordProblem()).
                    check.checkFormat(spos, header);
                    verified = next;
                    committed = spos;
                    committedSize = size;
                } else if (checks) {
                    verified = next;
                    committed = -1;
                }
            }
            // The meta blocks that an aborted record reaches over, after the checks of its
            // header, with P before it (bergdb 028-79): its content is not read. A committed
            // record's is the database's, and parsed where another file's bytes can begin
            // in it (recordProblem()).
            if (lastByte[0] == 0) {
                refuseForeignBlock(spos, lastPos, lastPos + 1, length, last,
                        "the aborted record at " + spos + ", of size " + size + ",", before,
                        beforeCommitted, beforeSize, check);
            }
            // The meta block after a whole record that ends at its position (bergdb 028-79):
            // P is the block's position, the end of the record, if the record is one.
            final long after = lastPos + 1;
            if (after % META_BLOCK_DISTANCE == 0 && after > last.getPos() && after < length) {
                final String problem = foreignBlock(after, length, last, -1);
                if (problem != null) {
                    throw badTail("The meta block at " + after + ", after the record at "
                            + spos + ", which ends there, " + problem + " (bergdb 028-79).",
                            verified == next ? after : verified, committed, committedSize,
                            check, id, length);
                }
            }
            spos = next;
        }
    }

    /**
     * Refuses the record at 'spos', 'what', if a meta block position after the last valid
     * block, 'last', from after 'spos' to before 'to' (the record's last byte, or the end of
     * the stream for a record that it cuts) holds bytes that are not this database's
     * (foreignBlock(); bergdb 028-79): a BadTailException with P before the record, as
     * badTail() gives it for 'verified' and 'committed'. 'end' is the record's end, or the
     * stream's for a record that it cuts.
     */
    private void refuseForeignBlock(long spos, long to, long end, long length, MetaBlock last,
            String what, long verified, long committed, int committedSize, RecordCheck check) {
        long block = Math.max(spos, last.getPos()) / META_BLOCK_DISTANCE * META_BLOCK_DISTANCE
                + META_BLOCK_DISTANCE;
        for (; block < to; block += META_BLOCK_DISTANCE) {
            final String problem = foreignBlock(block, length, last, end);
            if (problem != null) {
                throw badTail("The meta block at " + block + ", in " + what + " " + problem
                        + " (bergdb 028-79).", verified, committed, committedSize, check,
                        last.getId(), length);
            }
        }
    }

    /**
     * null if the meta block at 'pos', after 'last', the last valid block, holds this
     * database's bytes as far as the stream, of 'length' bytes, holds them (2026-11-28, bergdb
     * 028-79): zeros (bergdb 028-60), or the begin of the block that this database writes at
     * 'pos', followed by zeros: of this version, with the bytes of 'last' but the last
     * transaction's position (offsets 16 to 23, any) and its own position, 'pos', at offset 46.
     * Such are the blocks after the last valid one that a stream of this database holds:
     * recovery's fill, the magic bytes and the version (bergdb 005-27), its completion of a
     * block that the end of the stream cut, a block that a crash cut, a block of zeros.
     * Else what the block holds: such as another file's bytes, which a kill can leave in the
     * last file (bergdb 035-02), an older stream file's block of this database, another
     * database's, or a block of another version.
     *
     * <p>The block's first 8 bytes, the magic bytes and the version (since the review of
     * 2026-11-28 of bergdb 028-79): a block that the end of the stream cut after 1 to 7 of its
     * bytes, with zeros after them, as a kill's zeros (bergdb 028-60) on a storage that keeps
     * them leave it, is completed by recovery's fill from the end of the stream
     * (fixMetaBlockIfNeeded()), which writes the rest of the magic bytes and the version
     * after the zeros: such a block, the database's first bytes, a run of zeros and the
     * template's bytes from the run's end, is the database's (until then a start refused it,
     * a sound stream on MemoryStream). A block of the database's first 1 to 4 bytes and
     * zeros to its end, the fill's when the zeros reached past byte 8, is the database's only
     * where the stream ends in it, or where the record's bytes after it are zeros, to 'end',
     * the record's end or the stream's, as the completion of a record writes them, the meta
     * blocks among them passed over (zerosAfterBlock()); 'end' -1 for a block after a whole
     * record, where a refusal after it puts P at the block (badTail()). Until then such a
     * block followed by other bytes in the record was taken, and a later start that read it
     * as its first block refused the stream, as no valid block begins so. Until the second
     * review of bergdb 028-79 (2026-11-28, E) the zeros were checked only to the next block:
     * such a block followed by zeros past it, then other bytes, was taken, and a later start
     * from the block refused the stream in the same way.</p>
     */
    private String foreignBlock(long pos, long length, MetaBlock last, long end) {
        final int n = (int) Math.min(META_BLOCK_SIZE, length - pos);
        final byte[] bytes = new byte[n];
        readRaw(pos, bytes);
        int w = n;      // the bytes up to the last that is not zero
        while (w > 0 && bytes[w - 1] == 0) {
            w--;
        }
        if (w == 0) {
            return null;
        }
        final byte[] own = last.getBlock().clone();
        Bytes.longToBytesLE(pos, own, MetaBlock.POS_OFFSET);
        final int k = Math.min(n, 8);
        int m = 0;      // the bytes of the magic and the version, as far as they go
        while (m < k && bytes[m] == own[m]) {
            m++;
        }
        if (m > 0 && m < k && w <= 8) {
            int e = m;  // the zeros after them
            while (e < k && bytes[e] == 0) {
                e++;
            }
            int t = e;  // the template's bytes after the zeros
            while (t < k && bytes[t] == own[t]) {
                t++;
            }
            if (t == k && (e < k || n < META_BLOCK_SIZE || end < 0
                    || zerosAfterBlock(pos + META_BLOCK_SIZE, end))) {
                return null;
            }
            if (t == k) {
                return "holds the first " + m + " bytes of a meta block and zeros, and bytes "
                        + "that are not zero after it in the record: not a block that the end "
                        + "of the stream cut, which recovery completes with the magic bytes and "
                        + "the version. A kill of the process during an append can leave "
                        + "another file's bytes there";
            }
        }
        int i = 0;
        while (i < w && (bytes[i] == own[i] || (i >= 16 && i < 24))) {
            i++;
        }
        if (i == w) {
            return null;
        }
        final String which;
        if (i < 4) {
            which = "does not begin as a meta block";
        } else if (i < 8) {
            which = n < 8 ? "does not begin as a block of this version"
                    : "is a block of version " + Bytes.bytesToIntLE(bytes, 4);
        } else if (n == META_BLOCK_SIZE && bytes[n - 1] == LAST_BYTE) {
            which = "is a valid block of another place or database: it holds the position "
                    + Bytes.bytesToLongLE(bytes, MetaBlock.POS_OFFSET) + " and the database ID "
                    + StringUtil.toHex(Arrays.copyOfRange(bytes, 24, 40));
        } else {
            which = "is not the block of this database at its place: it differs from it at"
                    + " offset " + i;
        }
        return "holds bytes that are not this database's: it " + which + ". A kill of the "
                + "process during an append can leave another file's bytes there";
    }

    /**
     * Whether the record at 'spos', which the end of the stream cuts after 'remaining' of its
     * record bytes, 'header' the first of them (up to check.headerSize()), is a partial append
     * of this database's records, as a kill leaves it, or the recovery's completion of one
     * (bergdb 028-67, C1; T1, 2026-11-28): its header holds its check; or its bytes up to the last
     * that is not zero, its size field's at least as far as the stream holds it, begin a
     * header as far as they go (check.tornHeaderFits()), and the record's bytes after them to
     * the end of the stream are zeros. Zeros at the end of a cut record are taken as bytes not
     * written: a kill during an append can leave them within the stream's length (bergdb
     * 028-60), and the recovery's completion writes zeros only, but for the missing bytes of
     * a size field that the end cuts (fixLastTransactionIfNeeded()). So every later start
     * takes what a start's completion wrote, whatever part of it the stream holds: after a
     * kill during it, after FileStream's open has left its zeros out (028-60, part 2), or
     * with a meta block that it wrote inside the record. Until 2026-11-28 the walk took a header
     * of 32 bytes only if it held its check, and fewer only if they ended the stream, so it
     * refused all of these when the record's first 32 bytes were in the stream, or when the
     * completion had written its byte 4, the filler 4 (031-06, review 3, T1). The bytes after
     * the header are read, at most to the record's end, only if the header does not hold its
     * check and its bytes before fit.
     */
    private boolean tornRecordIsOwn(RecordCheck check, long spos, byte[] header,
            long remaining, byte[] id) {
        final int headerSize = check.headerSize();
        if (header.length == headerSize && check.headerChecks(spos, header, id)) {
            return true;
        }
        int written = header.length;
        while (written > 4 && header[written - 1] == 0) {
            written--;
        }
        return written < headerSize && check.tornHeaderFits(spos, header, written)
                && (remaining <= headerSize || recordBytesZero(spos, headerSize, remaining));
    }

    /** Whether the record bytes 'from' to 'to' of the record at 'spos' are all zero. */
    private boolean recordBytesZero(long spos, long from, long to) {
        final byte[] buffer = new byte[(int) Math.min(to - from, 64 * 1024)];
        for (long at = from; at < to; at += buffer.length) {
            final int n = (int) Math.min(to - at, buffer.length);
            read(getSpos(spos, at), buffer, 0, n);
            for (int i = 0; i < n; i++) {
                if (buffer[i] != 0) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * The refusal of a tail that is not the stream's own records (bergdb 028-67, C1): 'cause',
     * then P and the way out. P is 'verified', the end of the last record found to be one,
     * or the start of 'committed', the committed record that ends there, if it does not parse
     * (with 'check'): the tail's other bytes can begin inside it, after its header.
     */
    private BadTailException badTail(String cause, long verified, long committed,
            int committedSize, RecordCheck check, byte[] id, long length) {
        long cut = verified;
        if (check != null && committed >= 0) {
            String problem = recordProblem(check, committed, committedSize, id);
            if (problem != null) {
                cut = committed;
                cause += " The record before it, at " + committed + ", is not one either: "
                        + problem;
            }
        }
        // P right after a meta block after the last valid one that a later start could not
        // read as its first (readFirstMetaBlock()), a block of the database's first bytes and
        // zeros: P at the block, so that the cut at P leaves no such block (2026-11-28, the
        // review of bergdb 028-79). The block is no record's.
        final long block = cut - META_BLOCK_SIZE;
        if (cut % META_BLOCK_DISTANCE == META_BLOCK_SIZE && block > posOfLastValidMetaBlock
                && !readableAsFirst(block, length)) {
            cut = block;
        }
        return tailRefusal(cause, cut, length);
    }

    /**
     * Whether the meta block at 'pos', as far as the stream of 'length' bytes holds it, is
     * one that readFirstMetaBlock() passes over or takes: zeros, or the magic bytes and the
     * version as far as they go (bergdb 028-79).
     */
    private boolean readableAsFirst(long pos, long length) {
        final byte[] bytes = new byte[(int) Math.min(META_BLOCK_SIZE, length - pos)];
        readRaw(pos, bytes);
        return isZeros(bytes) || MetaBlock.beginsAsBlock(bytes);
    }

    /**
     * Whether the record bytes from 'from', right after a meta block, to 'to' are zero, the
     * meta blocks among them passed over (2026-11-28, the second review of bergdb 028-79, E):
     * for foreignBlock(), the bytes after a block in a record, to the record's end or the
     * stream's. The blocks among them are refuseForeignBlock()'s, which checks each block of
     * the record after the last valid one on its own (foreignBlock()). Read in pieces of 64
     * KiB, up to the first piece that holds a byte that is not zero; a range found zero is
     * kept for the walk (zerosFrom, zerosTo), so that a later block of the record, whose
     * range lies in it, reads nothing, and a range not zero ends the walk, as the record is
     * then refused. So the walk reads each byte after the last valid block at most once for
     * it, and none of a record before that block: the bytes of the appends after the block,
     * which a kill cut (a write on FileStream is at most 5 MB, bergdb 028-80), not a whole
     * record, which can be many MB.
     */
    private boolean zerosAfterBlock(long from, long to) {
        if (to == zerosTo && from >= zerosFrom) {
            return true;
        }
        if (!recordBytesZero(from, 0, getTransPos(to) - getTransPos(from))) {
            return false;
        }
        zerosFrom = from;
        zerosTo = to;
        return true;
    }

    /** check.recordProblem() for the record of 'size' bytes at 'pos', read whole. */
    private String recordProblem(RecordCheck check, long pos, int size, byte[] id) {
        byte[] record = new byte[size];
        read(pos, record, 0, size);
        return check.recordProblem(pos, record, id);
    }

    /** The BadTailException for 'cause', a tail from 'cut' on, and the way out. */
    private static BadTailException tailRefusal(String cause, long cut, long length) {
        return new BadTailException(cause + " The stream's records end at stream position "
                + cut + ": from there to the stream's end, " + length + ", it holds bytes "
                + "that are not its records. A kill of the process during an append can leave "
                + "such bytes in the last stream file, within its length: zeros, or the bytes "
                + "of a file deleted before, such as an older stream file or another "
                + "database's, as on macOS (APFS; bergdb 028-67, 035-02); so can a storage "
                + "that loses or damages bytes. The start has written nothing. To start the "
                + "database, keep a copy of its files, then cut the stream at " + cut
                + ": cut the stream file that holds it to " + cut + " less the file's first "
                + "position, which is the number in its name times 100,000, and remove the "
                + "later stream files, if any; the stream's bytes from there on are lost.",
                cut);
    }
    
    /**
     * The rule of the files before a gap (Frans, 2026-11-27; bergdb 028-66, with 028-67's C3):
     * the bytes that the storage holds before its first position and deletes at the next cut
     * (AppendOnlyStream.checkLeftovers(), FileStream's files before a gap at its open) are
     * deleted only if each piece's first meta block is this database's: of this version,
     * valid, with its own position and 'id', the database ID of the stream's first block
     * (leftoverProblem()). Otherwise the storage throws, which refuses the start; recover()
     * calls this before anything is written, and the storage deletes nothing before a check
     * that passed. Such a piece is a cut's leftover after a power loss (FileStream, "A gap in
     * the files"), or a file put there by hand: another database's, a file of another version
     * or a damaged one is refused, and an older copy of this database's file passes, as its
     * blocks hold the same ID and their own positions.
     * 
     * @throws StreamIoException  with the storage's exception as the cause, for FileStream a
     *      BadDirStateException that names the file and the way out
     */
    private void checkLeftovers(final byte[] id) {
        try {
            aos.checkLeftovers((position, length, bytes)
                    -> leftoverProblem(position, length, bytes, id));
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
    }
    
    /**
     * null if the piece of 'length' bytes from stream position 'position', which 'bytes'
     * reads, begins as a part of the stream of the database of ID 'id' (bergdb 028-66): its
     * first meta block, the first whole block at or after 'position', is of this version,
     * valid, and holds its own position and 'id' (bergdb 028-67, C3); else what is wrong.
     * Every file of a FileStream begins at a meta block.
     */
    static String leftoverProblem(long position, long length, AppendOnlyStream.PieceReader bytes,
            byte[] id) throws IOException {
        final long pos = (position + META_BLOCK_DISTANCE - 1) / META_BLOCK_DISTANCE
                * META_BLOCK_DISTANCE;
        if (pos + META_BLOCK_SIZE > position + length) {
            return "it holds no meta block: it ends at " + (position + length) + ", and its"
                    + " first would be at " + pos + ", " + META_BLOCK_SIZE + " bytes";
        }
        final byte[] block = new byte[META_BLOCK_SIZE];
        bytes.read(pos, block, 0, META_BLOCK_SIZE);
        final String where = "its first meta block, at " + pos + ", ";
        for (int i = 0; i < 4; i++) {
            if (block[i] != MetaBlock.MAGIC[i]) {
                return where + "does not begin as a meta block: not BergDB's bytes, or"
                        + " damaged";
            }
        }
        if (!MetaBlock.beginsAsBlock(block)) {
            return where + "is of version " + Bytes.bytesToIntLE(block, 4) + ", and this"
                    + " database's are of version " + MetaBlock.CURRENT_VERSION + ": of another"
                    + " version of BergDB";
        }
        final MetaBlock b = new MetaBlock(block, pos);
        if (!b.isValid()) {
            return where + "is not valid, its last byte " + block[META_BLOCK_SIZE - 1]
                    + ": damaged";
        }
        if (b.getStoredPos() != pos) {
            return where + "holds the position " + b.getStoredPos() + ", not its own:"
                    + " written at another place, or damaged";
        }
        if (!b.hasId(id)) {
            // The ID of the stream after the gap, which is the other database's if a file
            // there was put by hand (bergdb 028-66, review R3): either may be another's.
            return where + "holds the database ID " + StringUtil.toHex(b.getId())
                    + ", and the stream's first meta block after the gap holds "
                    + StringUtil.toHex(id) + ": the file and the files after the gap are of two"
                    + " databases, and either may be another database's";
        }
        return null;
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
        if (spos >= META_BLOCK_SIZE && spos < aos.getFirstPos() && spos < block.getPos()) {
            // bergdb 028-66: the start needs bytes that the storage does not have.
            throw new StreamFormatException("The meta block at " + block.getPos()
                    + " names the last transaction at " + spos + ", before the stream's first"
                    + " position, " + aos.getFirstPos() + ": the stream lacks bytes that the"
                    + " database needs, from " + spos + " on. The start has written and"
                    + " deleted nothing (bergdb 028-66)." + frontAccount());
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
     * <p>Since 2026-11-28 (bergdb 028-80; 033's review of the start, F3) also a stream of
     * zeros only, from position 0 and at most a meta block distance long: a creation's first
     * write that a kill left as zeros within the file's length, from its first page on,
     * where its bytes should be, as on macOS (bergdb 028-60; 031-02, F1). Such a stream
     * holds no meta block and no record, so no data. FileStream's open leaves it as it is,
     * the stream's only file (a repair never empties a stream), and the start refused it
     * with "Could not find *any* valid meta block", a StreamFormatException, where every
     * other cut of a creation, with or without zeros after it, gives this one. The bound is
     * FileStream's first file: the stream moves to a second file only after the first is
     * forced (FileStream, newFile()), so only a write into the first file can leave zeros
     * from position 0; a longer stream of zeros is refused as before. A stream that begins
     * after 0, a cut one, is not a creation.</p>
     *
     * @param creationLength  The length of a new database's stream: the first meta block
     *      and the first transaction.
     * @throws StreamIoException
     */
    public boolean isIncompleteCreation(long creationLength) {
        final long length = aos.getLength();
        if (length == 0 || aos.getFirstPos() > 0) {
            return false;
        }
        if (length <= META_BLOCK_DISTANCE && rawZeros(length)) {
            return true;        // A creation's first write left as zeros (bergdb 028-80).
        }
        if (length > creationLength) {
            return false;
        }
        
        byte[] block = new byte[(int) Math.min(length, META_BLOCK_SIZE)];
        readRaw(0, block);
        if (!MetaBlock.beginsAsBlock(block)) {
            return false;   // Not a BergDB stream, an encrypted one, or another version.
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

    /**
     * Whether the stream holds a creation's first transaction, committed, and no committed
     * transaction after it (2026-11-19, bergdb 028-18): a crash, as a power loss, after a
     * database's first transaction was written and before its second was, when a creation
     * writes two (Db: the primordial record and the record of the startup distance). That
     * is: the stream is no longer than a meta block distance (no second meta block) and
     * does not begin after 0; its first meta block is complete and valid and names no
     * transaction; the transaction after it ends at 'creationLength' and is committed (its
     * last byte not 0); and after it the stream ends, or a transaction follows that is cut
     * by the end of the stream (its size too), or failed (its last byte 0) and ends the
     * stream. A stream that this method or isIncompleteCreation() does not take holds a
     * committed transaction after the first, or is not one that a creation and a crash
     * leave. This method only reads. Caller must hold DB.writeLock.
     *
     * @param creationLength  The length of the first meta block and the first transaction.
     * @throws StreamIoException
     */
    public boolean holdsFirstTransactionAlone(long creationLength) {
        final long length = aos.getLength();
        if (length < creationLength || length >= META_BLOCK_DISTANCE || aos.getFirstPos() > 0
                || creationLength <= META_BLOCK_SIZE) {
            return false;
        }

        byte[] block = new byte[META_BLOCK_SIZE];
        readRaw(0, block);
        if (!MetaBlock.beginsAsBlock(block)) {
            return false;
        }
        MetaBlock first = new MetaBlock(block, 0);
        if (!first.isValid() || first.getLastTransSpos() != Constants.SposNULL) {
            return false;
        }
        byte[] sizeBytes = new byte[4];
        readRaw(META_BLOCK_SIZE, sizeBytes);
        if (Bytes.bytesToIntLE(sizeBytes, 0) != creationLength - META_BLOCK_SIZE) {
            return false;
        }
        byte[] lastByte = new byte[1];
        readRaw(creationLength - 1, lastByte);
        if (lastByte[0] == 0) {
            return false;       // Failed: isIncompleteCreation() takes it, if alone.
        }

        final long rest = length - creationLength;
        if (rest < 4) {
            return true;        // No second transaction, or a part of its size.
        }
        readRaw(creationLength, sizeBytes);
        int transSize = Bytes.bytesToIntLE(sizeBytes, 0);
        if (rest != transSize) {
            return rest < transSize;    // Cut; else more bytes follow it.
        }
        readRaw(length - 1, lastByte);
        return lastByte[0] == 0;
    }
    
    /**
     * Whether the stream's bytes from 0 to 'length' are all zero (bergdb 028-80): read in
     * pieces, the first of a meta block's size, until a byte that is not zero.
     */
    private boolean rawZeros(long length) {
        for (long pos = 0; pos < length; ) {
            final byte[] bytes = new byte[(int) Math.min(length - pos,
                    pos == 0 ? META_BLOCK_SIZE : 64 * 1024)];
            readRaw(pos, bytes);
            if (!isZeros(bytes)) {
                return false;
            }
            pos += bytes.length;
        }
        return true;
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
     * The last transaction needs to be "filled out" with zero bytes. Since bergdb 028-67
     * 'spos' is the record that walkTail() found the end of the stream to cut, after its
     * checks; the loop is the walk as before, and it reads that record only. A size field
     * that the end cuts is completed first (transHeaderFixBytes()); all the other bytes that
     * the completion appends are zeros (since 2026-11-28, bergdb 028-67, T1), so that the record
     * that a later start finds, after a kill during the completion or with its zeros left out
     * by FileStream's open (028-60), is again a record's begin followed by zeros, which
     * walkTail() takes, and whose completion appends the same bytes.
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
                // Special case, the size field not completely written.
                
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

    /**
     * The bytes that complete a size field of which 'existingBytes', 1 to 3 bytes, are in the
     * stream: zeros, but the first, which is 1 if zeros give a size below MIN_TRANS_SIZE. The
     * record's bytes from its byte 4 on are zeros (fixLastTransactionIfNeeded()). Until
     * 2026-11-28 (bergdb 028-67, T1) the completion went on to byte 4, also after a cut of 4
     * bytes, and wrote there TORN_HEADER_FILLER, 4 (since 2016; until 2026-10-25, bergdb
     * 005-40, StoredTrans.CURRENT_FORMAT_VERSION), and the least size was 17: a later start
     * that found the record cut again, after a kill during its completion or with its zeros
     * left out by FileStream's open (028-60), refused it for that byte or that size.
     */
    private static byte[] transHeaderFixBytes(byte[] existingBytes) {
        // 2026-10-13 (CrashTest): "large enough" was 6, so a cut after one size
        // byte of 6 to 16 gave a transaction that NodeStream rejected at startup
        // ("Bad transaction size"). Then MIN_TRANS_SIZE, 17; 48 since 2026-11-28.
        if (existingBytes.length < 1 || existingBytes.length >= 4) {
            throw new IllegalArgumentException("existingBytes: " + StringUtil.toHex(existingBytes));
        }
        
        byte[] buffer = new byte[4];
        System.arraycopy(existingBytes, 0, buffer, 0, existingBytes.length);
        byte[] fixBytes = new byte[4 - existingBytes.length];
        if (Bytes.bytesToIntLE(buffer, 0) < MIN_TRANS_SIZE) {
            fixBytes[0] = 1;
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
            
            // 2026-11-25 (bergdb 028-60): a block whose bytes are zero as far as they go, as a
            // zeroed tail leaves it, is completed with zeros: it is then zero throughout, a
            // block that readMetaBlock() reads as not valid. With the template's magic bytes
            // and version after 1 to 7 zero bytes, it was neither, and a later read of it, as
            // the next start's when no valid block follows it, refused the stream.
            int byteCount = RecoverableStream.META_BLOCK_SIZE - blockPos;
            byte[] fill = MetaBlock.FILL_OUT_TEMPLATE;
            if (blockPos > 0) {
                byte[] written = new byte[blockPos];
                readRaw(size - blockPos, written);
                if (isZeros(written)) {
                    fill = new byte[RecoverableStream.META_BLOCK_SIZE];
                }
            }
            try {
                aos.append(fill, blockPos, byteCount);
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
        metaBlock.setStoredPos(metaPos);        // bergdb 028-67, C3
        aos.append(metaBlock.getBlock(), 0, RecoverableStream.META_BLOCK_SIZE);
        this.posOfLastValidMetaBlock = metaPos;
        this.lastTransSposOfLastValidMetaBlock = metaBlock.getLastTransSpos();
        
        //System.out.println("RecoverableStream, wrote MetaBlock, pos: " + metaPos 
        //        + ", startupPos: " + metaBlock.getStartupPos());
    }
    
    /**
     * Returns the last valid meta block, or null if no such block exists. A block of zero
     * bytes is not valid (bergdb 028-60; readMetaBlock()). Since 2026-11-27 (bergdb 028-67,
     * C3) a block is valid only if it holds the position it is read at and the database ID
     * of the stream's first valid block (readFirstMetaBlock()); a block of other bytes or of
     * another version after the first is passed over too, as stale bytes at a meta position
     * are. None is valid if that first valid block does not hold its own position.
     * 
     * @throws StreamIoException
     * @throws StreamFormatException  among them BadMagicBytes and VersioningStreamException,
     *      for the stream's first block
     */
    public MetaBlock readLastValidMetaBlock() {
        MetaBlock first = readFirstMetaBlock();
        if (first == null) {
            return null;
        }
        long length = aos.getLength();
        long spos = length - META_BLOCK_SIZE;
        spos = spos < 0 ? 0 : spos;        
        MetaBlock block = readAValidMetaBlock(aos, spos, 0, first.getId());
        if (block == null) {
            return null;
        }
        this.posOfLastValidMetaBlock = block.getPos();
        this.lastTransSposOfLastValidMetaBlock = block.getLastTransSpos();
        
        return block;
    }
    
    /**
     * The stream's first meta block: the first valid block at or after its first position,
     * complete in the stream, if it holds its own position; else null (bergdb 028-67, C3).
     * Its database ID is the stream's: another block is valid only if it holds it. The
     * stream's other bytes are cut only from its end, and another file's bytes after a kill
     * are in the last file, from a page boundary on, so the first valid block is the
     * stream's own. A block of other bytes or of another version throws here, as
     * readMetaBlock() does: the stream is not one of this version of BergDB, or an earlier
     * release encrypted it.
     *
     * <p>Blocks that are not valid before it are passed over (2026-11-28, week.sh's
     * apps-kill-cc on 8a0897cf), as the search for the last valid block passes over them: a
     * block that a crash cut, which recovery completes as one that is not valid
     * (fixMetaBlockIfNeeded(); bergdb 005-27), or a block of zeros inside a record that a
     * kill left zero and recovery aborted (bergdb 028-60). Such a block stays in the
     * stream, and a cut that deletes the files before it makes it the first block of a
     * stream that is sound: until then the start refused it, "Could not find *any* valid
     * meta block". A cut stream holds a valid block of its own after its first position,
     * written before the cut deleted anything: the cut is not after the record that the
     * last valid block names (getPosOfTransCompletedBefore(); Reclaim), and FileStream
     * deletes a file only after the stream is forced up to its length at the cut. A stream
     * from 0 has its first block valid unless its creation did not complete, which the
     * start finds before (isIncompleteCreation()), or a storage damaged it.</p>
     *
     * @throws StreamIoException
     * @throws BadMagicBytes
     * @throws VersioningStreamException
     */
    private MetaBlock readFirstMetaBlock() {
        final long firstIndex = (aos.getFirstPos() + META_BLOCK_DISTANCE - 1)
                / META_BLOCK_DISTANCE;
        final long length = aos.getLength();
        long pos = firstIndex * META_BLOCK_DISTANCE;
        if (pos + META_BLOCK_SIZE > length) {
            // A stream shorter than its first block: its first 8 bytes, if there, are refused
            // as readMetaBlock() refuses them, as the search for the last block read them
            // before bergdb 028-67; zeros, or the magic bytes and the version, are not.
            if (aos.getLength() - pos >= 8) {
                byte[] header = new byte[8];
                readRaw(pos, header);
                if (!isZeros(header)) {
                    checkBlockHeader(header);
                }
            }
            return null;
        }
        for (; pos + META_BLOCK_SIZE <= length; pos += META_BLOCK_DISTANCE) {
            final MetaBlock block = readMetaBlock(aos, pos);
            if (block.isValid()) {
                return block.isOwn(null) ? block : null;
            }
        }
        return null;
    }

    /**
     * The stream's first meta block, which recover() takes the stream's database ID from
     * (readFirstMetaBlock()): the first valid block at or after the first position, if it
     * holds its own position; null if there is none, or if a block before it is not of this
     * version or not BergDB's, which recover() then refuses as before. Reads only; for a
     * start's comparison of the ID with created.txt's before recover() (2026-11-28, bergdb
     * 028-81).
     *
     * @throws StreamIoException
     */
    public MetaBlock readFirstValidMetaBlock() {
        try {
            return readFirstMetaBlock();
        } catch (StreamFormatException e) {
            return null;        // recover() refuses the stream with it.
        }
    }

    /**
     * The database ID of the stream: the one recover() read in the stream's first meta block,
     * or before recover(), the in-memory block's (bergdb 028-67).
     */
    private byte[] ownId() {
        final byte[] id = streamId;
        return id != null ? id : metaBlock.getId();
    }

    public MetaBlock getMetaBlock() {
        return metaBlock;
    }
    
    /**
     * Returns the length of the underlying append-only stream, with the recovery's writes
     * that recover(RecordCheck, true) holds (bergdb 028-70).
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
     * For a start's refusal of a stream that lacks bytes it needs (2026-11-27, bergdb 028-66):
     * what the storage says of the bytes before its first position, " The storage: " and
     * the message of the ReadBelowFirstPosException of a read of the byte before it; "" for a
     * stream from 0, or if the read throws something else. FileStream's message names a gap
     * in its files. Only a start that refuses calls it.
     */
    public String frontAccount() {
        final long first = aos.getFirstPos();
        if (first <= 0) {
            return "";
        }
        try {
            aos.read(first - 1, new byte[1], 0, 1);
        } catch (ReadBelowFirstPosException e) {
            return " The storage: " + e.getMessage();
        } catch (IOException e) {
            // Not this method's to report: the start refuses with its own message.
        }
        return "";
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
        final byte[] id = ownId();
        MetaBlock meta = readAValidMetaBlock(aos, spos, 0, id);
        long blockPos = meta != null ? meta.getPos()
                : (firstPos + META_BLOCK_DISTANCE - 1) / META_BLOCK_DISTANCE * META_BLOCK_DISTANCE;
        
        for (; blockPos + META_BLOCK_SIZE <= aos.getLength(); blockPos += META_BLOCK_DISTANCE) {
            meta = readOwnMetaBlock(aos, blockPos, id);
            if (meta == null) {
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
     * the last valid meta block at or before 'spos' names, if it is at or after both the
     * first position and 'cut', the position of reclaim's last cut (Db.getFirstAvailablePos(),
     * 0 before the first); otherwise the first record at or after both. The cut is a record's
     * start (Reclaim: pCut is a transaction's nextPos), and so is the first record, after
     * meta block 0, of a stream not cut. The first position is a record's start only in a
     * stream cut exactly there (CutStream, a test's cut): FileStream cuts whole files and
     * MemoryStream whole arrays of 1 MB, so a record can begin before the first position and
     * end after it. Until 2026-11-25 (bergdb 028-55) the walk began at the first position in
     * such a stream too, inside that record, and Db.getTrans() refused the position of a
     * committed transaction over 1 MiB after the cut, where the meta blocks name that record.
     * 'cut' is read after the first position: reclaim sets it before it cuts the stream, so a
     * cut between the two reads does not leave it below the first position. A named record
     * before the cut is not taken (2026-11-25, bergdb 028-56): it was taken if it was at or
     * after the first position read here, and a cut by another thread after that read, as
     * reclaim's cut allows, could remove it before the walk read it; Db.getTrans() then
     * expired a transaction at or after the cut. The meta blocks at or before the later of
     * the first position and the cut are not read, as the records they name are before it:
     * every read of the walk is at or after the cut. A cut after 'cut' is read can still
     * remove what the walk reads; recordHolding() then starts again. Unlike
     * getPosOfTransCompletedBefore(), it does not search after 'spos' in a cut stream. A
     * walk from it reads the headers of the records between that meta block, or the cut, and
     * 'spos' and of the one that reaches over the block; more only if meta blocks are not
     * valid. 'spos' must not be in a meta block. Any thread may call it.
     *
     * @throws StreamIoException  as the reads throw it; and if 'spos' is before reclaim's
     *      cut and the cut after the first position, with a ReadBelowFirstPosException as the
     *      cause, before any read: reclaim has cut the record at 'spos', and Db.getTrans()
     *      expires, as for a read below the first position
     * @throws StreamFormatException  if a meta block is malformed
     */
    public long getRecordStartBefore(long spos, LongSupplier cut) {
        final long firstPos = aos.getFirstPos();
        final long cutPos = cut.getAsLong();
        if (cutPos > firstPos && spos < cutPos) {
            throw new StreamIoException(new ReadBelowFirstPosException("No record's start to "
                    + "walk from at or before stream pos " + spos + ", which is before "
                    + "reclaim's cut, " + cutPos + "; the first position is " + firstPos + "."));
        }
        final long first = Math.max(firstPos, cutPos);
        MetaBlock meta = readAValidMetaBlock(aos, spos, first / META_BLOCK_DISTANCE + 1,
                ownId());
        if (meta != null) {
            long named = meta.getLastTransSpos();
            if (named != Constants.SposNULL && named >= first) {
                return named;
            }
        }
        final long inBlock = first % META_BLOCK_DISTANCE;
        return inBlock < META_BLOCK_SIZE ? first - inBlock + META_BLOCK_SIZE : first;
    }
    
    /**
     * Reads and returns the last valid meta block that starts before or at 'spos', of the
     * blocks of index 'fromIndex' and after only (2026-11-25, bergdb 028-56). If no such
     * meta block exists, null is returned. Since 2026-11-27 (bergdb 028-67, C3) a valid block
     * is one of this stream's: it holds its own position and the database ID 'id'
     * (readOwnMetaBlock()).
     * 
     * @throws StreamIoException
     * @throws StreamFormatException  if a block of this stream is malformed (checkFormat())
     */
    private static MetaBlock readAValidMetaBlock(AppendOnlyStream aos, long spos,
            long fromIndex, byte[] id) {
        long metaIndex;
        MetaBlock result = null;
        
        metaIndex = spos / META_BLOCK_DISTANCE;
        
        // 2026-10-13: the search went down to block 0, also when the front of the
        // stream had been cut (pretruncate), and then failed reading the cut part. Blocks
        // before the first position of the stream are not searched.
        final long firstIndex = Math.max(fromIndex,
                (aos.getFirstPos() + META_BLOCK_DISTANCE - 1) / META_BLOCK_DISTANCE);
        
        for (long i = metaIndex; i >= firstIndex; i--) {
        	long blockPos = i * META_BLOCK_DISTANCE;
            result = readOwnMetaBlock(aos, blockPos, id);
            if (result != null) {
                result.checkFormat();
                break;
            }
        }
        
        return result;
    }

    /**
     * The meta block at 'blockPos' if it is one of this stream's (MetaBlock.isOwn(id)): valid,
     * holding 'blockPos' and the database ID 'id'; else null (bergdb 028-67, C3). A block
     * of other bytes or of another version than this one's (readMetaBlock() throws for it) is
     * not one either: after the stream's first block, which readFirstMetaBlock() reads, such
     * bytes at a meta position are another file's at the stream's tail, or damage, and the
     * walk of the records refuses them where they matter (walkTail()).
     *
     * @throws StreamIoException
     */
    private static MetaBlock readOwnMetaBlock(AppendOnlyStream aos, long blockPos, byte[] id) {
        final MetaBlock block;
        try {
            block = readMetaBlock(aos, blockPos);
        } catch (BadMagicBytes | VersioningStreamException e) {
            return null;
        }
        return block.isOwn(id) ? block : null;
    }
    
    /**
     * Returns the MetaBlock at the given stream position.
     * The block may be invalid, caller should check it. A block of 128 zero bytes is
     * returned as one that is not valid (2026-11-25, bergdb 028-60).
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
            // 2026-11-25 (bergdb 028-60): a block of zero bytes is not valid, as a block that
            // a crash cut is not, and the readers go on to the valid one before it. A kill of
            // the process during an append can leave the stream's last bytes zero within its
            // length, from a page boundary on (macOS, APFS; bergdb 031-02, F1), and meta
            // blocks' positions among them. Until then such a block threw BadMagicBytes, and
            // the start refused the database as a stream that is not BergDB's, before its
            // recovery, which takes zeros inside the last record as a cut tail (recover()).
            // Any other bytes than the magic ones are refused as before.
            if (isZeros(header)) {
                byte[] block = new byte[RecoverableStream.META_BLOCK_SIZE];
                try {
                    aos.read(blockPos, block, 0, block.length);
                } catch (IOException e) {
                    throw new StreamIoException(e);
                }
                if (isZeros(block)) {
                    return new MetaBlock(block, blockPos);      // Not valid: its last byte is 0.
                }
            }
        }
        checkBlockHeader(header);
        
        byte[] metaBytes = new byte[RecoverableStream.META_BLOCK_SIZE];
        
        try {
            aos.read(blockPos, metaBytes, 0, metaBytes.length);
        } catch (IOException e) {
            throw new StreamIoException(e);
        }
        
        return new MetaBlock(metaBytes, blockPos);
    }
    
    /**
     * Refuses the first 8 bytes of a meta block, 'header', unless they are the magic bytes
     * and this version: BadMagicBytes, or a VersioningStreamException (versionRefused()).
     */
    private static void checkBlockHeader(byte[] header) {
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
    }

    /** Whether every byte of 'bytes' is 0 (bergdb 028-60). */
    private static boolean isZeros(byte[] bytes) {
        for (byte b : bytes) {
            if (b != 0) {
                return false;
            }
        }
        return true;
    }
    
    /**
     * The message of a VersioningStreamException for a meta block whose version is not
     * MetaBlock.CURRENT_VERSION (bergdb 028-15, option A): it names the release that
     * wrote an older one, and what a user does. Until bergdb 028-30 (2026-11-20) it said to
     * read a database of version 154 with release 2026.5, which refuses one of 2026.4 or
     * earlier (record format 6 or older): the user reads it with the release that wrote it.
     */
    static String versionRefused(int version) {
        String s = "Cannot read meta block with version " + version + ". Version supported: "
                + MetaBlock.CURRENT_VERSION + ". ";
        if (version == MetaBlock.VERSION_154) {
            return s + "Version 154 is a database written by BergDB release 2026.5 or earlier, "
                    + "which this release does not open: its startup distance is in its meta "
                    + "blocks, and this release keeps it elsewhere (bergdb 028-15). To keep its "
                    + "data, make the database again: read it with the release that wrote it "
                    + "(release 2026.5 opens a database of 2026.5, not one of 2026.4 or "
                    + "earlier) and put the data into a new database with this release, for "
                    + "example with two programs, one on each release's jar. The start has "
                    + "written nothing.";
        }
        if (version == MetaBlock.VERSION_155) {
            return s + "Version 155 is a database written by BergDB release 2026.6, which this "
                    + "release does not open: there is no upgrade path, and release 2026.6 "
                    + "still opens it (bergdb 031-06); or by a development build of 2026.7 "
                    + "before 2026-11-27, whose meta blocks do not hold their own positions "
                    + "(bergdb 028-67). The start has written nothing.";
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
            
            // 56 since 2026-11-28, when MIN_TRANS_SIZE became 48 (bergdb 028-67, T1); 20 before.
            byte[] transBytes = new byte[56];
            Bytes.intToBytesLE(56, transBytes, 0);
            transBytes[transBytes.length - 1] = LAST_BYTE;
            r1.append(transBytes, 0, 2, false, -1);
                // Only first 2 bytes of trans (trans byte size incomplete).
            
            RecoverableStream r2 = new RecoverableStream(mstream, new MetaBlock());
            r2.recover();
            
            Assert.assertEquals(RecoverableStream.META_BLOCK_SIZE + 56, mstream.getLength());
            
            byte[] buffer = new byte[1];
            mstream.read(RecoverableStream.META_BLOCK_SIZE + 56 - 1, buffer, 0, 1);
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
         * Bergdb 028-60: a zeroed tail over meta blocks. A kill of the process during an
         * append can leave the stream's last bytes zero within its length, from a page
         * boundary on (macOS, APFS; bergdb 031-02, F1), and the zeros can cover a meta
         * block's position. Here the last record spans the blocks at 200,000 and 400,000, and
         * its bytes from 4,096 bytes after its start to the stream's end are zero, with the
         * end at the record's end and inside it. Recovery passes over the zero blocks to the
         * valid one before them, as over a block that a crash cut, and the record, cut or
         * whole, is aborted: the records before it are kept, a read that starts at a zero
         * block finds them, and a later append and recovery work. Zeros that reach past a
         * record's end are refused with the size 0 at the next record, "Bad transaction size
         * in db stream, 0, spos P", and the stream cut at P recovers. Until 2026-11-25,
         * readMetaBlock() threw BadMagicBytes for a zero block, and the start refused each of
         * them as a stream that is not BergDB's.
         */
        @Nano
        public static void testZeroedTailOverMetaBlocks() throws IOException {
            MemoryStream m = new MemoryStream();
            RecoverableStream r = new RecoverableStream(m, new MetaBlock());
            final long[] starts = appendNamedTransactions(r, 150);
            final long last = r.getNextSpos();
            byte[] large = new byte[300 * 1000];
            Bytes.intToBytesLE(large.length, large, 0);
            large[large.length - 1] = LAST_BYTE;
            r.append(large, 0, large.length, true, -1);
            r.getMetaBlock().setLastTransSpos(last);
            final long end = m.getLength();
            Assert.assertTrue(last + " to " + end, last + 4096 < META_BLOCK_DISTANCE
                    && end > 2 * META_BLOCK_DISTANCE + META_BLOCK_SIZE);

            for (long length : new long[] {end, 2 * META_BLOCK_DISTANCE + 1000}) {
                final String what = "length " + length;
                MemoryStream z = m.copy();
                z.truncate(length);
                final long zerosFrom = last + 4096;
                MemoryStream.TestAccess.write(z, new byte[(int) (length - zerosFrom)], zerosFrom);

                RecoverableStream r2 = new RecoverableStream(z, new MetaBlock());
                r2.recover();
                Assert.assertEquals(what, end, z.getLength());
                Assert.assertEquals(what, 0, r2.readLastValidMetaBlock().getPos());
                Assert.assertEquals(what, starts.length, count(new Iterator(r2, 0)));
                Assert.assertEquals(what, starts.length,
                        count(new Iterator(r2, 2 * META_BLOCK_DISTANCE + 500)));

                byte[] small = new byte[20];
                Bytes.intToBytesLE(small.length, small, 0);
                small[small.length - 1] = LAST_BYTE;
                r2.append(small, 0, small.length, true, -1);
                RecoverableStream r3 = new RecoverableStream(z, new MetaBlock());
                r3.recover();
                Assert.assertEquals(what, end + small.length, z.getLength());
                Assert.assertEquals(what, starts.length + 1, count(new Iterator(r3, 0)));
            }

            // Zeros from inside the last small record: past its end, refused at the large one.
            MemoryStream z = m.copy();
            final long zerosFrom = starts[starts.length - 1] + 500;
            MemoryStream.TestAccess.write(z, new byte[(int) (end - zerosFrom)], zerosFrom);
            try {
                new RecoverableStream(z, new MetaBlock()).recover();
                throw new AssertionError("recovered zeros past a record's end");
            } catch (StreamFormatException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().startsWith(
                        "Bad transaction size in db stream, 0, spos " + last + ". "));
            }
            Assert.assertEquals(end, z.getLength());
            z.truncate(last);
            RecoverableStream r4 = new RecoverableStream(z, new MetaBlock());
            r4.recover();
            Assert.assertEquals(last, z.getLength());
            Assert.assertEquals(starts.length - 1, count(new Iterator(r4, 0)));
        }

        /**
         * Bergdb 028-60: a zeroed tail that ends 1 to 127 bytes into a meta block's position.
         * Recovery completes a block that a crash cut; one whose bytes are zero as far as they
         * go it completes with zeros, so that it is zero throughout and not valid, as
         * readMetaBlock() reads it. With FILL_OUT_TEMPLATE's magic bytes and version after
         * zeros, a block ending 1 to 7 bytes in was neither a block nor zeros, and the next
         * recovery, which reads it as the last block, refused the stream (BadMagicBytes). A
         * stream that ends at the block's position gets the template, as since 005-27.
         */
        @Nano
        public static void testZeroedTailEndingInMetaBlock() throws IOException {
            MemoryStream m = new MemoryStream();
            RecoverableStream r = new RecoverableStream(m, new MetaBlock());
            final long[] starts = appendNamedTransactions(r, 150);
            final long last = r.getNextSpos();
            byte[] large = new byte[100 * 1000];
            Bytes.intToBytesLE(large.length, large, 0);
            large[large.length - 1] = LAST_BYTE;
            r.append(large, 0, large.length, true, -1);
            r.getMetaBlock().setLastTransSpos(last);
            final long end = m.getLength();
            Assert.assertTrue(last + " to " + end, last + 4096 < META_BLOCK_DISTANCE
                    && end > META_BLOCK_DISTANCE + META_BLOCK_SIZE);

            for (int x : new int[] {0, 1, 3, 7, 8, 64, 127}) {
                final String what = "the stream ends " + x + " bytes into the block";
                final long length = META_BLOCK_DISTANCE + x;
                MemoryStream z = m.copy();
                z.truncate(length);
                final long zerosFrom = last + 4096;
                MemoryStream.TestAccess.write(z, new byte[(int) (length - zerosFrom)], zerosFrom);

                new RecoverableStream(z, new MetaBlock()).recover();
                Assert.assertEquals(what, end, z.getLength());
                byte[] block = new byte[META_BLOCK_SIZE];
                z.read(META_BLOCK_DISTANCE, block, 0, block.length);
                Assert.assertArrayEquals(what, x == 0 ? MetaBlock.FILL_OUT_TEMPLATE
                        : new byte[META_BLOCK_SIZE], block);

                RecoverableStream r2 = new RecoverableStream(z, new MetaBlock());
                r2.recover();
                Assert.assertEquals(what, end, z.getLength());
                Assert.assertEquals(what, 0, r2.readLastValidMetaBlock().getPos());
                Assert.assertEquals(what, starts.length, count(new Iterator(r2, end - 1)));
            }
        }

        private static int count(Iterator iter) {
            int n = 0;
            while (iter.next()) {
                n++;
            }
            return n;
        }

        /**
         * Regression test for bergdb 005-40: a recovery that cannot read the meta blocks, here
         * of a stream whose every byte is changed, as an earlier release's encryption or a
         * wrong key left it, writes nothing, also when a crash has cut the stream at or in a
         * meta block. Until 2026-10-25 it filled out that meta block first, and the stream's
         * own bytes then had garbage there (at 0, 3 and 5 bytes into the block, its magic
         * bytes or its version), so that no recovery succeeded again. Until 2026-11-27 (bergdb
         * 028-69) the test changed the bytes with the internal encryption.
         */
        @Nano
        public static void testRecoverUnreadableWritesNothing() throws IOException {
            MemoryStream plain = new MemoryStream();
            long[] starts = appendNamedTransactions(new RecoverableStream(plain, new MetaBlock()), 
                    250);
            MemoryStream changed = new MemoryStream();
            byte[] all = flipped(bytesOf(plain));
            changed.append(all, 0, all.length);
            int complete = 0;           // Those that end before the meta block at 200,000.
            for (long start : starts) {
                complete += getSpos(start, 1000) <= META_BLOCK_DISTANCE ? 1 : 0;
            }
            
            for (int x : new int[] {0, 3, 5, 50}) {
                MemoryStream m = changed.copy();
                m.truncate(META_BLOCK_DISTANCE + x);
                String what = "cut " + x + " bytes into the meta block";
                try {
                    new RecoverableStream(m, new MetaBlock()).recover();
                    throw new AssertionError(what + ": recovered a stream it cannot read");
                } catch (BadMagicBytes e) {
                    // Expected.
                }
                Assert.assertEquals(what, META_BLOCK_DISTANCE + x, m.getLength());
                    
                // The stream's own bytes recover as before the cut.
                MemoryStream right = new MemoryStream();
                byte[] bytes = flipped(bytesOf(m));
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
        
        private static byte[] bytesOf(MemoryStream m) throws IOException {
            byte[] bytes = new byte[(int) m.getLength()];
            m.read(0, bytes, 0, bytes.length);
            return bytes;
        }
        
        /** The bytes with every bit flipped, in place; flipped again, they are as before. */
        private static byte[] flipped(byte[] bytes) {
            for (int i = 0; i < bytes.length; i++) {
                bytes[i] ^= (byte) 0xff;
            }
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
                MemoryStream.TestAccess.write(mstream, new byte[]{(byte) 157, 0}, pos + 4);
            }
            
            for (int x : new int[] {0, 3, 50}) {
                MemoryStream m = mstream.copy();
                m.truncate(META_BLOCK_DISTANCE + x);
                try {
                    new RecoverableStream(m, new MetaBlock()).recover();
                    throw new AssertionError("recovered, " + x + " bytes into the meta block");
                } catch (VersioningStreamException e) {
                    Assert.assertTrue(e.getMessage(), e.getMessage().contains("157"));
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
         * follow. Zeros only are one, up to a meta block distance (bergdb 028-80): a creation's
         * first write that a kill left as zeros. The method only reads.
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
            
            // Zeros only, as a kill can leave a creation's first write (bergdb 028-80), up to
            // a meta block distance; not longer, nor with a byte that is not zero.
            for (int n : new int[] {1, 100, META_BLOCK_SIZE, creation, 4096, META_BLOCK_DISTANCE,
                    META_BLOCK_DISTANCE + 1}) {
                MemoryStream zeros = new MemoryStream();
                zeros.append(new byte[n], 0, n);
                Assert.assertEquals(n + " zero bytes", n <= META_BLOCK_DISTANCE,
                        isIncompleteCreation(zeros, creation));
                for (int at : new int[] {0, n / 2, n - 1}) {
                    MemoryStream m = zeros.copy();
                    MemoryStream.TestAccess.write(m, new byte[] {LAST_BYTE}, at);
                    Assert.assertFalse(n + " zero bytes but at " + at,
                            isIncompleteCreation(m, creation));
                }
            }
            
            // Not the beginning of a meta block of this version.
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
        
        /**
         * Bergdb 028-18: holdsFirstTransactionAlone(), which a start checks before recovery.
         * The creation's first transaction of 144 bytes after the first meta block, as Db
         * writes it, committed: alone it is one, and so with any cut of a second transaction
         * of 192 bytes after it, or that transaction whole and failed. Not one: a cut in the
         * first transaction or the first failed (isIncompleteCreation's), the second
         * committed, bytes after the second, a first transaction of another size, a block
         * that names a transaction, a stream that reaches the second meta block. The method
         * only reads.
         */
        @Nano
        public static void testHoldsFirstTransactionAlone() throws IOException {
            final int creation = META_BLOCK_SIZE + 144;
            MemoryStream created = new MemoryStream();
            new RecoverableStream(created, new MetaBlock()).append(transBytes(144, LAST_BYTE), 0,
                    144, true, -1);
            Assert.assertTrue("alone", holdsFirstAlone(created, creation));
            for (int cut = 0; cut < creation; cut++) {
                MemoryStream m = created.copy();
                m.truncate(cut);
                Assert.assertFalse("cut at " + cut, holdsFirstAlone(m, creation));
            }
            MemoryStream failedFirst = created.copy();
            MemoryStream.TestAccess.write(failedFirst, new byte[] {0}, creation - 1);
            Assert.assertFalse("the first failed", holdsFirstAlone(failedFirst, creation));
            Assert.assertFalse("another length", holdsFirstAlone(created, creation - 8));
            
            MemoryStream both = created.copy();
            new RecoverableStream(both, new MetaBlock()).append(transBytes(192, LAST_BYTE), 0,
                    192, true, -1);
            for (int cut = creation; cut < creation + 192; cut++) {
                MemoryStream m = both.copy();
                m.truncate(cut);
                Assert.assertTrue("cut at " + cut, holdsFirstAlone(m, creation));
            }
            Assert.assertFalse("the second committed", holdsFirstAlone(both, creation));
            MemoryStream failed = both.copy();
            MemoryStream.TestAccess.write(failed, new byte[] {0}, creation + 191);
            Assert.assertTrue("the second failed", holdsFirstAlone(failed, creation));
            for (MemoryStream m : new MemoryStream[] {both.copy(), failed.copy()}) {
                new RecoverableStream(m, new MetaBlock()).append(transBytes(24, LAST_BYTE), 0,
                        12, false, -1);
                Assert.assertFalse("bytes after the second", holdsFirstAlone(m, creation));
            }
            
            MemoryStream names = created.copy();
            byte[] pos = new byte[8];
            Bytes.longToBytesLE(META_BLOCK_SIZE, pos, 0);
            MemoryStream.TestAccess.write(names, pos, 16);
            Assert.assertFalse("a block that names a transaction",
                    holdsFirstAlone(names, creation));
            MemoryStream large = created.copy();
            new RecoverableStream(large, new MetaBlock()).append(
                    transBytes(META_BLOCK_DISTANCE + 1000, LAST_BYTE), 0,
                    META_BLOCK_DISTANCE, false, -1);
            Assert.assertFalse("past the second meta block", holdsFirstAlone(large, creation));
        }
        
        /** holdsFirstTransactionAlone() on the stream m, which it must leave as it was. */
        private static boolean holdsFirstAlone(MemoryStream m, long creationLength)
                throws IOException {
            byte[] before = bytesOf(m);
            boolean result = new RecoverableStream(m, new MetaBlock())
                    .holdsFirstTransactionAlone(creationLength);
            Assert.assertArrayEquals("unchanged", before, bytesOf(m));
            return result;
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
            // Test with one existing byte that is large enough. 40 was until 2026-11-28, when
            // MIN_TRANS_SIZE became 48 (bergdb 028-67, T1); the completion of 40 is 296.
            
            byte[] existing = new byte[]{48};
            byte[] fix = transHeaderFixBytes(existing);
            
            byte[] total = Util.concat(existing, fix);
            int size = Bytes.bytesToIntLE(total, 0);
            
            Assert.assertEquals(48, size);
            Assert.assertEquals(3, fix.length);
            Assert.assertEquals(256 + 40, Bytes.bytesToIntLE(
                    Util.concat(new byte[] {40}, transHeaderFixBytes(new byte[] {40})), 0));
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
         * bergdb 028-55: getRecordStartBefore() in a stream cut at one of its 1 MB arrays, its
         * first position inside the record that reaches over it, with reclaim's cut after it.
         * Up to the first meta block after the cut, the meta blocks name a record before the
         * first position: the start is the cut, a record's start, where it was the first
         * position, after its meta block. A position after the first position and before the
         * cut expires; with no cut (0, a stream cut exactly at its first position, as
         * CutStream), the start is the first position, after its meta block, as before.
         */
        @Nano
        public static void testRecordStartBeforeAfterCut() {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r = new RecoverableStream(mstream, new MetaBlock());
            long[] starts = appendNamedTransactions(r, 1300);
            final long first = 5 * META_BLOCK_DISTANCE;
            mstream.pretruncate(first + 3000);      // At one of its 1 MB arrays.
            Assert.assertEquals(first, mstream.getFirstPos());
            int i = 0;
            long named = -1;        // the record that the meta block at 1,200,000 names
            for (int k = 0; k < starts.length; k++) {
                Assert.assertTrue("no record at the first position", starts[k] != first + 128);
                i = starts[k] < first + 3000 ? k + 1 : i;
                named = getSpos(starts[k], 1000) < 6 * META_BLOCK_DISTANCE ? starts[k] : named;
            }
            final long cut = starts[i];
            for (long spos : new long[] {cut, starts[i + 1], 6 * META_BLOCK_DISTANCE - 8}) {
                Assert.assertEquals("spos " + spos, cut, r.getRecordStartBefore(spos, () -> cut));
            }
            Assert.assertEquals(named, r.getRecordStartBefore(named + 8000, () -> cut));
            try {
                r.getRecordStartBefore(first + 1000, () -> cut);
                throw new AssertionError("taken, before the cut");
            } catch (StreamIoException e) {
                Assert.assertTrue("" + e.getCause(),
                        e.getCause() instanceof ReadBelowFirstPosException);
            }
            Assert.assertEquals(first + META_BLOCK_SIZE, r.getRecordStartBefore(cut, () -> 0));
        }
        
        /**
         * A stream whose front a cut took off can begin at a meta block that is not valid
         * (2026-11-28, week.sh's apps-kill-cc on 8a0897cf, Kill seed 2078503, db 4): a kill
         * ended the stream at the block's position, after the bytes of the record that reaches
         * over it and before the block, and the next start's recovery completed the block as
         * one that is not valid (bergdb 005-27) and the record as an aborted one; or a kill
         * left the record's bytes zero from a page boundary on, the block's among them, and
         * recovery aborted the record (bergdb 028-60). The block stays in the stream, and a
         * cut that deletes what is before it makes it the stream's first block. Since bergdb
         * 028-67, C3, until this test, the start took the stream's first block only and
         * refused the stream, "Could not find *any* valid meta block"; the first valid block
         * after it is the stream's first block now, the stream recovers, and its records from
         * the one that the next block names are read.
         */
        @Nano
        public static void testCutStreamBeginsAtInvalidBlock() throws IOException {
            final long block = 5 * META_BLOCK_DISTANCE;     // At one of MemoryStream's arrays.
            for (boolean zeros : new boolean[] {false, true}) {
                MemoryStream m = new MemoryStream();
                RecoverableStream r1 = new RecoverableStream(m, new MetaBlock());
                byte[] t = new byte[1000];
                Bytes.intToBytesLE(t.length, t, 0);
                t[t.length - 1] = LAST_BYTE;
                while (r1.getNextSpos() + 10 * t.length < block) {
                    final long start = r1.getNextSpos();
                    r1.append(t, 0, t.length, true, -1);
                    r1.getMetaBlock().setLastTransSpos(start);
                }
                // The record that reaches over the block.
                byte[] over = new byte[20000];
                Bytes.intToBytesLE(over.length, over, 0);
                over[over.length - 1] = LAST_BYTE;
                final long overStart = r1.getNextSpos();
                r1.append(over, 0, over.length, true, -1);
                Assert.assertTrue(overStart + 4096 < block && m.getLength() > block + 10000);
                if (zeros) {
                    final long from = overStart + 4096;
                    MemoryStream.TestAccess.write(m, new byte[(int) (m.getLength() - from)], from);
                } else {
                    m.truncate(block);
                }
                
                RecoverableStream r2 = new RecoverableStream(m, new MetaBlock());
                r2.recover();
                Assert.assertFalse(readMetaBlock(m, block).isValid());
                Assert.assertEquals(block - META_BLOCK_DISTANCE, r2.readLastValidMetaBlock().getPos());
                final long[] starts = appendNamedTransactions(r2, 700);
                
                m.pretruncate(block + 3000);
                Assert.assertEquals(block, m.getFirstPos());
                RecoverableStream r3 = new RecoverableStream(m, new MetaBlock());
                r3.recover();
                final long last = (m.getLength() - META_BLOCK_SIZE) / META_BLOCK_DISTANCE
                        * META_BLOCK_DISTANCE;
                Assert.assertEquals(last, r3.readLastValidMetaBlock().getPos());
                
                long named = -1;        // the record that the block at 1,200,000 names
                for (long start : starts) {
                    named = getSpos(start, 1000) < block + META_BLOCK_DISTANCE ? start : named;
                }
                Assert.assertEquals(named, r3.getPosOfTransCompletedBefore(block + 50000));
                Iterator iter = new Iterator(r3, 0);
                int count = 0;
                while (iter.next()) {
                    Assert.assertEquals(1000, iter.getBytes().length);
                    count++;
                }
                int expected = 0;
                for (long start : starts) {
                    expected += start >= named ? 1 : 0;
                }
                Assert.assertEquals("zeros " + zeros, expected, count);
            }
        }
        
        /**
         * Bergdb 028-70: recover(check, true) holds the recovery's writes. After it the
         * storage is as before, byte for byte, and the stream's length and reads are those of
         * the stream that recover() without the hold leaves; writeRecovery(), or the next
         * append, writes the same bytes as recover() did, the meta blocks inside the
         * completion among them. The cases: a record of 3 meta block distances cut after
         * 250,000 bytes, whose completion crosses two meta blocks; a stream cut in a meta
         * block after a record that ends at its position (crashAtMetaBlockPosition()); a
         * record whose size field the end of the stream cuts after 2 bytes.
         */
        @Nano
        public static void testRecoveryHeld() throws IOException {
            for (int c = 0; c < 3; c++) {
                for (boolean byAppend : new boolean[] {false, true}) {
                    final String what = "case " + c + (byAppend ? ", by an append" : "");
                    final MemoryStream m = new MemoryStream();
                    final RecoverableStream r1 = new RecoverableStream(m, new MetaBlock());
                    final long cut;
                    if (c == 0) {
                        appendRecord(r1, 3 * META_BLOCK_DISTANCE + 20);
                        cut = 250000;
                    } else if (c == 1) {
                        appendRecord(r1, META_BLOCK_DISTANCE - META_BLOCK_SIZE);
                        cut = META_BLOCK_DISTANCE + 50;
                    } else {
                        appendRecord(r1, 1000);
                        cut = m.getLength() + 2;
                        appendRecord(r1, 1000);
                    }
                    m.truncate(cut);
                    final MemoryStream a = copyOf(m);
                    final RecoverableStream ra = new RecoverableStream(a, new MetaBlock());
                    ra.recover(null, false);
                    final MemoryStream b = copyOf(m);
                    final RecoverableStream rb = new RecoverableStream(b, new MetaBlock());
                    rb.recover(null, true);
                    Assert.assertArrayEquals(what + ": held", bytesOf(m), bytesOf(b));
                    Assert.assertTrue(what + ": a completion", a.getLength() > cut);
                    Assert.assertEquals(what + ": the length", a.getLength(), rb.getLength());
                    final long from = META_BLOCK_SIZE;
                    final int n = (int) getRemainingTransBytes(from, a.getLength());
                    final byte[] readA = new byte[n];
                    final byte[] readB = new byte[n];
                    ra.read(from, readA, 0, n);
                    rb.read(from, readB, 0, n);
                    Assert.assertArrayEquals(what + ": the reads", readA, readB);
                    final byte[] whole = new byte[(int) a.getLength()];
                    a.read(0, whole, 0, whole.length);
                    final byte[] blocks = new byte[(int) a.getLength() - (int) cut];
                    rb.aos.read(cut, blocks, 0, blocks.length);
                    Assert.assertArrayEquals(what + ": the bytes held",
                            Arrays.copyOfRange(whole, (int) cut, whole.length), blocks);
                    if (byAppend) {
                        appendRecord(ra, 64);
                        appendRecord(rb, 64);
                    } else {
                        rb.writeRecovery();
                        rb.writeRecovery();
                    }
                    Assert.assertArrayEquals(what + ": written", bytesOf(a), bytesOf(b));
                }
            }
        }

        /**
         * Bergdb 028-79 (033's review of the start, F2): the bytes at a meta block's position
         * after the last valid block, in a record whose content the walk does not read, or
         * right after a whole record that ends there. Other bytes there, which a kill can
         * leave in the last file (random bytes, a block of this database of another place,
         * one of another database, one of version 155), are refused with a BadTailException,
         * the stream unchanged: in the record that the end of the stream cuts and in an
         * aborted record, with P the record's start; after a whole record that ends at the
         * block, with P the block's position, not 128 after it. The database's own bytes there
         * are taken: zeros, recovery's fill, a block cut after 60 bytes and completed. Before,
         * every case was taken but the third with bytes after the block, refused with P 128
         * after it, and the cut at P kept the block's bytes in the stream.
         */
        @Nano
        public static void testForeignBlockRefused() throws IOException {
            final long x = 2 * META_BLOCK_DISTANCE;
            final MemoryStream over = new MemoryStream();       // a record over x
            final RecoverableStream r = new RecoverableStream(over, new MetaBlock());
            while (over.getLength() < x - 20000) {
                appendRecord(r, 1000);
            }
            final long record = over.getLength();
            appendRecord(r, 50000);
            final MemoryStream ends = new MemoryStream();       // a record that ends at x
            final RecoverableStream r2 = new RecoverableStream(ends, new MetaBlock());
            while (ends.getLength() < x - 10000) {
                appendRecord(r2, 1000);
            }
            final long before = ends.getLength();
            appendRecord(r2, (int) (x - before));
            appendRecord(r2, 1000);
            final byte[] own = new byte[META_BLOCK_SIZE];
            over.read(x, own, 0, META_BLOCK_SIZE);
            Assert.assertTrue("the record's block", MetaBlock.isValid(own));
            final byte[] own2 = new byte[META_BLOCK_SIZE];
            ends.read(x, own2, 0, META_BLOCK_SIZE);
            Assert.assertTrue("the block after the record", MetaBlock.isValid(own2));

            final byte[] random = new byte[META_BLOCK_SIZE];
            new java.util.Random(79).nextBytes(random);
            final byte[] place = own.clone();
            Bytes.longToBytesLE(x - META_BLOCK_DISTANCE, place, MetaBlock.POS_OFFSET);
            final byte[] other = own.clone();
            other[30] ^= 1;
            final byte[] v155 = own.clone();
            v155[4] = (byte) MetaBlock.VERSION_155;
            final byte[] cut = MetaBlock.FILL_OUT_TEMPLATE.clone();
            System.arraycopy(own, 0, cut, 0, 60);
            final Object[][] blocks = {{"random bytes", random, true},
                {"a block of another place", place, true}, {"another database's", other, true},
                {"version 155", v155, true}, {"zeros", new byte[META_BLOCK_SIZE], false},
                {"the fill", MetaBlock.FILL_OUT_TEMPLATE.clone(), false},
                {"a block cut and completed", cut, false}};
            for (Object[] b : blocks) {
                final byte[] block = (byte[]) b[1];
                final boolean foreign = (Boolean) b[2];
                for (int c = 0; c < 4; c++) {
                    final String what = b[0] + (c == 0 ? ", in a cut record"
                            : c == 1 ? ", in an aborted record"
                            : c == 2 ? ", after a record, 300 bytes" : ", after a record, 50 bytes");
                    final MemoryStream m = c < 2 ? copyOf(over) : copyOf(ends);
                    final byte[] bytes = c == 3 ? Arrays.copyOf(block, 50) : block;
                    MemoryStream.TestAccess.write(m, bytes, x);
                    if (c == 0) {
                        m.truncate(x + 10000);
                    } else if (c == 1) {
                        MemoryStream.TestAccess.write(m, new byte[1], getSpos(record, 50000 - 1));
                    } else {
                        m.truncate(x + (c == 2 ? 300 : 50));
                        if (c == 2) {
                            MemoryStream.TestAccess.write(m, Arrays.copyOf(random, 172),
                                    x + META_BLOCK_SIZE);
                        }
                    }
                    final byte[] image = bytesOf(m);
                    final RecoverableStream rs = new RecoverableStream(m, new MetaBlock());
                    long p = -1;
                    try {
                        rs.recover();
                    } catch (BadTailException e) {
                        p = e.getCutPos();
                        Assert.assertArrayEquals(what + ": unchanged", image, bytesOf(m));
                    }
                    final long expected = !foreign ? (c == 2 ? x + META_BLOCK_SIZE : -1)
                            : c < 2 ? record : x;
                    Assert.assertEquals(what + ": P", expected, p);
                }
            }
        }

        /**
         * Bergdb 028-79, the review of 2026-11-28: a meta block's first 8 bytes. (A) A block of
         * the database's first 1 to 4 bytes and zeros, with other bytes after it in the
         * record that the end of the stream cuts, as a kill 1 to 4 bytes into a file and
         * other bytes from there leave it, is refused with P the record's start; with zeros
         * after it, as recovery's completion writes them, it is taken. After a whole record
         * that ends at the block, with other bytes after it, P is the block's position, not
         * 128 after it. (B) A block that the end of the stream cut after 1 to 3 bytes, with
         * zeros after them to 2 to 4 bytes into it, as a kill's zeros on a storage that keeps
         * them leave it, is completed by the fill from the stream's end, and the next start
         * takes the stream, in a record over the block and after one that ends at it. Before,
         * (A) was taken, and a later start that read the block as its first refused the
         * stream; (B) was refused at the second start, "does not begin as a meta block", and
         * (A) after a whole record was refused with P 128 after the block.
         */
        @Nano
        public static void testFirstBytesOfABlock() throws IOException {
            final long x = 2 * META_BLOCK_DISTANCE;
            final MemoryStream over = new MemoryStream();       // a record over x
            final RecoverableStream r = new RecoverableStream(over, new MetaBlock());
            while (over.getLength() < x - 20000) {
                appendRecord(r, 1000);
            }
            final long record = over.getLength();
            appendRecord(r, 50000);
            final MemoryStream ends = new MemoryStream();       // a record that ends at x
            final RecoverableStream r2 = new RecoverableStream(ends, new MetaBlock());
            while (ends.getLength() < x - 10000) {
                appendRecord(r2, 1000);
            }
            appendRecord(r2, (int) (x - ends.getLength()));
            appendRecord(r2, 1000);
            final byte[] own = new byte[META_BLOCK_SIZE];
            over.read(x, own, 0, META_BLOCK_SIZE);
            final byte[] other = new byte[900];
            new java.util.Random(80).nextBytes(other);

            for (int k = 1; k <= 4; k++) {
                final byte[] block = Arrays.copyOf(Arrays.copyOf(own, k), META_BLOCK_SIZE);
                for (int c = 0; c < 3; c++) {
                    final String what = k + " bytes and zeros, " + (c == 0
                            ? "other bytes after it in a cut record"
                            : c == 1 ? "zeros after it in a cut record"
                            : "other bytes after it, after a record");
                    final MemoryStream m = c < 2 ? copyOf(over) : copyOf(ends);
                    MemoryStream.TestAccess.write(m, block, x);
                    m.truncate(x + META_BLOCK_SIZE + other.length);
                    MemoryStream.TestAccess.write(m, c == 1 ? new byte[other.length] : other,
                            x + META_BLOCK_SIZE);
                    final byte[] image = bytesOf(m);
                    long p = -1;
                    try {
                        new RecoverableStream(m, new MetaBlock()).recover();
                    } catch (BadTailException e) {
                        p = e.getCutPos();
                        Assert.assertArrayEquals(what + ": unchanged", image, bytesOf(m));
                    }
                    Assert.assertEquals(what + ": P", c == 0 ? record : c == 1 ? -1 : x, p);
                }
            }
            for (int k = 1; k <= 3; k++) {
                for (int j = k + 1; j <= 4; j++) {
                    for (int c = 0; c < 2; c++) {
                        final String what = k + " bytes, zeros to " + j
                                + (c == 0 ? ", in a record" : ", after a record");
                        final MemoryStream m = c == 0 ? copyOf(over) : copyOf(ends);
                        MemoryStream.TestAccess.write(m, Arrays.copyOf(own, j), x);
                        MemoryStream.TestAccess.write(m, new byte[j - k], x + k);
                        m.truncate(x + j);
                        new RecoverableStream(m, new MetaBlock()).recover();
                        Assert.assertTrue(what + ": completed", m.getLength() >= x + 128);
                        final byte[] image = bytesOf(m);
                        new RecoverableStream(m, new MetaBlock()).recover();
                        Assert.assertArrayEquals(what + ": taken as it is", image, bytesOf(m));
                    }
                }
            }
        }

        /**
         * Bergdb 028-79, its second review of 2026-11-28 (E): a block of the database's first 1
         * to 4 bytes and zeros, followed by zeros past the next meta block and then other
         * bytes in the record, as a kill 1 to 4 bytes into a file leaves it where the zeros
         * after it reach past 200 kB, is refused with P the record's start, in the record
         * that the end of the stream cuts and in an aborted record, the stream unchanged; cut
         * at P, it starts. With zeros after it to the end of the stream or of the record, a
         * later block among them of zeros or the database's own cut after 60 bytes, it is
         * taken. Before, the zeros were checked only to the next meta block, and the stream
         * was taken with the block, which a later start that read it as its first refused
         * (BadMagicBytes, or a VersioningStreamException).
         */
        @Nano
        public static void testFirstBytesOfABlockZerosPastTheNextBlock() throws IOException {
            final long x = 2 * META_BLOCK_DISTANCE;
            final long y = x + META_BLOCK_DISTANCE;
            final MemoryStream over = new MemoryStream();       // a record over x and y
            final RecoverableStream r = new RecoverableStream(over, new MetaBlock());
            while (over.getLength() < x - 20000) {
                appendRecord(r, 1000);
            }
            final long record = over.getLength();
            final int size = 300000;
            appendRecord(r, size);
            appendRecord(r, 1000);
            Assert.assertTrue("the record ends after y", getSpos(record, size) > y + 20000);
            Assert.assertTrue("no block after y", over.getLength() < y + META_BLOCK_DISTANCE);
            final byte[] own = new byte[META_BLOCK_SIZE];
            over.read(x, own, 0, META_BLOCK_SIZE);
            final byte[] ownY = new byte[META_BLOCK_SIZE];
            over.read(y, ownY, 0, META_BLOCK_SIZE);
            final byte[] other = new byte[9000];
            new java.util.Random(81).nextBytes(other);

            for (int k = 1; k <= 4; k++) {
                for (int c = 0; c < 5; c++) {
                    final String what = k + " bytes and zeros, zeros after it past the next "
                            + "block, " + (c == 0 ? "then other bytes, in a cut record"
                            : c == 1 ? "then other bytes, in an aborted record"
                            : c == 2 ? "to the end, in a cut record"
                            : c == 3 ? "to the end, the next block the database's cut, in a "
                                    + "cut record"
                            : "to the record's end, in an aborted record");
                    final MemoryStream m = copyOf(over);
                    final boolean cut = c == 0 || c == 2 || c == 3;
                    if (cut) {
                        m.truncate(y + 4096 + other.length);
                    }
                    MemoryStream.TestAccess.write(m, Arrays.copyOf(own, k), x);
                    final long zerosEnd = cut ? m.getLength() : getSpos(record, size - 1) + 1;
                    MemoryStream.TestAccess.write(m, new byte[(int) (zerosEnd - x - k)], x + k);
                    if (c < 2) {
                        MemoryStream.TestAccess.write(m, other, y + 4096);
                    } else if (c == 3) {
                        MemoryStream.TestAccess.write(m, Arrays.copyOf(ownY, 60), y);
                    }
                    final byte[] image = bytesOf(m);
                    long p = -1;
                    try {
                        new RecoverableStream(m, new MetaBlock()).recover();
                    } catch (BadTailException e) {
                        p = e.getCutPos();
                        Assert.assertArrayEquals(what + ": unchanged", image, bytesOf(m));
                    }
                    Assert.assertEquals(what + ": P", c < 2 ? record : -1, p);
                    if (c < 2) {
                        m.truncate(p);
                        new RecoverableStream(m, new MetaBlock()).recover();
                        new RecoverableStream(m, new MetaBlock()).recover();
                        Assert.assertEquals(what + ": cut at P", record, m.getLength());
                    }
                }
            }
        }

        private static void appendRecord(RecoverableStream r, int size) {
            final byte[] t = new byte[size];
            Bytes.intToBytesLE(size, t, 0);
            Arrays.fill(t, 4, size - 1, (byte) 7);
            t[size - 1] = LAST_BYTE;
            r.append(t, 0, size, true, -1);
        }

        private static MemoryStream copyOf(MemoryStream m) throws IOException {
            final MemoryStream copy = new MemoryStream();
            final byte[] b = bytesOf(m);
            copy.append(b, 0, b.length);
            return copy;
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
            // Version 156 should work (155 until bergdb 028-67, 154 until bergdb 028-15).
            
            MemoryStream mstream = new MemoryStream();
            MetaBlock meta = new MetaBlock();            
            RecoverableStream r1 = new RecoverableStream(mstream, meta);
            
            byte[] bytes = new byte[1000];
            r1.append(bytes, 0, bytes.length, false, 1234L);
            mstream.close();
            
            MemoryStream m = mstream.copy();
            MemoryStream.TestAccess.write(m, new byte[]{(byte) 156, 0}, 4);
            
            RecoverableStream.readMetaBlock(m, 0);
        }
        
        /**
         * Bergdb 028-15 (option A): a meta block of version 154, as every release until
         * 2026.5 wrote, is refused with a message that names release 2026.5 and what a user
         * does, reading it with the release that wrote it (bergdb 028-30); a newer version
         * with one that says so. Since bergdb 028-67, 155, release 2026.6's and that of builds
         * of 2026.7 before 2026-11-27, with a message that names both.
         */
        @Nano
        public static void testReadMetaBlockVersion154Refused() throws IOException {
            MemoryStream mstream = new MemoryStream();
            RecoverableStream r1 = new RecoverableStream(mstream, new MetaBlock());
            byte[] bytes = new byte[1000];
            r1.append(bytes, 0, bytes.length, false, 1234L);
            mstream.close();
            
            for (int version : new int[] {154, 155, 157}) {
                MemoryStream m = mstream.copy();
                MemoryStream.TestAccess.write(m, new byte[]{(byte) version, 0}, 4);
                try {
                    RecoverableStream.readMetaBlock(m, 0);
                    throw new AssertionError("version " + version + " read");
                } catch (VersioningStreamException e) {
                    String s = e.getMessage();
                    Assert.assertTrue(s, s.contains("version " + version));
                    Assert.assertTrue(s, s.contains(version == 154 ? "release 2026.5"
                            : version == 155 ? "release 2026.6" : "newer"));
                    Assert.assertTrue(s, version != 154 || s.contains("the release that wrote it"));
                    Assert.assertTrue(s, version != 155 || s.contains("028-67"));
                }
            }
        }
        
        /**
         * bergdb 028-66, the rule of the files before a gap (Frans, 2026-11-27):
         * leftoverProblem() passes a piece whose first meta block, the first whole block at or
         * after its start, is of this version, valid, at its own position and of the database
         * ID, also of a piece that begins between two blocks; else it says what is wrong, and
         * reads no more than the block.
         */
        @Nano
        public static void testLeftoverProblem() throws IOException {
            final byte[] id = new byte[16];
            Arrays.fill(id, (byte) 66);
            final MetaBlock m = new MetaBlock();
            m.setId(id);
            m.setStoredPos(200000);
            final byte[] good = m.getBlock().clone();
            final byte[][] block = {good};
            AppendOnlyStream.PieceReader reader = (position, dest, offset, length) -> {
                Assert.assertEquals(200000L, position);
                Assert.assertEquals(META_BLOCK_SIZE, length);
                System.arraycopy(block[0], 0, dest, offset, length);
            };
            Assert.assertTrue(leftoverProblem(200000, 200000, reader, id) == null);
            Assert.assertTrue(leftoverProblem(100000, 200000, reader, id) == null);
            String p = leftoverProblem(100000, 100000, reader, id);
            Assert.assertTrue(p, p.contains("holds no meta block"));
            p = leftoverProblem(200000, 127, reader, id);
            Assert.assertTrue(p, p.contains("holds no meta block"));
            
            byte[] other = id.clone();
            other[15] = 67;
            p = leftoverProblem(200000, 200000, reader, other);
            Assert.assertTrue(p, p.contains("holds the database ID " + StringUtil.toHex(id))
                    && p.contains("after the gap holds " + StringUtil.toHex(other))
                    && p.contains("either may be another database's"));
            
            block[0] = good.clone();
            Bytes.intToBytesLE(155, block[0], 4);
            p = leftoverProblem(200000, 200000, reader, id);
            Assert.assertTrue(p, p.contains("of version 155"));
            block[0] = good.clone();
            block[0][0] = 'B';
            p = leftoverProblem(200000, 200000, reader, id);
            Assert.assertTrue(p, p.contains("does not begin as a meta block"));
            block[0] = good.clone();
            block[0][META_BLOCK_SIZE - 1] = 0;
            p = leftoverProblem(200000, 200000, reader, id);
            Assert.assertTrue(p, p.contains("is not valid"));
            block[0] = good.clone();
            Bytes.longToBytesLE(400000, block[0], MetaBlock.POS_OFFSET);
            p = leftoverProblem(200000, 200000, reader, id);
            Assert.assertTrue(p, p.contains("holds the position 400000, not its own"));
        }
    }
}
