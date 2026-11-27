package bergdb.stream;

import java.io.IOException;

/**
 * <p>An append-only stream is an append-only storage of a stream of bytes.
 * The stream can be appended to with: <code>append()</code>, and read with <code>read()</code>.
 * Existing bytes that have already been appended to the stream will never be modified.
 * Additionally, an AppendOnlyStream has the method <code>pretruncate()</code> that truncates the
 * stream from the beginning of it, that is, it removes the first bytes of the stream.</p>
 *
 * <p>The stream format and storage/database contract are being specified in bergdb 014.
 * Historical crash assumptions and startup stream correction are investigated in
 * bergdb 014-01, sections 2 to 5.</p>
 *
 * <p>CRASHES. BergDB assumes that the bytes read back are exactly the bytes appended, and that
 * after a crash (of the process, the OS or the power) the stream is a prefix of the bytes
 * appended: it ends at some position, at least as far as the bytes forced to storage, and
 * holds every byte before it and none after it. The implementation, with the storage under
 * it (file system, block device, flash), must ensure this; BergDB does not.
 * A start recovers only a truncated tail; other damage is an integrity failure outside this
 * contract (bergdb 014-01, section 7). The front may move forward at a crash, never past
 * the position of a pretruncate() call made before it (2026-11-27, bergdb 028-66): the
 * stream may then begin later than it did, and still holds every byte from there to its
 * end. FileStream deletes the files of a cut with one force of the directory a batch, and a
 * power loss can keep the delete of a newer file and lose that of an older one, a gap that
 * its open takes as the stream's new front. A caller that cuts must have its record of the
 * cut durable before it calls pretruncate() (Reclaim, cutIfDurable), as the bytes before
 * the position may be gone after a crash. BergDB assumes correct storage: its checksums and
 * checks find some damage of the stored bytes, not all, as a best effort, and damage that
 * passes them gives wrong values with no error (bergdb 019-10; Db, "Errors").</p>
 * 
 * <p>CONCURRENCY.
 * Implementations can assume that the interface user adheres to the following concurrency rules:
 * 1. Method calls to read() are made by multiple concurrent threads. 
 * 2. Method calls to all other methods (including constructors) are made from threads holding the
 * same lock (the "write lock"). 
 * Put briefly, we allow a single writer and a multiple 
 * readers (calling read()). In particular, calling getSize() and getFirstPos() 
 * requires holding the write lock.
 * It is the responsibility of the implementations of this interface that the changes
 * by the writer thread are visible to the readers calling read().</p>
 * 
 * @author Frans Lundberg
 */
public interface AppendOnlyStream {
    
    /**
     * Returns the length of the stream; the length of an AppendOnlyStream is the total number 
     * of bytes ever appended to the stream. The length always increases.
     * Thus, calls to pretruncate will *not* reduce the length of the stream.
     */
    public long getLength();
    
    /**
     * Returns the first valid stream position that can be read from the stream. 
     * In a newly created AppendOnlyStream without any previous stream data, 
     * this method will return 0. After pretruncate has been called, the result 
     * of this method can be larger than 0.
     */
    public long getFirstPos();
    
    /**
     * Reads some bytes from the stream. This method blocks until exactly
     * 'length' number of bytes have been read or an exception has been thrown.
     * 
     * <p>Anything else that read() throws breaks this contract. Of the database's main
     * stream, an unchecked exception fails the storage and the database, as an IOException
     * does, and an Error fails the database and is thrown as it is to the call that read
     * (2026-11-06, bergdb 019-10; Db, "Errors").</p>
     * 
     * @throws IllegalArgumentException if 'destOffset' or 'length' is negative, or their sum
     *      is greater than dest.length (so if 'length' is greater than dest.length); the
     *      stream is left as it was.
     * @throws IOException if there is an error when reading the data.
     * @throws java.io.EOFException if there is not enough data to read.
     */
    public void read(long position, byte[] dest, int destOffset, int length) throws IOException;
    
    /**
     * Appends 'length' bytes to the write-once stream.
     * When this method returns, it is guaranteed that the data just written 
     * can be read by the read method and the new size of the stream is available from
     * getSize().
     * The completion advances StorageManager's durable length, which sync() waits for, and
     * the storage says what it means (2026-11-04, bergdb 005-47). FileStream, by default,
     * forces the bytes and any newly created backing-file names before append returns: a
     * completed append survives a power loss. With its per-append forcing off, append writes
     * the bytes to the operating system and returns: a completed append survives a crash of
     * the process, not one of the OS or a power loss, and such a crash can also leave a hole
     * that recovery does not handle (bergdb 014-01; see FileStream). Memory-backed test
     * streams do not provide a hardware-durability guarantee.
     * 
     * @throws IllegalArgumentException if 'sourceOffset' or 'length' is negative, or their
     *      sum is greater than source.length (so if 'length' is greater than source.length);
     *      the stream is left as it was.
     * @throws IOException if the data could not be added to the stream.
     */
    public void append(byte[] source, int sourceOffset, int length) throws IOException;
    
    /**
     * <p>This method is called to notify the stream that stream positions strictly less than 
     * 'spos' will never be used and thus can be discarded.
     * There is no requirement that the stream actually deletes files or reclaims
     * storage space immediately when this method is called.
     * The stream implementation chooses how to use this information.
     * This method should return quickly. It might be run within a client request thread, so the
     * DB client might have to wait for this method to return.</p>
     * 
     * <p>A position greater than the length of the stream is refused: the method throws
     * (IllegalArgumentException, or IOException) and the stream is left as it was. A stream
     * that buffers appends, BufferedStream, instead holds such a position back until it has
     * written that far; one that never discards data, OneFileStream, ignores every
     * position.</p>
     * 
     * @param position Stream items with a stream position strictly less than 'position' will 
     * not be used any longer.
     * @throws IOException if there is an IO error with the underlying stream.
     */
    public void pretruncate(long position) throws IOException;
    
    /**
     * Checks the bytes that the stream holds before its first position, does not read and
     * deletes at a later cut (2026-11-27, Frans; bergdb 028-66): FileStream's files before a
     * gap in its files at its open, the leftovers. 'check' gets each such piece, oldest first,
     * with its first position, its length and a reader of its bytes; if it finds one that may
     * not be deleted, this method throws an IOException that names the piece and what the
     * check found, and the stream deletes none of them. The stream deletes them only after a
     * call that found none, at the first pretruncate() at or after its first position. The
     * database's start calls it before it writes or cuts anything (RecoverableStream,
     * recover()), with a check that each piece's first meta block is the database's. A stream
     * that holds no such bytes, as by default, returns. A stream that wraps another passes
     * the call on (BufferedStream, StorageManager); one that does not leaves the wrapped
     * stream's leftovers unchecked, and so not deleted.
     * 
     * @throws IOException  if a piece may not be deleted, or a read of one fails
     */
    public default void checkLeftovers(LeftoverCheck check) throws IOException {
    }
    
    /**
     * The check of the bytes that a stream holds before its first position
     * (checkLeftovers(); bergdb 028-66).
     */
    @FunctionalInterface
    public interface LeftoverCheck {
        /**
         * null if the piece of 'length' bytes from stream position 'position' may be deleted,
         * else what the check found; 'bytes' reads the piece, at the stream positions from
         * 'position' to 'position' + 'length', as read() reads the stream.
         */
        String problem(long position, long length, PieceReader bytes) throws IOException;
    }
    
    /** Reads the bytes of a piece that checkLeftovers() gives (bergdb 028-66). */
    @FunctionalInterface
    public interface PieceReader {
        /**
         * Reads 'length' bytes at stream position 'position' into 'dest' at 'destOffset'.
         * 
         * @throws java.io.EOFException  if they are not all in the piece
         */
        void read(long position, byte[] dest, int destOffset, int length) throws IOException;
    }
    
    /**
     * Flushes the stream to the underlying storage and releases resources allocated by
     * this object.
     */
    public void close() throws IOException;
}

/*
---- Log ----
261127 checkLeftovers(): the bytes held before the first position, checked before a cut deletes them (bergdb 028-66).
261127 Class Javadoc: the front may move forward at a crash, never past a cut made before it (bergdb 028-66).
261106 read(): an unexpected exception fails the database; correct storage assumed (bergdb 019-10).
261105 Class Javadoc: the crash contract, a prefix of the bytes appended (bergdb 014-01).
261105 Removed seekFirstPos(), added for replication, which is gone (bergdb 019-04).
261104 append(): the storage says what a completed append means, forced or written (bergdb 005-47).
261024 pretruncate(): a position past the length is refused (bergdb 005-37).
130326 Added seekTo().
130322 Added "throws IOException" to close().
130319 Renamed method getSize() --> getLength().
130215 Removed setListener(), removed stop().
130116 New concurrency specification.
121018 Specified concurrency in Javadoc.
120502 Renamed to AppendOnlyStream (from WriteOnceStream).
*/
