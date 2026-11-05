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
 * contract (bergdb 014-01, section 7).</p>
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
     * @throws IllegalArgumentException if 'length' is negative or greater than dest.length.
     * @throws IOException if there is an error when reading the data.
     * @throws EOFException if there is not enough data to read.
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
     * @throws IllegalArgumentException if 'length' is less than 0 or greater than source.length.
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
     * Flushes the stream to the underlying storage and releases resources allocated by
     * this object.
     */
    public void close() throws IOException;
}

/*
---- Log ----
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
