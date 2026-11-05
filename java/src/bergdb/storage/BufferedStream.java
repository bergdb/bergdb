package bergdb.storage;

import java.io.Closeable;
import java.io.EOFException;
import java.io.IOException;

import bergdb.common.Bug;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.MemoryStream;

/**
 * An active buffer for an AppendOnlyStream that outputs the data to an
 * underlying AppendOnlyStream in a separate thread once a certain time has passed
 * or the size of the buffered data is large enough. This object is used to
 * increase throughput by "bunch-up" of small writes into larger chunks of data.
 * It is similar to Nagle's algorithm for TCP/IP traffic. The user of the object
 * must call stop() or close() to stop the internal thread.
 * 
 * <p>When nothing has been buffered for a whole buffer time, the thread waits until the
 * next append, stop() or close() (2026-10-21, bergdb item 005-14), so that an idle
 * stream does not wake it.
 * 
 * <p>A sync that waits for buffered bytes has them written at once, without waiting for
 * the buffer time: it calls flushSoon() (group commit, 2026-10-27, bergdb item 005-48).
 * The buffer time is then the longest time that bytes nobody syncs on stay buffered.
 * An append that reaches a quarter of the buffer wakes the thread too (bergdb 005-76).
 * 
 * @author Frans Lundberg
 */
public class BufferedStream implements AppendOnlyStream, Closeable {
    //
    // 1212 Frans: Implementation note: I tried to implement finalize() to stop
    // the consumer thread. This is *not possible*. Threads are never garbage collected, they are
    // always considered reachable (a thread is a garbage collector "root object"). 
    // This is true also for daemon threads. The thread "consumer" has a reference 
    // to this object. We must rely on the user of this class to call close().
    //
    private final byte[] buffer;
    private final int bufferCapacity;
    private final int tenPercentOfBufferCapacity;
    private final int twentyFivePercentOfBufferCapacity;
    private final int fiftyPercentOfBufferCapacity;
    private long streamLength; // underlying stream length
    private long totalLength; // total length: buffered in memory + stream
                              // length
    private final AppendOnlyStream stream;   // underlying stream
    private final Thread consumer;
    private long pStart; // offset for producer (absolute coordinate)
    private long cStart; // offset for consumer (absolute coordinate)
    private int cSize; // size of buffer used currently be consumer
    private int waitCount;
    private boolean stop = false;
    private boolean flushAndClose = false; // can be set to true by
                                           // flushAndStop() only.
    private IOException exception = null;
    private IOException failure = null;     // the first failed flush (bergdb 005-32)
    private IOException closeFailure = null;    // the first failed close (bergdb 015-78)
    private long pendingCut = 0;    // a pretruncate position not yet flushed; see pretruncate()
    private final int waitTime;
    private final int waitsBeforeFlush;
    private AppendListener appendListener;
    private boolean idle = false;   // the consumer waits without a timeout, see runConsumer()
    private long flushTo = 0;       // a sync waits for the bytes before it, see flushSoon()
    private final Waits roomWaits = new Waits();    // the writer's, for test reports (005-46)

    /**
     * Creates a new buffered stream with default buffer size and buffer time.
     * 
     * @param stream
     *            The append-only stream to buffer.
     */
    public BufferedStream(AppendOnlyStream stream) {
        // The defaults of the main stream (StorageManager); the buffer time was 100 ms,
        // for a rotational drive, until 2026-10-20 (bergdb item 005-13).

        this(stream, StorageManager.DEFAULT_BUFFER_SIZE, StorageManager.DEFAULT_BUFFER_TIME);
    }

    /**
     * Creates a new BufferedStream.
     * 
     * @param stream
     *            The output stream.
     * @param bufferCapacity
     *            Capacity of the buffer in bytes.
     * @param bufferTime
     *            The approximate maximum time to buffer data in milliseconds.
     */
    public BufferedStream(AppendOnlyStream stream, int bufferCapacity, int bufferTime) {
        if (stream == null) {
            throw new IllegalArgumentException("stream == null not allowed");
        }

        if (bufferCapacity < 100) {
            throw new IllegalArgumentException("bufferCapacity too small, " + bufferCapacity + ".");
        }

        if (bufferTime < 10) {
            throw new IllegalArgumentException("bufferTime too small, " + bufferTime + ".");
        }

        this.appendListener = new NullAppendListener();
        this.stream = stream;
        this.bufferCapacity = bufferCapacity;
        this.tenPercentOfBufferCapacity = bufferCapacity / 10;
        this.twentyFivePercentOfBufferCapacity = bufferCapacity / 4;
        this.fiftyPercentOfBufferCapacity = bufferCapacity / 2;
        this.waitTime = bufferTime / 4;
        this.waitsBeforeFlush = 4;
        buffer = new byte[bufferCapacity];
        streamLength = stream.getLength();
        totalLength = streamLength;

        // 2026-10-13 (java/stress/CrashTest.java): pStart and cStart were 0 here, but
        // readFromBuffer() takes stream positions. For a stream that was not empty, reads
        // of bytes still in the buffer returned other bytes.
        pStart = streamLength;
        cStart = streamLength;
        cSize = 0;

        consumer = new Thread(new Runnable() {
            public void run() {
                runConsumer();
            }
        });
        consumer.setName("BufferedStream-consumer-" + consumer.getId());
        consumer.setDaemon(true);
    }

    /**
     * Always call this method after the constructor to start the internal
     * thread that appends to the underlying stream.
     */
    public void start() {
        consumer.start();
    }
    
    public AppendOnlyStream getUnderlyingStream() {
        return stream;
    }

    private void runConsumer() {
        try {
            consume();
        } finally {
            // In a finally (2026-11-05, bergdb 015-34): an interrupt that met stop() returned
            // from consume() before the close, and the stream's files and directory lock
            // stayed open.
            closeStream();
        }
    }
    
    /** The consumer's loop: flushes what is buffered until stop() or a failed flush. */
    private void consume() {
        waitCount = 0;

        A: while (!stop) {
            synchronized (this) {
                try {
                    // 2026-10-21 (bergdb 005-14): when nothing has been buffered for a whole
                    // buffer time, wait without a timeout until append(), stop() or close()
                    // wakes us. The thread woke every bufferTime / 4 also when the stream
                    // was idle. The first flush after it comes one wait later (it came 0 to
                    // one wait later).
                    while (pStart == cStart && waitCount >= waitsBeforeFlush && !stop && !flushAndClose) {
                        idle = true;
                        wait();
                    }
                    idle = false;
                    if (stop) {
                        break A;
                    }
                    // No wait while a sync waits (bergdb 005-48), or with a quarter ready
                    // (bergdb 005-76). An append's wake may arrive during the last flush.
                    if (!syncWaits() && pStart - cStart < twentyFivePercentOfBufferCapacity) {
                        wait(waitTime);
                    }
                } catch (InterruptedException e) {
                    if (stop) {
                        return;
                    }
                    // 2026-10-27 (bergdb 005-46): BergDB's own thread goes on. An interrupt
                    // from outside, such as ThreadGroup.interrupt(), threw a Bug here, the
                    // thread ended, and the database hung: commits and syncs waited for ever.
                    continue;
                }

                // 2026-10-21 (005-14): the count stops at waitsBeforeFlush. It counted every
                // wake while nothing was written, and after 2^31 wakes (190 days at a buffer
                // time of 20 ms) it was negative: the timer flushed nothing for as long again.
                if (waitCount < waitsBeforeFlush) {
                    waitCount++;
                }

                if (!shouldFlush()) {
                    continue;
                }

                cSize = (int) (pStart - cStart);
                // Here, we have a reserved interval [cStart, cStart + cSize - 1] for the
                // consumer that the producer must respect (must not use).

                assert cSize <= bufferCapacity : "Bad cSize " + cSize + ", bufferCapacity="
                        + bufferCapacity;
                waitCount = 0;

                if (stop) {
                    break A;
                }
            }

            flushToStream();
        }
    }
    
    /**
     * Closes the underlying stream, and keeps its first failure for close() to throw
     * (2026-11-05, bergdb 015-78): the thread closes it as it ends, and dropped the
     * IOException; close() closed it again, which could work, and returned as if the close
     * had worked. An unchecked exception or an Error of the close is kept too, as the cause.
     */
    private void closeStream() {
        IOException failed = null;
        try {
            stream.close();
        } catch (IOException e) {
            failed = e;
        } catch (RuntimeException | Error e) {
            failed = new IOException("The close of the stream failed (the cause).", e);
        }
        if (failed != null) {
            synchronized (this) {
                if (closeFailure == null) closeFailure = failed;
            }
        }
    }

    private final boolean shouldFlush() {
        assert Thread.holdsLock(this);
        long sizeAvailableToFlush = pStart - cStart;
        // 2026-10-21 (bergdb 005-14): only when something is buffered, also when closing.
        // close() sets flushAndClose before stop; a consumer that woke between the two with
        // nothing buffered flushed 0 bytes, and flushToStream() then appended the whole ring
        // buffer, stale bytes, to the stream: the database failed to start ("Bad
        // transaction size"). 34 of 24,000 closes in a test (005-14, CloseRace).
        boolean result = sizeAvailableToFlush > 0 && (flushAndClose
                || sizeAvailableToFlush >= twentyFivePercentOfBufferCapacity
                || waitCount >= waitsBeforeFlush
                || flushTo > cStart);           // a sync waits (bergdb 005-48)
        return result;
    }

    /** True when a sync waits for bytes that are still buffered (bergdb 005-48). */
    private boolean syncWaits() {
        assert Thread.holdsLock(this);
        return flushTo > cStart && pStart > cStart;
    }

    /**
     * Flushes bytes from ring buffer to underlying stream. Used by consumer.
     */
    private void flushToStream() {
        // We do not flush more than half of the buffer to leave room for
        // producer to add data
        // while consumer is writing (flushing) to underlying filesystem.

        assert cSize <= buffer.length;

        final int sizeToFlush = cSize > fiftyPercentOfBufferCapacity ? fiftyPercentOfBufferCapacity
                : cSize;
        
        // 0 bytes would append the whole buffer (index2 is then index1 - 1); see shouldFlush().
        assert sizeToFlush > 0 : "bad sizeToFlush: " + sizeToFlush;

        int index1 = (int) (cStart % bufferCapacity);
        int index2 = (int) ((cStart + sizeToFlush - 1) % bufferCapacity);
        IOException ex = null;

        try {
            if (index2 >= index1) {     // Was '>', which wrote wrong bytes for a 1-byte flush.
                stream.append(buffer, index1, sizeToFlush);
            } else {
                stream.append(buffer, index1, bufferCapacity - index1);
                stream.append(buffer, 0, index2 + 1);
            }
        } catch (IOException e) {
            ex = e;
        } catch (RuntimeException | Error e) {
            ex = flushFailure(e);
        }
        
        if (ex != null) {
            // 2026-10-13: the failed bytes were counted as appended, and the
            // listener was told so; a sync then returned as if they were durable. Now the
            // stream stops, and the listener is told of the failure.
            stopAfterFailure(ex);
            return;
        }

        // 2026-10-13: a pending cut that these bytes reach is made before the
        // flush is published. It was made after, so close() could return, and close the
        // stream, before the cut (BufferedStream.testPretruncateBeyondFlushed failed now
        // and then). And before the listener, which releases syncs.
        // 2026-11-05 (bergdb 015-82): the last check for a pending cut and the publication
        // of the flush are one step under the lock, so a pretruncate() either sees the new
        // streamLength or leaves its cut for this loop. The pending cut was taken once,
        // before the publication: a cut that pretruncate() kept while the consumer made
        // that one, against the old streamLength, waited for a next flush, and close()
        // returned without it.

        final long flushedLength = streamLength + sizeToFlush;
        long myStreamSize;

        while (true) {
            long cut;
            synchronized (this) {
                if (pendingCut > 0 && pendingCut <= flushedLength) {
                    cut = pendingCut;
                    pendingCut = 0;
                } else {
                    // this.exception set only when not set before.
                    // This method is called by flushAndClose() which sets
                    // this.exception before
                    // flushToStream() is called.

                    if (this.exception == null) {
                        this.exception = ex;
                    }

                    streamLength += sizeToFlush;
                    cStart += sizeToFlush;
                    cSize -= sizeToFlush;

                    myStreamSize = streamLength;

                    notifyAll();
                    // notifies producer thread or caller of flushAndStop() that data
                    // has been flushed.
                    break;
                }
            }

            try {
                stream.pretruncate(cut);
            } catch (IOException e) {
                // A failed deletion/directory force is a storage failure too.
                // Do not publish this flush or release durability waiters.
                stopAfterFailure(e);
                return;
            } catch (RuntimeException | Error e) {
                stopAfterFailure(flushFailure(e));
                return;
            }
        }

        appendListener.dataAppended(myStreamSize);
    }

    /**
     * Anything else that a flush throws stops the stream too (2026-10-24, bergdb 005-32): an
     * Error, such as an assertion of FileStream, ended the thread without telling the
     * listener, and every later sync waited for ever.
     */
    private static IOException flushFailure(Throwable e) {
        return new IOException("The flush failed (the cause).", e);
    }

    private void stopAfterFailure(IOException failure) {
        synchronized (this) {
            if (this.exception == null) this.exception = failure;
            if (this.failure == null) this.failure = failure;
            stop = true;
            notifyAll();
        }
        appendListener.appendFailed(failure);
    }

    public synchronized long getLength() {
        return totalLength;
    }

    public long getFirstPos() {
        return stream.getFirstPos();
    }

    public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
        //
        // Different cases.
        // 1. Out of bounds: position + length > totalSize. --> EOFException
        // 2. All in stream. position + length < streamSize.
        // 3. All in buffer. position + length >= streamSize AND <= totalSize
        // 4. One part in buffer, one part in stream.
        //
        // Reads from buffer are made in synchronized block; it is very fast.
        //

        Util.checkRange(dest, destOffset, length);     // Bergdb 019-02: was an assert.

        long pos1 = position;
        long pos2 = position + length - 1;
        long streamBytesToRead;
        long bufferBytesToRead;

        synchronized (this) {
            if (this.exception != null) {
                throw new IOException(
                        "Cannot read from the failed stream, fail exception message: "
                                + exception.getMessage());
            }

            // ">=" since 2026-10-21 (bergdb 005-25): pos2 is the last byte read, and
            // totalLength - 1 the last byte there is. A read of the byte after the end gave
            // a stale byte of the ring buffer. EOFException, as AppendOnlyStream.read()'s
            // Javadoc says, since 2026-11-05 (bergdb 015-83); it was an IOException.
            if (pos2 >= totalLength) {
                throw new EOFException("Cannot read " + length + " bytes at position " + position
                        + ", stream size is " + totalLength + ".");
            }

            if (pos1 >= streamLength) {
                // only from buffer
                streamBytesToRead = 0;
                readFromBuffer(position, dest, destOffset, length);
            } else if (pos2 < streamLength) {
                // only from stream
                streamBytesToRead = pos2 - pos1 + 1;
            } else {
                // from stream and buffer
                streamBytesToRead = streamLength - pos1;
                bufferBytesToRead = length - streamBytesToRead;
                readFromBuffer(position + streamBytesToRead, dest,
                        (int) (destOffset + streamBytesToRead), (int) bufferBytesToRead);
            }
        }

        assert streamBytesToRead <= Integer.MAX_VALUE;
        assert streamBytesToRead >= 0;

        if (streamBytesToRead > 0) {
            stream.read(position, dest, destOffset, (int) streamBytesToRead);
        }
    }

    private void readFromBuffer(long position, byte[] dest, int destOffset, int length) {
        assert Thread.holdsLock(this);

        if (length == 0) {
            // Special case treated separately.
            return;
        }

        int index1 = (int) (position % bufferCapacity);
        int index2 = (int) ((position + length - 1) % bufferCapacity);

        if (index2 >= index1) {
            // assert index1 < buffer.length;
            // assert index1 >= 0;
            // assert destOffset < dest.length;
            // assert destOffset >= 0;
            int lengthToCopy = index2 - index1 + 1;
            // assert index1 + lengthToCopy <= buffer.length;
            // assert destOffset + lengthToCopy <= dest.length;
            System.arraycopy(buffer, index1, dest, destOffset, lengthToCopy);
        } else {
            // assert index2 < index1;
            // assert index1 < buffer.length;
            // assert index1 >= 0;
            // assert destOffset < dest.length;
            // assert destOffset >= 0;
            int lengthToCopy = bufferCapacity - index1;
            // assert index1 + lengthToCopy <= buffer.length;
            // assert destOffset + lengthToCopy <= dest.length : "destOffset=" +
            // destOffset
            // + ", lengthToCopy=" + lengthToCopy + ", dest.length=" +
            // dest.length
            // + ", index1=" + index1 + ", index2=" + index2 + ", length=" +
            // length;

            System.arraycopy(buffer, index1, dest, destOffset, bufferCapacity - index1);
            destOffset += bufferCapacity - index1;

            assert destOffset < dest.length;
            lengthToCopy = index2 + 1;
            assert lengthToCopy <= buffer.length;
            assert destOffset + lengthToCopy <= dest.length;

            System.arraycopy(buffer, 0, dest, destOffset, index2 + 1);
        }
    }

    private int availableBufferSize() {
        assert Thread.holdsLock(this);
        assert pStart - cStart <= Integer.MAX_VALUE;
        int sizeUsed = (int) (pStart - cStart);
        assert sizeUsed >= 0;
        int available = bufferCapacity - sizeUsed;
        return available;
    }

    /**
     * This method may return before the data has been written to the underlying
     * stream. If that is the case, the AppendListener will not be notified of
     * until after this method returns.
     */
    public void append(byte[] source, int sourceOffset, int length) throws IOException {
        boolean interrupted = false;
        long waitStart = 0;

        try {
            synchronized (this) {
                if (this.exception != null) {
                    throw exception;
                }
                // Refused before anything changes (2026-11-05, bergdb 015-79): a negative
                // length returned as an append of nothing, and StorageManager lowered its
                // length by it. A length past the array, an array exception at the copy, too
                // (bergdb 019-02).
                Util.checkRange(source, sourceOffset, length);

                while (length > 0) {
                    int available = availableBufferSize();
                    if (available < length && available < tenPercentOfBufferCapacity) {
                        // The thread that makes room has stopped: after stop() or a failed flush
                        // (2026-10-24, bergdb 005-35). The writer waited here for ever, with the
                        // database's write lock, so a failing disk hung the database.
                        if (stop) {
                            throw new IOException("The stream has stopped while an append waited "
                                    + "for room in its buffer.", failure);
                        }
                        if (waitStart == 0) {
                            waitStart = System.nanoTime();
                        }
                        try {
                            wait(); // wait for consumer to write to output stream
                        } catch (InterruptedException e) {
                            // 2026-10-27 (bergdb 005-46): not interruptible. The interrupt threw
                            // an IOException, which failed the storage, and so the database: the
                            // wait comes after the transaction's go point.
                            interrupted = true;
                        }
                    } else {
                        int len = length <= available ? length : available;
                        long bufferedBefore = pStart - cStart;
                        appendToBuffer(source, sourceOffset, len);
                        if (idle || (bufferedBefore < twentyFivePercentOfBufferCapacity
                                && pStart - cStart >= twentyFivePercentOfBufferCapacity)) {
                            notifyAll();    // Idle (005-14), or one wake per crossing (005-76).
                        }
                        length -= len;
                        sourceOffset += len;
                    }
                }
                if (waitStart != 0) {
                    roomWaits.add(System.nanoTime() - waitStart);
                }
            }
        } finally {
            if (interrupted) {
                Thread.currentThread().interrupt();
            }
        }
    }
    
    /**
     * Has the thread write what is buffered now, without waiting for the buffer time, if a
     * byte before position 'length' is still buffered; returns at once (2026-10-27, bergdb
     * 005-48, group commit). A sync that waits for those bytes calls it. The thread writes
     * what is buffered in one flush (an append and its force, of at most half the buffer);
     * bytes that arrive meanwhile wait in the buffer, and if a sync waits for them too, the
     * next flush starts when this one ends. So a sync waits for about one force at low load,
     * and under load the force paces the groups. Before, a sync waited for the timer, about
     * a buffer time. The bytes written do not change, only where one append ends and the
     * next begins.
     */
    public synchronized void flushSoon(long length) {
        if (length > flushTo) {
            flushTo = length;
            notifyAll();    // Wakes the consumer, waiting or idle.
        }
    }
    
    /**
     * The writer's waits for room in the buffer since the last call, as a line for test
     * reports, and starts counting again (2026-10-27, bergdb 005-46). Such a wait is the
     * disk's limit, not BergDB's: it does not count against item 009's pause target, but a
     * report notes it (Frans, 2026-10-27).
     */
    public String takeRoomWaits() {
        return roomWaits.take();
    }

    private void appendToBuffer(byte[] source, int offset, int len) {
        assert Thread.holdsLock(this);

        int index1 = (int) (pStart % bufferCapacity);
        int index2 = (int) ((pStart + len - 1) % bufferCapacity);

        if (index2 >= index1) {
            System.arraycopy(source, offset, buffer, index1, index2 - index1 + 1);
        } else {
            System.arraycopy(source, offset, buffer, index1, bufferCapacity - index1);
            offset += bufferCapacity - index1;
            System.arraycopy(source, offset, buffer, 0, index2 + 1);
        }

        this.pStart += len;
        this.totalLength += len;
    }

    /**
     * Pretruncates the underlying stream. A position past the bytes flushed so far is kept
     * and applied after the flush that reaches it.
     * 2026-10-13 (testPretruncateBeyondFlushed): the position was passed on at
     * once, also when it was still in the buffer; MemoryStream then failed, and the
     * underlying stream could be cut past its end.
     */
    public void pretruncate(long position) throws IOException {
        synchronized (this) {
            if (position > streamLength) {
                pendingCut = Math.max(pendingCut, position);
                return;
            }
        }
        stream.pretruncate(position);
    }
    
    public void setAppendListener(AppendListener appendListener) {
        if (appendListener == null) {
            throw new IllegalArgumentException("appendListener == null not allowed");
        }
        this.appendListener = appendListener;
    }

    /**
     * Writes what is buffered, stops the thread and closes the underlying stream. Returns when
     * the thread has ended, also after a flush that failed, and then throws that failure
     * (2026-10-24, bergdb 005-32): it waited for ever, as the buffer never empties after a
     * failed flush. After stop(), it writes nothing more, and returns when the thread has
     * ended; it returned at once. Every call throws the failure, of a flush, else of the
     * first close of the underlying stream (by the thread or by close(); bergdb 015-78).
     * 
     * @throws IOException  If a flush failed, or a close of the underlying stream.
     */
    public void close() throws IOException {
        // Not interruptible (2026-10-27, bergdb 005-46): an interrupt returned at once, before
        // the buffer was written and the stream closed, and the consumer thread stayed, waking
        // every wait time, with its files open. The interrupt flag is set again at the end.
        boolean interrupted = false;
        synchronized (this) {
            this.flushAndClose = true;
            notifyAll();    // Wakes an idle consumer (005-14).
            if (this.exception == null) {
                this.exception = new IOException("Stream being closed by flushAndClose()");
            }

            while (pStart - cStart > 0 && !stop) {
                try {
                    wait(); // Waiting for consumer to flush to output stream
                } catch (InterruptedException e) {
                    interrupted = true;
                }
            }
        }

        stop();

        // The thread closes the stream as it ends. Not from the thread itself: the listener
        // of a failed flush closes this stream (StorageManager.handleStreamException).
        if (Thread.currentThread() != consumer) {
            while (true) {
                try {
                    consumer.join();
                    break;
                } catch (InterruptedException e) {
                    interrupted = true;
                }
            }
        }
        if (interrupted) {
            Thread.currentThread().interrupt();
        }

        closeStream();
        
        IOException failed;
        synchronized (this) {
            failed = failure != null ? failure : closeFailure;
        }
        if (failed != null) {
            throw failed;
        }
    }

    /**
     * Eventually stops thread and closes stream. This method returns
     * immediately. What is still buffered is not written; close() writes it. A writer that
     * waits for room in the buffer gets an IOException (bergdb 005-35).
     */
    public void stop() {
        synchronized (this) {
            if (this.exception == null) {
                this.exception = new IOException("Stream being stopped.");
            }
            this.stop = true;
            notifyAll();    // Wakes an idle consumer (005-14).
        }
    }
    
    /**
     * Waits for test reports (bergdb 005-46): how many, in all, the longest, and the five
     * longest with the JVM uptime at their end. Thread-safe.
     */
    static final class Waits {
        private long count, totalNanos;
        private final long[] longest = new long[5];         // nanoseconds, longest first
        private final long[] longestUptime = new long[5];   // milliseconds

        synchronized void add(long nanos) {
            count++;
            totalNanos += nanos;
            for (int i = 0; i < longest.length; i++) {
                if (nanos > longest[i]) {
                    System.arraycopy(longest, i, longest, i + 1, longest.length - i - 1);
                    System.arraycopy(longestUptime, i, longestUptime, i + 1, longest.length - i - 1);
                    longest[i] = nanos;
                    longestUptime[i] = java.lang.management.ManagementFactory.getRuntimeMXBean()
                            .getUptime();
                    break;
                }
            }
        }

        /** A line, and the count starts again. */
        synchronized String take() {
            StringBuilder sb = new StringBuilder();
            sb.append(String.format("waits for room in the write buffer %d, %.1f ms in all",
                    count, totalNanos / 1e6));
            if (count > 0) {
                sb.append("; longest at uptime");
                for (int i = 0; i < longest.length && longest[i] > 0; i++) {
                    sb.append(String.format(" %.3fs (%.1f ms)", longestUptime[i] / 1e3,
                            longest[i] / 1e6));
                }
            }
            count = 0;
            totalNanos = 0;
            java.util.Arrays.fill(longest, 0);
            java.util.Arrays.fill(longestUptime, 0);
            return sb.toString();
        }
    }
    
    // ======== Test ========

    /** bergdb 005-76: reaching a quarter wakes a consumer in its timed wait. */
    @Nano
    public static void testQuarterWakesConsumer() throws Exception {
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 1024, 60000);
        java.util.concurrent.CountDownLatch flushed = new java.util.concurrent.CountDownLatch(1);
        b.setAppendListener(new AppendListener() {
            public void dataAppended(long length) { flushed.countDown(); }
            public void appendFailed(IOException e) {}
        });
        b.start();
        try {
            long deadline = System.nanoTime() + 2000000000L;
            while (b.consumer.getState() != Thread.State.TIMED_WAITING) {
                Assert.assertTrue("consumer did not enter its timed wait",
                        System.nanoTime() < deadline);
                Thread.sleep(1);
            }
            b.append(new byte[255], 0, 255);   // Just below the quarter.
            Assert.assertEquals(0, m.getLength());
            b.append(new byte[] {42}, 0, 1);   // Exactly a quarter, without a sync.
            Assert.assertTrue("the quarter-full append did not wake the consumer",
                    flushed.await(2, java.util.concurrent.TimeUnit.SECONDS));
            byte[] bytes = new byte[256];
            m.read(0, bytes, 0, bytes.length);
            Assert.assertEquals((byte) 42, bytes[255]);
        } finally {
            b.close();
        }
    }

    /** bergdb 005-76: bytes arriving during a flush need no new threshold crossing. */
    @Nano
    public static void testQuarterBacklogDoesNotWait() throws Exception {
        java.util.concurrent.CountDownLatch entered = new java.util.concurrent.CountDownLatch(1);
        java.util.concurrent.CountDownLatch release = new java.util.concurrent.CountDownLatch(1);
        java.util.concurrent.CountDownLatch flushed = new java.util.concurrent.CountDownLatch(2);
        MemoryStream m = new MemoryStream() {
            @Override public void append(byte[] source, int offset, int length) throws IOException {
                if (getLength() == 0) {
                    entered.countDown();
                    try {
                        if (!release.await(2, java.util.concurrent.TimeUnit.SECONDS)) {
                            throw new IOException("test did not release the first flush");
                        }
                    } catch (InterruptedException e) {
                        throw new IOException(e);
                    }
                }
                super.append(source, offset, length);
            }
        };
        BufferedStream b = new BufferedStream(m, 1024, 60000);
        b.setAppendListener(new AppendListener() {
            public void dataAppended(long length) { flushed.countDown(); }
            public void appendFailed(IOException e) {}
        });
        b.append(new byte[512], 0, 512);
        b.flushSoon(512);   // Start the first flush also on the code before the fix.
        b.start();
        try {
            Assert.assertTrue("first flush did not start",
                    entered.await(2, java.util.concurrent.TimeUnit.SECONDS));
            b.append(new byte[256], 0, 256);   // Above a quarter throughout this append.
            release.countDown();
            Assert.assertTrue("the quarter-full backlog waited for the timer",
                    flushed.await(2, java.util.concurrent.TimeUnit.SECONDS));
            Assert.assertEquals(768, m.getLength());
        } finally {
            release.countDown();
            b.close();
        }
    }

    /** bergdb 005-76: a writer faster than the timer can drain need not wait for room. */
    @Nano
    public static void testQuarterAvoidsRoomWaits() throws Exception {
        MemoryStream m = new MemoryStream() {
            @Override public void append(byte[] source, int offset, int length) throws IOException {
                try {
                    Thread.sleep(3);   // A small force latency, without a real disk.
                } catch (InterruptedException e) {
                    throw new IOException(e);
                }
                super.append(source, offset, length);
            }
        };
        BufferedStream b = new BufferedStream(m, 256 * 1024, 4000);
        b.start();
        try {
            byte[] bytes = new byte[1024];
            for (int i = 0; i < 512; i++) {
                java.util.Arrays.fill(bytes, (byte) i);
                b.append(bytes, 0, bytes.length);
                Thread.sleep(1);
            }
            String waits = b.takeRoomWaits();
            Assert.assertTrue(waits, waits.startsWith("waits for room in the write buffer 0,"));
        } finally {
            b.close();
        }
        Assert.assertEquals(512 * 1024, m.getLength());
        byte[] bytes = new byte[512 * 1024];
        m.read(0, bytes, 0, bytes.length);
        for (int i = 0; i < bytes.length; i++) {
            Assert.assertEquals((byte) (i / 1024), bytes[i]);
        }
    }

    @Nano
    public static void test1() throws IOException, InterruptedException {
        // Note, test relies on timing. Not deterministic.
        MemoryStream m = new MemoryStream();
        @SuppressWarnings("resource")
        BufferedStream b = new BufferedStream(m, 1000, 20);
        b.start();

        try {
            byte[] bytes = new byte[] { 1, 2 };
            b.append(bytes, 0, bytes.length);
            Assert.assertEquals(0, m.getLength());
            Thread.sleep(30);
            if (m.getLength() == 0) {
                Thread.sleep(60);
            }
            Assert.assertEquals(2, m.getLength());
        } finally {
            b.stop();
        }
    }

    /**
     * Regression test for a bug found 2026-10-13: on a stream that was not empty,
     * a read of bytes still in the buffer returned other bytes.
     */
    @Nano
    public static void testReadFromBufferOfNonEmptyStream() throws IOException {
        MemoryStream m = new MemoryStream();
        m.append(new byte[150], 0, 150);
        BufferedStream b = new BufferedStream(m, 100, 1000);   // Not started: no flush.
        
        byte[] bytes = new byte[] {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
        b.append(bytes, 0, bytes.length);
        byte[] dest = new byte[bytes.length];
        b.read(150, dest, 0, dest.length);
        Assert.assertTrue(java.util.Arrays.equals(bytes, dest));
        
        dest = new byte[12];
        b.read(148, dest, 0, dest.length);   // From the stream and the buffer.
        Assert.assertEquals((byte) 0, dest[1]);
        Assert.assertEquals((byte) 1, dest[2]);
        Assert.assertEquals((byte) 10, dest[11]);
    }

    /** Regression test for bergdb 005-25: a read one byte past the end gave a stale byte. */
    @Nano
    public static void testReadOneBytePastEnd() throws IOException {
        BufferedStream b = new BufferedStream(new MemoryStream(), 100, 1000);   // not started
        b.append(new byte[] {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}, 0, 10);
        byte[] d = new byte[2];
        b.read(8, d, 0, 2);
        Assert.assertEquals((byte) 10, d[1]);
        try {
            b.read(9, d, 0, 2);
            throw new AssertionError("a read past the end succeeded");
        } catch (IOException e) {
            // Expected.
        }
        try {
            b.read(10, d, 0, 1);
            throw new AssertionError("a read past the end succeeded");
        } catch (IOException e) {
            // Expected.
        }
        b.append(new byte[] {11}, 0, 1);
        b.read(10, d, 0, 1);
        Assert.assertEquals((byte) 11, d[0]);
    }
    
    /**
     * Regression test for a bug found 2026-10-13: a pretruncate position that was
     * still in the buffer was passed on to the underlying stream at once.
     */
    @Nano
    public static void testPretruncateBeyondFlushed() throws IOException {
        CutStream c = new CutStream();      // Refuses a cut past its end.
        BufferedStream b = new BufferedStream(c, 1000, 10);
        b.append(new byte[300], 0, 300);
        b.pretruncate(200);                 // Not started: nothing flushed.
        Assert.assertEquals(0L, c.getCut());
        b.start();
        b.close();
        Assert.assertEquals(200L, c.getCut());
    }

    /**
     * Regression test for bergdb 015-82 (016-06's R5-F7): a cut that pretruncate() kept while
     * the consumer made the pending cut of a flush, against the old streamLength, was not
     * made by that flush, and close() returned without it (the last cut 200, not 300).
     */
    @Nano
    public static void testPendingCutDuringACut() throws Exception {
        java.util.concurrent.CountDownLatch entered = new java.util.concurrent.CountDownLatch(1);
        java.util.concurrent.CountDownLatch release = new java.util.concurrent.CountDownLatch(1);
        java.util.concurrent.CountDownLatch flushed = new java.util.concurrent.CountDownLatch(1);
        java.util.concurrent.atomic.AtomicLong lastCut = new java.util.concurrent.atomic.AtomicLong();
        MemoryStream m = new MemoryStream() {
            @Override public void pretruncate(long position) {
                lastCut.accumulateAndGet(position, Math::max);
                if (position == 200) {      // The first cut waits until the test releases it.
                    entered.countDown();
                    try {
                        release.await(2, java.util.concurrent.TimeUnit.SECONDS);
                    } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                }
                super.pretruncate(position);
            }
        };
        m.append(new byte[100], 0, 100);
        BufferedStream b = new BufferedStream(m, 1000, 10);
        b.setAppendListener(new AppendListener() {
            public void dataAppended(long length) { flushed.countDown(); }
            public void appendFailed(IOException e) {}
        });
        b.append(new byte[300], 0, 300);
        b.pretruncate(200);                 // Not started: kept for the flush.
        b.start();
        try {
            Assert.assertTrue("the first cut did not start",
                    entered.await(2, java.util.concurrent.TimeUnit.SECONDS));
            b.pretruncate(300);             // Within the bytes of the flush that is cutting.
            release.countDown();
            Assert.assertTrue("the flush was not published",
                    flushed.await(2, java.util.concurrent.TimeUnit.SECONDS));
        } finally {
            release.countDown();
            b.close();
        }
        Assert.assertEquals(400L, m.getLength());
        Assert.assertEquals(300L, lastCut.get());
    }

    /**
     * 2026-10-21 (bergdb item 005-14): after a buffer time with nothing buffered, the
     * consumer waits without a timeout (WAITING, not TIMED_WAITING), and an append wakes it.
     */
    @Nano
    public static void testIdleConsumerWaitsForAppend() throws IOException, InterruptedException {
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 1000, 10);
        b.start();
        try {
            b.append(new byte[] { 1, 2 }, 0, 2);
            awaitIdle(b);
            Assert.assertEquals(2, m.getLength());
            b.append(new byte[] { 3 }, 0, 1);
            long t0 = System.nanoTime();
            while (m.getLength() < 3) {
                Assert.assertTrue("an append to an idle stream was not flushed in 2 s",
                        System.nanoTime() - t0 < 2000000000L);
                Thread.sleep(1);
            }
            awaitIdle(b);
        } finally {
            b.close();
        }
    }

    /** 2026-10-21 (005-14): stop() and close() end an idle consumer. */
    @Nano
    public static void testStopAndCloseEndIdleConsumer() throws IOException, InterruptedException {
        for (int close = 0; close < 2; close++) {
            MemoryStream m = new MemoryStream();
            BufferedStream b = new BufferedStream(m, 1000, 10);
            b.start();
            b.append(new byte[] { 1 }, 0, 1);
            awaitIdle(b);
            if (close == 1) {
                b.close();
            } else {
                b.stop();
            }
            b.consumer.join(2000);
            Assert.assertTrue(!b.consumer.isAlive());
            Assert.assertEquals(1, m.getLength());
        }
    }

    /**
     * 2026-10-21 (005-14): the wait count stops at waitsBeforeFlush. It counted every wake
     * while nothing was written, and overflowed after 2^31 wakes.
     */
    @Nano
    public static void testWaitCountStaysSmall() throws IOException, InterruptedException {
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 1000, 10);
        b.start();
        try {
            Thread.sleep(50);       // About 20 wakes of 2 ms (3 ms on macOS) before the fix.
            synchronized (b) {
                Assert.assertTrue("waitCount " + b.waitCount, b.waitCount <= b.waitsBeforeFlush);
            }
        } finally {
            b.close();
        }
    }

    /**
     * 2026-10-21 (005-14): no flush when nothing is buffered, also when closing. A flush of
     * 0 bytes appended the whole ring buffer to the stream.
     */
    @Nano
    public static void testNoFlushOfNothingWhenClosing() throws IOException {
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 100, 10);     // Not started: the test is the consumer.
        b.append(new byte[] { 1, 2, 3, 4, 5, 6, 7 }, 0, 7);
        synchronized (b) {
            b.flushAndClose = true;
            Assert.assertTrue(b.shouldFlush());
            b.cSize = (int) (b.pStart - b.cStart);
        }
        b.flushToStream();
        Assert.assertEquals(7, m.getLength());
        synchronized (b) {
            Assert.assertTrue(!b.shouldFlush());
        }
    }

    /** Waits until the consumer waits without a timeout; fails after 2 s. */
    private static void awaitIdle(BufferedStream b) throws InterruptedException {
        long t0 = System.nanoTime();
        while (b.consumer.getState() != Thread.State.WAITING) {
            Assert.assertTrue("the consumer of an idle stream is " + b.consumer.getState()
                    + ", not WAITING", System.nanoTime() - t0 < 2000000000L);
            Thread.sleep(1);
        }
    }

    @Nano
    public static void testClose() throws IOException, InterruptedException {
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 1000, 20);
        b.start();

        try {
            byte[] bytes = new byte[] { 1, 2 };
            b.append(bytes, 0, bytes.length);
            Assert.assertEquals(0, m.getLength());
        } finally {
            b.close();
        }

        Assert.assertEquals(2, m.getLength());
    }

    @Nano
    public static void testWriteAfterClose1() throws IOException, InterruptedException {
        MemoryStream m = new MemoryStream();
        @SuppressWarnings("resource")
        BufferedStream b = new BufferedStream(m, 1000, 20);
        b.start();

        byte[] bytes = new byte[] { 1, 2 };
        b.append(bytes, 0, bytes.length);
        b.stop();

        IOException ex = null;
        try {
            b.append(new byte[] { 3 }, 0, 1);
        } catch (IOException e) {
            ex = e;
        }

        Assert.assertTrue(ex != null);
    }

    @Nano
    public static void testWriteAfterClose2() throws IOException, InterruptedException {
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 1000, 20);
        b.start();

        byte[] bytes = new byte[] { 1, 2 };
        b.append(bytes, 0, bytes.length);
        b.close();

        IOException ex = null;
        try {
            b.append(new byte[] { 3 }, 0, 1);
        } catch (IOException e) {
            ex = e;
        }

        Assert.assertTrue(ex != null);
    }

    @Nano
    public static void testReadAfterClose1() throws IOException, InterruptedException {
        MemoryStream m = new MemoryStream();
        @SuppressWarnings("resource")
        BufferedStream b = new BufferedStream(m, 1000, 20);
        b.start();

        byte[] bytes = new byte[] { 1, 2 };
        b.append(bytes, 0, bytes.length);
        b.stop();

        IOException ex = null;
        try {
            byte[] readBuffer = new byte[1];
            b.read(0, readBuffer, 0, readBuffer.length);
        } catch (IOException e) {
            ex = e;
        }

        Assert.assertTrue(ex != null);
    }

    @Nano
    public static void testReadAfterClose2() throws IOException, InterruptedException {
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 1000, 20);
        b.start();

        byte[] bytes = new byte[] { 1, 2 };
        b.append(bytes, 0, bytes.length);
        b.close();

        IOException ex = null;
        try {
            byte[] readBuffer = new byte[1];
            b.read(0, readBuffer, 0, readBuffer.length);
        } catch (IOException e) {
            ex = e;
        }

        Assert.assertTrue(ex != null);
    }

    @Nano
    public static void testWriteMuch() throws IOException {
        // Writes more then buffer size.
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 1000, 20);
        b.start();
        byte[] bytes = new byte[3000];
        b.append(bytes, 0, bytes.length);
        b.close();
        Assert.assertEquals(3000, m.getLength());
    }

    @Nano
    public static void testWriteLittle() throws IOException {
        // Writes one byte at a time.
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 100, 20);
        b.start();
        byte[] bytes = new byte[1];

        for (int i = 0; i < 222; i++) {
            bytes[0] = (byte) i;
            b.append(bytes, 0, bytes.length);
        }
        b.close();
        Assert.assertEquals(222, m.getLength());
    }

    @Nano
    public static void testWriteZero() throws IOException {
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 100, 20);
        b.start();
        byte[] bytes = new byte[0];

        for (int i = 0; i < 22; i++) {
            b.append(bytes, 0, bytes.length);
        }
        b.close();
        Assert.assertEquals(0, m.getLength());
    }

    /**
     * Regression test for bergdb 005-32: close() waited for ever when the last flush failed,
     * as the buffer never empties then. Now it returns when the thread has ended, and throws
     * the failure. An Error in a flush fails the stream as an IOException does, and the
     * listener is told; before, it ended the thread without a word.
     */
    @Nano
    public static void testCloseAfterFailedFlush() throws Exception {
        for (int i = 0; i < 2; i++) {
            final FailingStream failing = new FailingStream();
            failing.failure = i == 0 ? new IOException("the disk fails")
                    : new AssertionError("an assertion of the stream");
            final BufferedStream b = new BufferedStream(failing, 1000, 20);
            final IOException[] told = new IOException[1];
            b.setAppendListener(new AppendListener() {
                public void dataAppended(long length) {}
                public void appendFailed(IOException e) {
                    told[0] = e;
                }
            });
            b.start();
            b.append(new byte[100], 0, 100);
            final Throwable[] thrown = new Throwable[1];
            Thread t = new Thread() {
                public void run() {
                    try {
                        b.close();
                    } catch (Throwable e) {
                        thrown[0] = e;
                    }
                }
            };
            t.setDaemon(true);
            t.start();
            t.join(5000);
            Assert.assertFalse("close() returns, " + i, t.isAlive());
            Assert.assertTrue("it throws the failure: " + thrown[0], thrown[0] instanceof IOException);
            Assert.assertTrue("the listener is told, " + i, told[0] != null);
            if (i == 1) {
                Assert.assertTrue("the Error is the cause", told[0].getCause() instanceof AssertionError);
            }
            Assert.assertFalse("the thread has ended, " + i, b.consumer.isAlive());
        }
    }
    
    /** A MemoryStream whose appends throw 'failure' while it is set (bergdb 005-32). */
    private static class FailingStream implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        volatile Throwable failure = null;
        
        public long getLength() {
            return inner.getLength();
        }
        
        public long getFirstPos() {
            return inner.getFirstPos();
        }
        
        public void read(long position, byte[] dest, int destOffset, int length) 
                throws IOException {
            inner.read(position, dest, destOffset, length);
        }
        
        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            Throwable f = failure;
            if (f instanceof IOException) {
                throw (IOException) f;
            } else if (f instanceof Error) {
                throw (Error) f;
            } else if (f instanceof RuntimeException) {
                throw (RuntimeException) f;
            }
            inner.append(source, sourceOffset, length);
        }
        
        public void pretruncate(long position) throws IOException {
            inner.pretruncate(position);
        }
        
        public void close() {
            inner.close();
        }
    }
    
    /** A stream whose appends wait while 'hold' is set; for the interrupt tests (005-46). */
    private static class HeldStream extends FailingStream {
        volatile java.util.concurrent.CountDownLatch hold;
        final java.util.concurrent.CountDownLatch held = new java.util.concurrent.CountDownLatch(1);
        
        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            java.util.concurrent.CountDownLatch h = hold;
            if (h != null) {
                held.countDown();
                try {
                    h.await();
                } catch (InterruptedException e) {
                    throw new IOException(e);
                }
            }
            super.append(source, sourceOffset, length);
        }
    }
    
    /**
     * Regression test for bergdb 005-46: a writer that waited for room in the buffer threw an
     * IOException when its thread was interrupted, which failed the storage and the database.
     * Now the wait goes on, the append completes, and the interrupt flag is set after it.
     */
    @Nano
    public static void testAppendWaitIgnoresInterrupt() throws Exception {
        HeldStream m = new HeldStream();
        m.hold = new java.util.concurrent.CountDownLatch(1);
        final BufferedStream b = new BufferedStream(m, 1000, 10);
        b.start();
        try {
            b.append(new byte[900], 0, 900);
            Assert.assertTrue(m.held.await(5, java.util.concurrent.TimeUnit.SECONDS));
            final Throwable[] failure = new Throwable[1];
            final boolean[] flag = new boolean[1];
            Thread writer = new Thread(new Runnable() {
                public void run() {
                    Thread.currentThread().interrupt();
                    try {
                        b.append(new byte[900], 0, 900);
                    } catch (Throwable e) {
                        failure[0] = e;
                    }
                    flag[0] = Thread.interrupted();
                }
            });
            writer.start();
            Thread.sleep(100);
            Assert.assertTrue("the writer did not wait for room", writer.isAlive());
            m.hold.countDown();
            writer.join(5000);
            Assert.assertTrue(failure[0] == null);
            Assert.assertTrue("the interrupt flag was lost", flag[0]);
            Assert.assertTrue(b.takeRoomWaits().startsWith("waits for room in the write buffer 1,"));
        } finally {
            m.hold.countDown();
            b.close();
        }
        Assert.assertEquals(1800, m.getLength());
    }
    
    /**
     * Regression test for bergdb 005-46: close() by an interrupted thread returned at once,
     * before the buffer was written and the stream closed, and the consumer thread stayed.
     * Now close() waits, and the interrupt flag is set after it.
     */
    @Nano
    public static void testCloseIgnoresInterrupt() throws Exception {
        HeldStream m = new HeldStream();
        m.hold = new java.util.concurrent.CountDownLatch(1);
        BufferedStream b = new BufferedStream(m, 1000, 10);
        b.start();
        b.append(new byte[500], 0, 500);
        Assert.assertTrue(m.held.await(5, java.util.concurrent.TimeUnit.SECONDS));
        new Thread(new Runnable() {
            public void run() {
                try {
                    Thread.sleep(100);
                } catch (InterruptedException e) {
                    // empty
                }
                m.hold.countDown();
            }
        }).start();
        Thread.currentThread().interrupt();
        try {
            b.close();
            Assert.assertTrue("the interrupt flag was lost", Thread.currentThread().isInterrupted());
        } finally {
            Thread.interrupted();
        }
        Assert.assertEquals(500, m.getLength());
        Assert.assertTrue("the consumer thread stayed", !b.consumer.isAlive());
    }
    
    /**
     * Regression test for bergdb 005-46: an interrupt of the consumer thread from outside
     * (ThreadGroup.interrupt()) threw a Bug there, the thread ended, and the stream hung. Now
     * the thread goes on.
     */
    @Nano
    public static void testConsumerIgnoresInterrupt() throws Exception {
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 1000, 10);
        b.start();
        try {
            for (int i = 0; i < 20; i++) {
                b.consumer.interrupt();
                b.append(new byte[] {(byte) i}, 0, 1);
                Thread.sleep(2);
            }
            long t0 = System.nanoTime();
            while (m.getLength() < 20) {
                Assert.assertTrue("not written in 2 s", System.nanoTime() - t0 < 2000000000L);
                Thread.sleep(1);
            }
            Assert.assertTrue(b.consumer.isAlive());
        } finally {
            b.close();
        }
    }
    
    /**
     * Regression test for bergdb 015-34 (reviews R3-F6, R5-F2): a consumer interrupted as
     * stop() comes closes the underlying stream as it ends. The interrupt takes the consumer
     * out of its idle wait, and it must take the monitor again, which the test holds until
     * stop() has run; before, the consumer then returned without closing the stream: a
     * FileStream's files and its directory lock stayed open until the JVM ended.
     */
    @Nano
    public static void testStopWhileInterruptedClosesStream() throws Exception {
        final java.util.concurrent.atomic.AtomicInteger closes =
                new java.util.concurrent.atomic.AtomicInteger();
        MemoryStream m = new MemoryStream() {
            @Override public void close() {
                closes.incrementAndGet();
                super.close();
            }
        };
        BufferedStream b = new BufferedStream(m, 1000, 10);
        b.start();
        try {
            awaitIdle(b);
            synchronized (b) {
                b.consumer.interrupt();
                b.stop();
            }
            b.consumer.join(2000);
            Assert.assertFalse("the consumer ended", b.consumer.isAlive());
            Assert.assertEquals("the consumer closed the stream", 1, closes.get());
        } finally {
            b.close();
        }
    }
}
