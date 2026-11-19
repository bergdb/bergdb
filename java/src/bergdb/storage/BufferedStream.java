package bergdb.storage;

import java.io.Closeable;
import java.io.EOFException;
import java.io.IOException;
import java.util.concurrent.locks.ReentrantLock;

import bergdb.common.Bug;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.StrictStream;

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
 * <p>The buffer grows with use (2026-11-13, bergdb 026-07): it starts at INITIAL_CAPACITY,
 * or the given capacity if that is smaller, and an append that does not fit doubles it,
 * as often as needed, up to the given capacity, the largest buffer. A grown buffer
 * shrinks back to INITIAL_CAPACITY when the thread has had nothing to write for
 * shrinkDelayMs, 2 s. The thread's rules (the quarter, a flush of at most half, a writer that
 * waits for room) are those of the largest buffer, so the flushes and forces do not
 * change; only the heap does. It was the given capacity from the start, 10 MB for a
 * database: every started database held 11 MB of heap, whatever its size (bergdb 024-01,
 * PA7; 024-05, ST8; 020-24-10, U10-2).
 * 
 * <p>The underlying stream gets one call at a time, but read(), as AppendOnlyStream's
 * CONCURRENCY says (2026-11-06, bergdb 015-80): the thread's appends, the cuts and the
 * close hold ioLock, and getFirstPos() returns the first position kept after the last cut.
 * The thread's append ran beside the writer's cut and getFirstPos(). A cut that comes
 * during an append of the thread waits for it, and its force. ioLock is never held with
 * this object's monitor, and read() holds neither while it reads the underlying stream.
 * 
 * <p>The underlying stream is this object's from the constructor to close(): nothing else
 * appends to it, cuts it or closes it; others may read it. getFirstPos() depends on this:
 * it is the first position kept after this object's last cut (bergdb 015-80, review R4).
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
    /**
     * The ring buffer; null once the thread has ended (2026-11-09, bergdb 020-24-10, U10-3):
     * a closed database that the application still referenced held it, 10 MB, until the
     * object was dropped. The thread ends only after stop, and stop() and every failure set
     * 'exception' before, so every later append and read throws before it would use it.
     * Changed under this; read by the thread, and by the others under this.
     */
    private byte[] buffer;
    /**
     * The buffer's first length, and its length after a shrink: 64 KiB (bergdb 026-07).
     * A smaller given capacity is used as it is, and the buffer then never grows.
     */
    public static final int INITIAL_CAPACITY = 64 * 1024;
    /**
     * A grown buffer shrinks to INITIAL_CAPACITY after this long with nothing to write,
     * 2 s (bergdb 026-07; Frans, 2026-11-13, 09:59: "keep it as a constant, but use 2
     * seconds"; it was 1 s). The idle thread waits this long once, then without a timeout, as
     * before (005-14): a grown buffer costs one wake of an idle stream, a first-sized one
     * none. A field, not final, so that a test can make it short.
     */
    long shrinkDelayMs = 2000;
    /** The buffer's length, buffer.length, from INITIAL_CAPACITY to maxCapacity. Under this. */
    private int bufferCapacity;
    /** The largest buffer: the constructor's bufferCapacity (bergdb 026-07). */
    private final int maxCapacity;
    /**
     * The buffer grows up to this: maxCapacity, or the buffer's length after an allocation
     * failed (an OutOfMemoryError; the writer then waits for room, as with a full buffer of
     * the largest length) until the next shrink. Under this.
     */
    private int growLimit;
    /** A quarter of the largest buffer, whatever the buffer's length (bergdb 026-07). */
    private final int twentyFivePercentOfBufferCapacity;
    /** Half the largest buffer: a flush writes at most this (bergdb 026-07). */
    private final int fiftyPercentOfBufferCapacity;
    /**
     * The array and its length of the consumer's flush, taken with cSize, under this
     * (bergdb 026-07): the writer may replace 'buffer' with a grown copy during the flush.
     * The consumer's only.
     */
    private byte[] flushBuffer;
    private int flushCapacity;
    /** True while the idle consumer waits for the shrink, from idleSince (System.nanoTime). */
    private boolean idleTimed;
    private long idleSince;
    /** The grows and shrinks of the buffer, for tests (bergdb 026-07). Under this. */
    private int grows, shrinks;
    private long streamLength; // underlying stream length
    private long totalLength; // total length: buffered in memory + stream
                              // length
    private final AppendOnlyStream stream;   // underlying stream
    /**
     * Held for every call to the underlying stream but read() (2026-11-06, bergdb 015-80):
     * the thread's appends, the cuts with getFirstPos() after each, and its close.
     * AppendOnlyStream allows one writer at a time; the thread's append ran beside the
     * writer's cut and getFirstPos(). Fair, so that a cut waits for at most the append in
     * progress. Never held together with this object's monitor, and never by read().
     */
    private final ReentrantLock ioLock = new ReentrantLock(true);
    /** The underlying stream's first position after the last cut; see getFirstPos(). */
    private volatile long firstPos;
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
    /** See flushFailure() (bergdb 019-39). */
    private final IOException flushFailure = new IOException("The flush failed (the cause).");
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
     *            Capacity of the buffer in bytes, its largest: the buffer starts at
     *            INITIAL_CAPACITY, or this if smaller, and grows with use (bergdb 026-07).
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
        this.maxCapacity = bufferCapacity;
        this.growLimit = bufferCapacity;
        this.bufferCapacity = Math.min(bufferCapacity, INITIAL_CAPACITY);     // bergdb 026-07
        this.twentyFivePercentOfBufferCapacity = bufferCapacity / 4;
        this.fiftyPercentOfBufferCapacity = bufferCapacity / 2;
        this.waitTime = bufferTime / 4;
        this.waitsBeforeFlush = 4;
        buffer = new byte[this.bufferCapacity];
        streamLength = stream.getLength();
        totalLength = streamLength;
        firstPos = stream.getFirstPos();

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
        } catch (Throwable e) {
            // 2026-11-06 (bergdb 019-10): anything else that ends the thread, outside a flush
            // (a bug, an Error such as an OutOfMemoryError, also one of the listener's), fails
            // the stream as a failed flush does, so the storage and the database fail. It
            // ended the thread with nothing failed: commits waited for room, and syncs for
            // ever.
            stopAfterFailure(flushFailure(e));
        } finally {
            // In a finally (2026-11-05, bergdb 015-34): an interrupt that met stop() returned
            // from consume() before the close, and the stream's files and directory lock
            // stayed open.
            closeStream();
            releaseBuffer();
        }
    }
    
    /** Drops the buffer once the thread has ended or never ran; see 'buffer' (bergdb 020-24-10). */
    private synchronized void releaseBuffer() {
        assert exception != null;
        buffer = null;
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
                        if (!waitToShrink()) {
                            wait();
                        }
                    }
                    idle = false;
                    idleTimed = false;
                    if (stop) {
                        break A;
                    }
                    // No wait while a sync waits (bergdb 005-48), or with a quarter ready
                    // (bergdb 005-76). An append's wake may arrive during the last flush.
                    // Nor while a close waits for buffered bytes (bergdb 020-13, bug 4): its
                    // wake came during a flush, and the close waited a whole wait time, a
                    // quarter of the buffer time, for nothing.
                    if (!syncWaits() && !closeWaits() && !nearlyFull()
                            && pStart - cStart < twentyFivePercentOfBufferCapacity) {
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

                takeFlush();
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
        ioLock.lock();      // Not beside a writer's cut (bergdb 015-80).
        try {
            stream.close();
        } catch (IOException e) {
            failed = e;
        } catch (RuntimeException | Error e) {
            failed = new IOException("The close of the stream failed (the cause).", e);
        } finally {
            ioLock.unlock();
        }
        if (failed != null) {
            synchronized (this) {
                if (closeFailure == null) {
                    closeFailure = failed;
                    // Kept with a failed flush's failure, which close() throws (2026-11-05,
                    // bergdb 015-81, review R1 of night 006-12): it was dropped. Not when the
                    // close threw the flush's own IOException (2026-11-06, bergdb 019-37):
                    // addSuppressed threw "Self-suppression not permitted", which ended the
                    // thread, or left close() when the listener closed the stream.
                    if (failure != null && failure != failed) {
                        failure.addSuppressed(failed);
                    }
                }
            }
        }
    }

    /**
     * Takes what is buffered for the consumer's next flush: cSize, and the array and its
     * length (bergdb 026-07; see flushBuffer). Under this.
     */
    private void takeFlush() {
        assert Thread.holdsLock(this);
        cSize = (int) (pStart - cStart);
        // Here, we have a reserved interval [cStart, cStart + cSize - 1] for the
        // consumer that the producer must respect (must not use).

        assert cSize <= bufferCapacity : "Bad cSize " + cSize + ", bufferCapacity="
                + bufferCapacity;
        flushBuffer = buffer;
        flushCapacity = bufferCapacity;
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
                || nearlyFull()                 // bergdb 026-07
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
     * True when less than a tenth of the buffer is free (bergdb 026-07). Only a buffer that
     * could not grow gets there before the quarter, after a failed allocation: the writer
     * then waits for room, and the consumer writes at once, not after the timer.
     */
    private boolean nearlyFull() {
        assert Thread.holdsLock(this);
        return bufferCapacity - (pStart - cStart) < bufferCapacity / 10;
    }
    
    /**
     * The idle consumer's wait for the shrink (bergdb 026-07), with nothing buffered: false at
     * once for a buffer of its first length, and the consumer then waits without a timeout.
     * Else the first call of an idle time notes its start and waits until shrinkDelayMs has
     * passed since, and a call after that shrinks the buffer to INITIAL_CAPACITY and
     * returns false. Nothing is buffered and no flush runs, so no byte is copied.
     */
    private boolean waitToShrink() throws InterruptedException {
        assert Thread.holdsLock(this) && pStart == cStart;
        if (bufferCapacity <= INITIAL_CAPACITY) {
            return false;
        }
        long now = System.nanoTime();
        if (!idleTimed) {
            idleTimed = true;
            idleSince = now;
        }
        long left = shrinkDelayMs - (now - idleSince) / 1000000;
        if (left > 0) {
            wait(left);
            return true;
        }
        try {
            buffer = new byte[INITIAL_CAPACITY];
        } catch (OutOfMemoryError e) {
            return false;       // Keeps the grown buffer; the next idle time tries again.
        }
        bufferCapacity = INITIAL_CAPACITY;
        growLimit = maxCapacity;
        shrinks++;
        return false;
    }
    
    /**
     * Grows the buffer so that it holds what is buffered and 'length' bytes more, doubling
     * its length as often as needed, up to growLimit (bergdb 026-07). The writer's, when an
     * append does not fit. The buffered bytes are copied to the same positions of the new
     * ring; a flush in progress goes on with the old array, whose bytes it writes do not
     * change (see flushBuffer). An OutOfMemoryError of the allocation keeps the buffer as it
     * is, and sets growLimit to its length until the next shrink: the writer then waits for
     * room, as at the largest length.
     */
    private void grow(int length) {
        assert Thread.holdsLock(this);
        long buffered = pStart - cStart;
        long capacity = bufferCapacity;
        while (capacity < buffered + length && capacity < growLimit) {
            capacity *= 2;
        }
        int newCapacity = (int) Math.min(capacity, growLimit);
        byte[] b;
        try {
            b = new byte[newCapacity];
        } catch (OutOfMemoryError e) {
            growLimit = bufferCapacity;
            return;
        }
        for (long pos = cStart; pos < pStart; ) {
            int from = (int) (pos % bufferCapacity);
            int to = (int) (pos % newCapacity);
            int n = (int) Math.min(pStart - pos, Math.min(bufferCapacity - from, newCapacity - to));
            System.arraycopy(buffer, from, b, to, n);
            pos += n;
        }
        buffer = b;
        bufferCapacity = newCapacity;
        grows++;
    }
    
    /** True when close() waits for bytes that are still buffered (bergdb 020-13, bug 4). */
    private boolean closeWaits() {
        assert Thread.holdsLock(this);
        return flushAndClose && pStart > cStart;
    }

    /**
     * Flushes bytes from ring buffer to underlying stream. Used by consumer.
     */
    private void flushToStream() {
        // We do not flush more than half of the buffer to leave room for
        // producer to add data
        // while consumer is writing (flushing) to underlying filesystem.
        // Half of the largest buffer (bergdb 026-07): a smaller one grows to make room.
        // The array and its length taken with cSize: the writer may grow the buffer now.

        final byte[] flushBuffer = this.flushBuffer;
        final int flushCapacity = this.flushCapacity;
        this.flushBuffer = null;    // Not kept after a grow or a shrink.
        assert cSize <= flushBuffer.length;

        final int sizeToFlush = cSize > fiftyPercentOfBufferCapacity ? fiftyPercentOfBufferCapacity
                : cSize;
        
        // 0 bytes would append the whole buffer (index2 is then index1 - 1); see shouldFlush().
        assert sizeToFlush > 0 : "bad sizeToFlush: " + sizeToFlush;

        int index1 = (int) (cStart % flushCapacity);
        int index2 = (int) ((cStart + sizeToFlush - 1) % flushCapacity);
        IOException ex = null;

        try {
            if (index2 >= index1) {     // Was '>', which wrote wrong bytes for a 1-byte flush.
                appendToStream(flushBuffer, index1, sizeToFlush);
            } else {
                appendToStream(flushBuffer, index1, flushCapacity - index1);
                appendToStream(flushBuffer, 0, index2 + 1);
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
                cutStream(cut);
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

    /** One append to the underlying stream, holding ioLock (bergdb 015-80). */
    private void appendToStream(byte[] buffer, int offset, int length) throws IOException {
        ioLock.lock();
        try {
            stream.append(buffer, offset, length);
        } finally {
            ioLock.unlock();
        }
    }

    /**
     * Cuts the underlying stream, holding ioLock, and keeps its first position after the cut
     * (bergdb 015-80): the writer's cut, and the thread's pending one.
     */
    private void cutStream(long position) throws IOException {
        ioLock.lock();
        try {
            stream.pretruncate(position);
            firstPos = stream.getFirstPos();
        } finally {
            ioLock.unlock();
        }
    }

    /**
     * Anything else that a flush throws stops the stream too (2026-10-24, bergdb 005-32): an
     * Error, such as an assertion of FileStream, ended the thread without telling the
     * listener, and every later sync waited for ever.
     * 
     * <p>Allocates nothing (2026-11-06, bergdb 019-39): the IOException is made with the
     * stream, and gets the first such failure as its cause; its stack trace is the stream's
     * making. It was made here, and when the heap was still full, that threw too: the thread
     * ended with nothing failed, and syncs, a writer that waited for room and close() waited
     * for ever. The consumer thread only.</p>
     */
    private IOException flushFailure(Throwable e) {
        if (flushFailure.getCause() == null) flushFailure.initCause(e);
        return flushFailure;
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

    /**
     * The underlying stream's first position after the last cut (2026-11-06, bergdb 015-80):
     * it called the underlying stream, beside the thread's append. A stream's first position
     * changes only at a cut, every cut of it is made through this object (the class's rule),
     * and this object reads the position after each. Takes no lock: a commit asks it often
     * (NodeCollection.resolvePointers), and must not wait for the thread's append and force.
     */
    public long getFirstPos() {
        return firstPos;
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
        long pos2 = position + length - 1;     // Used after the checks below, which bound it.
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
            // Without the sum since 2026-11-09 (bergdb 021-14): pos2 overflowed for a
            // position within 'length' of Long.MAX_VALUE, the check passed, and the read took
            // bytes of the ring buffer or threw IndexOutOfBoundsException. totalLength and
            // length are not negative, so totalLength - length does not overflow.
            if (position > totalLength - length) {
                throw new EOFException("Cannot read " + length + " bytes at position " + position
                        + ", stream size is " + totalLength + ".");
            }
            if (length == 0) {
                return;     // Reads nothing, as before; pos2 underflows at Long.MIN_VALUE.
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
     * until after this method returns. An append that waits for room in the buffer throws
     * an IOException when stop(), close() or a failed flush comes during its wait, as an
     * append after them does (bergdb 020-23, V2-2); what it had put in the buffer before the
     * wait stays there.
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
                    if (available < length && bufferCapacity < growLimit) {
                        grow(length);       // bergdb 026-07
                        available = availableBufferSize();
                    }
                    if (available < length && available < bufferCapacity / 10) {
                        if (waitStart == 0) {
                            waitStart = System.nanoTime();
                        }
                        try {
                            notifyAll();    // A nearly full buffer is written at once (026-07).
                            wait(); // wait for consumer to write to output stream
                        } catch (InterruptedException e) {
                            // 2026-10-27 (bergdb 005-46): not interruptible. The interrupt threw
                            // an IOException, which failed the storage, and so the database: the
                            // wait comes after the transaction's go point.
                            interrupted = true;
                        }
                        // The thread that makes room has stopped: after stop() or a failed flush
                        // (2026-10-24, bergdb 005-35). The writer waited here for ever, with the
                        // database's write lock, so a failing disk hung the database.
                        // After the wait, and for close() too, as an append after them throws
                        // (2026-11-09, bergdb 020-23, V2-2): close(), stop() and a failed flush
                        // each set 'exception'. Checked before the wait, for a stop only, it
                        // missed a stop that came while the thread made room, and every close():
                        // the append went on, and could return normally with bytes that close()
                        // never wrote, as close() had found the buffer empty, or leave close()
                        // waiting a whole wait time for bytes that did not wake the thread.
                        // Outside AppendOnlyStream's CONCURRENCY rule 2: Db closes the storage
                        // after its last append; only a failure closes it beside an append
                        // (StorageManager.handleStreamException, from a read), and then the
                        // storage and the database have failed.
                        if (this.exception != null) {
                            throw new IOException("The stream has stopped, or begun to close, "
                                    + "while an append waited for room in its buffer.",
                                    failure != null ? failure : exception);
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
     * and applied after the flush that reaches it. One at or before them is cut at once,
     * holding ioLock (2026-11-06, bergdb 015-80): it waits for an append of the thread in
     * progress, and its force, at most one; it ran beside it.
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
        cutStream(position);
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
     * first close of the underlying stream (by the thread or by close(); bergdb 015-78); a
     * flush's failure has the close's as suppressed. Safe to call from several threads at
     * once: each returns when the thread has ended, after its close of the underlying stream.
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
        if (Thread.currentThread() != consumer) {
            releaseBuffer();     // The thread has ended, or was never started (U10-3).
        }
        
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
                    longestUptime[i] = Uptime.millis();
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

    /**
     * The uptime that Waits reports, in milliseconds: the JVM's, from java.lang.management,
     * which lines up with GC logs; where that package is missing, as on Android, the time
     * since this class was initialized (bergdb 006-18-03).
     */
    static final class Uptime {
        private static final long START = System.nanoTime();
        private static final boolean JVM = jvm();

        private static boolean jvm() {
            try {
                java.lang.management.ManagementFactory.getRuntimeMXBean().getUptime();
                return true;
            } catch (LinkageError e) {
                return false;
            }
        }

        static long millis() {
            return JVM ? java.lang.management.ManagementFactory.getRuntimeMXBean().getUptime()
                    : (System.nanoTime() - START) / 1000000;
        }
    }
    
    // ======== Test ========

    /**
     * bergdb 006-18-03: on a JVM, Waits takes the JVM's uptime, as before; on Android, which
     * has no java.lang.management, the time since Uptime was initialized.
     */
    @Nano
    public static void testUptimeIsTheJvms() {
        if (Util.runsAndroid()) {
            Assert.assertTrue(!Uptime.JVM);
            return;
        }
        long before = java.lang.management.ManagementFactory.getRuntimeMXBean().getUptime();
        long uptime = Uptime.millis();
        long after = java.lang.management.ManagementFactory.getRuntimeMXBean().getUptime();
        Assert.assertTrue(Uptime.JVM);
        Assert.assertTrue(before + " " + uptime + " " + after, before <= uptime && uptime <= after);
    }

    /**
     * bergdb 020-24-10, U10-3: the buffer is released when the thread ends, after close()
     * and after stop(), and by close() of a stream whose thread never ran; a read and an
     * append then throw. A closed database that the application still referenced held the
     * buffer, 10 MB, until the object was dropped.
     */
    @Nano
    public static void testBufferReleasedAtTheEnd() throws Exception {
        BufferedStream b = new BufferedStream(new MemoryStream(), 1000, 20);
        b.start();
        b.append(new byte[] {1, 2, 3}, 0, 3);
        b.close();
        synchronized (b) {
            Assert.assertTrue("closed", b.buffer == null);
        }
        Assert.assertEquals(3L, b.getUnderlyingStream().getLength());
        
        BufferedStream s = new BufferedStream(new MemoryStream(), 1000, 20);
        s.start();
        s.append(new byte[] {1, 2, 3}, 0, 3);
        s.stop();
        s.consumer.join(60_000);
        Assert.assertFalse("the consumer thread did not end within 60 s of stop()",
                s.consumer.isAlive());
        synchronized (s) {
            Assert.assertTrue("stopped", s.buffer == null);
        }
        try {
            s.read(0, new byte[1], 0, 1);
            throw new AssertionError("read a stopped stream");
        } catch (IOException e) {
            // Expected.
        }
        try {
            s.append(new byte[1], 0, 1);
            throw new AssertionError("appended to a stopped stream");
        } catch (IOException e) {
            // Expected.
        }
        s.close();
        
        BufferedStream n = new BufferedStream(new MemoryStream(), 1000, 20);
        n.close();      // Never started.
        synchronized (n) {
            Assert.assertTrue("never started", n.buffer == null);
        }
    }

    /** The byte of stream position 'pos' in the tests of growth (bergdb 026-07). */
    private static byte growByte(long pos) {
        return (byte) (pos * 31 + (pos >> 9));
    }
    
    private static byte[] growBytes(long pos, int length) {
        byte[] bytes = new byte[length];
        for (int i = 0; i < length; i++) {
            bytes[i] = growByte(pos + i);
        }
        return bytes;
    }
    
    /**
     * bergdb 026-07: the buffer starts at INITIAL_CAPACITY, grows to hold an append that does
     * not fit, its bytes read back the same from the grown buffer, and it shrinks back when
     * the consumer has been idle for shrinkDelayMs; an idle consumer with a first-sized
     * buffer waits without a timeout (005-14).
     */
    @Nano
    public static void testGrowsAndShrinks() throws Exception {
        MemoryStream m = new MemoryStream();
        BufferedStream b = new BufferedStream(m, 1500000, 20);
        b.shrinkDelayMs = 50;
        synchronized (b) {
            Assert.assertEquals(INITIAL_CAPACITY, b.buffer.length);
        }
        b.append(growBytes(0, 200000), 0, 200000);     // Not started: nothing is flushed.
        synchronized (b) {
            Assert.assertEquals(4 * INITIAL_CAPACITY, b.buffer.length);
            Assert.assertEquals(1, b.grows);
        }
        b.append(growBytes(200000, 900000), 0, 900000);   // Doubled to past the largest.
        synchronized (b) {
            Assert.assertEquals(1500000, b.buffer.length);
            Assert.assertEquals(2, b.grows);
        }
        b.start();
        try {
            byte[] bytes = new byte[1100000];
            b.read(0, bytes, 0, bytes.length);
            for (int i = 0; i < bytes.length; i++) {
                Assert.assertEquals(growByte(i), bytes[i]);
            }
            b.flushSoon(1100000);
            awaitIdle(b);
            synchronized (b) {
                Assert.assertEquals(INITIAL_CAPACITY, b.buffer.length);
                Assert.assertEquals(1, b.shrinks);
            }
            Assert.assertEquals(1100000, m.getLength());
            b.append(growBytes(1100000, 100), 0, 100);
            b.flushSoon(1100100);
            awaitIdle(b);
        } finally {
            b.close();
        }
        Assert.assertEquals(1100100, m.getLength());
        byte[] bytes = new byte[1100100];
        m.read(0, bytes, 0, bytes.length);
        for (int i = 0; i < bytes.length; i++) {
            Assert.assertEquals(growByte(i), bytes[i]);
        }
    }
    
    /**
     * bergdb 026-07: the writer grows the buffer while the consumer writes from it, with the
     * ring wrapped at both lengths, and every byte reaches the stream in order; reads of
     * buffered bytes during it give the stream's bytes. Appends of 1 to 70,000 bytes.
     */
    @Nano
    public static void testGrowsDuringFlushes() throws Exception {
        MemoryStream m = new MemoryStream() {
            @Override public void append(byte[] source, int offset, int length) throws IOException {
                try {
                    Thread.sleep(2);   // A force's latency, so that the backlog grows.
                } catch (InterruptedException e) {
                    throw new IOException(e);
                }
                super.append(source, offset, length);
            }
        };
        BufferedStream b = new BufferedStream(m, 2000000, 20);
        b.shrinkDelayMs = 20;
        b.start();
        java.util.Random random = new java.util.Random(26007);
        long pos = 0;
        try {
            for (int round = 0; round < 3; round++) {
                for (int i = 0; i < 300; i++) {
                    int length = i == 0 ? 100000     // Grows each round.
                            : 1 + (i % 7 == 0 ? random.nextInt(70000) : random.nextInt(3000));
                    b.append(growBytes(pos, length), 0, length);
                    pos += length;
                    int n = (int) Math.min(pos, 5000);
                    long at = pos - n;
                    byte[] read = new byte[n];
                    b.read(at, read, 0, n);
                    for (int k = 0; k < n; k++) {
                        Assert.assertEquals(growByte(at + k), read[k]);
                    }
                }
                b.flushSoon(pos);
                awaitIdle(b);     // After the shrink.
            }
            synchronized (b) {
                Assert.assertTrue("grows " + b.grows, b.grows >= 3);
                Assert.assertTrue("shrinks " + b.shrinks, b.shrinks >= 3);
            }
        } finally {
            b.close();
        }
        Assert.assertEquals(pos, m.getLength());
        byte[] bytes = new byte[(int) pos];
        m.read(0, bytes, 0, bytes.length);
        for (int i = 0; i < bytes.length; i++) {
            Assert.assertEquals(growByte(i), bytes[i]);
        }
    }
    
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
            long deadline = System.nanoTime() + 30000000000L;
            while (b.consumer.getState() != Thread.State.TIMED_WAITING) {
                Assert.assertTrue("consumer did not enter its timed wait",
                        System.nanoTime() < deadline);
                Thread.sleep(1);
            }
            b.append(new byte[255], 0, 255);   // Just below the quarter.
            Assert.assertEquals(0, m.getLength());
            b.append(new byte[] {42}, 0, 1);   // Exactly a quarter, without a sync.
            Assert.assertTrue("the quarter-full append did not wake the consumer",
                    flushed.await(10, java.util.concurrent.TimeUnit.SECONDS));
            byte[] bytes = new byte[256];
            m.read(0, bytes, 0, bytes.length);
            Assert.assertEquals((byte) 42, bytes[255]);
        } finally {
            b.close();
        }
    }

    /**
     * bergdb 020-13, bug 4: a close() that comes while the consumer flushes, with bytes
     * buffered after the flush's, flushes them at once. Its wake came while the consumer was
     * not waiting, and the consumer then waited a whole wait time (a quarter of the buffer
     * time; 15 s here) before it flushed them: PubTester.testTryWithResourcesCloses took 15 s
     * now and then in a loaded gate.
     */
    @Nano
    public static void testCloseDuringAFlushDoesNotWaitForTheTimer() throws Exception {
        final java.util.concurrent.CountDownLatch entered = new java.util.concurrent.CountDownLatch(1);
        final java.util.concurrent.CountDownLatch release = new java.util.concurrent.CountDownLatch(1);
        MemoryStream m = new MemoryStream() {
            @Override public void append(byte[] source, int offset, int length) throws IOException {
                if (getLength() == 0) {
                    entered.countDown();
                    try {
                        if (!release.await(30, java.util.concurrent.TimeUnit.SECONDS)) {
                            throw new IOException("test did not release the first flush");
                        }
                    } catch (InterruptedException e) {
                        throw new IOException(e);
                    }
                }
                super.append(source, offset, length);
            }
        };
        final BufferedStream b = new BufferedStream(m, 1024, 60000);
        b.append(new byte[512], 0, 512);
        b.flushSoon(512);
        b.start();
        Thread closer = null;
        try {
            Assert.assertTrue("first flush did not start",
                    entered.await(30, java.util.concurrent.TimeUnit.SECONDS));
            b.append(new byte[100], 0, 100);   // Below a quarter: the timer's wait applies.
            final IOException[] closeFailure = new IOException[1];
            closer = new Thread(() -> {
                try {
                    b.close();
                } catch (IOException e) {
                    closeFailure[0] = e;
                }
            });
            closer.start();
            long deadline = System.nanoTime() + 30000000000L;
            while (true) {          // close() has woken the busy consumer, and waits
                synchronized (b) {
                    if (b.flushAndClose) {
                        break;
                    }
                }
                Assert.assertTrue("close() did not start", System.nanoTime() < deadline);
                Thread.sleep(1);
            }
            long t0 = System.nanoTime();
            release.countDown();
            closer.join(30000);
            long ms = (System.nanoTime() - t0) / 1000000;
            Assert.assertFalse("close() waits after " + ms + " ms", closer.isAlive());
            Assert.assertTrue("close() took " + ms + " ms, the timer's wait", ms < 10000);
            Assert.assertEquals(612, m.getLength());
        } finally {
            release.countDown();
            if (closer != null) {
                closer.join(60_000);
                Assert.assertFalse("the closer thread did not end within 60 s", closer.isAlive());
            }
            b.close();
        }
    }

    /**
     * bergdb 020-23, V2-2: an append that waits for room in the buffer when close() begins
     * throws, as an append after close() does, and adds nothing; close() writes what was
     * buffered before it began, without waiting for the timer. The append went on after its
     * wait: it could return normally with bytes that close() never wrote, as close() had
     * found the buffer empty, or leave close() waiting a whole wait time (a quarter of the
     * buffer time; 15 s here) for bytes that did not wake the thread. Outside
     * AppendOnlyStream's CONCURRENCY rule 2, which Db keeps: it closes the storage after
     * the last append.
     */
    @Nano
    public static void testAppendWaitingForRoomWhenCloseBeginsThrows() throws Exception {
        final HeldStream m = new HeldStream();
        m.hold = new java.util.concurrent.CountDownLatch(1);
        final BufferedStream b = new BufferedStream(m, 1000, 60000);
        b.append(new byte[950], 0, 950);
        b.flushSoon(950);
        b.start();
        Thread writer = null;
        Thread closer = null;
        try {
            Assert.assertTrue("first flush did not start",
                    m.held.await(30, java.util.concurrent.TimeUnit.SECONDS));
            final Throwable[] appendFailure = new Throwable[1];
            writer = new Thread(() -> {
                try {
                    b.append(new byte[200], 0, 200);   // 50 bytes of room: it waits for room
                } catch (Throwable e) {
                    appendFailure[0] = e;
                }
            });
            writer.start();
            long deadline = System.nanoTime() + 30000000000L;
            while (writer.getState() != Thread.State.WAITING) {
                Assert.assertTrue("the writer did not wait for room", System.nanoTime() < deadline);
                Thread.sleep(1);
            }
            final IOException[] closeFailure = new IOException[1];
            closer = new Thread(() -> {
                try {
                    b.close();
                } catch (IOException e) {
                    closeFailure[0] = e;
                }
            });
            closer.start();
            deadline = System.nanoTime() + 30000000000L;
            while (true) {          // close() has begun, and waits for the held flush
                synchronized (b) {
                    if (b.flushAndClose) {
                        break;
                    }
                }
                Assert.assertTrue("close() did not start", System.nanoTime() < deadline);
                Thread.sleep(1);
            }
            long t0 = System.nanoTime();
            m.hold.countDown();
            writer.join(30000);
            closer.join(30000);
            long ms = (System.nanoTime() - t0) / 1000000;
            Assert.assertTrue("the append returned normally after close() began: "
                    + appendFailure[0], appendFailure[0] instanceof IOException);
            Assert.assertFalse("close() waits after " + ms + " ms", closer.isAlive());
            Assert.assertTrue("close() took " + ms + " ms, the timer's wait", ms < 10000);
            Assert.assertTrue("close() threw " + closeFailure[0], closeFailure[0] == null);
            Assert.assertEquals("the bytes appended before close()", 950, m.getLength());
        } finally {
            m.hold.countDown();
            if (writer != null) {
                writer.join(60_000);
                Assert.assertFalse("the writer thread did not end within 60 s", writer.isAlive());
            }
            if (closer != null) {
                closer.join(60_000);
                Assert.assertFalse("the closer thread did not end within 60 s", closer.isAlive());
            }
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
                        if (!release.await(30, java.util.concurrent.TimeUnit.SECONDS)) {
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
                    entered.await(30, java.util.concurrent.TimeUnit.SECONDS));
            b.append(new byte[256], 0, 256);   // Above a quarter throughout this append.
            release.countDown();
            Assert.assertTrue("the quarter-full backlog waited for the timer",
                    flushed.await(10, java.util.concurrent.TimeUnit.SECONDS));
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
        // The buffer's timer writes the bytes. A buffer time of 1 s, not 20 ms (bergdb
        // 021-28), so that the first assertion holds on a loaded machine too.
        MemoryStream m = new MemoryStream();
        @SuppressWarnings("resource")
        BufferedStream b = new BufferedStream(m, 1000, 1000);
        b.start();

        try {
            byte[] bytes = new byte[] { 1, 2 };
            long tA = System.nanoTime();
            b.append(bytes, 0, bytes.length);
            long length = m.getLength();
            // Checked unless this thread was stalled for most of the buffer time, as on a
            // loaded machine (bergdb 028-23): the timer may have written the bytes by then.
            if (System.nanoTime() - tA < 900L * 1000 * 1000) {
                Assert.assertEquals(0, length);
            }
            long t0 = System.nanoTime();
            while (m.getLength() == 0 && System.nanoTime() - t0 < 30L * 1000 * 1000 * 1000) {
                Thread.sleep(1);
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
     * Regression test for bergdb 021-14: a read whose end, position + length, overflows a
     * long passed the check of the end, and took bytes of the ring buffer (with a buffer of
     * 1024 bytes, 4 bytes at Long.MAX_VALUE - 2) or threw IndexOutOfBoundsException. It is a
     * read past the end: EOFException, and the stream is as it was.
     */
    @Nano
    public static void testReadPastEndNearMaxValue() throws IOException {
        byte[] bytes = new byte[] {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
        for (int capacity : new int[] {100, 128, 1000, 1024}) {
            BufferedStream b = new BufferedStream(new MemoryStream(), capacity, 1000);
            b.append(bytes, 0, bytes.length);       // Not started: in the buffer.
            for (int length : new int[] {1, 4, 32, 1000}) {
                for (long k = 0; k <= length; k++) {
                    long position = Long.MAX_VALUE - k;
                    try {
                        b.read(position, new byte[length], 0, length);
                        throw new AssertionError("read(" + position + ", " + length
                                + ") returned, buffer " + capacity);
                    } catch (EOFException e) {
                        // Expected.
                    }
                }
            }
            byte[] dest = new byte[bytes.length];
            b.read(0, dest, 0, dest.length);
            Assert.assertTrue(java.util.Arrays.equals(bytes, dest));
        }
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
                        release.await(30, java.util.concurrent.TimeUnit.SECONDS);
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
                    entered.await(30, java.util.concurrent.TimeUnit.SECONDS));
            b.pretruncate(300);             // Within the bytes of the flush that is cutting.
            release.countDown();
            Assert.assertTrue("the flush was not published",
                    flushed.await(30, java.util.concurrent.TimeUnit.SECONDS));
        } finally {
            release.countDown();
            b.close();
        }
        Assert.assertEquals(400L, m.getLength());
        Assert.assertEquals(300L, lastCut.get());
    }

    /**
     * Regression test for bergdb 015-80 (016-06's R5-F5), the paths that harness 6.3
     * (StorageContractTester) does not reach: a writer's cut, at or below the flushed length,
     * while the thread makes a pending cut, and while the thread closes the stream after
     * stop(). The cut must wait for the thread's call, not call the stream below beside it
     * (StrictStream: OVERLAP); getFirstPos() is then the stream below's. Below the close, a
     * CutStream, whose first position is the cut exactly; below the thread's cut at 200, a
     * MemoryStream, as the writer's cut at 80 comes after it, which a CutStream refuses (a cut
     * below an earlier one), and whose first position moves in steps of 1 MB, so the check
     * there is weak (testFirstPosAfterCuts checks the kept value after both kinds of cut).
     */
    @Nano
    public static void testWriterCutBesideThreadsCutAndClose() throws Exception {
        writerCutBeside(StrictStream.Op.PRETRUNCATE, new MemoryStream());
        writerCutBeside(StrictStream.Op.CLOSE, new CutStream());
    }

    private static void writerCutBeside(final StrictStream.Op held, AppendOnlyStream below)
            throws Exception {
        java.util.concurrent.CountDownLatch entered = new java.util.concurrent.CountDownLatch(1);
        java.util.concurrent.CountDownLatch release = new java.util.concurrent.CountDownLatch(1);
        below.append(new byte[100], 0, 100);
        final StrictStream strict = new StrictStream(below);
        strict.setHook((op, n) -> {
            if (op == held && entered.getCount() > 0) {
                entered.countDown();
                try {
                    if (!release.await(30, java.util.concurrent.TimeUnit.SECONDS)) {
                        throw new IOException("the test did not release " + held);
                    }
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    throw new IOException(e);
                }
            }
        });
        final BufferedStream b = new BufferedStream(strict, 1000, 10);
        final java.util.concurrent.atomic.AtomicReference<Throwable> thrown =
                new java.util.concurrent.atomic.AtomicReference<Throwable>();
        Thread writer = null;
        try {
            if (held == StrictStream.Op.PRETRUNCATE) {
                b.append(new byte[300], 0, 300);
                b.pretruncate(200);         // Not started: kept, the thread cuts after its append.
                b.start();
            } else {
                b.start();
                b.stop();                   // The thread closes the stream as it ends.
            }
            Assert.assertTrue(held + " of the thread was not held",
                    entered.await(30, java.util.concurrent.TimeUnit.SECONDS));
            writer = new Thread(() -> {
                try {
                    b.pretruncate(80);      // At or below the flushed length, 100.
                } catch (Throwable e) {
                    thrown.set(e);
                }
            }, "BufferedStream-test-writer");
            writer.start();
            // Until the writer waits for ioLock, or has cut beside the thread (bergdb 019-41: a
            // fixed wait of 200 ms, after which the cut could come after the thread's call).
            long end = System.nanoTime() + 30L * 1000 * 1000 * 1000;
            while (writer.isAlive() && !b.ioLock.hasQueuedThread(writer)) {
                Assert.assertTrue("the writer's cut neither waits nor ends",
                        System.nanoTime() < end);
                Thread.sleep(1);
            }
        } finally {
            release.countDown();
            if (writer != null) {
                writer.join(60_000);
                Assert.assertFalse("the writer thread did not end within 60 s", writer.isAlive());
            }
            b.close();
        }
        for (StrictStream.Breach breach : strict.breaches()) {
            if (breach.kind == StrictStream.Kind.OVERLAP) {
                throw new AssertionError("the writer's cut beside the thread's " + held + ": "
                        + breach.getMessage(), breach);
            }
        }
        Assert.assertTrue("the cut threw " + thrown.get(), thrown.get() == null);
        Assert.assertEquals(below.getFirstPos(), b.getFirstPos());
        if (below instanceof CutStream) {
            Assert.assertEquals(80L, b.getFirstPos());
        }
    }

    /**
     * bergdb 015-80: getFirstPos() is kept, not asked of the underlying stream; it is the
     * underlying stream's after a cut made at once, and after a kept cut once it is made.
     */
    @Nano
    public static void testFirstPosAfterCuts() throws IOException {
        CutStream c = new CutStream();      // Its first position is the last cut, exactly.
        c.append(new byte[100], 0, 100);
        BufferedStream b = new BufferedStream(c, 1000, 10);
        Assert.assertEquals(0L, b.getFirstPos());
        b.pretruncate(50);                  // Within the flushed bytes: made at once.
        Assert.assertEquals(50L, b.getFirstPos());
        b.append(new byte[300], 0, 300);
        b.pretruncate(200);                 // Not started: kept for the flush.
        Assert.assertEquals(50L, b.getFirstPos());
        b.start();
        b.close();
        Assert.assertEquals(200L, c.getFirstPos());
        Assert.assertEquals(200L, b.getFirstPos());
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
                Assert.assertTrue("an append to an idle stream was not flushed in 30 s",
                        System.nanoTime() - t0 < 30000000000L);
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
            b.consumer.join(30000);
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
            b.takeFlush();
        }
        b.flushToStream();
        Assert.assertEquals(7, m.getLength());
        synchronized (b) {
            Assert.assertTrue(!b.shouldFlush());
        }
    }

    /** Waits until the consumer waits without a timeout; fails after 30 s. */
    private static void awaitIdle(BufferedStream b) throws InterruptedException {
        long t0 = System.nanoTime();
        while (b.consumer.getState() != Thread.State.WAITING) {
            Assert.assertTrue("the consumer of an idle stream is " + b.consumer.getState()
                    + ", not WAITING", System.nanoTime() - t0 < 30000000000L);
            Thread.sleep(1);
        }
    }

    @Nano
    public static void testClose() throws IOException, InterruptedException {
        MemoryStream m = new MemoryStream();
        // A buffer time of 60 s, not 20 ms (bergdb 021-28): no timer's write before the
        // assertion, on a loaded machine too.
        BufferedStream b = new BufferedStream(m, 1000, 60000);
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
            t.join(30000);
            Assert.assertFalse("close() returns, " + i, t.isAlive());
            Assert.assertTrue("it throws the failure: " + thrown[0], thrown[0] instanceof IOException);
            Assert.assertTrue("the listener is told, " + i, told[0] != null);
            if (i == 1) {
                Assert.assertTrue("the Error is the cause", told[0].getCause() instanceof AssertionError);
            }
            Assert.assertFalse("the thread has ended, " + i, b.consumer.isAlive());
        }
    }
    
    /**
     * Review R1 of night 006-12, C2 (bergdb 015-81): a close that fails after a failed flush
     * is kept, as suppressed, on the flush's failure, which close() throws; once, however
     * often the stream is closed. Before, close() threw the flush's failure and dropped the
     * close's (closeFailure), and StorageManager.handleStreamException, which says it keeps
     * the close's failure on the storage's, found nothing to keep: the same object came back.
     */
    @Nano
    public static void testCloseFailureKeptOnFlushFailure() throws Exception {
        final FailingStream failing = new FailingStream();
        failing.failure = new IOException("the disk fails");
        failing.closeError = new IllegalStateException("the close fails");
        final BufferedStream b = new BufferedStream(failing, 1000, 20);
        b.start();
        b.append(new byte[100], 0, 100);
        IOException thrown = null;
        for (int i = 0; i < 2; i++) {
            try {
                b.close();
            } catch (IOException e) {
                thrown = e;
            }
            Assert.assertTrue("close() " + i + " throws the flush's failure: " + thrown,
                    thrown == failing.failure);
        }
        Throwable[] kept = thrown.getSuppressed();
        Assert.assertEquals("the close's failure, once: " + java.util.Arrays.toString(kept), 1,
                kept.length);
        Assert.assertTrue("its cause: " + kept[0].getCause(),
                kept[0].getCause() == failing.closeError);
    }
    
    /**
     * Regression test for bergdb 019-37: a stream whose close throws the failed flush's own
     * IOException again (harness 6.2, bergdb 018-03). closeStream() kept it as suppressed on
     * itself, and addSuppressed threw IllegalArgumentException ("Self-suppression not
     * permitted"): it ended the thread (i = 0), or left close() when the listener closed the
     * stream from the thread, as StorageManager.handleStreamException does (i = 1). Now
     * close() throws the flush's failure, and the thread ends without another exception.
     */
    @Nano
    public static void testCloseThrowsFlushFailureAgain() throws Exception {
        for (int i = 0; i < 2; i++) {
            final FailingStream failing = new FailingStream();
            failing.failure = new IOException("the disk fails");
            failing.closeThrowsFailure = true;
            final BufferedStream b = new BufferedStream(failing, 1000, 20);
            final Throwable[] escaped = new Throwable[1];
            b.consumer.setUncaughtExceptionHandler((t, e) -> escaped[0] = e);
            final Throwable[] listenerClose = new Throwable[1];
            if (i == 1) {
                b.setAppendListener(new AppendListener() {
                    public void dataAppended(long length) {}
                    public void appendFailed(IOException e) {
                        try {
                            b.close();
                        } catch (Throwable e1) {
                            listenerClose[0] = e1;
                        }
                    }
                });
            }
            b.start();
            b.append(new byte[100], 0, 100);
            IOException thrown = null;
            try {
                b.close();
            } catch (IOException e) {
                thrown = e;
            }
            Assert.assertTrue("close() throws the flush's failure, " + i + ": " + thrown,
                    thrown == failing.failure);
            Assert.assertFalse("the thread has ended, " + i, b.consumer.isAlive());
            Assert.assertTrue("nothing escapes the thread, " + i + ": " + escaped[0],
                    escaped[0] == null);
            if (i == 1) {
                Assert.assertTrue("the listener's close throws the flush's failure: "
                        + listenerClose[0], listenerClose[0] == failing.failure);
            }
            Assert.assertEquals("nothing suppressed, " + i, 0, thrown.getSuppressed().length);
        }
    }
    
    /** A MemoryStream whose appends throw 'failure' while it is set (bergdb 005-32). */
    private static class FailingStream implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        volatile Throwable failure = null;
        volatile RuntimeException closeError = null;    // thrown by close() (bergdb 015-81)
        volatile boolean closeThrowsFailure = false;    // close() throws 'failure' (019-37)
        
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
        
        public void close() throws IOException {
            inner.close();
            RuntimeException e = closeError;
            if (e != null) {
                throw e;
            }
            if (closeThrowsFailure && failure instanceof IOException) {
                throw (IOException) failure;
            }
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
            Assert.assertTrue(m.held.await(30, java.util.concurrent.TimeUnit.SECONDS));
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
            writer.join(30000);
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
        Assert.assertTrue(m.held.await(30, java.util.concurrent.TimeUnit.SECONDS));
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
                Assert.assertTrue("not written in 30 s", System.nanoTime() - t0 < 30000000000L);
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
            b.consumer.join(30000);
            Assert.assertFalse("the consumer ended", b.consumer.isAlive());
            Assert.assertEquals("the consumer closed the stream", 1, closes.get());
        } finally {
            b.close();
        }
    }
    
    /**
     * bergdb 019-39 (review R6 of 006-13, B3; review R7, B1): the consumer thread records an
     * Error of a flush as the IOException made with the stream, with the first Error as its
     * cause; it makes none, so that it records the failure also when the heap is full.
     * Before, a new IOException that threw too ended the thread with nothing failed, and
     * syncs, a writer that waited for room and close() waited for ever (review R7,
     * R7OomProbe).
     */
    @Nano
    public static void testFlushFailureMadeBefore() throws IOException {
        BufferedStream b = new BufferedStream(new MemoryStream(), 1000, 10);
        try {
            Error first = new Error("test: the first");
            IOException failure = b.flushFailure(first);
            Assert.assertTrue("made before", failure == b.flushFailure(new Error("a second")));
            Assert.assertTrue("the first as the cause", failure.getCause() == first);
        } finally {
            b.close();
        }
    }
    
    /**
     * bergdb 019-40 (review R6 of 006-13, C2): an Error that ends the thread outside a flush,
     * here the listener's, fails the stream, and the listener is told (bergdb 019-10).
     * Before, it ended the thread with nothing failed.
     */
    @Nano
    public static void testListenerErrorFailsTheStream() throws Exception {
        final AssertionError error = new AssertionError("test: the listener's Error");
        final IOException[] told = new IOException[1];
        final BufferedStream b = new BufferedStream(new MemoryStream(), 1000, 10);
        b.setAppendListener(new AppendListener() {
            public void dataAppended(long length) {
                throw error;
            }
            public void appendFailed(IOException e) {
                told[0] = e;
            }
        });
        b.start();
        b.append(new byte[100], 0, 100);
        b.consumer.join(10000);
        Assert.assertTrue("the listener is told: " + told[0],
                told[0] != null && told[0].getCause() == error);
        try {
            b.close();
        } catch (IOException e) {
            Assert.assertTrue("close() throws the failure", e == told[0]);
        }
    }
}
