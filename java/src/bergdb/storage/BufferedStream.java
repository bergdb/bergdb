package bergdb.storage;

import java.io.Closeable;
import java.io.IOException;

import bergdb.common.Bug;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * An active buffer for an AppendOnlyStream that outputs the data to an
 * underlying AppendOnlyStream in a separate thread once a certain time has passed
 * or the size of the buffered data is large enough. This object is used to
 * increase throughput by "bunch-up" of small writes into larger chunks of data.
 * It is similar to Nagle's algorithm for TCP/IP traffic. The user of the object
 * must call stop() or close() to stop the internal thread.
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
    private final int waitTime;
    private final int waitsBeforeFlush;
    private AppendListener appendListener;
    private volatile boolean appendHasBeenCalled = false;

    /**
     * Creates a new buffered stream with default buffer size and buffer time.
     * 
     * @param stream
     *            The append-only stream to buffer.
     */
    public BufferedStream(AppendOnlyStream stream) {
        // 10M bufferSize and 100 ms bufferTime are reasonable defaults for a
        // rotational drive.
        // See doc/reports-2013/performance-vs-buffer-settings.txt.

        this(stream, 10 * 1000000, 100);
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

        pStart = 0;
        cStart = 0;
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
        waitCount = 0;

        A: while (!stop) {
            synchronized (this) {
                try {
                    wait(waitTime);
                } catch (InterruptedException e) {
                    if (stop) {
                        return;
                    } else {
                        throw new Bug("Should not happen, consumer thread interrupted "
                                + "and stop==" + stop + ".");
                    }
                }

                waitCount++;

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

        try {
            stream.close();
        } catch (IOException e) {
            // Empty, nothing we can do about it.
        }
    }

    private final boolean shouldFlush() {
        assert Thread.holdsLock(this);
        long sizeAvailableToFlush = pStart - cStart;
        boolean result = flushAndClose || sizeAvailableToFlush >= twentyFivePercentOfBufferCapacity
                || (waitCount >= waitsBeforeFlush && sizeAvailableToFlush > 0);
        return result;
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
        
        assert sizeToFlush >= 0 : "bad sizeToFlush: " + sizeToFlush;

        int index1 = (int) (cStart % bufferCapacity);
        int index2 = (int) ((cStart + sizeToFlush - 1) % bufferCapacity);
        IOException ex = null;

        try {
            if (index2 > index1) {
                stream.append(buffer, index1, sizeToFlush);
            } else {
                stream.append(buffer, index1, bufferCapacity - index1);
                stream.append(buffer, 0, index2 + 1);
            }
        } catch (IOException e) {
            ex = e;
        }

        final long myStreamSize;

        synchronized (this) {
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
        }

        appendListener.dataAppended(myStreamSize);
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
        // 1. Out of bounds: position + length > totalSize. --> IOException
        // 2. All in stream. position + length < streamSize.
        // 3. All in buffer. position + length >= streamSize AND <= totalSize
        // 4. One part in buffer, one part in stream.
        //
        // Reads from buffer are made in synchronized block; it is very fast.
        //

        assert dest.length - destOffset >= length;

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

            if (pos2 > totalLength) {
                throw new IOException("Cannot read " + length + " bytes at position " + position
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
        this.appendHasBeenCalled = true;

        synchronized (this) {
            if (this.exception != null) {
                throw exception;
            }

            while (length > 0) {
                int available = availableBufferSize();
                if (available < length && available < tenPercentOfBufferCapacity) {
                    try {
                        wait(); // wait for consumer to write to output stream
                    } catch (InterruptedException e) {
                        throw new IOException("Thread interrupted while appending.");
                    }
                } else {
                    int len = length <= available ? length : available;
                    appendToBuffer(source, sourceOffset, len);
                    length -= len;
                    sourceOffset += len;
                }
            }
        }
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

    public void pretruncate(long position) throws IOException {
        stream.pretruncate(position);
    }

    /**
     * @throws IOException
     * @throws IllegalStateException
     */
    public void seekFirstPos(long position) throws IOException {
        if (appendHasBeenCalled) {
            throw new IllegalStateException("append() has been called, cannot call seekTo("
                    + position + ").");
        }

        stream.seekFirstPos(position);

        long length = stream.getLength();
        totalLength = length;
        streamLength = length;
    }

    public void setAppendListener(AppendListener appendListener) {
        if (appendListener == null) {
            throw new IllegalArgumentException("appendListener == null not allowed");
        }
        this.appendListener = appendListener;
    }

    public void close() throws IOException {
        synchronized (this) {
            this.flushAndClose = true;
            if (this.exception == null) {
                this.exception = new IOException("Stream being closed by flushAndClose()");
            }

            if (this.stop) {
                // Already stopped
                return;
            }

            while (pStart - cStart > 0) {
                try {
                    wait(); // Waiting for consumer to flush to output stream
                } catch (InterruptedException e) {
                    return;
                }
            }
        }

        stop();

        stream.close();
    }

    /**
     * Eventually stops thread and closes stream. This method returns
     * immediately.
     */
    public void stop() {
        synchronized (this) {
            if (this.exception == null) {
                this.exception = new IOException("Stream being stopped.");
            }
            this.stop = true;
        }
    }
    
    // ======== Test ========

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
}
