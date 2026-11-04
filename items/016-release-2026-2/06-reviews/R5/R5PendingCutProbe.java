package bergdb.core;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.storage.AppendListener;
import bergdb.storage.BufferedStream;
import bergdb.stream.MemoryStream;

/** A cut arriving during application of another pending cut must not be stranded. */
public class R5PendingCutProbe {
    private static final class Cuts extends MemoryStream {
        final AtomicLong lastCut = new AtomicLong();
        final CountDownLatch entered = new CountDownLatch(1);
        final CountDownLatch release = new CountDownLatch(1);
        @Override public void pretruncate(long pos) {
            lastCut.accumulateAndGet(pos, Math::max);
            if (pos == 200) {
                entered.countDown();
                try {
                    if (!release.await(500, TimeUnit.MILLISECONDS)) {
                        throw new AssertionError("test did not release first cut");
                    }
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    throw new AssertionError(e);
                }
            }
            super.pretruncate(pos);
        }
    }
    private static void require(boolean yes, String message) {
        if (!yes) throw new AssertionError(message);
    }
    public static void main(String[] args) throws Exception {
        Object lock = new Object();
        Cuts s = new Cuts();
        BufferedStream b;
        CountDownLatch flushed = new CountDownLatch(1);
        synchronized (lock) {
            s.append(new byte[100], 0, 100);
            b = new BufferedStream(s, 1000, 10);
            b.setAppendListener(new AppendListener() {
                public void dataAppended(long len) { flushed.countDown(); }
                public void appendFailed(java.io.IOException e) {
                    throw new AssertionError(e);
                }
            });
            b.append(new byte[300], 0, 300);
            b.pretruncate(200);
            b.start();
        }
        try {
            require(s.entered.await(500, TimeUnit.MILLISECONDS), "first cut did not start");
            // The underlying stream is already 400 bytes long, but B.streamLength
            // is still 100 until the consumer publishes this flush.
            synchronized (lock) { b.pretruncate(300); }
            s.release.countDown();
            require(flushed.await(500, TimeUnit.MILLISECONDS), "flush not published");
        } finally {
            s.release.countDown();
            synchronized (lock) { b.close(); }
        }
        System.out.println("requestedCut=300; delegatedCut=" + s.lastCut.get()
                + "; flushedLength=" + s.getLength() + "; bufferClosed=true");
        require(s.lastCut.get() == 200, "expected BASE's missed cut was not reproduced");
    }
}
