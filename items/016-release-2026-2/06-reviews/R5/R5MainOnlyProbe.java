package bergdb.core;

import java.io.IOException;
import java.util.Arrays;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;
import bergdb.common.NullProgressListener;
import bergdb.storage.BufferedStream;
import bergdb.storage.StorageManager;
import bergdb.stream.MemoryStream;

/** Short correctness probes, with one main stream and no replica. */
public class R5MainOnlyProbe {
    private static void require(boolean yes, String message) {
        if (!yes) throw new AssertionError(message);
    }

    private static final class HeldFirst extends MemoryStream {
        final CountDownLatch entered = new CountDownLatch(1);
        final CountDownLatch release = new CountDownLatch(1);
        final AtomicInteger appends = new AtomicInteger();

        @Override public void append(byte[] bytes, int offset, int length) throws IOException {
            if (appends.incrementAndGet() == 1) {
                entered.countDown();
                try {
                    require(release.await(500, TimeUnit.MILLISECONDS), "first flush not released");
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    throw new IOException(e);
                }
            }
            super.append(bytes, offset, length);
        }
    }

    private static Thread waiter(StorageManager m, long length,
            AtomicReference<Throwable> error) {
        Thread t = new Thread(() -> {
            try { m.sync(length); } catch (Throwable e) { error.compareAndSet(null, e); }
        }, "R5-sync-" + length);
        t.setDaemon(true);
        t.start();
        return t;
    }

    private static void awaitWaiting(Thread t) throws InterruptedException {
        long until = System.nanoTime() + 500_000_000L;
        while (t.getState() != Thread.State.TIMED_WAITING) {
            require(t.isAlive() && System.nanoTime() < until, "sync did not wait: " + t);
            Thread.sleep(1);
        }
    }

    private static void groupCommit() throws Exception {
        Object lock = new Object();
        HeldFirst s = new HeldFirst();
        StorageManager m;
        synchronized (lock) {
            m = new StorageManager.Builder(lock).stream("main", s, 4096, 60000).build();
            m.syncStreams(new NullProgressListener());
            m.append(new byte[100], 0, 100);
        }
        AtomicReference<Throwable> error = new AtomicReference<>();
        Thread first = null, second = null, third = null;
        try {
            first = waiter(m, 100, error);
            require(s.entered.await(500, TimeUnit.MILLISECONDS), "demand flush did not start");
            synchronized (lock) {
                m.append(new byte[100], 0, 100);
                m.append(new byte[100], 0, 100);
            }
            second = waiter(m, 200, error);
            third = waiter(m, 300, error);
            awaitWaiting(second);
            awaitWaiting(third);
            require(m.getDurableLength() == 0, "acknowledged an unfinished append");
            s.release.countDown();
            first.join(500);
            second.join(500);
            third.join(500);
            require(!first.isAlive() && !second.isAlive() && !third.isAlive(), "sync stuck");
            require(error.get() == null, "sync threw: " + error.get());
            require(m.getDurableLength() == 300 && s.getLength() == 300, "bad durable frontier");
            require(s.appends.get() == 2, "arrivals were not grouped: " + s.appends.get());
            System.out.println("group: 3 syncs; 2 appends; durable length 300; no early ack; PASS");
        } finally {
            s.release.countDown();
            for (Thread t : new Thread[] {first, second, third}) {
                if (t != null && t.isAlive()) { t.interrupt(); t.join(500); }
            }
            m.closeAndThrow();
        }
    }

    private static void ring() throws Exception {
        MemoryStream s = new MemoryStream();
        byte[] prefix = new byte[150];
        Arrays.fill(prefix, (byte) 17);
        s.append(prefix, 0, prefix.length);
        BufferedStream b = new BufferedStream(s, 1001, 60000);
        byte[] expected = new byte[150 + 32 * 317];
        System.arraycopy(prefix, 0, expected, 0, 150);
        b.start();
        try {
            for (int i = 0; i < 32; i++) {
                byte[] bytes = new byte[317];
                Arrays.fill(bytes, (byte) (i + 31));
                int pos = 150 + i * 317;
                System.arraycopy(bytes, 0, expected, pos, bytes.length);
                b.append(bytes, 0, bytes.length);
                byte[] actual = new byte[317];
                b.read(pos, actual, 0, actual.length);
                require(Arrays.equals(bytes, actual), "buffer/stream read mismatch at " + pos);
            }
        } finally {
            b.close();
        }
        MemoryStream copy = s.copy();
        try {
            byte[] actual = new byte[expected.length];
            copy.read(0, actual, 0, actual.length);
            require(copy.getLength() == expected.length && Arrays.equals(expected, actual),
                    "wrong bytes after wrapping and close");
            System.out.println("ring: nonempty start; odd capacity 1001; 10294 bytes exact; PASS");
        } finally { copy.close(); }
    }

    public static void main(String[] args) throws Exception {
        groupCommit();
        ring();
    }
}
