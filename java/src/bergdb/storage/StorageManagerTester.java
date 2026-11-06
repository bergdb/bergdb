package bergdb.storage;

import java.io.File;
import java.io.IOException;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.stream.CutStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.ReadBelowFirstPosException;

public class StorageManagerTester {

    /**
     * 2026-10-13 (bergdb 011-04, W1). A read of bytes that a cut removed
     * fails alone. Before, StorageManager closed the stream and set an error state, so that
     * every later read and append failed: the database stopped.
     */
    @Nano
    public static void testReadBelowFirstPosIsNotAStreamError() throws IOException {
        CutStream cut = new CutStream();
        byte[] bytes = new byte[1000];
        cut.append(bytes, 0, 1000);
        StorageManager m = new StorageManager.Builder().stream(cut).build();
        m.start();
        m.pretruncate(600);

        try {
            m.read(100, new byte[10], 0, 10);
            throw new AssertionError("a read below the cut succeeded");
        } catch (ReadBelowFirstPosException e) {
            // Expected.
        }

        m.read(700, new byte[10], 0, 10);
        m.append(bytes, 0, 100);
        m.read(1000, new byte[10], 0, 10);
        m.stop();
    }
    
    @Nano
    public static void testMultipleClose(TestEnvironment c) throws IOException, InterruptedException {
        File temp = c.createTempDir();
        
        File mainDir = new File(temp, "main");
        FileStream main = new FileStream(mainDir);
        
        byte[] bytes = new byte[1000];
        main.append(bytes, 0, 1000);
        main.append(bytes, 0, 1000);
        
        StorageManager m = new StorageManager.Builder().stream(main).build();
        m.start();
        
        m.close();
        m.close();
    }    
    
    @Nano
    public static void testWait1() throws IOException, InterruptedException {
        // Tests a call to sync() that should return immediately.
        
        MemoryStream m = new MemoryStream();
        final StorageManager manager = new StorageManager.Builder().stream(m).build();
        
        long t = System.nanoTime();
        manager.sync(0);
        t = System.nanoTime() - t;
        double time = t * 1e-9;
        Assert.assertTrue(time < 0.05);
        
        manager.stop();
    }
    
    @Nano
    public static void testWait2(final TestEnvironment c) throws IOException, InterruptedException {        
        MemoryStream m = new MemoryStream();
        Object writeLock = new Object();
        final StorageManager manager;
        
        synchronized (writeLock) {
            manager = new StorageManager.Builder().stream(m, 10*1000, 100).build();
            manager.start();
        }
        
        final double[] time = new double[1];
        
        Thread t = new Thread(new Runnable() {
            public void run() {
                long nanos = System.nanoTime();
                try {
                    manager.sync(10);
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
                nanos = System.nanoTime() - nanos;
                time[0] = nanos * 1e-9;
                c.report("waitTime", time[0]);
            }
        });
        
        t.start();
        byte[] bytes = new byte[12];
        synchronized (writeLock) {
            manager.append(bytes, 0, bytes.length);
        }
        t.join();
        
        // 2026-10-27 (bergdb 005-48, group commit): the sync has the buffer written at once.
        // It waited for the timer, 25 to 100 ms here, and the test asserted more than 20 ms.
        // Now it waits for the append and the flush only; the bytes are written when it
        // returns.
        Assert.assertEquals(12, m.getLength());
        Assert.assertTrue("time[0] = " + time[0], time[0] < 0.30);
        
        manager.stop();
    }
    
    /**
     * Group commit (2026-10-27, bergdb 005-48): sync() has the buffer of the stream written
     * at once, with a buffer time of 4 s. Before, it waited for the timer, about a buffer
     * time. Until 2026-11-04 (bergdb 005-11) the test also had a replica, and syncStrong().
     */
    @Nano
    public static void testSyncStartsTheFlush() throws IOException {
        MemoryStream m1 = new MemoryStream();
        Object writeLock = new Object();
        StorageManager manager;
        synchronized (writeLock) {
            manager = new StorageManager.Builder().stream(m1, 10 * 1000, 4000).build();
            manager.start();
        }
        
        try {
            byte[] bytes = new byte[100];
            synchronized (writeLock) {
                manager.append(bytes, 0, bytes.length);
            }
            long t0 = System.nanoTime();
            manager.sync(100);
            long ms1 = (System.nanoTime() - t0) / 1000000;
            Assert.assertEquals(100, m1.getLength());
            Assert.assertTrue("sync() took " + ms1 + " ms", ms1 < 1000);
        } finally {
            manager.close();
        }
    }

    /**
     * A waiting sync throws at once when the main stream fails (bergdb 019-41): the stream's
     * append is held until the sync waits, then throws. Until 019-41 nothing woke the sync,
     * which saw the failure at its next poll, up to 500 ms later.
     */
    @Nano
    public static void testSyncWokenByAFailure() throws Exception {
        final java.util.concurrent.CountDownLatch entered =
                new java.util.concurrent.CountDownLatch(1);
        final java.util.concurrent.CountDownLatch release =
                new java.util.concurrent.CountDownLatch(1);
        bergdb.stream.StrictStream s = new bergdb.stream.StrictStream(new MemoryStream());
        s.setHook((op, n) -> {
            if (op == bergdb.stream.StrictStream.Op.APPEND) {
                entered.countDown();
                try {
                    release.await(5, java.util.concurrent.TimeUnit.SECONDS);
                } catch (InterruptedException e) {
                    throw new IOException(e);
                }
                throw new IOException("the test's failure");
            }
        });
        final StorageManager m = new StorageManager.Builder().stream(s, 1000, 4000).build();
        m.start();
        final long[] thrownAt = new long[1];
        Thread syncer = new Thread(() -> {
            try {
                m.sync(100);
            } catch (IOException e) {
                thrownAt[0] = System.nanoTime();
            }
        }, "test-sync");
        try {
            m.append(new byte[100], 0, 100);
            syncer.start();
            Assert.assertTrue("the append was not held",
                    entered.await(5, java.util.concurrent.TimeUnit.SECONDS));
            long end = System.nanoTime() + 5000L * 1000 * 1000;
            while (syncer.getState() != Thread.State.TIMED_WAITING && System.nanoTime() < end) {
                Thread.sleep(1);
            }
            long t0 = System.nanoTime();
            release.countDown();
            syncer.join(5000);
            Assert.assertTrue("the sync threw", thrownAt[0] != 0);
            long ms = (thrownAt[0] - t0) / 1000000;
            Assert.assertTrue("the sync threw " + ms + " ms after the failure", ms < 50);
        } finally {
            release.countDown();
            syncer.join(5000);
            m.close();
        }
    }

    /**
     * bergdb 019-40 (review R6 of 006-13, C2): a failed read records the failure before
     * anything that allocates (bergdb 019-10). Before, the error's message came first, with
     * the failure's toString(), and an OutOfMemoryError there lost the failure for good.
     */
    @Nano
    public static void testReadFailureRecordedFirst() throws IOException {
        final OutOfMemoryError oom = new OutOfMemoryError("test: no memory for the message");
        final IOException failure = new IOException("test: a read error") {
            public String toString() {
                throw oom;
            }
        };
        MemoryStream main = new MemoryStream() {
            public void read(long position, byte[] dest, int off, int len) throws IOException {
                throw failure;
            }
        };
        main.append(new byte[100], 0, 100);
        StorageManager m = new StorageManager.Builder().stream(main).build();
        m.start();
        Throwable thrown = null;
        try {
            m.read(10, new byte[10], 0, 10);
        } catch (Throwable e) {
            thrown = e;
        }
        Assert.assertTrue("the read throws its failure", thrown == failure);
        Assert.assertTrue("the storage has failed", m.getFailure() == failure);
        m.close();
    }
}
