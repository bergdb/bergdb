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
}
