package bergdb.storage;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;

import bergdb.common.NullProgressListener;
import bergdb.common.ProgressListener;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.util.StorageInfo;
import bergdb.stream.CutStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.ReadBelowFirstPosException;

public class StorageManagerTester {

    @Nano
    public static void testSync1() throws IOException {
        MemoryStream m1 = new MemoryStream();
        MemoryStream m2 = new MemoryStream();
        
        byte[] buffer = new byte[100];
        buffer[0] = 1;
        buffer[99] = 2;
        
        m1.append(buffer, 0, buffer.length);
        m1.append(buffer, 0, buffer.length);
        m2.append(buffer, 0, buffer.length);
        
        Assert.assertEquals(200, m1.getLength());
        Assert.assertEquals(100, m2.getLength());
        
        Object writeLock = new Object();
        
        synchronized (writeLock) {
            StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("m1", m1).stream("m2", m2).build();
            manager.syncStreams(new NullProgressListener());
            manager.syncStrong(200);
            Assert.assertEquals(200, m1.getLength());
            Assert.assertEquals(200, m2.getLength());
            
            manager.stop();
        }
    }
    
    @Nano
    public static void testSync2() throws IOException {
        MemoryStream m1 = new MemoryStream();
        MemoryStream m2 = new MemoryStream();
        MemoryStream m3 = new MemoryStream();
        
        byte[] buffer = new byte[100];
        buffer[0] = 1;
        buffer[99] = 2;
        
        m1.append(buffer, 0, buffer.length);
        m1.append(buffer, 0, buffer.length);
        m2.append(buffer, 0, buffer.length);
        m2.append(buffer, 0, buffer.length);
        m2.append(buffer, 0, buffer.length);
        m3.append(buffer, 0, buffer.length);
        
        Assert.assertEquals(200, m1.getLength());
        Assert.assertEquals(300, m2.getLength());
        Assert.assertEquals(100, m3.getLength());
        
        Object writeLock = new Object();
        
        synchronized (writeLock) {
            StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("m1", m1)
                .stream("m2", m2)
                .stream("m3", m3).build();
            
            // Demand all stream to be confirmed.
            manager.setD2(new DurabilityRule() {
                public long computeSize(StorageInfo[] storages) {
                    long min = Long.MAX_VALUE;
                    for (int i = 0; i < storages.length; i++) {
                        long confirmedSize = storages[i].getConfirmedLength();
                        if (confirmedSize < min) {
                            min = confirmedSize;
                        }
                    }
                    return min;
                }
            });
            
            manager.syncStreams(new NullProgressListener());
            manager.syncStrong(300);
            manager.stop();
        }
        
        Assert.assertEquals(300, m1.getLength());
        Assert.assertEquals(300, m2.getLength());
        Assert.assertEquals(300, m3.getLength());
    }
    
    @Nano
    public static void testSync3() throws IOException {
        MemoryStream m1 = new MemoryStream();
        MemoryStream m2 = new MemoryStream();
        
        byte[] bytes = new byte[1000];
        m1.append(bytes, 0, 700);
        m2.append(bytes, 0, 200);
        
        Object writeLock = new Object();
        StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", m1).stream("r", m2).build();
        manager.syncStreams(new NullProgressListener());
        manager.syncStrong(700);
        
        Assert.assertEquals(700, m1.getLength());
        Assert.assertEquals(700, m2.getLength());
        manager.stop();
    }
    
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
        StorageManager m = new StorageManager.Builder(new Object()).stream("main", cut).build();
        m.syncStreams(new NullProgressListener());
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
    public static void testSync4(TestEnvironment c) throws IOException, InterruptedException {
        // Testing with real files.
        
        File temp = c.createTempDir();
        
        File mainDir = new File(temp, "main");
        File rDir = new File(temp, "r");
        
        FileStream main = new FileStream(mainDir);
        FileStream r = new FileStream(rDir);
        
        byte[] bytes = new byte[200*1000];
        bytes[0] = 1;
        bytes[999] = 2;
        
        main.append(bytes, 0, 200*1000);
        main.append(bytes, 0, 200*1000);
        main.append(bytes, 0, 200*900);
        
        //for (String s : mainDir.list()) {
        //    System.out.println("- " + s);
        //}
        
        main.pretruncate(200*1000);    // Removes first file
        
        //for (String s : mainDir.list()) {
        //    System.out.println("* " + s);
        //}
        
        StorageManager m = new StorageManager.Builder(new Object())
                .stream("main", main).stream("r", r).build();
        m.syncStreams(new NullProgressListener());
        m.close();
        
        // The stream's files, not bergdb.lock (bergdb 005-63).
        java.io.FilenameFilter streamFiles = (d, name) -> name.endsWith(".bergdb");
        String[] fileNames = mainDir.list(streamFiles);
        Arrays.sort(fileNames);
        Assert.assertEquals(2, fileNames.length);
        Assert.assertEquals("00000000000002.bergdb", fileNames[0]);
        Assert.assertEquals("00000000000004.bergdb", fileNames[1]);
        
        fileNames = rDir.list(streamFiles);
        Arrays.sort(fileNames);
        Assert.assertEquals(2, fileNames.length);
        Assert.assertEquals("00000000000002.bergdb", fileNames[0]);
        Assert.assertEquals("00000000000004.bergdb", fileNames[1]);
        
        File[] files = mainDir.listFiles(streamFiles);
        Arrays.sort(files);
        Assert.assertEquals(200*1000, files[0].length());
        Assert.assertEquals(200*900, files[1].length());
        
        files = rDir.listFiles(streamFiles);
        Arrays.sort(files);
        Assert.assertEquals(200*1000, files[0].length());
        Assert.assertEquals(200*900, files[1].length());
    }
    
    @Nano
    public static void testMultipleClose(TestEnvironment c) throws IOException, InterruptedException {
        File temp = c.createTempDir();
        
        File mainDir = new File(temp, "main");
        File rDir = new File(temp, "r");
        FileStream main = new FileStream(mainDir);
        FileStream r = new FileStream(rDir);
        
        byte[] bytes = new byte[1000];
        main.append(bytes, 0, 1000);
        main.append(bytes, 0, 1000);
        
        StorageManager m = new StorageManager.Builder(new Object())
                .stream("main", main).stream("r", r).build();
        m.syncStreams(new NullProgressListener());
        
        m.close();
        m.close();
    }    
    
    @Nano
    public static void testWait1() throws IOException, InterruptedException {
        // Tests a call to sync() that should return immediately.
        
        MemoryStream m = new MemoryStream();
        Object writeLock = new Object();
        final StorageManager manager;
        
        synchronized (writeLock) {
            manager = new StorageManager.Builder(writeLock).stream("s1", m).build();
        }
        
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
            manager = new StorageManager.Builder(writeLock).stream("s1", m, 10*1000, 100).build();
            manager.syncStreams(new NullProgressListener());
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
     * Group commit (2026-10-27, bergdb 005-48): sync() and syncStrong() have the buffers of
     * their streams written at once, here those of a main stream and a replica, with buffer
     * times of 4 s. Before, each waited for the timers, about a buffer time.
     */
    @Nano
    public static void testSyncStartsTheFlush() throws IOException {
        MemoryStream m1 = new MemoryStream();
        MemoryStream m2 = new MemoryStream();
        Object writeLock = new Object();
        StorageManager manager;
        synchronized (writeLock) {
            manager = new StorageManager.Builder(writeLock)
                    .stream("main", m1, 10 * 1000, 4000).stream("r", m2, 10 * 1000, 4000).build();
            manager.syncStreams(new NullProgressListener());
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
            
            synchronized (writeLock) {
                manager.append(bytes, 0, bytes.length);
            }
            t0 = System.nanoTime();
            manager.syncStrong(200);
            long ms2 = (System.nanoTime() - t0) / 1000000;
            Assert.assertEquals(200, m1.getLength());
            Assert.assertEquals(200, m2.getLength());
            Assert.assertTrue("sync() took " + ms1 + " ms, syncStrong() " + ms2 + " ms",
                    ms1 < 1000 && ms2 < 1000);
        } finally {
            manager.close();
        }
    }
    
    @Nano
    public static void testAddReplica1() throws IOException, InterruptedException {
        final MemoryStream m1 = new MemoryStream();
        final MemoryStream m2 = new MemoryStream();
        
        byte[] bytes = new byte[1000];
        m1.append(bytes, 0, 700);
        m2.append(bytes, 0, 200);
        
        Object writeLock = new Object();
        final StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", m1).build();
        manager.syncStreams(new NullProgressListener());
        
        Assert.assertEquals(700, m1.getLength());
        Assert.assertEquals(200, m2.getLength());
        
        final ProgressListener nullListener = new ProgressListener() {
            public void progress(int progressValue, String note) {
                // empty
            }
        };
        
        final StorageManager.SynchingStorage ss = manager.addReplica("r", m2, 1000, 10);
        
        Thread thread = new Thread(new Runnable() {
            public void run() {
                manager.syncReplica(ss, nullListener);
            }
        });
        thread.start();
        
        while (manager.getStorageInfo("r") == null) {
            Thread.sleep(10);
        }
        
        StorageInfo s = manager.getStorageInfo("r");
        
        while (true) {
            s = manager.getStorageInfo("r");
            assert s != null : "s is null";
            
            if (s.getStatus() == StorageInfo.STATUS_ACTIVE) {
                break;
            }
            
            Thread.sleep(5);
        }
        
        manager.close();
        Assert.assertEquals(700, m1.getLength());
        Assert.assertEquals(700, m2.getLength());
    }
    
    @Nano
    public static void testAddReplica2() throws IOException, InterruptedException {
        // Creates streams, adds replica, appends to StorageManager, asserts.
        
        /*
        NOTE Frans: got non-reproducable unit test error, on Cissi, 150723:
        FAILED! bergdb.storage.StorageManagerTester.testAddReplica2
        java.lang.AssertionError: Expected 800, got 1200.
            at bergdb.nanotest.Assert.assertEquals(Assert.java:37)
            at bergdb.storage.StorageManagerTester.testAddReplica2(StorageManagerTester.java:359)
            ...
        */
        
        final MemoryStream m1 = new MemoryStream();
        final MemoryStream m2 = new MemoryStream();
        
        final byte[] bytes = new byte[1000];
        m1.append(bytes, 0, 700);
        m2.append(bytes, 0, 200);
        
        Object writeLock = new Object();
        final StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", m1).build();
        manager.syncStreams(new NullProgressListener());
        
        Assert.assertEquals(700, m1.getLength());
        Assert.assertEquals(200, m2.getLength());
        
        final StorageManager.SynchingStorage ss = manager.addReplica("r", m2, 1000, 10);
                
        Thread thread = new Thread(new Runnable() { public void run() {
            manager.syncReplica(ss, new NullProgressListener());
        }});
        thread.start();
        
        while (manager.getStorageInfo("r") == null) {
            Thread.sleep(5);
        }
        
        StorageInfo s = manager.getStorageInfo("r");
        while (true) {
            s = manager.getStorageInfo("r");
            if (s.getStatus() == StorageInfo.STATUS_ACTIVE) {
                break;
            }
            
            Thread.sleep(10);
        }
        
        manager.append(bytes, 0, 100);

        Assert.assertEquals(700, m1.getLength());
        Assert.assertEquals(700, m2.getLength());
        
        manager.close();
        
        Assert.assertEquals(800, m1.getLength());
        Assert.assertEquals(800, m2.getLength());
    }
    
    @Nano
    public static void testAddReplica3(TestEnvironment c) throws IOException, InterruptedException {
        // Adds an empty replica, main stream has getFirstPos() > 0.
        
        File mainDir = c.createTempDir();
        File rDir = c.createTempDir();
        FileStream main = new FileStream(mainDir);
        FileStream r = new FileStream(rDir);
        
        byte[] bytes = new byte[200*1000];
        bytes[0] = 1;
        bytes[999] = 2;
        main.append(bytes, 0, 200*1000);
        main.append(bytes, 0, 200*1000);
        main.append(bytes, 0, 200*1000);
        main.pretruncate(200*1000);
        
        Object writeLock = new Object();
        final StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", main).build();
        manager.syncStreams(new NullProgressListener());
        
        Assert.assertEquals("main length", 200*3000, main.getLength());
        Assert.assertEquals("main first pos", 200*1000, main.getFirstPos());
        
        final StorageManager.SynchingStorage ss = manager.addReplica("r", r, 200*1000, 10);
        manager.syncReplica(ss, new NullProgressListener());
        manager.close();
        
        Assert.assertEquals("r first pos", 200*1000, r.getFirstPos());
        Assert.assertEquals("r length", 200*3000, r.getLength());
    }
    

    @Nano
    public static void testAddReplica4(TestEnvironment c) throws IOException {
        // Adds a replica with existing obsolete data.
        
        File mainDir = c.createTempDir();
        File rDir = c.createTempDir();
        FileStream main = new FileStream(mainDir);
        FileStream r = new FileStream(rDir);
        
        final byte[] bytes = new byte[200*1000];
        bytes[0] = 1;
        bytes[999] = 2;
        main.append(bytes, 0, 200*1000);
        r.append(bytes, 0, 200*1000);
        main.append(bytes, 0, 200*1000);
        main.append(bytes, 0, 200*1000);
        main.pretruncate(200*2000);
        
        Object writeLock = new Object();
        StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", main).build();
        manager.syncStreams(new NullProgressListener());
        
        Assert.assertEquals("main length", 200*3000, main.getLength());
        Assert.assertEquals("main first pos", 200*2000, main.getFirstPos());
        
        StorageManager.SynchingStorage ss = manager.addReplica("r", r, 100*1000, 10);
        manager.syncReplica(ss, new NullProgressListener());
        manager.close();
        
        Assert.assertEquals("r first pos", 200*2000, r.getFirstPos());
        Assert.assertEquals("r length", 200*3000, r.getLength());
    }
    
    @Nano
    public static void testAddReplica5(TestEnvironment c) throws IOException {
        // Adds a replica with existing obsolete and non-obsolete data.
        
        File mainDir = c.createTempDir();
        File rDir = c.createTempDir();
        FileStream main = new FileStream(mainDir);
        FileStream r = new FileStream(rDir);
        
        byte[] bytes = new byte[200*1000];
        bytes[0] = 1;
        bytes[999] = 2;
        main.append(bytes, 0, 200*1000);
        r.append(bytes, 0, 200*1000);
        main.append(bytes, 0, 200*1000);
        r.append(bytes, 0, 200*1000);
        main.append(bytes, 0, 200*1000);
        r.append(bytes, 0, 200*500);
        
        main.pretruncate(200*2000);
        r.pretruncate(200*1000);
        
        Object writeLock = new Object();
        StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", main).build();
        manager.syncStreams(new NullProgressListener());
        
        Assert.assertEquals("main length", 200*3000, main.getLength());
        Assert.assertEquals("main first pos", 200*2000, main.getFirstPos());
        
        StorageManager.SynchingStorage ss = manager.addReplica("r", r, 1000*1000, 10);
        manager.syncReplica(ss, new NullProgressListener());
        manager.close();
        
        Assert.assertEquals("r first pos", 200*1000, r.getFirstPos());
        Assert.assertEquals("r length", 200*3000, r.getLength());
    }
    
    @Nano
    public static void testAddReplicaWhileAppending() throws IOException, InterruptedException {
        final MemoryStream m1 = new MemoryStream();
        final MemoryStream m2 = new MemoryStream();
        
        final byte[] bytes = new byte[1000];
        m1.append(bytes, 0, 700);
        m2.append(bytes, 0, 200);
        
        Object writeLock = new Object();
        final StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", m1).build();
        manager.syncStreams(new NullProgressListener());
        
        Assert.assertEquals(700, m1.getLength());
        Assert.assertEquals(200, m2.getLength());
        
        Thread writer = new Thread(new Runnable() {
            public void run() {
                for (int i = 0; i < 5; i++) {
                    try {
                        manager.append(bytes, 0, 10);
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                    
                    try {
                        Thread.sleep(10);
                    } catch (InterruptedException e) {
                        throw new RuntimeException(e);
                    }
                }
            }
        });
        writer.setName("DBStorageManager.testAddReplicaWhileAppending");
        writer.start();
        
        final ProgressListener nullListener = new ProgressListener() {
            public void progress(int progressValue, String note) {}   // empty
        };
        
        final StorageManager.SynchingStorage ss = manager.addReplica("r", m2, 1000, 10);
        
        Thread thread = new Thread(new Runnable() { public void run() {
            manager.syncReplica(ss, nullListener);
        }});
        thread.start();
        
        while (manager.getStorageInfo("r") == null) {
            Thread.sleep(5);
        }
        
        StorageInfo s = manager.getStorageInfo("r");
        while (true) {
            s = manager.getStorageInfo("r");
            if (s.getStatus() == StorageInfo.STATUS_ACTIVE) {
                break;
            }
            
            Thread.sleep(10);
        }
        
        writer.join();
        manager.syncStrong(750);
        
        Assert.assertEquals(750, m1.getLength());
        Assert.assertEquals(750, m2.getLength());
        
        manager.close();
    }
    
    @Nano
    public static void testRemoveReplica1() throws IOException {
        MemoryStream m1 = new MemoryStream();
        MemoryStream m2 = new MemoryStream();
        
        byte[] bytes = new byte[1000];
        m1.append(bytes, 0, 700);
        m2.append(bytes, 0, 200);
        
        Object writeLock = new Object();
        StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", m1).stream("r", m2).build();
        manager.syncStreams(new NullProgressListener());
        manager.syncStrong(700);
        
        Assert.assertEquals(700, m1.getLength());
        Assert.assertEquals(700, m2.getLength());
        
        manager.removeReplica("nonExistantNameDoesNothing");
        Assert.assertTrue(manager.getStorageInfo("r") != null);
        manager.removeReplica("r");
        Assert.assertTrue(manager.getStorageInfo("r") == null);
        
        manager.stop();
    }
    
    @Nano
    public static void testRemoveReplica2() throws IOException {
        MemoryStream m1 = new MemoryStream();
        MemoryStream m2 = new MemoryStream();
        
        byte[] bytes = new byte[1000];
        m1.append(bytes, 0, 700);
        m2.append(bytes, 0, 200);
        
        Object writeLock = new Object();
        StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", m1).stream("r", m2).build();
        manager.syncStreams(new NullProgressListener());
        manager.syncStrong(700);
        
        Assert.assertEquals(700, m1.getLength());
        Assert.assertEquals(700, m2.getLength());
        
        Assert.assertTrue(manager.getStorageInfo("r") != null);
        manager.removeReplica("r");
        Assert.assertTrue(manager.getStorageInfo("r") == null);
        
        manager.append(bytes, 0, 20);
        manager.syncStrong(720);
        Assert.assertEquals(720, m1.getLength());
        Assert.assertEquals(700, m2.getLength());
        
        manager.stop();
    }
}
