package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.Random;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StreamIoException;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;

/**
 * Interrupts of the calling thread, and of BergDB's own storage thread (2026-10-27, bergdb
 * 005-46). The rule: an interrupt never fails the database or hangs it. Three calls only
 * wait and end on an interrupt: sync() (it throws), a job's join() (it returns; in
 * bergdb.pubimp's tests) and the Pub API's wait before a rerun. Every other call ignores an
 * interrupt until it is done. A call keeps the thread's interrupt flag set if it was set
 * before or during the call. Before, a commit that made a physical cut or waited for room in
 * the write buffer failed the database, close() returned before the storage was closed, a
 * new FileStream threw, and an interrupt of the storage thread hung the database.
 *
 * <p>Every test stops or closes each database it starts.</p>
 */
public class InterruptTester {
    static final long SEC = Clock.UNITS_PER_SEC;

    private InterruptTester() {}

    /** Runs 'r' with the interrupt flag set, and checks that the flag is still set after. */
    private static void interrupted(Runnable r) {
        Thread.currentThread().interrupt();
        try {
            r.run();
            Assert.assertTrue("the interrupt flag was lost", Thread.currentThread().isInterrupted());
        } finally {
            Thread.interrupted();
        }
    }

    private static File tempDir(String name) throws IOException {
        return Files.createTempDirectory("bergdb-interrupt-" + name + "-").toFile();
    }

    private static void remove(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) remove(c);
        f.delete();
    }

    /** Works on the database: a put and a get, without an interrupt. */
    private static void works(Db db) {
        db.execute(db.trans().put("/works", new byte[] {7}).build());
        Assert.assertEquals((byte) 7, DbUtil.get(db, "/works")[0]);
    }

    /**
     * A commit that makes a physical cut, its thread interrupted (InterruptCutProbe of
     * 005-46): the directory's force closed its FileChannel, the cut threw
     * ClosedByInterruptException, and the database failed. The configuration is
     * FileStreamPowerLossTester's; a sync every fifth commit lets the cuts be made.
     */
    @Nano
    public static void testCommitsThatMakeCuts() throws Exception {
        File dir = tempDir("cut");
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(SEC);
        final FileStream fs = new FileStream(dir);
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        final Db db = b.stream("main", fs, 1000 * 1000, 10).clock(clock).startupDistance(20000)
                .start();
        db.setRetainDuration(2 * SEC);      // Kept in the stream (bergdb 015-87).
        try {
            Random r = new Random(1);
            long time = SEC;
            long firstPos = fs.getFirstPos();
            int cuts = 0;
            for (int i = 0; i < 600 && cuts < 3; i++) {
                time += SEC / 10;
                clock.setTime(time);
                final byte[] value = new byte[1000 + r.nextInt(1000)];
                final String key = "/k" + r.nextInt(12);
                interrupted(() -> db.execute(db.trans().put(key, value).build()));
                if (i % 5 == 0) {
                    db.sync(SyncLevel.ORDINARY);
                }
                if (fs.getFirstPos() != firstPos) {
                    firstPos = fs.getFirstPos();
                    cuts++;
                }
            }
            Assert.assertTrue("no physical cut was made", cuts > 0);
            fs.awaitDeletes();
            works(db);
        } finally {
            db.close();
            remove(dir);
        }
    }

    /** A FileStreamIo whose file forces wait while 'hold' is set. */
    private static final class HeldForces extends FileStreamIo {
        volatile CountDownLatch hold;

        protected void forceFile(File file, RandomAccessFile handle) throws IOException {
            CountDownLatch h = hold;
            if (h != null) {
                try {
                    h.await(10, TimeUnit.SECONDS);
                } catch (InterruptedException e) {
                    throw new IOException(e);
                }
            }
            super.forceFile(file, handle);
        }
    }

    /**
     * A commit that waits for room in the write buffer, its thread interrupted: the wait threw
     * an IOException ("Thread interrupted while appending."), which failed the storage and
     * the database. Now it waits on, and the test report counts the wait.
     */
    @Nano
    public static void testCommitThatWaitsForRoom() throws Exception {
        File dir = tempDir("room");
        HeldForces io = new HeldForces();
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        final Db db = b.stream("main", new FileStream(dir, io), 100 * 1000, 10).start();
        try {
            db.sync(SyncLevel.ORDINARY);
            db.internal().takeWriteBufferWaits();
            final CountDownLatch hold = new CountDownLatch(1);
            io.hold = hold;
            new Thread(new Runnable() {
                public void run() {
                    try {
                        Thread.sleep(300);
                    } catch (InterruptedException e) {
                        // empty
                    }
                    hold.countDown();
                }
            }).start();
            for (int i = 0; i < 20; i++) {
                final String key = "/r" + i;
                interrupted(() -> db.execute(db.trans().put(key, new byte[20 * 1000]).build()));
            }
            io.hold = null;
            String waits = db.internal().takeWriteBufferWaits();
            Assert.assertTrue(waits, !waits.startsWith("waits for room in the write buffer 0,"));
            works(db);
        } finally {
            io.hold = null;
            db.close();
            remove(dir);
        }
    }

    /**
     * sync() by an interrupted thread throws, the database goes on, and the flag stays set;
     * the wait cleared it.
     */
    @Nano
    public static void testSync() throws Exception {
        File dir = tempDir("sync");
        final Db db = Db.builder().stream("main", new FileStream(dir)).testId().start();
        try {
            db.execute(db.trans().put("/a", new byte[100]).build());
            interrupted(() -> {
                try {
                    db.sync(SyncLevel.ORDINARY);
                } catch (StreamIoException e) {
                    // Expected, unless the transaction was durable already.
                }
            });
            works(db);
        } finally {
            db.close();
            remove(dir);
        }
    }

    /**
     * A new FileStream, a start, a commit, a get and close() by an interrupted thread. The new
     * FileStream threw ClosedByInterruptException (its directory force), and close(), the
     * first close, returned before the write buffer was written and the stream closed.
     */
    @Nano
    public static void testStartCommitAndClose() throws Exception {
        final File dir = tempDir("close");
        try {
            final FileStream[] fs = new FileStream[1];
            final Db[] db = new Db[1];
            interrupted(() -> {
                try {
                    fs[0] = new FileStream(dir);
                } catch (IOException e) {
                    throw new AssertionError(e);
                }
                db[0] = Db.builder().stream("main", fs[0]).testId().start();
                for (int i = 0; i < 100; i++) {
                    db[0].execute(db[0].trans().put("/c" + i, new byte[100]).build());
                }
                DbUtil.get(db[0], "/c1");
                db[0].close();
            });
            try {
                fs[0].read(0, new byte[1], 0, 1);
                throw new AssertionError("the stream was open after close()");
            } catch (IOException e) {
                // Expected: closed.
            }
            Db again = Db.builder().stream("main", new FileStream(dir)).testId().start();
            try {
                Assert.assertTrue(DbUtil.get(again, "/c99") != null);
            } finally {
                again.close();
            }
        } finally {
            remove(dir);
        }
    }

    /**
     * BergDB's storage thread interrupted from outside, as ThreadGroup.interrupt() does: it
     * ended with a Bug, and commits and syncs then waited for ever. Now it goes on.
     */
    @Nano
    public static void testStorageThreadInterrupted() throws Exception {
        File dir = tempDir("storage");
        final Db db = Db.builder().stream("main", new FileStream(dir)).testId().start();
        try {
            db.execute(db.trans().put("/a", new byte[100]).build());
            db.sync(SyncLevel.ORDINARY);
            for (Thread t : Thread.getAllStackTraces().keySet()) {
                if (t.getName().startsWith("BufferedStream-consumer")) {
                    t.interrupt();
                }
            }
            final Throwable[] failure = new Throwable[1];
            Thread syncer = new Thread(new Runnable() {
                public void run() {
                    try {
                        db.execute(db.trans().put("/b", new byte[100]).build());
                        db.sync(SyncLevel.ORDINARY);
                    } catch (Throwable e) {
                        failure[0] = e;
                    }
                }
            });
            syncer.setDaemon(true);
            syncer.start();
            syncer.join(30 * 1000);
            Assert.assertTrue("the sync hung", !syncer.isAlive());
            Assert.assertTrue(failure[0] == null);
            works(db);
        } finally {
            db.close();
            remove(dir);
        }
    }

    /** Waits for Jmx.Speed's monitor thread to sleep, and returns it. */
    private static Thread sleepingMonitor() throws InterruptedException {
        long end = System.nanoTime() + 30 * 1000 * 1000 * 1000L;
        while (System.nanoTime() < end) {
            for (Thread t : Thread.getAllStackTraces().keySet()) {
                if (t.getName().equals("DBMonitor.MThread")
                        && t.getState() == Thread.State.TIMED_WAITING) {
                    return t;
                }
            }
            Thread.sleep(1);
        }
        throw new AssertionError("no sleeping monitor thread");
    }

    /**
     * Jmx.Speed's monitor thread interrupted (bergdb 015-38, R3-F4 of 016-06): it ended, its
     * speeds stayed as they were, and registerAndStart() did not start it again, as its
     * thread was still set. Now it goes on. About a second: stop() waits for its sleep.
     */
    @Nano("f")
    public static void testJmxMonitorInterrupted() throws Exception {
        Db db = Db.builder().testSetup().start();
        Jmx.Speed speed = new Jmx.Speed(db);
        try {
            speed.registerAndStart();
            Thread monitor = sleepingMonitor();
            monitor.interrupt();
            monitor.join(200);
            Assert.assertTrue("the monitor ended on an interrupt", monitor.isAlive());
        } finally {
            speed.stop();
            db.close();
        }
    }

    /**
     * Jmx.Speed.stop() with the caller's interrupt flag set (bergdb 015-38, R3-F4 of 016-06):
     * it returned before the monitor thread ended, and cleared the flag. Now it waits for the
     * monitor and keeps the flag. About a second: stop() waits for the monitor's sleep.
     */
    @Nano("f")
    public static void testJmxStopInterrupted() throws Exception {
        Db db = Db.builder().testSetup().start();
        Jmx.Speed speed = new Jmx.Speed(db);
        try {
            speed.registerAndStart();
            final Thread monitor = sleepingMonitor();
            interrupted(new Runnable() {
                public void run() {
                    try {
                        speed.stop();
                    } catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                }
            });
            Assert.assertTrue("stop() returned before the monitor ended", !monitor.isAlive());
        } finally {
            db.close();
        }
    }
}
