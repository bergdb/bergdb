package bergdb.core;

import java.io.IOException;
import java.io.InterruptedIOException;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.util.HashSet;
import java.util.Set;

import bergdb.common.StringUtil;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.StorageInfo;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.MemoryStream;

/**
 * Tests of a transaction that fails after its go point (bergdb 005-01, register M49 of
 * docs/level4-alignment.md; item 003, 003-01's test plan). Until 005-01 such a transaction
 * was half committed: its time became readable with its first puts in memory, and the next
 * transaction wrote its nodes as its own. Now the database fails: the call gets a
 * DbFailedException (an Error is thrown as it is), the transaction's time never becomes a
 * lookup time, every later transaction and read is refused, nothing more is appended, and a
 * restart gives the state before the transaction, also with eviction and the audit on.
 *
 * <p>And of a read or a sync that fails on the storage (bergdb 005-30), which fails the
 * database in the same way. Before 005-30 the read threw a StreamIoException or a
 * StreamFormatException and the database stayed active, half dead: the storage below
 * refuses all I/O after an I/O error. Not failures: a read that a cut has overtaken
 * (ReclaimReaderTester), one while the database stops, an interrupted sync.</p>
 *
 * <p>And of a start that throws, which closes its storage before the exception leaves, and
 * of an Error in a flush, which fails the stream as an IOException does (bergdb 005-32).</p>
 */
public class DbTesterFailure {

    /**
     * 003-01's reproduction (2.1): the second put of a transaction has a value transformation
     * that throws. Before 005-01, /a = a1 was readable after the failure, and the next
     * transaction wrote it.
     */
    @Nano
    public static void testValueTransformationThrows() {
        final long auditFailures = Audit.failures();
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).audit(1).start();
        db.execute(db.trans().put("/a", "a0").put("/b", "b0").build());
        db.sync(SyncLevel.STRONG);
        final long time = db.lookupTime(Long.MAX_VALUE);
        final long length = s.getLength();

        final IllegalStateException thrown = new IllegalStateException("the transformation fails");
        Trans t = db.trans()
                .put(Keys.toSegments("/a"), null, bytes("a1"), null)
                .put(Keys.toSegments("/b"), null, bytes("b1"), new ValueTransformation() {
                    public byte[] transform(long transTime, byte[] inputValue, byte[] previous) {
                        throw thrown;
                    }
                })
                .build();
        DbFailedException e = executeFails(db, t);
        Assert.assertTrue("the cause", e.getCause() == thrown);
        Assert.assertEquals("the lookup time", time, db.lookupTime(Long.MAX_VALUE));
        assertRefused(db, thrown);

        db.sync(SyncLevel.STRONG);      // Still works, for the transactions before.
        Assert.assertEquals("the stream's length", length, s.getLength());
        db.close();

        Db db2 = Db.builder().testSetup(s.copy()).audit(1).start();
        Assert.assertEquals("a0", DbUtil.getString(db2, "/a"));
        Assert.assertEquals("b0", DbUtil.getString(db2, "/b"));
        db2.execute(db2.trans().put("/c", "c2").build());
        Assert.assertEquals("c2", DbUtil.getString(db2, "/c"));
        db2.close();
        Assert.assertEquals("audit failures", auditFailures, Audit.failures());
    }

    /**
     * An Error after the go point is thrown as it is, and fails the database: later calls
     * get a DbFailedException with the Error as the cause.
     */
    @Nano
    public static void testErrorIsThrownAsItIs() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("/a", "a0").build());

        final Error thrown = new Error("an Error in the transaction");
        Trans t = db.trans()
                .put(Keys.toSegments("/a"), null, bytes("a1"), new ValueTransformation() {
                    public byte[] transform(long transTime, byte[] inputValue, byte[] previous) {
                        throw thrown;
                    }
                })
                .build();
        Error error = null;
        try {
            db.execute(t);
        } catch (Error e) {
            error = e;
        }
        Assert.assertTrue("the Error itself", error == thrown);
        assertRefused(db, thrown);
        db.close();
    }

    /**
     * A read error when a put loads an index node that eviction has released (Level 4; also
     * the lazy startup's case). The put follows a path that the warm-up did not read: a key
     * transformation gives the key, as the Pub API's "${transactionTime}" does, and makes
     * the stream fail. The first put has changed the Dag by then.
     */
    @Nano
    public static void testReadErrorInPut() {
        failInPut(false);
    }

    /**
     * As testReadErrorInPut, with a corrupt node instead (a checksum error): the storage stays
     * healthy, so before 005-01 the next transaction wrote the failed one's nodes. Now
     * nothing more is appended.
     */
    @Nano
    public static void testCorruptNodeInPut() {
        failInPut(true);
    }

    private static final int KEYS = 2000;

    private static void failInPut(final boolean corrupt) {
        final long auditFailures = Audit.failures();
        final FaultStream s = new FaultStream();
        Db db = startEvicting(s, 0);
        fill(db);
        db.sync(SyncLevel.STRONG);
        final long time = db.lookupTime(Long.MAX_VALUE);
        final long length = s.getLength();

        KeyTransformation kt = new KeyTransformation() {
            public void transform(Trans trans, int index) {
                if (corrupt) {
                    s.corruptReads = true;
                } else {
                    s.failReads = true;
                }
                long[] key = Keys.toSegments(key(KEYS / 2));
                trans.kvs[index].setKey(key);
                trans.writeKeyHashes[index] = Keys.hash(key);
            }
        };
        Trans t = db.trans()
                .put(Keys.toSegments("/a"), null, bytes("a1"), null)
                .put(Keys.toSegments("/z"), kt, bytes("x"), null)
                .build();
        DbFailedException e = executeFails(db, t);
        Assert.assertTrue("faults made", s.faults > 0);
        if (corrupt) {
            Assert.assertTrue("the cause: " + e.getCause(),
                    e.getCause() instanceof StreamFormatException);
        } else {
            Assert.assertTrue("the cause: " + e.getCause(),
                    e.getCause() instanceof StreamIoException);
        }
        Assert.assertEquals("the lookup time", time, db.lookupTime(Long.MAX_VALUE));
        assertRefused(db, e.getCause());

        if (corrupt) {
            db.sync(SyncLevel.STRONG);
            Assert.assertEquals("the stream's length", length, s.getLength());
        }
        s.failReads = false;
        s.corruptReads = false;
        db.close();

        Db db2 = startEvicting(s.inner.copy(), 1);
        Assert.assertNull(DbUtil.get(db2, "/a"));
        Assert.assertNull(DbUtil.get(db2, "/z"));
        for (int j = 0; j < KEYS; j++) {
            Assert.assertEquals(key(j), "v" + j, DbUtil.getString(db2, key(j)));
        }
        db2.execute(db2.trans().put("/a", "a2").put(key(KEYS / 2), "w").build());
        Assert.assertEquals("a2", DbUtil.getString(db2, "/a"));
        Assert.assertEquals("w", DbUtil.getString(db2, key(KEYS / 2)));
        db2.close();
        Assert.assertEquals("audit failures", auditFailures, Audit.failures());
    }

    /**
     * An append that fails in store(), after the go point: the database fails. A restart
     * gives the state before: the transaction whose buffered record was never written is
     * lost, as in a crash, and the failing one too. The test waits for the failed flush
     * without a sync: since bergdb 005-30 the sync would fail the database first
     * (testSyncFails). Before, it was an f-test with such a sync.
     */
    @Nano
    public static void testAppendErrorInStore() {
        FaultStream s = new FaultStream();
        Db db = Db.builder().testSetup(s).start();
        db.execute(db.trans().put("/a", "a0").build());
        db.sync(SyncLevel.STRONG);

        s.failAppends = true;
        db.execute(db.trans().put("/a", "a1").build());     // In memory and buffered only.
        waitForStorageError(db);

        DbFailedException e = executeFails(db, db.trans().put("/b", "b1").build());
        Assert.assertTrue("the cause: " + e.getCause(), e.getCause() instanceof StreamIoException);
        assertRefused(db, e.getCause());
        s.failAppends = false;
        db.close();

        Db db2 = Db.builder().testSetup(s.inner.copy()).start();
        Assert.assertEquals("a0", DbUtil.getString(db2, "/a"));
        Assert.assertNull(DbUtil.get(db2, "/b"));
        db2.close();
    }

    /**
     * A writer that waits for the write lock while another transaction fails is refused, as it
     * gets the lock: it must not run on what the failed transaction left in memory.
     */
    @Nano
    public static void testWriterWaitingForTheLock() throws Exception {
        final MemoryStream s = new MemoryStream();
        final Db db = Db.builder().testSetup(s).start();
        db.execute(db.trans().put("/a", "a0").build());
        db.sync(SyncLevel.STRONG);

        final Throwable[] waiting = new Throwable[1];
        final Thread writer2 = new Thread(new Runnable() {
            public void run() {
                try {
                    db.execute(db.trans().put("/c", "c1").build());
                } catch (Throwable e) {
                    waiting[0] = e;
                }
            }
        });

        final IllegalStateException thrown = new IllegalStateException("the transformation fails");
        Trans t = db.trans()
                .put(Keys.toSegments("/a"), null, bytes("a1"), null)
                .put(Keys.toSegments("/b"), null, bytes("b1"), new ValueTransformation() {
                    public byte[] transform(long transTime, byte[] inputValue, byte[] previous) {
                        writer2.start();
                        waitUntilBlockedOnTheWriteLock(writer2);
                        throw thrown;
                    }
                })
                .build();
        DbFailedException e = executeFails(db, t);
        Assert.assertTrue("the cause", e.getCause() == thrown);
        writer2.join(10 * 1000);
        Assert.assertTrue("the waiting writer is refused: " + waiting[0],
                waiting[0] instanceof DbFailedException && waiting[0].getCause() == thrown);
        db.close();

        Db db2 = Db.builder().testSetup(s.copy()).start();
        Assert.assertEquals("a0", DbUtil.getString(db2, "/a"));
        Assert.assertNull(DbUtil.get(db2, "/b"));
        Assert.assertNull(DbUtil.get(db2, "/c"));
        db2.close();
    }

    /** A transaction refused before its go point leaves the database as it was, and running. */
    @Nano
    public static void testRefusedBeforeTheGoPoint() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("/a", "a0").build());
        long readTime = db.lookupTime(Long.MAX_VALUE);
        db.execute(db.trans().put("/a", "a1").build());

        Trans t = db.trans().lookupTime(readTime).keyRead("/a").put("/b", "b1").build();
        RerunException rerun = null;
        try {
            db.execute(t);
        } catch (RerunException e) {
            rerun = e;
        }
        Assert.assertTrue("refused", rerun != null);
        Assert.assertNull(DbUtil.get(db, "/b"));

        db.execute(db.trans().put("/c", "c1").build());
        Assert.assertEquals("a1", DbUtil.getString(db, "/a"));
        Assert.assertEquals("c1", DbUtil.getString(db, "/c"));
        db.close();
    }

    // ======== A read or a sync that fails on the storage (bergdb 005-30) ========

    /**
     * A get that loads an index node that eviction has released meets a read error: the
     * storage then refuses all I/O. Before 005-30 the get threw the StreamIoException and
     * the database went on, half dead.
     */
    @Nano
    public static void testReadErrorInGetOne() {
        failInRead(false, false);
    }

    /** As testReadErrorInGetOne, in a scan (Db.getMany). */
    @Nano
    public static void testReadErrorInGetMany() {
        failInRead(true, false);
    }

    /**
     * As testReadErrorInGetOne, with a corrupt node (a checksum error): the storage stays
     * healthy, but the data read is lost, or there is a bug.
     */
    @Nano
    public static void testCorruptNodeInGetOne() {
        failInRead(false, true);
    }

    /** As testCorruptNodeInGetOne, in a scan. */
    @Nano
    public static void testCorruptNodeInGetMany() {
        failInRead(true, true);
    }

    /**
     * The read fails the database: it throws a DbFailedException with the read's exception
     * as the cause, every later transaction and read is refused with it, nothing more is
     * appended, and a restart, with the audit on, gives every key.
     */
    private static void failInRead(boolean many, boolean corrupt) {
        final long auditFailures = Audit.failures();
        final FaultStream s = new FaultStream();
        Db db = startEvicting(s, 0);
        fill(db);
        db.sync(SyncLevel.STRONG);
        final long length = s.getLength();

        if (corrupt) {
            s.corruptReads = true;
        } else {
            s.failReads = true;
        }
        DbFailedException e = null;
        try {
            if (many) {
                DbUtil.checksum(db);
            } else {
                DbUtil.get(db, key(KEYS / 2));
            }
        } catch (DbFailedException ex) {
            e = ex;
        }
        Assert.assertTrue("the read fails the database", e != null);
        Assert.assertTrue("faults made", s.faults > 0);
        if (corrupt) {
            Assert.assertTrue("the cause: " + e.getCause(),
                    e.getCause() instanceof StreamChecksumException);
        } else {
            Assert.assertTrue("the cause: " + e.getCause(),
                    e.getCause() instanceof StreamIoException);
        }
        assertRefused(db, e.getCause());
        s.failReads = false;
        s.corruptReads = false;
        if (corrupt) {
            db.sync(SyncLevel.STRONG);      // The storage is healthy.
        }
        Assert.assertEquals("the stream's length", length, s.getLength());
        db.close();

        Db db2 = startEvicting(s.inner.copy(), 1);
        for (int j = 0; j < KEYS; j++) {
            Assert.assertEquals(key(j), "v" + j, DbUtil.getString(db2, key(j)));
        }
        db2.execute(db2.trans().put(key(KEYS / 2), "w").build());
        Assert.assertEquals("w", DbUtil.getString(db2, key(KEYS / 2)));
        db2.close();
        Assert.assertEquals("audit failures", auditFailures, Audit.failures());
    }

    /**
     * A read error in the warm-up of a transaction, before its go point, fails the database
     * as well; the transaction has not begun.
     */
    @Nano
    public static void testReadErrorInWarmup() {
        final FaultStream s = new FaultStream();
        Db db = startEvicting(s, 0);
        fill(db);
        db.sync(SyncLevel.STRONG);
        final long time = db.lookupTime(Long.MAX_VALUE);
        final long length = s.getLength();

        s.failReads = true;
        DbFailedException e = executeFails(db, db.trans().put(key(KEYS / 2), "w").build());
        Assert.assertTrue("faults made", s.faults > 0);
        Assert.assertTrue("the cause: " + e.getCause(), e.getCause() instanceof StreamIoException);
        Assert.assertEquals("the lookup time", time, db.lookupTime(Long.MAX_VALUE));
        assertRefused(db, e.getCause());
        s.failReads = false;
        Assert.assertEquals("the stream's length", length, s.getLength());
        db.close();

        Db db2 = startEvicting(s.inner.copy(), 1);
        Assert.assertEquals("v" + (KEYS / 2), DbUtil.getString(db2, key(KEYS / 2)));
        db2.close();
    }

    /**
     * A sync that fails fails the database: the storage has failed (here, the flush of a
     * buffered transaction). The sync throws a DbFailedException with the StreamIoException
     * as the cause, and every later transaction and read is refused with it. A restart gives
     * the state before the transaction that was never written. An f-test: the sync returns
     * at StorageManager's next 500 ms poll, as nothing wakes it.
     */
    @Nano("f")
    public static void testSyncFails() {
        FaultStream s = new FaultStream();
        Db db = Db.builder().testSetup(s).start();
        db.execute(db.trans().put("/a", "a0").build());
        db.sync(SyncLevel.STRONG);

        s.failAppends = true;
        db.execute(db.trans().put("/a", "a1").build());     // In memory and buffered only.
        DbFailedException e = null;
        try {
            db.sync(SyncLevel.STRONG);
        } catch (DbFailedException ex) {
            e = ex;
        }
        Assert.assertTrue("the sync fails the database", e != null);
        Assert.assertTrue("the cause: " + e.getCause(), e.getCause() instanceof StreamIoException);
        assertRefused(db, e.getCause());
        s.failAppends = false;
        db.close();

        Db db2 = Db.builder().testSetup(s.inner.copy()).start();
        Assert.assertEquals("a0", DbUtil.getString(db2, "/a"));
        db2.close();
    }

    /**
     * A sync whose thread is interrupted while it waits throws a StreamIoException, as
     * before, and the database goes on: an interrupt is not a failure of the storage
     * (StorageManager throws an InterruptedIOException).
     */
    @Nano
    public static void testInterruptedSync() throws Exception {
        final FaultStream s = new FaultStream();
        final Db db = Db.builder().testSetup(s).start();
        db.execute(db.trans().put("/a", "a0").build());
        db.sync(SyncLevel.STRONG);

        s.holdAppends = true;       // The flush waits, and so does the sync.
        db.execute(db.trans().put("/a", "a1").build());
        final Throwable[] thrown = new Throwable[1];
        Thread syncer = new Thread(new Runnable() {
            public void run() {
                try {
                    db.sync(SyncLevel.STRONG);
                } catch (Throwable e) {
                    thrown[0] = e;
                }
            }
        });
        syncer.start();
        final long end = System.nanoTime() + 10L * 1000 * 1000 * 1000;
        while (syncer.getState() != Thread.State.TIMED_WAITING && System.nanoTime() < end) {
            Thread.sleep(1);
        }
        syncer.interrupt();
        syncer.join(10 * 1000);
        Assert.assertTrue("the sync is interrupted: " + thrown[0],
                thrown[0] instanceof StreamIoException
                && thrown[0].getCause() instanceof InterruptedIOException);

        s.holdAppends = false;
        db.sync(SyncLevel.STRONG);
        db.execute(db.trans().put("/b", "b1").build());
        Assert.assertEquals("a1", DbUtil.getString(db, "/a"));
        Assert.assertEquals("b1", DbUtil.getString(db, "/b"));
        db.close();
    }

    /**
     * A read that runs while the database stops does not fail it: the close of the storage
     * runs under running reads ("Storage is closing."). The read throws the StreamIoException
     * as it is, and the database is stopping, not failed. Here the scan closes the database
     * after its first KV and then loads a node that eviction has released. With close(),
     * which has closed the storage when it returns; stop() closes it in the background since
     * bergdb 005-35, so the load could come before it.
     */
    @Nano
    public static void testReadDuringStop() {
        final FaultStream s = new FaultStream();
        final Db db = startEvicting(s, 0);
        fill(db);
        db.sync(SyncLevel.STRONG);

        GetMany g = db.newGetMany();
        g.lookupTime = Long.MAX_VALUE;
        g.stopCondition = new GetMany.StopCondition() {
            private boolean first = true;

            public int handleKvt(Kvt kvt) {
                if (first) {
                    first = false;
                    db.close();
                }
                return CONTINUE;
            }

            public void eod() {}
        };
        RuntimeException thrown = null;
        try {
            db.getMany(g);
        } catch (RuntimeException e) {
            thrown = e;
        }
        Assert.assertTrue("the read fails as it is: " + thrown,
                thrown instanceof StreamIoException);

        DbStoppingException stopping = null;
        try {
            db.execute(db.trans().put("/later", "x").build());
        } catch (DbStoppingException e) {
            stopping = e;
        }
        Assert.assertTrue("stopping, not failed", stopping != null);
    }

    /**
     * Db.getTrans, the Pub API's Connection.transactionInfo(): a read error fails the
     * database, and after it getTrans is refused (it read on after a failure). So does a
     * format error (here, a corrupt read) since bergdb 005-34, which made the positions that
     * a get gives right; before it, a format error did not fail the database.
     */
    @Nano
    public static void testGetTrans() {
        for (int i = 0; i < 2; i++) {
            final boolean corrupt = i == 0;
            FaultStream s = new FaultStream();
            Db db = Db.builder().testSetup(s).start();
            Trans t = db.trans().put("/a", "a0").build();
            db.execute(t);
            db.sync(SyncLevel.STRONG);
            Assert.assertEquals("the transaction", t.tt, db.getTrans(t.tpos).tt);

            if (corrupt) {
                s.corruptReads = true;
            } else {
                s.failReads = true;
            }
            DbFailedException e = null;
            try {
                db.getTrans(t.tpos);
            } catch (DbFailedException ex) {
                e = ex;
            }
            Assert.assertTrue("the read fails the database, corrupt " + corrupt, e != null);
            Class<?> cause = corrupt ? StreamFormatException.class : StreamIoException.class;
            Assert.assertTrue("the cause: " + e.getCause(), cause.isInstance(e.getCause()));
            assertRefused(db, e.getCause());
            s.corruptReads = false;
            s.failReads = false;
            db.close();
        }
    }

    /**
     * Db.getTrans of a transaction that reclaim has removed (here, a cut of the stream
     * itself) throws a LookupTimeNotAvailableException, and the database goes on, as for a
     * read that a cut has overtaken (docs/levels.md, W1).
     */
    @Nano
    public static void testGetTransBelowTheCut() throws IOException {
        CutStream s = new CutStream();
        Db db = Db.builder().testSetup(s).start();
        Trans t1 = db.trans().put("/a", "a0").build();
        db.execute(t1);
        Trans t2 = db.trans().put("/b", "b0").build();
        db.execute(t2);
        db.sync(SyncLevel.STRONG);
        s.pretruncate(t2.tpos);

        LookupTimeNotAvailableException expired = null;
        try {
            db.getTrans(t1.tpos);
        } catch (LookupTimeNotAvailableException e) {
            expired = e;
        }
        Assert.assertTrue("expired", expired != null);
        Assert.assertEquals("the database goes on", t2.tt, db.getTrans(t2.tpos).tt);
        db.execute(db.trans().put("/c", "c0").build());
        Assert.assertEquals("c0", DbUtil.getString(db, "/c"));
        db.close();
    }

    // ======== Helpers ========

    /**
     * Regression test for bergdb 005-32: a start that throws closes its storage before the
     * exception leaves. What it appended is written, its stream is closed, no thread of its
     * storage runs, and later calls are refused. Here a damaged stream whose first
     * transaction failed, with a cut one after it (005-28): recovery zero-fills the cut one,
     * and startup then throws at the failed one. Before, the storage ran on until the garbage
     * collector finalized the Db. Until 2026-10-25 the stream was a creation cut in its first
     * transaction, which a start now refuses before recovery, and writes nothing (005-33).
     */
    @Nano
    public static void testFailedStartClosesStorage() throws IOException {
        MemoryStream created = new MemoryStream();
        Db first = Db.builder().testSetup(created).start();
        Trans t = first.trans().put("/k", "v").build();
        first.execute(t);
        first.close();
        MemoryStream s = created.copy();
        MemoryStream.TestAccess.write(s, new byte[] {0}, Db.CREATION_LENGTH - 1);
        s.truncate(t.lastPos);              // t cut before its last byte.
        
        Set<Thread> before = storageThreads();
        Db db = Db.builder().testSetup(s).build();
        StreamFormatException e = null;
        try {
            db.start();
        } catch (StreamFormatException ex) {
            e = ex;
        }
        Assert.assertTrue("the start throws", e != null);
        Assert.assertEquals("the zero fill is written", t.lastPos + 1, s.getLength());
        assertNoNewStorageThreads(before);
        assertClosed(s);
        assertStopped(db);
    }
    
    /**
     * bergdb 005-32: a start with a main and a replica of two histories fails (005-28, 005-11's
     * P9 in small), after it has copied the replica's last transaction to the main. The copy
     * is written before the exception leaves, both streams are closed, and no thread runs.
     * Before, a start of the main alone right after it raced with the failed start's thread,
     * which wrote the copy later, and lost a synced transaction 4 times in 20.
     */
    @Nano
    public static void testFailedStartOfTwoHistories() throws IOException {
        MemoryStream m0 = new MemoryStream();
        MemoryStream r0 = new MemoryStream();
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.stream("main", m0, 100 * 1000, 10);
        b.stream("r", r0, 100 * 1000, 10);
        b.startupDistance(10);
        Db db = b.start();
        Trans x = null;
        Trans t = null;
        for (int k = 0; k < 4; k++) {
            x = t;
            t = db.trans().put("/k" + k, "v" + k).build();
            db.execute(t);
        }
        db.close();
        Assert.assertTrue("t's startup pos is x", t.startupPos == x.tpos && x.nextPos == t.tpos);
        MemoryStream m1 = m0.copy();
        m1.truncate(x.lastPos);             // A crash: x torn, t lost.
        DbBuilder alone = Db.builder();
        alone.testSetupExceptStream();
        alone.stream("main", m1, 100 * 1000, 10);
        alone.start().close();              // Recovery zero-fills x.
        
        MemoryStream m = m1.copy();
        MemoryStream r = r0.copy();
        Assert.assertTrue("the replica is longer", r.getLength() > m.getLength());
        Set<Thread> before = storageThreads();
        DbBuilder both = Db.builder();
        both.testSetupExceptStream();
        both.stream("main", m, 100 * 1000, 10);
        both.stream("r", r, 100 * 1000, 10);
        Db db2 = both.build();
        StreamFormatException e = null;
        try {
            db2.start();
        } catch (StreamFormatException ex) {
            e = ex;
        }
        Assert.assertTrue("the start throws", e != null);
        Assert.assertEquals("the copy to the main is written", r.getLength(), m.getLength());
        assertNoNewStorageThreads(before);
        assertClosed(m);
        assertClosed(r);
        assertStopped(db2);
    }
    
    /**
     * bergdb 005-32: an Error in a flush (as an assertion of FileStream) ended the storage
     * thread without telling the storage, and a sync waited for ever. Now the flush fails the
     * stream, and the sync fails the database (005-30); close() returns.
     */
    @Nano
    public static void testErrorInFlushFailsSync() throws Exception {
        final FaultStream s = new FaultStream();
        final Db db = Db.builder().testSetup(s).start();
        db.sync(SyncLevel.STRONG);
        s.errorInAppends = true;
        db.execute(db.trans().put("/a", "a0").build());
        Throwable thrown = within(10000, new Runnable() {
            public void run() {
                db.sync(SyncLevel.STRONG);
            }
        });
        Assert.assertTrue("the sync fails: " + thrown, thrown instanceof DbFailedException);
        Assert.assertTrue("the flush's failure: " + thrown.getCause(),
                String.valueOf(thrown.getCause()).contains("The flush failed"));
        Assert.assertTrue("close() returns", within(10000, new Runnable() {
            public void run() {
                db.close();
            }
        }) == null);
    }
    
    /**
     * Node size 8, a startup distance of 1,000 bytes, so that index nodes are written and
     * can be evicted; every evictable object evicted after every transaction; the audit
     * after every 'audit'-th transaction and at startup, or off (0).
     */
    private static Db startEvicting(AppendOnlyStream s, int audit) {
        return Db.builder().testSetup(s).maxNodeSize8().startupDistance(1000)
                .evictionSchedule(Eviction.Schedule.EVERY, 1).audit(audit).start();
    }

    private static String key(int i) {
        return "/k" + (10000 + i);
    }

    /** Puts the KEYS keys, ten a transaction. */
    private static void fill(Db db) {
        for (int i = 0; i < KEYS; i += 10) {
            Trans.Builder b = db.trans();
            for (int j = i; j < i + 10; j++) {
                b.put(key(j), "v" + j);
            }
            db.execute(b.build());
        }
    }

    /** Waits, up to 10 s, until the main storage has failed, as after a failed flush. */
    private static void waitForStorageError(Db db) {
        final long end = System.nanoTime() + 10L * 1000 * 1000 * 1000;
        while (db.getStorageInfos()[0].getStatus() != StorageInfo.STATUS_ERROR) {
            if (System.nanoTime() > end) {
                throw new AssertionError("the storage did not fail");
            }
            try {
                Thread.sleep(1);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
    }

    private static byte[] bytes(String s) {
        return StringUtil.toBytes(s);
    }

    private static DbFailedException executeFails(Db db, Trans t) {
        DbFailedException failed = null;
        try {
            db.execute(t);
        } catch (DbFailedException e) {
            failed = e;
        }
        Assert.assertTrue("the transaction fails the database", failed != null);
        return failed;
    }

    /**
     * Every later transaction and read is refused, with the first failure as the cause; the
     * reads: a get, a scan, and getTrans (since bergdb 005-30).
     */
    private static void assertRefused(Db db, Throwable cause) {
        for (int i = 0; i < 4; i++) {
            DbFailedException refused = null;
            try {
                if (i == 0) {
                    db.execute(db.trans().put("/later", "x").build());
                } else if (i == 1) {
                    DbUtil.get(db, "/a");
                } else if (i == 2) {
                    DbUtil.getFirstKey(db, Long.MAX_VALUE, null);
                } else {
                    db.getTrans(RecoverableStream.META_BLOCK_SIZE);     // The first one.
                }
            } catch (DbFailedException e) {
                refused = e;
            }
            Assert.assertTrue("refused, " + i, refused != null && refused.getCause() == cause);
        }
    }

    /** Waits, up to 10 s, until the thread waits for the write lock of a Db. */
    private static void waitUntilBlockedOnTheWriteLock(Thread thread) {
        final long end = System.nanoTime() + 10L * 1000 * 1000 * 1000;
        while (System.nanoTime() < end) {
            ThreadInfo info = ManagementFactory.getThreadMXBean().getThreadInfo(thread.getId());
            if (info != null && info.getThreadState() == Thread.State.BLOCKED
                    && info.getLockName() != null
                    && info.getLockName().startsWith(Db.WriteLock.class.getName())) {
                return;
            }
            try {
                Thread.sleep(1);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
        throw new AssertionError("the thread did not come to wait for the write lock");
    }

    /**
     * A test stream over a MemoryStream that fails on purpose, when set: its reads throw an
     * IOException (a read error: the storage then fails), or return the bytes with the last one
     * changed (a corrupt node: a checksum error, the storage stays healthy); its appends throw,
     * or wait until holdAppends is cleared.
     */
    /** The threads of BufferedStreams that are alive (bergdb 005-32). */
    public static Set<Thread> storageThreads() {
        Set<Thread> result = new HashSet<Thread>();
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            if (t.getName().startsWith("BufferedStream-consumer") && t.isAlive()) {
                result.add(t);
            }
        }
        return result;
    }
    
    /** No storage thread runs that did not run 'before' (bergdb 005-32). */
    public static void assertNoNewStorageThreads(Set<Thread> before) {
        Set<Thread> after = storageThreads();
        after.removeAll(before);
        Assert.assertTrue("storage threads left: " + after, after.isEmpty());
    }
    
    /** A MemoryStream that is closed refuses an append. */
    public static void assertClosed(MemoryStream s) {
        long length = s.getLength();
        try {
            s.append(new byte[1], 0, 1);
            throw new AssertionError("the stream is open");
        } catch (IOException e) {
            // Expected.
        }
        Assert.assertEquals("no append", length, s.getLength());
    }
    
    /** A stopped database refuses transactions and reads. */
    private static void assertStopped(Db db) {
        try {
            db.execute(db.trans().put("/later", "x").build());
            throw new AssertionError("a transaction was taken");
        } catch (DbStoppingException e) {
            // Expected.
        }
        try {
            DbUtil.get(db, "/later");
            throw new AssertionError("a read was taken");
        } catch (DbStoppingException e) {
            // Expected.
        }
    }
    
    /** Runs r in a daemon thread for up to ms; returns what it threw, null, or HUNG. */
    static Throwable within(int ms, final Runnable r) throws InterruptedException {
        final Throwable[] thrown = new Throwable[1];
        Thread th = new Thread() {
            public void run() {
                try {
                    r.run();
                } catch (Throwable e) {
                    thrown[0] = e;
                }
            }
        };
        th.setDaemon(true);
        th.start();
        th.join(ms);
        if (th.isAlive()) {
            return new AssertionError("HUNG: still running after " + ms + " ms");
        }
        return thrown[0];
    }
    
    static class FaultStream implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        volatile boolean failReads = false;
        volatile boolean corruptReads = false;
        volatile boolean failAppends = false;
        volatile boolean errorInAppends = false;    // an Error, as an assertion (bergdb 005-32)
        volatile boolean holdAppends = false;
        volatile int faults = 0;

        public long getLength() {
            return inner.getLength();
        }

        public long getFirstPos() {
            return inner.getFirstPos();
        }

        public void read(long position, byte[] dest, int destOffset, int length)
                throws IOException {
            if (failReads) {
                faults++;
                throw new IOException("FaultStream: a read error, as set");
            }
            inner.read(position, dest, destOffset, length);
            if (corruptReads && length > 8) {
                faults++;
                dest[destOffset + length - 1] ^= 0x55;
            }
        }

        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            while (holdAppends) {
                try {
                    Thread.sleep(1);
                } catch (InterruptedException e) {
                    throw new IOException("FaultStream: interrupted while appends are held");
                }
            }
            if (failAppends) {
                faults++;
                throw new IOException("FaultStream: an append error, as set");
            }
            if (errorInAppends) {
                faults++;
                throw new AssertionError("FaultStream: an Error in an append, as set");
            }
            inner.append(source, sourceOffset, length);
        }

        public void pretruncate(long position) throws IOException {
            inner.pretruncate(position);
        }

        public void seekFirstPos(long position) throws IOException {
            inner.seekFirstPos(position);
        }

        public void close() throws IOException {
            inner.close();
        }
    }
}
