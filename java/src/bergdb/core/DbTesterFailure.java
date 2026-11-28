package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.InterruptedIOException;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.common.StringUtil;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.Spos;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.Platform;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

/**
 * Tests of a transaction that fails after its go point (bergdb 005-01, register M49 of
 * bergdb 001-08; item 003, 003-01's test plan). Until 005-01 such a transaction
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
     * 003-01's reproduction (2.1): the second put of a transaction throws, after the go point.
     * Before 005-01, /a = a1 was readable after the failure, and the next transaction wrote
     * it. Until bergdb 026-06 a value transformation that threw made the throw, and the test
     * was testValueTransformationThrows; since then a value transformation runs before the go
     * point and its exception refuses the transaction (DbTesterLimits), so the test hooks
     * throw at the put (throwAtPut).
     */
    @Nano
    public static void testPutThrows() {
        final long auditFailures = Audit.failures();
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).audit(1).start();
        db.execute(db.trans().put("/a", "a0").put("/b", "b0").build());
        db.sync(SyncLevel.ORDINARY);
        final long time = db.lookupTime(Long.MAX_VALUE);
        final long length = s.getLength();

        final IllegalStateException thrown = new IllegalStateException("the put fails");
        Trans t = db.trans()
                .put(Keys.toSegments("/a"), null, bytes("a1"), null)
                .put(Keys.toSegments("/b"), null, bytes("b1"), null)
                .build();
        final DbFailedException e;
        Db.testHooks = throwAtPut("/b", thrown, null);
        try {
            e = executeFails(db, t);
        } finally {
            Db.testHooks = null;
        }
        Assert.assertTrue("the cause", e.getCause() == thrown);
        Assert.assertEquals("the lookup time", time, db.lookupTime(Long.MAX_VALUE));
        assertRefused(db, thrown);

        db.sync(SyncLevel.ORDINARY);      // Still works, for the transactions before.
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
     * get a DbFailedException with the Error as the cause. The test hooks throw it at the put
     * (throwAtPut); until bergdb 026-06 a value transformation did, which now runs before the
     * go point, where an Error fails the database too (bergdb 019-10; DbTesterLimits).
     */
    @Nano
    public static void testErrorIsThrownAsItIs() {
        Db db = Db.builder().testSetup().start();
        db.execute(db.trans().put("/a", "a0").build());

        final Error thrown = new Error("an Error in the transaction");
        Trans t = db.trans()
                .put(Keys.toSegments("/a"), null, bytes("a1"), null)
                .build();
        Error error = null;
        Db.testHooks = throwAtPut("/a", thrown, null);
        try {
            db.execute(t);
        } catch (Error e) {
            error = e;
        } finally {
            Db.testHooks = null;
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
        db.sync(SyncLevel.ORDINARY);
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
            db.sync(SyncLevel.ORDINARY);
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
        db.sync(SyncLevel.ORDINARY);

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
        db.sync(SyncLevel.ORDINARY);

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

        final IllegalStateException thrown = new IllegalStateException("the put fails");
        Trans t = db.trans()
                .put(Keys.toSegments("/a"), null, bytes("a1"), null)
                .put(Keys.toSegments("/b"), null, bytes("b1"), null)
                .build();
        final DbFailedException e;
        Db.testHooks = throwAtPut("/b", thrown, new Runnable() {
            public void run() {
                writer2.start();
                waitUntilBlockedOnTheWriteLock(writer2);
            }
        });
        try {
            e = executeFails(db, t);
        } finally {
            Db.testHooks = null;
        }
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

    /**
     * bergdb 031-06 (review-main, R1): a Trans whose execution failed the database after its
     * go point, in a record that carried a step of reclaim, executed again on the restarted
     * database, after another commit has taken the step that was due: its record is the
     * record of a new Trans with the same KVs at the same time, byte for byte. Until
     * 2026-11-27 the failed execution left the plan's fields on the Trans (Trans.touch,
     * recordCap and the others), set only with a plan and cleared only after a record that
     * worked, and the execution again, whose record carried no plan, ran a test's touch over
     * the transaction's own keys: other got-dirty lists, another stream (the review's
     * RmReuseProbe, 16 of 20 runs). Both points: the failure after the record's append, and
     * before it, in the puts after the step's touch.
     */
    @Nano
    public static void testTransExecutedAgainAfterAFailure() throws IOException {
        for (final boolean afterAppend : new boolean[] {true, false}) {
            transExecutedAgainAfterAFailure(afterAppend);
        }
    }
    
    private static void transExecutedAgainAfterAFailure(final boolean afterAppend)
            throws IOException {
        final long SEC = Clock.UNITS_PER_SEC;
        final IllegalStateException thrown = new IllegalStateException("the test's failure");
        final boolean[] armed = new boolean[1], touched = new boolean[1];
        final Trans[] executed = new Trans[1];
        final boolean[] planned = new boolean[1], touch = new boolean[1];
        final Db.TestHooks hooks = new Db.TestHooks() {
            public void beforePlan(Db.ExecuteData x) {
                touched[0] = false;
            }
            public void nodeTouched(Node node) {
                touched[0] = true;          // the record has a touch: it carries a step
            }
            public void kvApplied(long[] key, byte[] value) {
                if (armed[0] && !afterAppend && touched[0]) {
                    armed[0] = false;
                    throw thrown;
                }
            }
            public void beforeApply(Db.ExecuteData x) {
                executed[0] = x.trans;
                planned[0] = x.plan != null;
                touch[0] = x.trans.touch;
            }
            public void transExecuted(Db.ExecuteData x) {
                if (armed[0] && afterAppend && x.plan != null && x.trans.touch && !x.trans.part) {
                    armed[0] = false;
                    throw thrown;
                }
            }
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeReplaced(Node node) {}
        };
        final CutStream s = new CutStream();
        final CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        Db db = Db.builder().testSetup(s).clock(clock).maxNodeSize8().start();
        db.setStartupDistance(2000);
        db.setRetainDuration(SEC);
        final java.util.Random r = new java.util.Random(1);
        Trans failed = null;
        byte[] failedValue = null;
        int failedAt = -1;
        Db.testHooks = hooks;
        try {
            for (int i = 0; i < 5000 && failed == null; i++) {
                time += SEC / 100;
                clock.setTime(time);
                final byte[] v = new byte[100 + r.nextInt(400)];
                r.nextBytes(v);
                final Trans t = reusedTrans(db, i, v);
                armed[0] = i >= 300;
                try {
                    db.execute(t);
                } catch (DbFailedException e) {
                    Assert.assertTrue("the cause", e.getCause() == thrown);
                    failed = t;
                    failedValue = v;
                    failedAt = i;
                }
            }
        } finally {
            Db.testHooks = null;
        }
        Assert.assertTrue("a commit that carried a step failed the database", failed != null);
        db.close();
        
        // On two copies of the stream: another commit, which carries the step that was due,
        // then the action again, with the Trans that failed and with a new one of its KVs.
        final byte[][] images = new byte[2][];
        final long[] firstPos = new long[2];
        boolean wrongTouch = false;
        for (int run = 0; run < 2; run++) {
            final CutStream c = s.copy();
            final CoreTestClock clock2 = new CoreTestClock();
            clock2.setTime(time);
            final Db d = Db.builder().testSetup(c).clock(clock2).maxNodeSize8().start();
            try {
                clock2.setTime(time + SEC / 100);
                d.execute(d.trans().put("/other", new byte[] {7}).build());
                clock2.setTime(time + 2 * SEC / 100);
                final Trans again = run == 0 ? failed : reusedTrans(d, failedAt, failedValue);
                Db.testHooks = hooks;
                try {
                    d.execute(again);
                } finally {
                    Db.testHooks = null;
                }
                Assert.assertTrue("executed", executed[0] == again);
                wrongTouch |= !planned[0] && touch[0];
                clock2.setTime(time + 3 * SEC / 100);
                d.execute(d.trans().put("/after", new byte[] {8}).build());
            } finally {
                d.close();
            }
            firstPos[run] = c.getFirstPos();
            images[run] = new byte[(int) (c.getLength() - c.getFirstPos())];
            c.read(c.getFirstPos(), images[run], 0, images[run].length);
        }
        final String at = ", the failure " + (afterAppend ? "after" : "before")
                + " the append, at action " + failedAt;
        Assert.assertEquals("the first position" + at, firstPos[0], firstPos[1]);
        Assert.assertTrue("the same stream" + at, Arrays.equals(images[0], images[1]));
        Assert.assertFalse("a touch in a record without a plan" + at, wrongTouch);
    }
    
    /** The transaction of action i of transExecutedAgainAfterAFailure(). */
    private static Trans reusedTrans(Db db, int i, byte[] v) {
        return db.trans().put("/k" + (i % 150), v).put("/n/new" + i, new byte[] {1, 2, 3})
                .delete("/missing/" + i).build();
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
        db.sync(SyncLevel.ORDINARY);
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
            db.sync(SyncLevel.ORDINARY);      // The storage is healthy.
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
     * A get, a scan, getTrans and a transaction's warm-up, whose read of the storage throws
     * an unchecked exception or an Error (bergdb 019-10): the database fails. The unchecked
     * exception, a breach of the stream's contract, fails the storage as an I/O error does:
     * the call throws a DbFailedException with a StreamIoException as the cause. The Error
     * is thrown as it is (Frans, 2026-11-06, 10:18 and 10:31: an Error during a call fails
     * the database, and the application ends its process; Db, "Errors"). Every later
     * transaction and read is refused with a DbFailedException whose cause is the first
     * failure, nothing is appended, and a restart has the key. Before 019-10, the get and the
     * warm-up threw either as it was, and the next transaction and get worked; after the
     * night's fix, the Error was a DbFailedException's cause, wrapped in a StreamIoException.
     */
    @Nano
    public static void testUncheckedReadFailsTheDatabase() {
        final String[] calls = {"a get", "a scan", "getTrans", "the warm-up"};
        for (int i = 0; i < 2 * calls.length; i++) {
            final boolean error = i % 2 == 1;
            final String call = calls[i / 2];
            final FaultStream s = new FaultStream();
            Db db = startEvicting(s, 0);
            fill(db);
            db.sync(SyncLevel.ORDINARY);
            final long length = s.getLength();
            if (error) {
                s.errorInReads = true;
            } else {
                s.uncheckedReads = true;
            }
            Throwable thrown = null;
            try {
                if (i / 2 == 0) {
                    DbUtil.get(db, key(KEYS / 2));
                } else if (i / 2 == 1) {
                    DbUtil.checksum(db);
                } else if (i / 2 == 2) {
                    db.getTrans(RecoverableStream.META_BLOCK_SIZE);     // The first one.
                } else {
                    db.execute(db.trans().put(key(KEYS / 2), "w").build());
                }
            } catch (Throwable e) {
                thrown = e;
            }
            final String what = (error ? "an Error" : "an unchecked exception") + " in " + call;
            s.uncheckedReads = false;
            s.errorInReads = false;
            try {
                Assert.assertTrue(what + ": faults made", s.faults > 0);
                final Throwable failure;
                if (error) {
                    Assert.assertTrue(what + " is thrown as it is: " + thrown,
                            thrown == s.readError);
                    failure = thrown;
                } else {
                    Assert.assertTrue(what + " fails the database: " + thrown,
                            thrown instanceof DbFailedException);
                    failure = thrown.getCause();
                    Assert.assertTrue(what + ", the cause: " + failure,
                            failure instanceof StreamIoException);
                }
                assertRefused(db, failure, what);
                Assert.assertEquals(what + ": the stream's length", length, s.getLength());
            } finally {
                db.close();
            }

            Db db2 = startEvicting(s.inner.copy(), 1);
            Assert.assertEquals(what, "v" + (KEYS / 2), DbUtil.getString(db2, key(KEYS / 2)));
            db2.close();
        }
    }
    
    /**
     * An Error of the application's code that a call runs, a getMany's StopCondition, fails
     * the database too (2026-11-06, bergdb 019-10): the database cannot tell whose Error it
     * is. The Error is thrown as it is, and every later transaction and read is refused with
     * a DbFailedException with it as the cause. Before, it passed through, and the database
     * went on.
     */
    @Nano
    public static void testErrorInStopConditionFailsTheDatabase() {
        Db db = Db.builder().testSetup().start();
        try {
            db.execute(db.trans().put("/a", "a0").put("/b", "b0").build());
            final AssertionError error = new AssertionError("the StopCondition's Error");
            GetMany g = db.newGetMany();
            g.lookupTime = Long.MAX_VALUE;
            g.stopCondition = new GetMany.StopCondition() {
                public int handleKvt(Kvt kvt) {
                    throw error;
                }
                public void eod() {}
            };
            Throwable thrown = null;
            try {
                db.getMany(g);
            } catch (Throwable e) {
                thrown = e;
            }
            Assert.assertTrue("the Error itself: " + thrown, thrown == error);
            assertRefused(db, error);
        } finally {
            db.close();
        }
    }

    /**
     * A get that loads an index node whose checksum is right but whose key count does not
     * fit its size (bergdb 015-07): the parse refuses it with a StreamFormatException, and
     * the read fails the database as for a checksum error. Before, the parse threw an
     * ArrayIndexOutOfBoundsException, which escaped the read's failure handling (it caught a
     * StreamException only), and the database stayed active and took the next transaction
     * (005-82's probe).
     */
    @Nano
    public static void testBadKeyCountInGetOne() {
        failInLoad(0);
    }

    /** As testBadKeyCountInGetOne, in a scan (Db.getMany). */
    @Nano
    public static void testBadKeyCountInGetMany() {
        failInLoad(1);
    }

    /** As testBadKeyCountInGetOne, in a put, whose warm-up loads the node. */
    @Nano
    public static void testBadKeyCountInPut() {
        failInLoad(2);
    }

    /**
     * The load fails the database: the call throws a DbFailedException whose cause is the
     * parse's StreamFormatException, every later transaction and read is refused with it,
     * nothing more is appended, and a restart, with the audit on, gives every key.
     */
    private static void failInLoad(int what) {
        final long auditFailures = Audit.failures();
        final KeyCountStream s = new KeyCountStream();
        Db db = startEvicting(s, 0);
        fill(db);
        db.sync(SyncLevel.ORDINARY);
        final long length = s.getLength();

        s.damage = true;
        DbFailedException e = null;
        try {
            if (what == 0) {
                DbUtil.get(db, key(KEYS / 2));
            } else if (what == 1) {
                DbUtil.checksum(db);
            } else {
                db.execute(db.trans().put(key(KEYS / 2), "w").build());
            }
        } catch (DbFailedException ex) {
            e = ex;
        } catch (RuntimeException ex) {
            throw new AssertionError("the load did not fail the database: " + ex, ex);
        }
        Assert.assertTrue("the load fails the database", e != null);
        Assert.assertTrue("damaged reads", s.damaged > 0);
        Assert.assertTrue("the cause: " + e.getCause(),
                e.getCause().getClass() == StreamFormatException.class
                && e.getCause().getMessage().startsWith("Bad key count"));
        assertRefused(db, e.getCause());
        s.damage = false;
        db.sync(SyncLevel.ORDINARY);      // The storage is healthy.
        Assert.assertEquals("the stream's length", length, s.getLength());
        db.close();

        Db db2 = startEvicting(s.inner.copy(), 1);
        for (int j = 0; j < KEYS; j++) {
            Assert.assertEquals(key(j), "v" + j, DbUtil.getString(db2, key(j)));
        }
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
        db.sync(SyncLevel.ORDINARY);
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
        db.sync(SyncLevel.ORDINARY);

        s.failAppends = true;
        db.execute(db.trans().put("/a", "a1").build());     // In memory and buffered only.
        DbFailedException e = null;
        try {
            db.sync(SyncLevel.ORDINARY);
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
        db.sync(SyncLevel.ORDINARY);

        s.holdAppends = true;       // The flush waits, and so does the sync.
        db.execute(db.trans().put("/a", "a1").build());
        final Throwable[] thrown = new Throwable[1];
        Thread syncer = new Thread(new Runnable() {
            public void run() {
                try {
                    db.sync(SyncLevel.ORDINARY);
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
        db.sync(SyncLevel.ORDINARY);
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
        db.sync(SyncLevel.ORDINARY);

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
     * Regression test for bergdb 015-17: a get that runs while another thread closes the
     * database, and reads a file after the storage thread has closed it, fails as a read
     * while the database stops does (the StreamIoException as it is), and close() does not
     * report it: the close wrote and closed everything. The read's "File closed" was the
     * FileStream's failure, and BufferedStream.close(), which closes the FileStream again
     * after its thread's close, threw it: Db.close() threw it as a failed close
     * (InterruptStress, 016-08's F3). CloseRaceStream holds the get in its read until the
     * storage thread has closed the files, and that close until the read has failed: the
     * stress run's interleaving. A restart then has every key.
     */
    @Nano
    public static void testGetDuringClose() throws Exception {
        final File dir = Files.createTempDirectory("bergdb-getduringclose-").toFile();
        try {
            final CloseRaceStream s = new CloseRaceStream(new FileStream(dir));
            final Db db = startEvicting(s, 0);
            fill(db);
            db.sync(SyncLevel.ORDINARY);
            final Throwable[] thrown = new Throwable[1];
            Thread reader = new Thread(new Runnable() {
                public void run() {
                    try {
                        DbUtil.getString(db, key(5));
                    } catch (Throwable e) {
                        thrown[0] = e;
                    }
                }
            });
            reader.setDaemon(true);
            s.reader = reader;
            reader.start();
            Assert.assertTrue("the get reads the stream", s.inRead.await(10, TimeUnit.SECONDS));
            db.close();
            reader.join(10 * 1000);
            Assert.assertTrue("the get still runs after 10 s", !reader.isAlive());
            Assert.assertTrue("the read met the closed files", s.readDone.getCount() == 0);
            Assert.assertTrue("the get fails as a read while the database stops: " + thrown[0],
                    thrown[0] instanceof StreamIoException);
            Assert.assertTrue("the storage thread's close and close()'s", s.closes >= 2);
            DbStoppingException stopping = null;
            try {
                db.execute(db.trans().put("/later", "x").build());
            } catch (DbStoppingException e) {
                stopping = e;
            }
            Assert.assertTrue("stopping, not failed", stopping != null);

            Db again = startEvicting(new FileStream(dir), 0);
            try {
                for (int i = 0; i < KEYS; i++) {
                    Assert.assertEquals("v" + i, DbUtil.getString(again, key(i)));
                }
            } finally {
                again.close();
            }
        } finally {
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) f.delete();
            dir.delete();
        }
    }

    /**
     * A stream over a FileStream for testGetDuringClose (bergdb 015-17): the first read of
     * thread 'reader' waits, once it has begun, until the first close() has closed the
     * FileStream, and then reads; that close waits until the read is done.
     */
    static final class CloseRaceStream implements AppendOnlyStream {
        final FileStream inner;
        volatile Thread reader;
        final CountDownLatch inRead = new CountDownLatch(1);
        final CountDownLatch closed = new CountDownLatch(1);
        final CountDownLatch readDone = new CountDownLatch(1);
        int closes = 0;     // under this

        CloseRaceStream(FileStream inner) {
            this.inner = inner;
        }

        private static void await(CountDownLatch latch) throws IOException {
            try {
                if (!latch.await(10, TimeUnit.SECONDS)) {
                    throw new IOException("CloseRaceStream: waited 10 s");
                }
            } catch (InterruptedException e) {
                throw new IOException(e);
            }
        }

        public long getLength() {
            return inner.getLength();
        }

        public long getFirstPos() {
            return inner.getFirstPos();
        }

        public void read(long position, byte[] dest, int destOffset, int length)
                throws IOException {
            if (Thread.currentThread() != reader || inRead.getCount() == 0) {
                inner.read(position, dest, destOffset, length);
                return;
            }
            inRead.countDown();
            await(closed);
            try {
                inner.read(position, dest, destOffset, length);
            } finally {
                readDone.countDown();
            }
        }

        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            inner.append(source, sourceOffset, length);
        }

        public void pretruncate(long position) throws IOException {
            inner.pretruncate(position);
        }

        public void close() throws IOException {
            final boolean first;
            synchronized (this) {
                first = closes++ == 0;
            }
            inner.close();
            if (first && reader != null && inRead.getCount() == 0) {
                closed.countDown();
                await(readDone);
            }
        }
    }

    /**
     * Db.getTrans, the Pub API's Connection.transactionInfo(): a read error fails the
     * database, and after it getTrans is refused (it read on after a failure). So does a
     * format error (here, a corrupt read) since bergdb 005-34, which made the positions that
     * a get gives right; before it, a format error did not fail the database. Since bergdb
     * 021-27 a format error fails the database only for a position the database has given
     * (Internal.getTrans(), as transactionInfo() reads); Db.getTrans() takes the position as
     * a caller's and refuses it with IllegalArgumentException, and the database goes on.
     */
    @Nano
    public static void testGetTrans() {
        for (int i = 0; i < 2; i++) {
            final boolean corrupt = i == 0;
            FaultStream s = new FaultStream();
            Db db = Db.builder().testSetup(s).start();
            Trans t = db.trans().put("/a", "a0").build();
            db.execute(t);
            db.sync(SyncLevel.ORDINARY);
            Assert.assertEquals("the transaction", t.tt, db.getTrans(t.tpos).tt);

            if (corrupt) {
                s.corruptReads = true;
                IllegalArgumentException refused = null;
                try {
                    db.getTrans(t.tpos);
                } catch (IllegalArgumentException ex) {
                    refused = ex;
                }
                Assert.assertTrue("a caller's position refused",
                        refused != null && refused.getCause() instanceof StreamFormatException);
                s.corruptReads = false;
                Assert.assertEquals("the database goes on", "a0", DbUtil.getString(db, "/a"));
                s.corruptReads = true;
            } else {
                s.failReads = true;
            }
            DbFailedException e = null;
            try {
                if (corrupt) {
                    db.internal().getTrans(t.tpos);
                } else {
                    db.getTrans(t.tpos);
                }
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
     * bergdb 021-13 (020-24-01, U1-1 and U1-2): Db.getTrans of the position that a get gives
     * while the writer appends the value's record. The writer sets the positions of the
     * record's nodes before it appends the record, and a get gives the value's position from
     * then on. getTrans read the record: with none of it in the stream it threw
     * IllegalArgumentException ("at or past the end of the stream"); with a part, the
     * record's size went beyond the stream's length, a StreamFormatException that failed the
     * database. Now it waits for the writer and gives the transaction. The writer is held in
     * its append by the storage's buffer, full as the flush is held (FaultStream): before
     * any of the record (case none, a buffer of 100,000 bytes), or after the record's part
     * before a meta block, whose append waits (case part, a buffer that is full just there).
     */
    @Nano
    public static void testGetTransOfARecordBeingAppended() throws Exception {
        for (int i = 0; i < 2; i++) {
            final boolean part = i == 1;
            final String what = part ? "part" : "none";
            final int d = RecoverableStream.META_BLOCK_DISTANCE;
            // The creation's records: the primordial one and the startup distance's (028-15).
            final long created = DbTester.createdLength();
            final int bufferSize = part ? d - (int) created + 64 : 100 * 1000;
            final FaultStream s = new FaultStream();
            final DbBuilder b = Db.builder();
            b.testSetupExceptStream();
            b.stream("main", s, bufferSize, 10);
            final Db db = b.start();
            final Throwable[] thrown = new Throwable[1];
            Thread writer = null;
            try {
                db.sync(SyncLevel.ORDINARY);     // The buffer is empty.
                Assert.assertEquals(created, db.getStreamLength());
                s.holdAppends = true;            // The flush waits; the buffer fills.
                
                // A record that fills the buffer but about 3,000 bytes, then one of 6,000. In
                // case part, the buffer holds the bytes from the end of the creation's record
                // to the meta block at d, and 64 more: the second record begins about 3,000
                // bytes before d, and after its part before d the buffer has room for 64
                // bytes, too few for the meta block.
                db.execute(db.trans().put("/f", new byte[bufferSize - 3200]).build());
                final Trans t1 = db.trans().put("/a", new byte[6000]).build();
                writer = new Thread(() -> {
                    try {
                        db.execute(t1);
                    } catch (Throwable e) {
                        thrown[0] = e;
                    }
                });
                writer.start();
                waitUntilWaitingForRoom(writer, what);
                
                final GetData gd = db.newGetData();
                final long[] key = Keys.toSegments("/a");
                final long end = System.nanoTime() + 10L * 1000 * 1000 * 1000;
                while (db.getOne(Long.MAX_VALUE, key, gd) == null || gd.tpos == Spos.NULL) {
                    Assert.assertTrue(what + ": the get gives the position", 
                            System.nanoTime() < end);
                    Thread.sleep(1);
                }
                final long tpos = gd.tpos;
                Assert.assertTrue(what + ": the record is not appended in whole, " + tpos,
                        tpos >= db.internal().nodeStream().getAppendedEnd());
                Assert.assertTrue(what + ": the record and the meta block, " + tpos,
                        part == (tpos < d && tpos + 6000 > d));
                
                final Object[] got = new Object[1];
                Thread reader = new Thread(() -> {
                    try {
                        got[0] = db.getTrans(tpos);
                    } catch (Throwable e) {
                        got[0] = e;
                    }
                });
                reader.start();
                waitUntilBlockedOnTheWriteLockOrDone(reader, what, got);
                
                // A position inside the record waits too, then is refused (bergdb 021-27).
                final Object[] gotInside = new Object[1];
                Thread inside = new Thread(() -> {
                    try {
                        gotInside[0] = db.getTrans(tpos + 8);
                    } catch (Throwable e) {
                        gotInside[0] = e;
                    }
                });
                inside.start();
                waitUntilBlockedOnTheWriteLockOrDone(inside, what + ", inside", gotInside);
                
                s.holdAppends = false;
                writer.join(10 * 1000);
                reader.join(10 * 1000);
                inside.join(10 * 1000);
                Assert.assertTrue(what + ": inside the record, refused, " + gotInside[0],
                        gotInside[0] instanceof IllegalArgumentException);
                Assert.assertTrue(what + ": the writer, " + thrown[0], 
                        !writer.isAlive() && thrown[0] == null);
                Assert.assertTrue(what + ": the transaction, " + got[0],
                        got[0] instanceof StoredTrans && ((StoredTrans) got[0]).tt == t1.tt);
                db.execute(db.trans().put("/b", "b0").build());
                Assert.assertEquals("b0", DbUtil.getString(db, "/b"));
            } finally {
                s.holdAppends = false;
                if (writer != null) {
                    writer.join(10 * 1000);
                }
                db.close();
            }
        }
    }
    
    /** Waits, up to 10 s, until the writer waits for room in the storage's buffer. */
    private static void waitUntilWaitingForRoom(Thread writer, String what) 
            throws InterruptedException {
        final long end = System.nanoTime() + 10L * 1000 * 1000 * 1000;
        while (System.nanoTime() < end) {
            if (Platform.waitsFor(writer, Thread.State.WAITING,
                    bergdb.storage.BufferedStream.class.getName())) {
                return;
            }
            Thread.sleep(1);
        }
        throw new AssertionError(what + ": the writer did not come to wait for room");
    }
    
    /** 
     * Waits, up to 10 s, until the reader waits for the write lock of a Db; fails if it is
     * done first (bergdb 021-13).
     */
    private static void waitUntilBlockedOnTheWriteLockOrDone(Thread reader, String what,
            Object[] got) throws InterruptedException {
        final long end = System.nanoTime() + 10L * 1000 * 1000 * 1000;
        while (System.nanoTime() < end) {
            if (Platform.waitsFor(reader, Thread.State.BLOCKED, Db.WriteLock.class.getName())) {
                return;
            }
            if (!reader.isAlive()) {
                final Throwable cause = got[0] instanceof Throwable 
                        ? ((Throwable) got[0]).getCause() : null;
                throw new AssertionError(what + ": getTrans did not wait for the writer, "
                        + "it gave " + got[0] + (cause != null ? ", the cause " + cause : ""));
            }
            Thread.sleep(1);
        }
        throw new AssertionError(what + ": the reader did not come to wait for the write lock");
    }

    /**
     * Db.getTrans of a transaction that reclaim has removed (here, a cut made as reclaim
     * makes it, through the storage's buffer, which keeps the database's first position)
     * throws a LookupTimeNotAvailableException, and the database goes on, as for a read
     * that a cut has overtaken (bergdb 011-04, W1). The stream below was cut directly until
     * 2026-11-06, so the database's first position did not see the cut (bergdb 015-80,
     * review R4's C2). A position inside a record below the cut expires so too, and one
     * inside a record after it is refused with IllegalArgumentException (bergdb 021-27).
     */
    @Nano
    public static void testGetTransBelowTheCut() throws IOException {
        CutStream s = new CutStream();
        Db db = Db.builder().testSetup(s).start();
        Trans t1 = db.trans().put("/a", "a0").build();
        db.execute(t1);
        Trans t2 = db.trans().put("/b", "b0").build();
        db.execute(t2);
        db.sync(SyncLevel.ORDINARY);
        db.internal().getMainStream().pretruncate(t2.tpos);
        Assert.assertEquals("the database's first position", t2.tpos,
                db.internal().getMainStream().getFirstPos());

        LookupTimeNotAvailableException expired = null;
        try {
            db.getTrans(t1.tpos);
        } catch (LookupTimeNotAvailableException e) {
            expired = e;
        }
        Assert.assertTrue("expired", expired != null);
        expired = null;
        try {
            db.getTrans(t1.tpos + 8);
        } catch (LookupTimeNotAvailableException e) {
            expired = e;
        }
        Assert.assertTrue("inside a record below the cut, expired", expired != null);
        IllegalArgumentException refused = null;
        try {
            db.getTrans(t2.tpos + 8);
        } catch (IllegalArgumentException e) {
            refused = e;
        }
        Assert.assertTrue("inside a record after the cut, refused", refused != null);
        Assert.assertEquals("the database goes on", t2.tt, db.getTrans(t2.tpos).tt);
        // A record over 1 MiB is read at a caller's position after a walk from the cut, as no
        // meta block after the cut is at or before it (bergdb 021-27, Q27-1).
        Trans t3 = db.trans().put("/d", new byte[1100 * 1000]).build();
        db.execute(t3);
        Assert.assertEquals("a large record after the cut", t3.tt, db.getTrans(t3.tpos).tt);
        db.execute(db.trans().put("/c", "c0").build());
        Assert.assertEquals("c0", DbUtil.getString(db, "/c"));
        db.close();
    }

    /**
     * Regression test for bergdb 028-55: Db.getTrans of a committed record over 1 MiB, at its
     * position, after reclaim has cut a MemoryStream, which drops whole arrays of 1 MB as
     * FileStream drops whole files: the stream's first position is an array's start, below
     * the cut, inside the record that reaches over it. The walk to a large record (bergdb
     * 021-27, Q27-1) began at that first position when the meta block before the record
     * named one below it, read a size inside a record there, and refused the position. Here
     * every record holds a value of 1.1 MB, so each one reaches over an array's start, and
     * every record from the cut on is read at its position, by Db.getTrans and by
     * Internal.getTrans (Connection.transactionInfo()'s read, which has no walk).
     */
    @Nano
    public static void testGetTransAfterACutInsideARecord() {
        final CoreTestClock clock = new CoreTestClock();
        final MemoryStream stream = new MemoryStream();
        final Db db = Db.builder().testSetup(stream).clock(clock).start();
        try {
            db.setStartupDistance(100 * 1000);
            db.setRetainDuration(Clock.UNITS_PER_SEC);
            final byte[] value = new byte[1100 * 1000];
            int after = 0;
            for (int i = 1; i <= 60 && after < 3; i++) {
                clock.setTime(i * Clock.UNITS_PER_SEC);
                db.execute(db.trans().put("/k", value).build());
                db.sync(SyncLevel.ORDINARY);    // A cut waits until its table is durable.
                after += stream.getFirstPos() > 0 ? 1 : 0;
            }
            final long cut = db.getFirstAvailablePos();
            Assert.assertTrue("cut inside an array, after its start: " + stream.getFirstPos()
                    + " < " + cut, after == 3 && stream.getFirstPos() < cut);
            int large = 0;
            synchronized (db.internal().getWriteLock()) {
                final NodeStream.TransIterator ti =
                        db.internal().nodeStream().createTransIteratorFromExactStartupPos(cut);
                while (ti.next()) {
                    final long tt = ti.getStoredTrans().tt;
                    large += ti.transBuffer.length > NodeStream.CALLERS_SIZE_LIMIT ? 1 : 0;
                    Assert.assertEquals("Db.getTrans at " + ti.tpos + ", the cut " + cut
                            + ", the first position " + stream.getFirstPos(), tt,
                            db.getTrans(ti.tpos).tt);
                    Assert.assertEquals("Internal.getTrans at " + ti.tpos, tt,
                            db.internal().getTrans(ti.tpos).tt);
                }
            }
            Assert.assertTrue("records over 1 MiB after the cut: " + large, large >= 3);
        } finally {
            db.close();
        }
    }

    /**
     * Regression test for bergdb 028-56: Db.getTrans of a committed record over 1 MiB, at the
     * position that a get gave, at or after reclaim's cut, while the stream is cut. The walk
     * to a large record (bergdb 021-27, Q27-1; 028-55) read the stream's first position, then
     * the meta block before the record, which named a record below the cut and at or after
     * that first position; a cut between the two reads removed the named record, the walk
     * read below the first position, and the call expired a transaction that is kept. A
     * retry read it. Here the stream holds its cuts back (CutHeldStream) while reclaim's cut
     * moves on; the reader stops at the walk's first read, which was of that meta block, the
     * stream is cut at reclaim's cut, to the start of the array that holds it, and the
     * reader goes on. Found by a review of 028-55 (2026-11-25), with a probe that this test
     * follows.
     */
    @Nano
    public static void testGetTransCutDuringTheWalk() throws Exception {
        final CoreTestClock clock = new CoreTestClock();
        final CutHeldStream stream = new CutHeldStream();
        final Db db = Db.builder().testSetup(stream).clock(clock).start();
        final StoredTrans[] read = new StoredTrans[1];
        final Throwable[] thrown = new Throwable[1];
        Thread reader = null;
        try {
            db.setStartupDistance(100 * 1000);
            db.setRetainDuration(Clock.UNITS_PER_SEC);
            final byte[] value = new byte[1100 * 1000];
            clock.setTime(Clock.UNITS_PER_SEC);
            db.execute(db.trans().put("/a", value).build());
            db.sync(SyncLevel.ORDINARY);
            // bergdb 031-06: the iteration begins in the record after /a's, at its position;
            // an empty commit is that record, so that reclaim's cut is before /target's
            // record, as main's begin record after /a's put it. The layout the test needs,
            // checked here, so that a change of it fails with its reason.
            clock.setTime(3 * Clock.UNITS_PER_SEC / 2);
            final long emptyPos = db.getStreamLength();
            db.execute(db.trans().build());
            final Reclaim.IterationInfo begun = db.internal().reclaim().currentIteration();
            Assert.assertTrue("the layout: an iteration begun by the empty commit's record, at "
                    + emptyPos + ": " + (begun == null ? null : begun.pStart), begun != null
                    && begun.pStart <= emptyPos);
            clock.setTime(2 * Clock.UNITS_PER_SEC);
            db.execute(db.trans().put("/target", value).build());
            db.sync(SyncLevel.ORDINARY);
            final GetData gd = db.newGetData();
            db.getOne(Long.MAX_VALUE, Keys.toSegments("/target"), gd);
            final long tpos = gd.tpos;
            final long tt = db.internal().getTrans(tpos).tt;
            for (int i = 3; i <= 100 && db.getFirstAvailablePos() == 0; i++) {
                clock.setTime(i * Clock.UNITS_PER_SEC);
                db.execute(db.trans().put("/b", value).build());
                db.sync(SyncLevel.ORDINARY);
            }
            final long cut = db.getFirstAvailablePos();
            Assert.assertTrue("reclaim's cut at or before the record, the stream not cut: cut "
                    + cut + ", tpos " + tpos + ", the first position " + stream.getFirstPos(),
                    cut > 0 && cut <= tpos && stream.getFirstPos() == 0);
            Assert.assertEquals("before the stream is cut", tt, db.getTrans(tpos).tt);

            stream.below = tpos;
            reader = new Thread(new Runnable() {
                public void run() {
                    try {
                        read[0] = db.getTrans(tpos);
                    } catch (Throwable e) {
                        thrown[0] = e;
                    }
                }
            });
            reader.setDaemon(true);
            stream.reader = reader;
            reader.start();
            Assert.assertTrue("the reader walks", stream.inRead.await(10, TimeUnit.SECONDS));
            synchronized (db.internal().getWriteLock()) {
                stream.cutHeld = false;
                db.internal().getMainStream().pretruncate(cut);
            }
            final long first = stream.getFirstPos();
            Assert.assertTrue("cut to an array's start before the cut: " + first,
                    first > 0 && first < cut);
            stream.cutMade.countDown();
            reader.join(10 * 1000);
            Assert.assertTrue("the reader still runs after 10 s", !reader.isAlive());
            if (thrown[0] != null) {
                throw new AssertionError("Db.getTrans at " + tpos + ", the cut " + cut
                        + ", the first position " + first, thrown[0]);
            }
            Assert.assertEquals("Db.getTrans, the stream cut during the walk", tt, read[0].tt);
            Assert.assertEquals("after it", tt, db.getTrans(tpos).tt);
        } finally {
            stream.cutMade.countDown();
            if (reader != null) {
                reader.join(10 * 1000);
            }
            db.close();
        }
    }

    /**
     * A MemoryStream for testGetTransCutDuringTheWalk (bergdb 028-56): it makes no cut while
     * 'cutHeld', which AppendOnlyStream.pretruncate() allows; and the first read by thread
     * 'reader' before 'below' waits until 'cutMade'. Db.getTrans() reads before its position
     * only in the walk to it, after it has read the first position and reclaim's cut.
     */
    static final class CutHeldStream implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        volatile boolean cutHeld = true;
        volatile Thread reader;
        volatile long below = -1;
        final CountDownLatch inRead = new CountDownLatch(1);
        final CountDownLatch cutMade = new CountDownLatch(1);

        public long getLength() {
            return inner.getLength();
        }

        public long getFirstPos() {
            return inner.getFirstPos();
        }

        public void read(long position, byte[] dest, int destOffset, int length)
                throws IOException {
            if (Thread.currentThread() == reader && position < below
                    && inRead.getCount() > 0) {
                inRead.countDown();
                CloseRaceStream.await(cutMade);
            }
            inner.read(position, dest, destOffset, length);
        }

        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            inner.append(source, sourceOffset, length);
        }

        public void pretruncate(long position) {
            if (!cutHeld) {
                inner.pretruncate(position);
            }
        }

        public void close() {
            inner.close();
        }
    }

    /**
     * Db.getTrans of a record that next() reads whole, its size and last byte right, but whose
     * parse fails (bergdb 005-82): here a byte of a value node's value is flipped, and the
     * node's checksum fails. The read fails the database with the StreamChecksumException as
     * the cause. Before, getTrans parsed the record outside its failure handling: the
     * exception escaped as it was, and the database stayed active and took writes (bergdb
     * 012-14, section 6.7).
     */
    @Nano
    public static void testGetTransChecksum() throws IOException {
        getTransOfDamagedRecord(0);
    }

    /**
     * As testGetTransChecksum, with the flipped byte in the value node's size, its high byte:
     * the node does not fit inside its declared record (bergdb 005-74), and the parse refuses
     * the record before the checksum, with a StreamFormatException.
     */
    @Nano
    public static void testGetTransMalformed() throws IOException {
        getTransOfDamagedRecord(1);
    }

    /**
     * As testGetTransChecksum, with a value node whose checksum is right but whose value
     * size is -1: the parse refuses it with a StreamFormatException ("Bad value size", bergdb
     * 015-07), the cause of the failure. Until 005-82 the parse's NegativeArraySizeException
     * escaped as it was; from 005-82 to 015-07 getTrans made it the cause of a
     * StreamFormatException (testGetTransUncheckedParseError; that wrap is tested by
     * testParseTransWraps now).
     */
    @Nano
    public static void testGetTransBadValueSize() throws IOException {
        getTransOfDamagedRecord(2);
    }

    /**
     * Db.parseTrans, getTrans's parse (bergdb 005-82): a RuntimeException other than a
     * StreamFormatException becomes the cause of a StreamFormatException, which fails the
     * database. Since 015-07 no malformed record is known to give one, so a record buffer of
     * null stands for a bug: StoredTrans.parse throws an IllegalArgumentException for it.
     */
    @Nano
    public static void testParseTransWraps() {
        Db db = Db.builder().testSetup().start();
        Trans t = db.trans().put("/a", "a0").build();
        db.execute(t);
        NodeStream.TransIterator ti =
                db.internal().nodeStream().createTransIteratorFromExactStartupPos(t.tpos);
        Assert.assertTrue("the transaction", ti.next());
        ti.transBuffer = null;
        StreamFormatException e = null;
        try {
            Db.parseTrans(ti, t.tpos);
        } catch (StreamFormatException ex) {
            e = ex;
        } finally {
            db.close();
        }
        Assert.assertTrue("wrapped: " + e, e != null
                && e.getCause() instanceof IllegalArgumentException
                && e.getMessage().startsWith("A malformed record at stream pos " + t.tpos));
    }

    /**
     * Two transactions, synced; the reads of the first one's value node then give it damaged
     * (FaultStream.patch): 0, a byte of the value flipped; 1, the high byte of the node's
     * size flipped; 2, the value's size -1, with the checksum made right. getTrans of the
     * first fails the database, and every later transaction and read is refused with that
     * cause, getTrans of the second too; nothing is appended. Damage in the reads only: the
     * restart reads both, and getTrans gives them. Since bergdb 021-27 that is
     * Internal.getTrans(), for a position the database has given, as transactionInfo()
     * reads; Db.getTrans() takes the position as a caller's and refuses it first, with
     * IllegalArgumentException, the damage its cause, and the database goes on.
     */
    private static void getTransOfDamagedRecord(int damage) throws IOException {
        FaultStream s = new FaultStream();
        Db db = Db.builder().testSetup(s).start();
        Trans t1 = db.trans().put("/a", "a0").build();
        db.execute(t1);
        Trans t2 = db.trans().put("/b", "b0").build();
        db.execute(t2);
        db.sync(SyncLevel.ORDINARY);
        final long length = s.getLength();
        
        // The value node of /a, as stored: size 4, type 1, version 1, zero 2, checksum 4,
        // id 8, offset from the record 4, the value's size 4, then the value (StoredValueNode;
        // the checksum 2 bytes, at 6, until bergdb 024-25).
        long vpos = -1;
        for (StoredNode n : db.getTrans(t1.tpos).nodes) {
            if (n instanceof StoredValueNode
                    && Arrays.equals(bytes("a0"), ((StoredValueNode) n).getNode().value)) {
                vpos = n.getNode().getSpos();
            }
        }
        Assert.assertTrue("the value node", vpos > 0);
        byte[] node = new byte[4];
        s.inner.read(vpos, node, 0, 4);
        node = new byte[Bytes.bytesToIntLE(node, 0)];
        s.inner.read(vpos, node, 0, node.length);
        Class<?> cause;
        if (damage == 0) {
            node[28] ^= 0x01;
            cause = StreamChecksumException.class;
        } else if (damage == 1) {
            node[3] ^= 0x01;
            cause = StreamFormatException.class;
        } else {
            Bytes.intToBytesLE(-1, node, 24);
            NodeChecksum.set(node, 0, node.length);
            cause = StreamFormatException.class;
        }
        s.patchAt = vpos;
        s.patch = node;

        IllegalArgumentException refused1 = null;
        try {
            db.getTrans(t1.tpos);
        } catch (IllegalArgumentException ex) {
            refused1 = ex;
        }
        Assert.assertTrue("a caller's position refused: " + refused1,
                refused1 != null && refused1.getCause().getClass() == cause);
        Assert.assertEquals("the database goes on", t2.tt, db.getTrans(t2.tpos).tt);
        Assert.assertEquals("b0", DbUtil.getString(db, "/b"));

        DbFailedException e = null;
        try {
            db.internal().getTrans(t1.tpos);
        } catch (DbFailedException ex) {
            e = ex;
        } catch (RuntimeException ex) {
            throw new AssertionError("the read did not fail the database: " + ex, ex);
        }
        Assert.assertTrue("the read fails the database", e != null);
        Assert.assertTrue("faults made", s.faults > 0);
        Assert.assertTrue("the cause: " + e.getCause(), e.getCause().getClass() == cause);
        if (damage == 1) {
            Assert.assertTrue("the cause: " + e.getCause(),
                    e.getCause().getMessage().startsWith("Bad node size"));
        } else if (damage == 2) {
            Assert.assertTrue("the cause: " + e.getCause(), e.getCause().getCause() == null
                    && e.getCause().getMessage().startsWith("Bad value size"));
        }
        assertRefused(db, e.getCause());
        DbFailedException refused = null;
        try {
            db.getTrans(t2.tpos);
        } catch (DbFailedException ex) {
            refused = ex;
        }
        Assert.assertTrue("getTrans of the second refused",
                refused != null && refused.getCause() == e.getCause());
        s.patch = null;
        db.sync(SyncLevel.ORDINARY);      // The storage is healthy.
        Assert.assertEquals("the stream's length", length, s.getLength());
        db.close();

        Db db2 = Db.builder().testSetup(s.inner.copy()).start();
        Assert.assertEquals("a0", DbUtil.getString(db2, "/a"));
        Assert.assertEquals("b0", DbUtil.getString(db2, "/b"));
        Assert.assertEquals("the first", t1.tt, db2.getTrans(t1.tpos).tt);
        Assert.assertEquals("the second", t2.tt, db2.getTrans(t2.tpos).tt);
        db2.close();
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
     * bergdb 005-32: an Error in a flush (as an assertion of FileStream) ended the storage
     * thread without telling the storage, and a sync waited for ever. Now the flush fails the
     * stream, and the sync fails the database (005-30); close() returns.
     */
    @Nano
    public static void testErrorInFlushFailsSync() throws Exception {
        final FaultStream s = new FaultStream();
        final Db db = Db.builder().testSetup(s).start();
        db.sync(SyncLevel.ORDINARY);
        s.errorInAppends = true;
        db.execute(db.trans().put("/a", "a0").build());
        Throwable thrown = within(10000, new Runnable() {
            public void run() {
                db.sync(SyncLevel.ORDINARY);
            }
        });
        Assert.assertTrue("the sync fails: " + thrown, thrown instanceof DbFailedException);
        boolean flush = false;          // In the cause chain (StorageManager, bergdb 019-10).
        for (Throwable t = thrown.getCause(); t != null && !flush; t = t.getCause()) {
            flush = String.valueOf(t.getMessage()).contains("The flush failed");
        }
        Assert.assertTrue("the flush's failure: " + thrown.getCause(), flush);
        Assert.assertTrue("close() returns", within(10000, new Runnable() {
            public void run() {
                db.close();
            }
        }) == null);
    }

    /**
     * bergdb 015-35 (review R3-F10, R5-F3): a write of the storage thread that fails, with
     * no call of the application on the storage, fails the database too (010-01, P7). Before,
     * the storage failed but the database stayed active: a get served from memory went on and
     * returned /a = a1, whose record the failure kept off the stream, until a transaction, a
     * sync or a load met the failure.
     */
    @Nano
    public static void testBackgroundWriteFailureFailsReads() throws Exception {
        final FaultStream s = new FaultStream();
        final Db db = Db.builder().testSetup(s).start();
        try {
            db.execute(db.trans().put("/a", "a0").build());
            db.sync(SyncLevel.ORDINARY);
            s.failAppends = true;
            db.execute(db.trans().put("/a", "a1").build());
            waitForStorageError(db);

            DbFailedException failed = null;
            String value = null;
            try {
                value = DbUtil.getString(db, "/a");
            } catch (DbFailedException e) {
                failed = e;
            }
            Assert.assertTrue("a get from memory after the failed write: " + value,
                    failed != null);
            Assert.assertTrue("the write's failure: " + failed.getCause(),
                    failed.getCause() instanceof StreamIoException
                    && String.valueOf(failed.getCause().getCause()).contains("an append error"));
            assertRefused(db, failed.getCause());
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-81 (review R5-F6): a failed write whose stream then throws an unchecked
     * exception from its close, as the storage closes it, fails a sync and the database.
     * Before, the close's exception left StorageManager.handleStreamException before the
     * storage had its error, and ended the storage thread: the sync waited for ever, and the
     * database stayed active. Two fixes guard it, and the test fails only without both (review
     * R1 of night 006-12, C1): 015-81's order (the error before the close) and 015-78's
     * BufferedStream.closeStream(), which catches the unchecked close error. The order alone
     * is pinned by testCloseWaitsForTheFailedStreamsClose.
     */
    @Nano
    public static void testUncheckedCloseErrorAfterFailedWriteFailsSync() throws Exception {
        final FaultStream s = new FaultStream();
        final Db db = Db.builder().testSetup(s).start();
        try {
            db.execute(db.trans().put("/a", "a0").build());
            db.sync(SyncLevel.ORDINARY);
            s.failAppends = true;
            s.errorInClose = true;
            db.execute(db.trans().put("/a", "a1").build());
            Throwable thrown = within(5000, new Runnable() {
                public void run() {
                    db.sync(SyncLevel.ORDINARY);
                }
            });
            Assert.assertTrue("the sync fails: " + thrown, thrown instanceof DbFailedException);
            // 015-81's order: the storage has its error before it closes the stream, so the sync
            // can fail before the close's error is met (2026-11-10: once on s1, JDK 27). Wait
            // for the storage thread's close, at most 30 s, as within() waits for the sync.
            long end = System.currentTimeMillis() + 30 * 1000;
            while (s.faults < 2 && System.currentTimeMillis() < end) {
                Thread.sleep(1);
            }
            Assert.assertTrue("the close's error was met", s.faults >= 2);
            assertRefused(db, thrown.getCause());
        } finally {
            s.errorInClose = false;
            db.close();
        }
    }

    /**
     * Review R1 of night 006-12, B1 (bergdb 015-35, 015-81): Db.close() returns only after
     * the stream is closed, also when a failure of the storage has another thread closing
     * it. Here a read fails while a write is held in the stream's append, so the reader's
     * close of the storage waits for that write. The failure is seen during that close (015-81
     * sets it first, and a get fails at it, 015-35), and a close() then waits for the stream.
     * Before, StorageManager.closeInner skipped the close of a failed storage, which
     * "handleStreamException closed", and close() returned while the reader still closed: the
     * stream open, a FileStream's directory lock held, so that a start in the same JVM could
     * meet DirectoryInUseException.
     */
    @Nano
    public static void testCloseWaitsForTheFailedStreamsClose() throws Exception {
        final FaultStream s = new FaultStream();
        final Db db = Db.builder().testSetup(s).start();
        Thread reader = null;
        try {
            final Trans t = db.trans().put("/a", "a0").build();
            db.execute(t);
            db.sync(SyncLevel.ORDINARY);
            s.holdAppends = true;
            db.execute(db.trans().put("/b", "b0").build());     // Held in the stream's append.
            s.failReads = true;
            reader = new Thread() {
                public void run() {
                    try {
                        db.getTrans(t.tpos);
                    } catch (RuntimeException e) {
                        // Expected: the read fails the storage, and its close waits; the
                        // database is failed, or stopping when the read returns.
                    }
                }
            };
            reader.setDaemon(true);
            reader.start();
            waitForStorageError(db);
            DbFailedException failed = null;
            try {
                DbUtil.get(db, "/a");
            } catch (DbFailedException e) {
                failed = e;
            }
            Assert.assertTrue("a get fails while the stream's close waits", failed != null);
            
            Thread closer = new Thread() {
                public void run() {
                    db.close();
                }
            };
            closer.setDaemon(true);
            closer.start();
            closer.join(300);
            Assert.assertTrue("close() waits for the stream's close; the stream closed: "
                    + s.closed, closer.isAlive());
            s.holdAppends = false;
            closer.join(10000);
            Assert.assertFalse("close() returns", closer.isAlive());
            Assert.assertTrue("the stream is closed as close() returns", s.closed);
        } finally {
            s.holdAppends = false;
            if (reader != null) {
                reader.join(10000);
            }
            db.close();
        }
    }
    
    /**
     * bergdb 019-09 (review R1 of night 006-12, re-review of 3cb19f7, B2): a write of the
     * storage thread fails, and the application's next call is close(), which throws
     * StreamIoException with the write's failure as the cause (Frans's option (a)): the
     * transactions that were buffered are lost, and close() is the one call left to say so
     * (010-01, P7). Before, close() set STOPPING first, so 015-35's check never failed the
     * database, StorageManager.closeInner returned no failure for a failed main stream, and
     * close() returned normally: no call reported the failure.
     */
    @Nano
    public static void testCloseReportsBackgroundWriteFailure() throws Exception {
        final FaultStream s = new FaultStream();
        final Db db = Db.builder().testSetup(s).start();
        try {
            db.execute(db.trans().put("/a", "a0").build());
            db.sync(SyncLevel.ORDINARY);
            s.failAppends = true;
            db.execute(db.trans().put("/a", "a1").build());
            waitForStorageError(db);
            Throwable thrown = within(10000, new Runnable() {
                public void run() {
                    db.close();
                }
            });
            Assert.assertTrue("close() throws StreamIoException: " + thrown,
                    thrown instanceof StreamIoException);
            Assert.assertTrue("the write's failure: " + thrown.getCause(),
                    String.valueOf(thrown.getCause()).contains("an append error"));
            Assert.assertTrue("the stream is closed", s.closed);
        } finally {
            db.stop();
        }
    }
    
    /**
     * bergdb 019-09: as testCloseReportsBackgroundWriteFailure, with stop() before close():
     * close() after stop() throws the failure too, as it does for a failed final flush.
     */
    @Nano
    public static void testCloseAfterStopReportsBackgroundWriteFailure() throws Exception {
        final FaultStream s = new FaultStream();
        final Db db = Db.builder().testSetup(s).start();
        try {
            db.execute(db.trans().put("/a", "a0").build());
            db.sync(SyncLevel.ORDINARY);
            s.failAppends = true;
            db.execute(db.trans().put("/a", "a1").build());
            waitForStorageError(db);
            db.stop();
            Throwable thrown = within(10000, new Runnable() {
                public void run() {
                    db.close();
                }
            });
            Assert.assertTrue("close() after stop() throws StreamIoException: " + thrown,
                    thrown instanceof StreamIoException);
            Assert.assertTrue("the write's failure: " + thrown.getCause(),
                    String.valueOf(thrown.getCause()).contains("an append error"));
        } finally {
            db.stop();
        }
    }
    
    /**
     * bergdb 019-09, option (a): a database that a call has failed with the storage's
     * failure closes normally, also after stop(): the failure was reported, by the get here
     * (a DbFailedException), and DbFailedException asks the application to close the
     * database and start it again. With option (b) this close would throw too.
     */
    @Nano
    public static void testCloseOfFailedDatabaseReturnsNormally() throws Exception {
        for (final boolean stopFirst : new boolean[] {false, true}) {
            final FaultStream s = new FaultStream();
            final Db db = Db.builder().testSetup(s).start();
            try {
                db.execute(db.trans().put("/a", "a0").build());
                db.sync(SyncLevel.ORDINARY);
                s.failAppends = true;
                db.execute(db.trans().put("/a", "a1").build());
                waitForStorageError(db);
                DbFailedException failed = null;
                try {
                    DbUtil.get(db, "/a");
                } catch (DbFailedException e) {
                    failed = e;
                }
                Assert.assertTrue("a get fails", failed != null);
                if (stopFirst) {
                    db.stop();
                }
                Throwable thrown = within(10000, new Runnable() {
                    public void run() {
                        db.close();
                    }
                });
                Assert.assertTrue("close() returns normally (stop first: " + stopFirst
                        + "): " + thrown, thrown == null);
            } finally {
                db.stop();
            }
        }
    }
    
    /**
     * bergdb 019-39 (review R6 of 006-13, B2): a stop() whose closer thread cannot start, as
     * at an OutOfMemoryError, closes the database on its own thread and throws the Error;
     * close() then returns. Before, closeBegun stayed set with no closer, and close() waited
     * for ever.
     */
    @Nano
    public static void testStopWhoseCloserCannotStart() throws Exception {
        final MemoryStream s = new MemoryStream();
        final Db db = Db.builder().testSetup(s).start();
        db.execute(db.trans().put("/a", "a0").build());
        final OutOfMemoryError oom = new OutOfMemoryError("test: no closer thread");
        Util.testHookStart = t -> {
            if (t.getName().startsWith("Db-close-")) throw oom;
        };
        Throwable thrown;
        try {
            thrown = within(10000, () -> db.stop());
        } finally {
            Util.testHookStart = null;
        }
        Assert.assertTrue("stop() throws the Error: " + thrown, thrown == oom);
        thrown = within(10000, () -> db.close());
        Assert.assertTrue("close() returns: " + thrown, thrown == null);
        Db db2 = Db.builder().testSetup(s.copy()).start();
        Assert.assertEquals("a0", DbUtil.getString(db2, "/a"));
        db2.close();
    }
    
    /**
     * bergdb 019-40 (review R6 of 006-13, C2): an Error in a sync, and in
     * setCacheSizeIndicator's start of the eviction thread, fails the database and is thrown
     * as it is (bergdb 019-10).
     */
    @Nano
    public static void testErrorInSyncOrCacheSizeFailsTheDatabase() {
        for (int i = 0; i < 2; i++) {
            final String call = i == 0 ? "sync()" : "setCacheSizeIndicator()";
            final OutOfMemoryError oom = new OutOfMemoryError("test: in " + call);
            final Db db = Db.builder().testSetup()
                    .evictionSchedule(Eviction.Schedule.BUDGET, 1).start();
            Throwable thrown = null;
            try {
                db.execute(db.trans().put("/a", "a0").build());
                StorageManager.testHookSync = () -> {
                    throw oom;
                };
                Util.testHookStart = t -> {
                    if (t.getName().equals("bergdb-evictor")) throw oom;
                };
                if (i == 0) {
                    db.sync(SyncLevel.ORDINARY);
                } else {
                    db.setCacheSizeIndicator(1);
                }
            } catch (Throwable e) {
                thrown = e;
            } finally {
                StorageManager.testHookSync = null;
                Util.testHookStart = null;
            }
            try {
                Assert.assertTrue(call + " throws the Error: " + thrown, thrown == oom);
                assertRefused(db, oom, call);
            } finally {
                db.close();
            }
        }
    }
    
    /**
     * Node size 8, a startup distance of 1,000 bytes, so that index nodes are written and
     * can be evicted; every evictable object evicted after every transaction; the audit
     * after every 'audit'-th transaction and at startup, or off (0).
     */
    private static Db startEvicting(AppendOnlyStream s, int audit) {
        Db db = Db.builder().testSetup(s).maxNodeSize8()
                .evictionSchedule(Eviction.Schedule.EVERY, 1).audit(audit).start();
        db.setStartupDistance(1000);      // nothing written if in force (bergdb 028-13)
        return db;
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

    /**
     * Waits, up to 30 s (10 s until bergdb 028-23), until the main storage has failed, as
     * after a failed flush.
     */
    private static void waitForStorageError(Db db) {
        final long end = System.nanoTime() + 30L * 1000 * 1000 * 1000;
        while (!db.internal().storageFailed()) {
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

    /**
     * Test hooks (Db.testHooks) that throw 'thrown', a RuntimeException or an Error, when a
     * transaction gives the Dag its operation at 'key' (Db.TestHooks.kvApplied, in Db.putKvs,
     * after the go point), after 'before' has run, if not null. A test sets them around one
     * execute() and sets Db.testHooks to null after it.
     */
    private static Db.TestHooks throwAtPut(final String key, final Throwable thrown,
            final Runnable before) {
        final long[] k = Keys.toSegments(key);
        return new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {}
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) {}
            public void kvApplied(long[] key, byte[] value) {
                if (Arrays.equals(key, k)) {
                    if (before != null) {
                        before.run();
                    }
                    if (thrown instanceof Error) {
                        throw (Error) thrown;
                    }
                    throw (RuntimeException) thrown;
                }
            }
        };
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
        assertRefused(db, cause, "");
    }

    /** As assertRefused(db, cause), with the case, 'what', named (bergdb 019-40). */
    private static void assertRefused(Db db, Throwable cause, String what) {
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
            Assert.assertTrue("refused, " + what + ", " + i + ": " + refused,
                    refused != null && refused.getCause() == cause);
        }
    }

    /** Waits, up to 10 s, until the thread waits for the write lock of a Db. */
    private static void waitUntilBlockedOnTheWriteLock(Thread thread) {
        final long end = System.nanoTime() + 10L * 1000 * 1000 * 1000;
        while (System.nanoTime() < end) {
            if (Platform.waitsFor(thread, Thread.State.BLOCKED, Db.WriteLock.class.getName())) {
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
    
    /**
     * Runs r in a daemon thread for up to ms, and at least 30 s, a hang guard that load does
     * not pass (bergdb 028-23); returns what it threw, null, or HUNG.
     */
    static Throwable within(int ms, final Runnable r) throws InterruptedException {
        ms = Math.max(ms, 30 * 1000);
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
    
    /**
     * A test stream over a MemoryStream that fails on purpose, when set: its reads throw an
     * IOException (a read error: the storage then fails), or return the bytes with the last one
     * changed (a corrupt node: a checksum error, the storage stays healthy), or with the bytes
     * of 'patch' at stream position patchAt instead of the stored ones (bergdb 005-82); its
     * appends throw, or wait until holdAppends is cleared.
     */
    static class FaultStream implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        volatile boolean failReads = false;
        volatile boolean uncheckedReads = false;    // bergdb 019-10
        volatile boolean errorInReads = false;      // bergdb 019-10
        final Error readError = new Error("FaultStream: an Error in a read, as set");
        volatile boolean corruptReads = false;
        volatile boolean failAppends = false;
        volatile boolean errorInAppends = false;    // an Error, as an assertion (bergdb 005-32)
        volatile boolean holdAppends = false;
        volatile boolean errorInClose = false;  // unchecked, after the close (bergdb 015-81)
        volatile boolean closed = false;        // set by close(), before an errorInClose
        volatile long patchAt = -1;
        volatile byte[] patch = null;
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
            if (uncheckedReads) {
                faults++;
                throw new IllegalStateException("FaultStream: an unchecked read error, as set");
            }
            if (errorInReads) {
                faults++;
                throw readError;
            }
            inner.read(position, dest, destOffset, length);
            if (corruptReads && length > 8) {
                faults++;
                dest[destOffset + length - 1] ^= 0x55;
            }
            final byte[] p = patch;
            final long at = patchAt;
            if (p != null && at < position + length && at + p.length > position) {
                faults++;
                for (long q = Math.max(at, position); q < Math.min(at + p.length,
                        position + length); q++) {
                    dest[destOffset + (int) (q - position)] = p[(int) (q - at)];
                }
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

        public void close() throws IOException {
            inner.close();
            closed = true;
            if (errorInClose) {
                faults++;
                throw new IllegalStateException("FaultStream: an unchecked close error, as set");
            }
        }
    }

    /**
     * A test stream over a MemoryStream whose reads of a whole key node, while 'damage' is
     * set, give the node a key count of 32,767 with its checksum made right (bergdb 015-07):
     * a node that passes the checksum but whose inner field does not fit its size. A load
     * reads a node with one read of its size (NodeStream.readNode); a read of a record starts
     * with its format byte, not a node's type, and is left as it is.
     */
    static class KeyCountStream implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        volatile boolean damage = false;
        volatile int damaged = 0;

        public long getLength() {
            return inner.getLength();
        }

        public long getFirstPos() {
            return inner.getFirstPos();
        }

        public void read(long position, byte[] dest, int destOffset, int length)
                throws IOException {
            inner.read(position, dest, destOffset, length);
            if (damage && length >= 32 && dest[destOffset + 4] == bergdb.dag.Node.TYPE_KEY_NODE
                    && bergdb.common.Bytes.bytesToIntLE(dest, destOffset) == length) {
                dest[destOffset + 13] = (byte) 0xff;      // the count, bytes 13 and 14
                dest[destOffset + 14] = (byte) 0x7f;
                NodeChecksum.set(dest, destOffset, length);
                damaged++;
            }
        }

        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            inner.append(source, sourceOffset, length);
        }

        public void pretruncate(long position) throws IOException {
            inner.pretruncate(position);
        }

        public void close() throws IOException {
            inner.close();
        }
    }
}
