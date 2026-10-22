package bergdb.core;

import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;

import bergdb.common.StringUtil;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.DbFailedException;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * Tests of a transaction that fails after its go point (bergdb 005-01, register M49 of
 * docs/level4-alignment.md; item 003, 003-01's test plan). Until 005-01 such a transaction
 * was half committed: its time became readable with its first puts in memory, and the next
 * transaction wrote its nodes as its own. Now the database fails: the call gets a
 * DbFailedException (an Error is thrown as it is), the transaction's time never becomes a
 * lookup time, every later transaction and read is refused, nothing more is appended, and a
 * restart gives the state before the transaction, also with eviction and the audit on.
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
        for (int i = 0; i < KEYS; i += 10) {
            Trans.Builder b = db.trans();
            for (int j = i; j < i + 10; j++) {
                b.put(key(j), "v" + j);
            }
            db.execute(b.build());
        }
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
     * lost, as in a crash, and the failing one too. An f-test: the sync after the failed
     * append returns at StorageManager's next 500 ms poll (DbTesterStream.testReadOnlyStream2).
     */
    @Nano("f")
    public static void testAppendErrorInStore() {
        FaultStream s = new FaultStream();
        Db db = Db.builder().testSetup(s).start();
        db.execute(db.trans().put("/a", "a0").build());
        db.sync(SyncLevel.STRONG);

        s.failAppends = true;
        db.execute(db.trans().put("/a", "a1").build());     // In memory and buffered only.
        StreamIoException syncException = null;
        try {
            db.sync(SyncLevel.STRONG);
        } catch (StreamIoException e) {
            syncException = e;
        }
        Assert.assertTrue("the sync fails", syncException != null);

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

    // ======== Helpers ========

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

    /** Every later transaction and read is refused, with the first failure as the cause. */
    private static void assertRefused(Db db, Throwable cause) {
        for (int i = 0; i < 3; i++) {
            DbFailedException refused = null;
            try {
                if (i == 0) {
                    db.execute(db.trans().put("/later", "x").build());
                } else if (i == 1) {
                    DbUtil.get(db, "/a");
                } else {
                    DbUtil.getFirstKey(db, Long.MAX_VALUE, null);
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
     * changed (a corrupt node: a checksum error, the storage stays healthy); its appends throw.
     */
    static class FaultStream implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        volatile boolean failReads = false;
        volatile boolean corruptReads = false;
        volatile boolean failAppends = false;
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
            if (failAppends) {
                faults++;
                throw new IOException("FaultStream: an append error, as set");
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
