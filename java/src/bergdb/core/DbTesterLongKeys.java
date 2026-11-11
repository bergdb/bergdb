package bergdb.core;

import java.util.Arrays;
import java.util.List;

import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * Long keys (bergdb 021-16; since bergdb 024-24 within the limits of 024-17). A key is a tree
 * of key nodes with a level per segment of 7 bytes (Keys.toSegments), and walks of that tree
 * were recursions with a frame per level: with the thread's default stack, a database with a
 * key of about 90 KB or more did not start (the start's check, Dag.visitMemoryNodes), and a
 * put of a key of 1,000,000 bytes after one of 100,000 with the same start failed the
 * database (Dag.freshTreeBound); a StackOverflowError each (020-24-05, U5-1 and U5-2). Since
 * release 2026.5 a user's key has at most Db.MAX_KEY_BYTES = 111 bytes (L2), and BergDB's own
 * keys, put through Trans.Builder's internal calls, at most what L3 leaves, 57,344 bytes in a
 * transaction: the tests put keys at those limits, at every node size, and check that one
 * byte more is refused with nothing written. Keys of 400 kB are walked below the Core's
 * checks in DagTester.testLongKeyWalks. Until 024-24 the tests put keys of 100,000 to
 * 1,000,000 bytes.
 */
public class DbTesterLongKeys {

    private static final long LATEST = Long.MAX_VALUE;

    private static byte[] key(String start, int length) {
        byte[] key = new byte[length];
        Arrays.fill(key, (byte) 'k');
        byte[] s = start.getBytes(java.nio.charset.StandardCharsets.UTF_8);
        System.arraycopy(s, 0, key, 0, s.length);
        return key;
    }

    /**
     * One of BergDB's own keys, which alone may pass L2: it starts with 01 25, the bkey of
     * "/#" (review rev24, R2).
     */
    private static byte[] ownKey(int length) {
        byte[] key = key("..", length);
        key[0] = 1;
        key[1] = 0x25;
        return key;
    }

    private static void assertValue(Db db, byte[] key, String value) {
        Assert.assertArrayEquals("the value of the key of " + key.length + " bytes",
                value.getBytes(java.nio.charset.StandardCharsets.UTF_8), DbUtil.get(db, key));
    }

    /** The keys of a scan of the whole database, forward or backward. */
    private static void assertScan(Db db, boolean forward, byte[]... keys) {
        GetMany g = db.newGetMany();
        g.lookupTime = LATEST;
        if (!forward) {
            g.setBackward();
        }
        g.stopCondition = new GetMany.DontStop();
        db.getMany(g);
        List<Kvt> result = g.result;
        Assert.assertEquals("the scan's KVs", keys.length, result.size());
        for (int i = 0; i < keys.length; i++) {
            Assert.assertTrue("the scan's key " + i,
                    Arrays.equals(Keys.toSegments(keys[i]), result.get(i).key));
        }
    }

    /** A builder of each node size: 8, 14, 30 and 62. */
    private static DbBuilder builder(int nodeSize, MemoryStream stream) {
        DbBuilder b = Db.builder().testSetup(stream);
        switch (nodeSize) {
        case 8: return b.maxNodeSize8();
        case 14: return b.maxNodeSize14();
        case 30: return b.maxNodeSize30();
        default: return b.maxNodeSize62();
        }
    }

    private static final int[] NODE_SIZES = {8, 14, 30, 62};

    /** Asserts that 'r' throws an exception of class 'c', and returns its message. */
    private static String refused(Class<? extends Throwable> c, Runnable r) {
        try {
            r.run();
        } catch (Throwable e) {
            Assert.assertTrue("refused with " + e, c.isInstance(e));
            return e.getMessage();
        }
        throw new AssertionError("not refused");
    }

    /**
     * U5-1 at the limit L2: a key of 111 bytes and a short key, put, and the database started
     * again from its stream, at each node size: the values are there, the scans list both
     * keys, and a put of another key of 111 bytes with the same start works. A key of 112
     * bytes is refused by the Trans.Builder call, as a put, as a delete, and as segments,
     * with IllegalArgumentException, and the database is unchanged (its transactions and
     * its scan). (U5-1 itself, 200,000 bytes, until bergdb 024-24.)
     */
    @Nano
    public static void testLongKeyRestart() {
        for (int nodeSize : NODE_SIZES) {
            final byte[] longKey = key("/d/", Db.MAX_KEY_BYTES);
            final byte[] shortKey = Keys.toBytes("/a");
            MemoryStream stream = new MemoryStream();
            Db db = builder(nodeSize, stream).start();
            try {
                db.execute(db.trans().put(longKey, "long".getBytes()).build());
                db.execute(db.trans().put(shortKey, "short".getBytes()).build());
                final long count = db.getTransactionCount();
                final byte[] over = key("/d/", Db.MAX_KEY_BYTES + 1);
                String m = refused(IllegalArgumentException.class,
                        () -> db.trans().put(over, new byte[0]));
                Assert.assertTrue(m, m.contains("112 bytes, more than 111 (bergdb 024-17, L2)"));
                refused(IllegalArgumentException.class, () -> db.trans().delete(over));
                refused(IllegalArgumentException.class,
                        () -> db.trans().put(Keys.toSegments(over), new byte[0]));
                refused(IllegalArgumentException.class,
                        () -> db.trans().delete(Keys.toSegments(over)));
                refused(IllegalArgumentException.class,
                        () -> db.trans().put(Keys.toSegments(over), null, new byte[0], null));
                Assert.assertEquals("node size " + nodeSize + ": transactions", count, 
                        db.getTransactionCount());
                assertScan(db, true, shortKey, longKey);
                db.sync(SyncLevel.ORDINARY);
                db.checkNodes();
                stream = stream.copy();     // A closed stream takes no append.
            } finally {
                db.close();
            }

            Db db2 = builder(nodeSize, stream).start();
            try {
                assertValue(db2, longKey, "long");
                assertValue(db2, shortKey, "short");
                assertScan(db2, true, shortKey, longKey);
                assertScan(db2, false, longKey, shortKey);
                db2.checkNodes();
                byte[] other = key("/d/", Db.MAX_KEY_BYTES);
                other[Db.MAX_KEY_BYTES - 1] = 'x';
                db2.execute(db2.trans().put(other, "other".getBytes()).build());
                assertValue(db2, other, "other");
                assertValue(db2, longKey, "long");
            } finally {
                db2.close();
            }
        }
    }

    /**
     * U5-2 at the limits: at each node size, a put of a key of 111 bytes (L2) after one of 50
     * with the same start; then BergDB's own keys, through Trans.Builder.putLongKey(), of
     * 10,000 bytes and then of 57,344, L3's whole, with the same start: both values are there
     * and the database goes on. A transaction of keys of 57,345 bytes in all is refused by
     * execute() with DbException (L3), nothing written. The startup distance of 200 MB keeps
     * the first key's nodes in memory, dirty, as in U5-2's test. (U5-2 itself, keys of
     * 100,000 and 1,000,000 bytes, until bergdb 024-24.)
     */
    @Nano
    public static void testLongKeyAfterItsStart() {
        for (int nodeSize : NODE_SIZES) {
            final byte[] first = key("/d/", 50);
            final byte[] second = key("/d/", Db.MAX_KEY_BYTES);
            final byte[] own1 = ownKey(10 * 1000);
            final byte[] own2 = ownKey(Db.MAX_TRANS_KEY_BYTES);
            Db db = builder(nodeSize, new MemoryStream()).startupDistance(200 * 1000 * 1000)
                    .start();
            try {
                db.execute(db.trans().put(first, "first".getBytes()).build());
                db.execute(db.trans().put(second, "second".getBytes()).build());
                assertValue(db, first, "first");
                assertValue(db, second, "second");
                db.execute(db.trans().putLongKey(Keys.toSegments(own1), null, 
                        "own1".getBytes(), null).build());
                db.execute(db.trans().putLongKey(Keys.toSegments(own2), null, 
                        "own2".getBytes(), null).build());
                assertValue(db, own1, "own1");
                assertValue(db, own2, "own2");
                final long count = db.getTransactionCount();
                final byte[] over = ownKey(Db.MAX_TRANS_KEY_BYTES + 1);
                String m = refused(bergdb.pub.util.DbException.class, () -> db.execute(
                        db.trans().putLongKey(Keys.toSegments(over), null, new byte[0], null)
                        .build()));
                Assert.assertTrue(m, m.contains("57345 bytes, more than 57344 (bergdb 024-17, "
                        + "L3)"));
                Assert.assertEquals("node size " + nodeSize + ": transactions", count,
                        db.getTransactionCount());
                Assert.assertEquals(null, DbUtil.get(db, over));
                db.execute(db.trans().put("/x", "x").build());
                assertValue(db, Keys.toBytes("/x"), "x");
                db.checkNodes();
            } finally {
                db.close();
            }
        }
    }
    /**
     * 021-16's depth through BergDB's own long keys (review rev24, R7): in a thread with a
     * stack of 256 kB, where a recursion with a frame a segment would overflow at these
     * 8,193 segments, a key of 10,000 bytes and then one of 57,344 (L3's whole) with the same
     * start, through putLongKey(), and a start again from the stream (the start's check,
     * Dag.visitMemoryNodes). The record limit is lowered to 30 MB so that execute()'s cheap
     * count fails and Dag.dirtyNodeBound walks the new key's segment trees
     * (freshTreeBound), as U5-2's put did.
     */
    @Nano
    public static void testOwnLongKeysSmallStack() throws InterruptedException {
        final Throwable[] failure = new Throwable[1];
        Thread t = new Thread(null, () -> {
            try {
                ownLongKeys();
            } catch (Throwable e) {
                failure[0] = e;
            }
        }, "a small stack", 256 * 1024);
        t.start();
        t.join();
        if (failure[0] != null) {
            throw new AssertionError("with a stack of 256 kB: " + failure[0], failure[0]);
        }
    }

    private static void ownLongKeys() {
        final long saved = StoredTrans.recordLimit;
        StoredTrans.recordLimit = 30 * 1000 * 1000;
        try {
            final byte[] first = ownKey(10 * 1000);
            final byte[] second = ownKey(Db.MAX_TRANS_KEY_BYTES);
            MemoryStream stream = new MemoryStream();
            Db db = Db.builder().testSetup(stream).startupDistance(200 * 1000 * 1000).start();
            try {
                db.execute(db.trans().putLongKey(Keys.toSegments(first), null, 
                        "first".getBytes(), null).build());
                db.execute(db.trans().putLongKey(Keys.toSegments(second), null, 
                        "second".getBytes(), null).build());
                assertValue(db, first, "first");
                assertValue(db, second, "second");
                db.sync(SyncLevel.ORDINARY);
                db.checkNodes();
                stream = stream.copy();
            } finally {
                db.close();
            }
            Db db2 = Db.builder().testSetup(stream).start();
            try {
                assertValue(db2, first, "first");
                assertValue(db2, second, "second");
                db2.checkNodes();
            } finally {
                db2.close();
            }
        } finally {
            StoredTrans.recordLimit = saved;
        }
    }
}
