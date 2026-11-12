package bergdb.core;

import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbException;
import bergdb.stream.MemoryStream;

/**
 * The keys that the Core writes itself (bergdb 024-37; 010-04, R5; Trans.coreKey()): the key
 * "/#i/-dummy", and "/#i/dreclaim/" and every key under it. A caller's put or delete there is
 * refused, by the Trans.Builder call that takes it with IllegalArgumentException, or by
 * Db.execute() with a DbException for the internal calls putLongKey() and deleteLongKey() and
 * for a key that a key transformation gives. Nothing is written, the database goes on, and
 * it starts again. Until 024-37 seven bytes put at "/#i/dreclaim/-settings.txt" were taken,
 * and every later start failed with InternalDataException (CA3; 022-06-2, U2-8).
 */
public class DbTesterCoreKeys {

    /** The Core's keys, and keys under its reclaim directory that it does not write today. */
    private static final String[] CORE = {"/#i/-dummy", "/#i/dreclaim/",
            "/#i/dreclaim/-settings.txt", "/#i/dreclaim/-table.txt", "/#i/dreclaim/-current.txt",
            "/#i/dreclaim/-fill.txt", "/#i/dreclaim/-other.txt", "/#i/dreclaim/dx/-y"};

    /** Keys next to them, and the Pub API's keys under "/#i/": taken. */
    private static final String[] OTHERS = {"/#i/-dummy2", "/#i/-dumm", "/#i/dreclaimx/-a",
            "/#i/dreclai/-a", "/#i/didef/-n", "/#i/dient/dn/-k", "/#i/didel/dn/-0000000000000001",
            "/#i/-other", "/#j/dreclaim/-settings.txt"};

    private static final String TEXT = "is one that the Core writes itself";

    /** Asserts that 'r' throws an exception of class 'c' whose message has TEXT. */
    private static void refused(String what, Class<? extends Throwable> c, Runnable r) {
        try {
            r.run();
        } catch (Throwable e) {
            Assert.assertTrue(what + ": refused with " + e, c.isInstance(e));
            Assert.assertTrue(what + ": " + e.getMessage(), e.getMessage().contains(TEXT));
            return;
        }
        throw new AssertionError(what + ": not refused");
    }

    /**
     * CA3: each way to put or delete a key of the Core's own is refused, nothing is written,
     * the database goes on and starts again with the settings and the dummy as the Core put
     * them. The keys next to them, and the Pub API's, are taken.
     */
    @Nano
    public static void testCallersWritesRefused() {
        final MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).start();
        final long retain = 3600 * Clock.UNITS_PER_SEC;
        try {
            db.setStartupDistance(500 * 1000);              // the Core's own writes pass
            db.setRetainDuration(retain);
            final byte[] settings = DbUtil.get(db, Long.MAX_VALUE, Reclaim.SETTINGS_KEY_NAME);
            Assert.assertTrue("the settings", settings != null);
            final long count = db.getTransactionCount();
            final byte[] seven = {1, 2, 3, 4, 5, 6, 7};

            for (String s : CORE) {
                final byte[] k = Keys.toBytes(s);
                final long[] seg = Keys.toSegments(k);
                final Db d = db;
                refused(s + ", put(String, byte[])", IllegalArgumentException.class,
                        () -> d.trans().put(s, seven));
                refused(s + ", put(String, String)", IllegalArgumentException.class,
                        () -> d.trans().put(s, "x"));
                refused(s + ", put(byte[], byte[])", IllegalArgumentException.class,
                        () -> d.trans().put(k, seven));
                refused(s + ", put(long[], byte[])", IllegalArgumentException.class,
                        () -> d.trans().put(seg, seven));
                refused(s + ", put(long[], kt, byte[], vt)", IllegalArgumentException.class,
                        () -> d.trans().put(seg, null, seven, null));
                refused(s + ", delete(String)", IllegalArgumentException.class,
                        () -> d.trans().delete(s));
                refused(s + ", delete(byte[])", IllegalArgumentException.class,
                        () -> d.trans().delete(k));
                refused(s + ", delete(long[])", IllegalArgumentException.class,
                        () -> d.trans().delete(seg));
                refused(s + ", putLongKey()", DbException.class, () -> d.execute(
                        d.trans().put("/a", "1").putLongKey(seg, null, seven, null).build()));
                refused(s + ", deleteLongKey()", DbException.class, () -> d.execute(
                        d.trans().put("/a", "1").deleteLongKey(seg).build()));
            }
            Assert.assertEquals("nothing written", count, db.getTransactionCount());
            Assert.assertNull(DbUtil.get(db, Long.MAX_VALUE, "/a"));

            for (String s : OTHERS) {
                db.execute(db.trans().putLongKey(Keys.toSegments(s), null, new byte[] {1}, null)
                        .build());
                Assert.assertArrayEquals(s, new byte[] {1}, DbUtil.get(db, Long.MAX_VALUE, s));
            }
            db.execute(db.trans().put("/after", "1").build());     // the database goes on
            db.close();

            db = Db.builder().testSetup(stream.copy()).start();     // and starts again
            Assert.assertEquals("the retain duration", retain, db.getRetainDuration());
            Assert.assertArrayEquals("the settings", settings,
                    DbUtil.get(db, Long.MAX_VALUE, Reclaim.SETTINGS_KEY_NAME));
            Assert.assertEquals("the dummy", 200 * 1000,
                    DbUtil.get(db, Long.MAX_VALUE, "/#i/-dummy").length);
            Assert.assertArrayEquals("/after", new byte[] {'1'},
                    DbUtil.get(db, Long.MAX_VALUE, "/after"));
        } finally {
            db.close();
        }
    }

    /**
     * A key transformation that gives a key of the Core's own: the transaction is refused
     * by execute() with a DbException before its go point, nothing of it is written, the
     * KV gets its key as written back, and the database goes on.
     */
    @Nano
    public static void testKeyTransformationRefused() {
        final MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).start();
        try {
            for (String s : CORE) {
                final long[] target = Keys.toSegments(s);
                final KeyTransformation kt = new KeyTransformation() {
                    public void transform(Trans trans, int index) {
                        trans.kvs[index].setKey(target);
                        trans.writeKeyHashes[index] = Keys.hash(target);
                    }
                };
                final long count = db.getTransactionCount();
                final long[] written = Keys.toSegments("/t");
                final Trans t = db.trans().put(written, kt, new byte[] {1, 2, 3, 4, 5, 6, 7},
                        null).put("/u", "u").build();
                final Db d = db;
                refused(s + ", key transformation", DbException.class, () -> d.execute(t));
                Assert.assertEquals(s + ": nothing written", count, db.getTransactionCount());
                Assert.assertNull(DbUtil.get(db, Long.MAX_VALUE, "/u"));
                Assert.assertNull(DbUtil.get(db, Long.MAX_VALUE, s));
                Assert.assertTrue(s + ": the key as written",
                        Keys.compareArrays(written, t.kvs[0].getKey()) == 0
                        || Keys.compareArrays(written, t.kvs[1].getKey()) == 0);
            }
            db.execute(db.trans().put("/after", "1").build());     // the database goes on
            db.close();
            db = Db.builder().testSetup(stream.copy()).start();
            Assert.assertArrayEquals("/after", new byte[] {'1'},
                    DbUtil.get(db, Long.MAX_VALUE, "/after"));
        } finally {
            db.close();
        }
    }
}
