package bergdb.core;

import java.util.Arrays;

import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * The limits of release 2026.5 (bergdb 024-17, sections 6 and 8; 024-24; Db, "Limits"): for
 * each, a transaction at the limit is taken, and one a step over it is refused, by the call
 * that the Javadoc names and with the exception it names, with nothing written: the database's
 * transactions and values are as before, and it takes the next transaction. L1, operations;
 * L2, a key's bytes (more in DbTesterLongKeys); L3, the key bytes of a transaction; L4, a
 * value's bytes, and a value transformation's result over it, which fails the database (QL6);
 * L5, the keys and values of a transaction.
 */
public class DbTesterLimits {

    private static byte[] bytes(String s) {
        return s.getBytes(java.nio.charset.StandardCharsets.UTF_8);
    }

    /** Asserts that 'r' throws an exception of class 'c' whose message has 'text'. */
    private static void refused(String what, Class<? extends Throwable> c, String text,
            Runnable r) {
        try {
            r.run();
        } catch (Throwable e) {
            Assert.assertTrue(what + ": refused with " + e, c.isInstance(e));
            Assert.assertTrue(what + ": " + e.getMessage(), e.getMessage().contains(text));
            return;
        }
        throw new AssertionError(what + ": not refused");
    }

    /** Asserts that the transaction count is 'count' and the database takes a transaction. */
    private static void goesOn(String what, Db db, long count) {
        Assert.assertEquals(what + ": the transactions", count, db.getTransactionCount());
        db.execute(db.trans().put("/after", what).build());
        Assert.assertEquals(what, new String(DbUtil.get(db, "/after")));
    }

    /**
     * L1: 500 operations are taken, 501 refused by execute() with DbException, nothing
     * written. Two calls on one key are one operation (Trans.Builder.build()), so 501 calls of
     * which two share a key are taken; deletes count as puts do.
     */
    @Nano
    public static void testOperations() {
        Db db = Db.builder().testSetup().start();
        try {
            Trans.Builder b = db.trans();
            for (int i = 0; i < Db.MAX_OPERATIONS; i++) {
                b.put("/a/" + i, "v");
            }
            b.put("/a/0", "w");                     // the same key: still 500
            db.execute(b.build());
            Assert.assertEquals("w", new String(DbUtil.get(db, "/a/0")));
            final long count = db.getTransactionCount();

            Trans.Builder over = db.trans();
            for (int i = 0; i < Db.MAX_OPERATIONS; i++) {
                over.delete("/a/" + i);
            }
            over.put("/b", "b");
            refused("501 operations", DbException.class, "501 operations, more than 500 "
                    + "(bergdb 024-17, L1)", () -> db.execute(over.build()));
            Assert.assertNull(DbUtil.get(db, "/b"));
            Assert.assertEquals("v", new String(DbUtil.get(db, "/a/1")));
            goesOn("L1", db, count);
        } finally {
            db.close();
        }
    }

    /**
     * L2: a key of 111 bytes is taken by every call that takes a key, one of 112 refused by
     * the call with IllegalArgumentException; a key transformation that gives a key of 112
     * bytes is refused by execute() with DbException, nothing written (Db.transformKeys).
     */
    @Nano
    public static void testKeyBytes() {
        Db db = Db.builder().testSetup().start();
        try {
            byte[] k111 = new byte[Db.MAX_KEY_BYTES];
            Arrays.fill(k111, (byte) 'k');
            String s111 = new String(k111, java.nio.charset.StandardCharsets.US_ASCII);
            db.execute(db.trans().put(k111, bytes("1")).build());
            db.execute(db.trans().put(Keys.toSegments(s111.substring(1) + "x"), bytes("2"))
                    .build());
            db.execute(db.trans().put(s111.substring(1) + "y", "3").build());
            db.execute(db.trans().delete(k111).build());
            final long count = db.getTransactionCount();
            byte[] k112 = Arrays.copyOf(k111, Db.MAX_KEY_BYTES + 1);
            String s112 = s111 + "k";
            String text = "112 bytes, more than 111 (bergdb 024-17, L2)";
            refused("put(byte[])", IllegalArgumentException.class, text,
                    () -> db.trans().put(k112, new byte[0]));
            refused("put(String)", IllegalArgumentException.class, text,
                    () -> db.trans().put(s112, "v"));
            refused("put(String, byte[])", IllegalArgumentException.class, text,
                    () -> db.trans().put(s112, new byte[0]));
            refused("delete(String)", IllegalArgumentException.class, text,
                    () -> db.trans().delete(s112));
            // A two-byte char: 56 of them are 112 bytes.
            refused("put(String) of 56 letters å", IllegalArgumentException.class, text,
                    () -> db.trans().put("å".repeat(56), "v"));
            db.execute(db.trans().put("å".repeat(55), "v").build());

            final KeyTransformation longer = new KeyTransformation() {
                public void transform(Trans trans, int index) {
                    long[] key = Keys.toSegments(k112);
                    trans.kvs[index].setKey(key);
                    trans.writeKeyHashes[index] = Keys.hash(key);
                }
            };
            final long count2 = db.getTransactionCount();
            Trans t = db.trans().put(Keys.toSegments("/t"), longer, bytes("t"), null)
                    .put("/u", "u").build();
            refused("a key transformation to 112 bytes", DbException.class, text,
                    () -> db.execute(t));
            Assert.assertNull(DbUtil.get(db, "/u"));
            Assert.assertNull(DbUtil.get(db, k112));
            Assert.assertTrue("the key as written, given back",
                    Arrays.equals(Keys.toSegments("/t"), t.kvs[0].getKey()));
            Assert.assertTrue(count2 == count + 1);
            goesOn("L2", db, count2);
        } finally {
            db.close();
        }
    }

    /**
     * L3: keys of 57,344 bytes in all, BergDB's own longer keys through the internal call
     * Trans.Builder.putLongKey(), which does not check L2, are taken; 57,345 refused by
     * execute() with DbException, nothing written. User keys of 111 bytes never meet it: 500
     * of them, 55,500 bytes, are taken.
     */
    @Nano
    public static void testTransKeyBytes() {
        Db db = Db.builder().testSetup().start();
        try {
            Trans.Builder b = db.trans();
            for (int i = 0; i < Db.MAX_OPERATIONS; i++) {
                byte[] k = new byte[Db.MAX_KEY_BYTES];
                Arrays.fill(k, (byte) 'u');
                byte[] n = bytes(String.format("%05d", i));
                System.arraycopy(n, 0, k, 0, n.length);
                b.put(k, new byte[0]);
            }
            db.execute(b.build());

            Trans.Builder at = db.trans();
            int left = Db.MAX_TRANS_KEY_BYTES;
            for (int i = 0; left > 0; i++) {
                byte[] k = new byte[Math.min(left, 497)];   // the largest index entry
                Arrays.fill(k, (byte) 'e');
                byte[] n = bytes(String.format("/#i/%05d", i));
                System.arraycopy(n, 0, k, 0, Math.min(n.length, k.length));
                at.putLongKey(Keys.toSegments(k), null, new byte[0], null);
                left -= k.length;
            }
            db.execute(at.build());
            final long count = db.getTransactionCount();

            Trans.Builder over = db.trans();
            byte[] k = new byte[Db.MAX_TRANS_KEY_BYTES - 1];
            Arrays.fill(k, (byte) 'o');
            over.putLongKey(Keys.toSegments(k), null, new byte[0], null);
            over.deleteLongKey(Keys.toSegments(new byte[] {'o', 'o'}));
            refused("57,345 bytes of keys", DbException.class, "57345 bytes, more than 57344 "
                    + "(bergdb 024-17, L3)", () -> db.execute(over.build()));
            Assert.assertNull(DbUtil.get(db, k));
            goesOn("L3", db, count);
        } finally {
            db.close();
        }
    }

    /**
     * L4: a value of 8 MiB is taken, one of 8 MiB and a byte refused by the call that takes
     * it with IllegalArgumentException, nothing added to the builder.
     */
    @Nano
    public static void testValueBytes() {
        Db db = Db.builder().testSetup().start();
        try {
            byte[] v = new byte[Db.MAX_VALUE_BYTES];
            v[v.length - 1] = 7;
            db.execute(db.trans().put("/v", new byte[0]).put(bytes("/w"), v).build());
            Assert.assertEquals(Db.MAX_VALUE_BYTES, DbUtil.get(db, bytes("/w")).length);
            final long count = db.getTransactionCount();
            byte[] over = new byte[Db.MAX_VALUE_BYTES + 1];
            String text = "8388609 bytes, more than 8388608 (bergdb 024-17, L4)";
            Trans.Builder b = db.trans().put("/x", "x");
            refused("put(byte[], byte[])", IllegalArgumentException.class, text,
                    () -> b.put(bytes("/y"), over));
            refused("put(String, byte[])", IllegalArgumentException.class, text,
                    () -> b.put("/y", over));
            refused("put(long[], byte[])", IllegalArgumentException.class, text,
                    () -> b.put(Keys.toSegments("/y"), over));
            refused("put(long[], kt, byte[], vt)", IllegalArgumentException.class, text,
                    () -> b.put(Keys.toSegments("/y"), null, over, null));
            db.execute(b.build());              // the builder holds /x alone
            Assert.assertNull(DbUtil.get(db, "/y"));
            Assert.assertEquals("x", new String(DbUtil.get(db, "/x")));
            goesOn("L4", db, count + 1);
        } finally {
            db.close();
        }
    }

    /**
     * L5: keys and values of 32 MiB in all are taken, a byte more refused by execute() with
     * DbException, nothing written.
     */
    @Nano
    public static void testTransBytes() {
        Db db = Db.builder().testSetup().start();
        try {
            final int big = Db.MAX_VALUE_BYTES;
            String[] keys = {"/a", "/b", "/c", "/d"};
            // The last value takes what is left: 32 MiB less the keys' 8 bytes and three values.
            int last = (int) (Db.MAX_TRANS_BYTES - 8 - 3L * big);
            Trans.Builder at = db.trans();
            for (int i = 0; i < 3; i++) {
                at.put(bytes(keys[i]), new byte[big]);
            }
            at.put(bytes(keys[3]), new byte[last]);
            db.execute(at.build());
            Assert.assertEquals(last, DbUtil.get(db, bytes("/d")).length);
            final long count = db.getTransactionCount();

            Trans.Builder over = db.trans();
            for (int i = 0; i < 3; i++) {
                over.put(bytes(keys[i]), new byte[] {1});
                over.put(bytes(keys[i] + "x"), new byte[big]);
            }
            // Keys 4 x 2 + 3 x 3 = 17 bytes, values 3 x 8 MiB + 3, the last value the rest + 1.
            over.put(bytes("/e"), new byte[(int) (Db.MAX_TRANS_BYTES - 17 - 3L * big - 3 + 1)]);
            refused("32 MiB and a byte", DbException.class, "33554433 bytes, more than "
                    + "33554432 (bergdb 024-17, L5)", () -> db.execute(over.build()));
            Assert.assertNull(DbUtil.get(db, bytes("/e")));
            Assert.assertEquals(big, DbUtil.get(db, bytes("/a")).length);
            goesOn("L5", db, count);
        } finally {
            db.close();
        }
    }

    /**
     * QL6 (bergdb 024-17): a value transformation whose result passes L4 fails the database,
     * as an exception of the transformation does (ValueTransformation; 015-51); the restart
     * has the state before the transaction. A result at L4 is taken.
     */
    @Nano
    public static void testTransformedValueOverL4() {
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).start();
        try {
            db.execute(db.trans().put("/a", "a").build());
            db.execute(db.trans().put(Keys.toSegments("/t"), null, new byte[0],
                    (time, in, previous) -> new byte[Db.MAX_VALUE_BYTES]).build());
            Assert.assertEquals(Db.MAX_VALUE_BYTES, DbUtil.get(db, "/t").length);
            db.sync(SyncLevel.ORDINARY);
            Trans t = db.trans().put(Keys.toSegments("/u"), null, new byte[0],
                    (time, in, previous) -> new byte[Db.MAX_VALUE_BYTES + 1]).build();
            try {
                db.execute(t);
                throw new AssertionError("a transformed value over L4 was taken");
            } catch (DbFailedException e) {
                Assert.assertTrue(String.valueOf(e.getCause()), String.valueOf(
                        e.getCause().getMessage()).contains("(bergdb 024-17, L4)"));
            }
        } finally {
            db.close();
        }
        Db db2 = Db.builder().testSetup(stream.copy()).start();
        try {
            Assert.assertNull(DbUtil.get(db2, "/u"));
            Assert.assertEquals("a", new String(DbUtil.get(db2, "/a")));
            Assert.assertEquals(Db.MAX_VALUE_BYTES, DbUtil.get(db2, "/t").length);
            db2.execute(db2.trans().put("/after", "x").build());
        } finally {
            db2.close();
        }
    }
}
