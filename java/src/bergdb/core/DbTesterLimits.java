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
 * value's bytes, and a value transformation's result over it, refused since bergdb 026-06
 * (QL6), as one that throws; L5, the keys and values of a transaction, with the results of
 * value transformations since 026-06; L9, one of BergDB's own keys (since 2026-11-28; the
 * longer own keys of a stream written before it in DbTesterLongKeys and ReclaimRoomTester).
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
     * execute() with DbException, nothing written: 56 own keys, each within L9 (until
     * 2026-11-28 one own key of 57,343 bytes), and a delete of 2 bytes. User keys of 111
     * bytes never meet it: 500 of them, 55,500 bytes, are taken.
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
                byte[] k = new byte[Math.min(left, 496)];   // the largest index entry
                Arrays.fill(k, (byte) 'e');
                byte[] n = bytes(String.format("..%05d", i));
                System.arraycopy(n, 0, k, 0, Math.min(n.length, k.length));
                k[0] = 1;                   // BergDB's own: the bkey of "/#" (rev24, R2)
                k[1] = 0x25;
                at.putLongKey(Keys.toSegments(k), null, new byte[0], null);
                left -= k.length;
            }
            db.execute(at.build());
            final long count = db.getTransactionCount();

            Trans.Builder over = db.trans();
            byte[] k = null;
            for (int i = 0, overLeft = Db.MAX_TRANS_KEY_BYTES - 1; overLeft > 0; i++) {
                k = own(Math.min(overLeft, Db.MAX_OWN_KEY_BYTES), 'o');
                byte[] n = bytes(String.format("%05d", i));
                System.arraycopy(n, 0, k, 2, n.length);
                over.putLongKey(Keys.toSegments(k), null, new byte[0], null);
                overLeft -= k.length;
            }
            over.deleteLongKey(Keys.toSegments(new byte[] {'o', 'o'}));
            refused("57,345 bytes of keys", DbException.class, "57345 bytes, more than 57344 "
                    + "(bergdb 024-17, L3)", () -> db.execute(over.build()));
            Assert.assertNull(DbUtil.get(db, k));
            goesOn("L3", db, count);
        } finally {
            db.close();
        }
    }

    /** One of BergDB's own keys, under "/#" (01 25), of 'length' bytes of 'fill'. */
    private static byte[] own(int length, char fill) {
        byte[] k = new byte[length];
        Arrays.fill(k, (byte) fill);
        k[0] = 1;
        k[1] = 0x25;
        return k;
    }

    /** A key transformation that gives 'key'. */
    private static KeyTransformation toKey(final byte[] key) {
        return new KeyTransformation() {
            public void transform(Trans trans, int index) {
                long[] k = Keys.toSegments(key);
                trans.kvs[index].setKey(k);
                trans.writeKeyHashes[index] = Keys.hash(k);
            }
        };
    }

    /** A transaction of the one KV 'kv' set in Trans.kvs, which is public. */
    private static Trans throughKvs(Db db, Kv kv) {
        Trans t = db.trans().put("/x", "x").build();
        t.kvs = new Kv[] {kv};
        t.writeKeyHashes = new long[] {Keys.hash(kv.getKey())};
        return t;
    }

    /**
     * L9 (since 2026-11-28; bergdb 031-06, section 8, O1): one of BergDB's own keys, under
     * "/#" (01 25), of 1,023 and 1,024 bytes (147 segments) is taken at each place that
     * checks it, one of 1,025 refused, nothing written: by Trans.Builder.putLongKey() and
     * deleteLongKey() with IllegalArgumentException, which spoils the builder; by execute()
     * with DbException for a KV set in Trans.kvs (Db.checkLimits), a put or a delete, and
     * for a key transformation that gives one (Db.transformKeys), its key as written given
     * back.
     */
    @Nano
    public static void testOwnKeyBytes() {
        Db db = Db.builder().testSetup().start();
        try {
            final int cap = Db.MAX_OWN_KEY_BYTES;
            Assert.assertEquals(1024, cap);
            Assert.assertEquals(147, Keys.toSegments(own(cap, 'a')).length);
            for (int n : new int[] {cap - 1, cap}) {
                final String at = n + " bytes";
                byte[] k = own(n, 'a');
                db.execute(db.trans().putLongKey(Keys.toSegments(k), null, bytes("p"), null)
                        .build());
                Assert.assertEquals(at + ", putLongKey", "p", new String(DbUtil.get(db, k)));
                db.execute(db.trans().deleteLongKey(Keys.toSegments(k)).build());
                Assert.assertTrue(at + ", deleteLongKey", DbUtil.get(db, k) == null);
                Kv kv = new Kv(Keys.toSegments(k), bytes("t"));
                kv.longKey = true;
                db.execute(throughKvs(db, kv));
                Assert.assertEquals(at + ", Trans.kvs", "t", new String(DbUtil.get(db, k)));
                byte[] q = own(n, 'q');
                db.execute(db.trans().putLongKey(Keys.toSegments(own(10, 's')), toKey(q),
                        bytes("q"), null).build());
                Assert.assertEquals(at + ", a key transformation", "q",
                        new String(DbUtil.get(db, q)));
            }
            final long count = db.getTransactionCount();
            final byte[] over = own(cap + 1, 'o');
            final String text = "1025 bytes, more than 1024 (bergdb 024-17, L9)";
            final Trans.Builder b = db.trans().put("/b", "b");
            refused("putLongKey", IllegalArgumentException.class, text,
                    () -> b.putLongKey(Keys.toSegments(over), null, new byte[0], null));
            refused("the spoiled builder", IllegalStateException.class, "putLongKey() was "
                    + "refused", () -> b.build());
            refused("deleteLongKey", IllegalArgumentException.class, text,
                    () -> db.trans().deleteLongKey(Keys.toSegments(over)));
            for (byte[] v : new byte[][] {bytes("o"), null}) {
                Kv kv = new Kv(Keys.toSegments(over), v);
                kv.longKey = true;
                refused("Trans.kvs, " + (v == null ? "a delete" : "a put"), DbException.class,
                        text, () -> db.execute(throughKvs(db, kv)));
            }
            final long[] written = Keys.toSegments(own(10, 's'));
            final Trans t = db.trans().putLongKey(written, toKey(over), bytes("o"), null)
                    .put("/u", "u").build();
            refused("a key transformation to 1,025 bytes", DbException.class, text,
                    () -> db.execute(t));
            boolean givenBack = false;
            for (Kv kv : t.kvs) {
                givenBack |= kv.keyTransformation != null && Arrays.equals(written, kv.getKey());
            }
            Assert.assertTrue("the key as written, given back", givenBack);
            Assert.assertNull(DbUtil.get(db, over));
            Assert.assertNull(DbUtil.get(db, "/b"));
            Assert.assertNull(DbUtil.get(db, "/u"));
            goesOn("L9", db, count);
        } finally {
            db.close();
        }
    }

    /**
     * Review rev24, R1 and R2: Db.execute() checks each KV of a user transaction, whatever
     * built it (Trans.kvs is public): a value over L4 and a key over L2 put through t.kvs
     * are refused with DbException, nothing written (a value of 9 MiB put so failed the
     * database when reclaim copied it, the review's probe Rev24Reclaim); then reclaim runs
     * many iterations with no failure. The internal calls take a key over L2 only under
     * "/#" (01 25), and do not check a value's length: Db.execute() refuses it.
     */
    @Nano
    public static void testEachKvChecked() {
        final long sec = bergdb.pub.util.Clock.UNITS_PER_SEC;
        CoreTestClock clock = new CoreTestClock();
        long time = sec;
        clock.setTime(time);
        Db db = Db.builder().testSetup(new MemoryStream()).clock(clock).maxNodeSize8()
                .start();
        db.setStartupDistance(2000);
        try {
            db.setRetainDuration(sec);
            final long count = db.getTransactionCount();
            Trans t = db.trans().put("/x", "x").build();
            t.kvs = new Kv[] {new Kv(Keys.toSegments("/big"), new byte[9 << 20])};
            t.writeKeyHashes = new long[] {Keys.hash(t.kvs[0].getKey())};
            refused("a value of 9 MiB through t.kvs", DbException.class, "9437184 bytes, more "
                    + "than 8388608 (bergdb 024-17, L4)", () -> db.execute(t));
            Trans t2 = db.trans().put("/x", "x").build();
            t2.kvs = new Kv[] {new Kv(Keys.toSegments(new byte[5000]), new byte[1])};
            t2.writeKeyHashes = new long[] {Keys.hash(t2.kvs[0].getKey())};
            refused("a key of 5,000 bytes through t.kvs", DbException.class, "5000 bytes, "
                    + "more than 111 (bergdb 024-17, L2)", () -> db.execute(t2));
            refused("putLongKey, a user's key of 112 bytes", IllegalArgumentException.class,
                    "(bergdb 024-17, L2)", () -> db.trans().putLongKey(
                    Keys.toSegments(new byte[112]), null, new byte[0], null));
            refused("deleteLongKey, a user's key of 112 bytes", IllegalArgumentException.class,
                    "(bergdb 024-17, L2)", () -> db.trans().deleteLongKey(
                    Keys.toSegments(new byte[112])));
            byte[] own = new byte[112];
            own[0] = 1;
            own[1] = 0x25;
            Trans t3 = db.trans().putLongKey(Keys.toSegments(own), null, new byte[9 << 20],
                    null).build();
            refused("putLongKey, a value of 9 MiB", DbException.class, "(bergdb 024-17, L4)",
                    () -> db.execute(t3));
            Assert.assertEquals(count, db.getTransactionCount());
            Assert.assertNull(DbUtil.get(db, "/big"));
            for (int i = 0; i < 20000; i++) {
                time += sec / 20;
                clock.setTime(time);
                db.execute(db.trans().put("/k/" + (i % 50), new byte[300]).build());
            }
            Assert.assertTrue("reclaim ran", db.getReclaimIterationCount() > 0);
        } finally {
            db.close();
        }
    }

    /**
     * L4: a value of 8 MiB is taken, one of 8 MiB and a byte refused by the call that takes
     * it with IllegalArgumentException, which spoils the builder: its execute() throws
     * IllegalStateException and writes nothing, not even the builder's other put (bergdb
     * 024-26, U26-5; 024-27; until 2026-11-12 it wrote that put).
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
            Trans.Builder[] b = new Trans.Builder[4];
            for (int i = 0; i < b.length; i++) {
                b[i] = db.trans().put("/x", "x");
            }
            refused("put(byte[], byte[])", IllegalArgumentException.class, text,
                    () -> b[0].put(bytes("/y"), over));
            refused("put(String, byte[])", IllegalArgumentException.class, text,
                    () -> b[1].put("/y", over));
            refused("put(long[], byte[])", IllegalArgumentException.class, text,
                    () -> b[2].put(Keys.toSegments("/y"), over));
            refused("put(long[], kt, byte[], vt)", IllegalArgumentException.class, text,
                    () -> b[3].put(Keys.toSegments("/y"), null, over, null));
            for (Trans.Builder x : b) {         // spoiled (024-27): nothing written
                refused("execute()", IllegalStateException.class, "() was refused",
                        () -> db.execute(x));
            }
            Assert.assertNull(DbUtil.get(db, "/y"));
            Assert.assertNull(DbUtil.get(db, "/x"));
            goesOn("L4", db, count);
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
     * QL6 (bergdb 024-17), changed by bergdb 026-06: a value transformation whose result
     * passes L4 refuses the transaction with a DbException before its go point, nothing of it
     * written, and the database goes on; the restart has the state before the transaction
     * and the one after it. A result at L4 is taken. Until 026-06 the result over L4 failed
     * the database, as an exception of the transformation did.
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
            final long length = stream.getLength();
            final long count = db.getTransactionCount();
            final byte[] in = bytes("in");
            Trans t = db.trans().put(Keys.toSegments("/u"), null, in,
                    (time, input, previous) -> new byte[Db.MAX_VALUE_BYTES + 1]).build();
            refused("a result over L4", DbException.class, "gave a value of 8388609 bytes, "
                    + "more than 8388608 (bergdb 024-17, L4)", () -> db.execute(t));
            Assert.assertTrue("the value as given", t.kvs[0].getValue() == in);
            Assert.assertNull(DbUtil.get(db, "/u"));
            db.sync(SyncLevel.ORDINARY);
            Assert.assertEquals("nothing appended", length, stream.getLength());
            goesOn("QL6", db, count);
        } finally {
            db.close();
        }
        Db db2 = Db.builder().testSetup(stream.copy()).start();
        try {
            Assert.assertNull(DbUtil.get(db2, "/u"));
            Assert.assertEquals("a", new String(DbUtil.get(db2, "/a")));
            Assert.assertEquals("QL6", new String(DbUtil.get(db2, "/after")));
            Assert.assertEquals(Db.MAX_VALUE_BYTES, DbUtil.get(db2, "/t").length);
            db2.execute(db2.trans().put("/after2", "x").build());
        } finally {
            db2.close();
        }
    }

    /**
     * L5 counted with the results of value transformations (bergdb 026-06): four results of
     * 8 MiB, with their keys' bytes, pass 32 MiB, and the transaction is refused with a
     * DbException, nothing written, each KV's value as given; with the last result 8 bytes
     * shorter, the transaction takes 32 MiB exactly and is taken. Until 026-06 L5 counted the
     * values as given only, and the results were not counted.
     */
    @Nano
    public static void testTransformedValuesOverL5() {
        Db db = Db.builder().testSetup().start();
        try {
            final int big = Db.MAX_VALUE_BYTES;
            String[] keys = {"/a", "/b", "/c", "/d"};       // two bytes each as stored
            for (int shorter : new int[] {0, 8}) {
                final long count = db.getTransactionCount();
                Trans.Builder b = db.trans();
                for (int i = 0; i < keys.length; i++) {
                    final int length = i == keys.length - 1 ? big - shorter : big;
                    b.put(Keys.toSegments(keys[i]), null, bytes("in"),
                            (time, in, previous) -> new byte[length]);
                }
                Trans t = b.build();
                if (shorter == 0) {
                    refused("results over L5", DbException.class, (Db.MAX_TRANS_BYTES + 8)
                            + " bytes after its value transformations, more than "
                            + Db.MAX_TRANS_BYTES + " (bergdb 024-17, L5)", () -> db.execute(t));
                    for (int i = 0; i < keys.length; i++) {
                        Assert.assertEquals("as given", "in", new String(t.kvs[i].getValue()));
                        Assert.assertNull(DbUtil.get(db, keys[i]));
                    }
                    goesOn("L5 after", db, count);
                } else {
                    db.execute(t);
                    Assert.assertEquals(big - 8, DbUtil.get(db, keys[3]).length);
                    Assert.assertEquals(count + 1, db.getTransactionCount());
                }
            }
        } finally {
            db.close();
        }
    }

    /**
     * A value transformation that throws refuses the transaction with a DbException whose
     * cause is the exception, before the go point, and the database goes on (bergdb 026-06;
     * 010-04, R5): nothing is written; the Trans is left as it was, the same KVs with their
     * keys as written (a key transformation's key given back), their values as given (also
     * that of a transformation that ran before the one that threw) and their write hashes,
     * and t.tt; the time is given back, so the next transaction takes it. The same Trans then
     * runs again and commits, each transformation getting the value as given. Until 026-06
     * the exception failed the database (DbTesterFailure, 003-01's reproduction).
     */
    @Nano
    public static void testValueTransformationThrows() {
        final TestClock clock = new TestClock();
        clock.setTime(1000);
        final MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        try {
            db.execute(db.trans().put("/a", "a0").put("/u", "u0").put("/v", "v0").build());
            db.sync(SyncLevel.ORDINARY);
            final long length = stream.getLength();
            final long count = db.getTransactionCount();
            final long lookup = db.lookupTime(Long.MAX_VALUE);

            final RuntimeException thrown = new IllegalStateException("the transformation fails");
            final boolean[] throwing = {true};
            final long[] times = new long[2];
            final java.util.List<String> inputs = new java.util.ArrayList<String>();
            final KeyTransformation toKt = (trans, index) -> {
                long[] key = Keys.toSegments("/kt");
                trans.kvs[index].setKey(key);
                trans.writeKeyHashes[index] = Keys.hash(key);
            };
            final byte[] uIn = bytes("u1");
            final byte[] vIn = bytes("v1");
            Trans t = db.trans()
                    .put("/a", "a1")
                    .put(Keys.toSegments("/k"), toKt, bytes("k1"), null)
                    .put(Keys.toSegments("/u"), null, uIn, (time, in, previous) -> {
                        inputs.add("u:" + new String(in) + "<-" + new String(previous));
                        return bytes(new String(in) + "+" + new String(previous));
                    })
                    .put(Keys.toSegments("/v"), null, vIn, (time, in, previous) -> {
                        inputs.add("v:" + new String(in) + "<-" + new String(previous));
                        times[0] = time;
                        if (throwing[0]) {
                            throw thrown;
                        }
                        return bytes(new String(in) + "+" + new String(previous));
                    })
                    .build();
            final Kv[] kvs = t.kvs;
            final Kv[] kvsCopy = kvs.clone();
            final long[][] keys = new long[kvs.length][];
            for (int i = 0; i < kvs.length; i++) {
                keys[i] = kvs[i].getKey();
            }
            final long[] hashes = t.writeKeyHashes.clone();
            final long ttBefore = t.tt;

            DbException e = null;
            try {
                db.execute(t);
            } catch (DbException x) {
                e = x;
            }
            Assert.assertTrue("refused", e != null);
            Assert.assertTrue("the cause: " + e.getCause(), e.getCause() == thrown);
            Assert.assertTrue(e.getMessage(), e.getMessage().contains(
                    "The value transformation of \"/v\" threw (the cause)"));
            Assert.assertEquals("both ran, in key order", "[u:u1<-u0, v:v1<-v0]",
                    inputs.toString());

            // The Trans as it was.
            Assert.assertTrue("the same kvs", t.kvs == kvs);
            for (int i = 0; i < kvs.length; i++) {
                Assert.assertTrue("the same Kv " + i, kvs[i] == kvsCopy[i]);
                Assert.assertTrue("the key as written " + i, kvs[i].getKey() == keys[i]);
                Assert.assertEquals("the write hash " + i, hashes[i], t.writeKeyHashes[i]);
                Assert.assertEquals("the hash of the key " + i, Keys.hash(keys[i]),
                        t.writeKeyHashes[i]);
            }
            Assert.assertTrue("/u's value as given", kvs[2].getValue() == uIn);
            Assert.assertTrue("/v's value as given", kvs[3].getValue() == vIn);
            Assert.assertEquals("t.tt", ttBefore, t.tt);

            // The database as it was, and going on.
            Assert.assertTrue("active", db.internal().isActive());
            Assert.assertEquals("the lookup time", lookup, db.lookupTime(Long.MAX_VALUE));
            Assert.assertEquals("a0", new String(DbUtil.get(db, "/a")));
            Assert.assertEquals("u0", new String(DbUtil.get(db, "/u")));
            Assert.assertEquals("v0", new String(DbUtil.get(db, "/v")));
            Assert.assertNull(DbUtil.get(db, "/k"));
            Assert.assertNull(DbUtil.get(db, "/kt"));
            Assert.assertEquals("the transactions", count, db.getTransactionCount());
            db.sync(SyncLevel.ORDINARY);
            Assert.assertEquals("nothing appended", length, stream.getLength());

            // The time given back: the next transaction takes it.
            Trans t2 = db.trans().put("/b", "b2").build();
            db.execute(t2);
            Assert.assertEquals("the refused one's time", times[0], t2.tt);

            // The same Trans again: committed, each transformation given the value as given.
            throwing[0] = false;
            inputs.clear();
            db.execute(t);
            Assert.assertEquals("[u:u1<-u0, v:v1<-v0]", inputs.toString());
            Assert.assertEquals("a1", new String(DbUtil.get(db, "/a")));
            Assert.assertEquals("k1", new String(DbUtil.get(db, "/kt")));
            Assert.assertNull(DbUtil.get(db, "/k"));
            Assert.assertEquals("u1+u0", new String(DbUtil.get(db, "/u")));
            Assert.assertEquals("v1+v0", new String(DbUtil.get(db, "/v")));
            Assert.assertEquals("the time", times[0], t.tt);
            Assert.assertTrue("after t2", t.tt > t2.tt);
        } finally {
            db.close();
        }
        Db db2 = Db.builder().testSetup(stream.copy()).clock(clock).start();
        try {
            Assert.assertEquals("b2", new String(DbUtil.get(db2, "/b")));
            Assert.assertEquals("k1", new String(DbUtil.get(db2, "/kt")));
            Assert.assertEquals("v1+v0", new String(DbUtil.get(db2, "/v")));
        } finally {
            db2.close();
        }
    }

    /**
     * A value transformation that throws an Error: the Error is thrown as it is, and fails
     * the database, as an Error anywhere in a call does (bergdb 019-10; 026-06); a restart
     * has the state before the transaction.
     */
    @Nano
    public static void testValueTransformationError() {
        final MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).start();
        try {
            db.execute(db.trans().put("/a", "a0").build());
            final Error thrown = new Error("an Error in the transformation");
            Trans t = db.trans().put("/a", "a1").put(Keys.toSegments("/b"), null, bytes("b1"),
                    (time, in, previous) -> {
                        throw thrown;
                    }).build();
            Error error = null;
            try {
                db.execute(t);
            } catch (Error e) {
                error = e;
            }
            Assert.assertTrue("the Error itself", error == thrown);
            refused("the next transaction", DbFailedException.class, "",
                    () -> db.execute(db.trans().put("/c", "c").build()));
        } finally {
            db.close();
        }
        Db db2 = Db.builder().testSetup(stream.copy()).start();
        try {
            Assert.assertEquals("a0", new String(DbUtil.get(db2, "/a")));
            Assert.assertNull(DbUtil.get(db2, "/b"));
            db2.execute(db2.trans().put("/after", "x").build());
        } finally {
            db2.close();
        }
    }

    /**
     * A key transformation that throws a RuntimeException refuses the transaction with a
     * DbException whose cause is the exception, and the database goes on (bergdb 026-06;
     * 010-04, R5): the KV it changed before it threw, and one transformed before it, get
     * their keys as written and write hashes back; no value transformation runs; nothing is
     * written, and the next transaction takes the time. Until 026-06 the exception failed the
     * database (KeyTransformation).
     */
    @Nano
    public static void testKeyTransformationThrows() {
        final TestClock clock = new TestClock();
        clock.setTime(1000);
        final MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        try {
            db.execute(db.trans().put("/a", "a0").build());
            db.sync(SyncLevel.ORDINARY);
            final long length = stream.getLength();
            final long count = db.getTransactionCount();
            final RuntimeException thrown = new IllegalStateException("the key fails");
            final long[] times = new long[1];
            final boolean[] vtRan = {false};
            final KeyTransformation toB = (trans, index) -> {
                long[] key = Keys.toSegments("/b");
                trans.kvs[index].setKey(key);
                trans.writeKeyHashes[index] = Keys.hash(key);
            };
            final KeyTransformation half = (trans, index) -> {
                times[0] = trans.tt;
                long[] key = Keys.toSegments("/c");
                trans.kvs[index].setKey(key);
                trans.writeKeyHashes[index] = Keys.hash(key);
                throw thrown;
            };
            Trans t = db.trans()
                    .put("/a", "a1")
                    .put(Keys.toSegments("/k1"), toB, bytes("b1"), null)
                    .put(Keys.toSegments("/k2"), half, bytes("c1"), null)
                    .put(Keys.toSegments("/v"), null, bytes("v1"), (time, in, previous) -> {
                        vtRan[0] = true;
                        return in;
                    })
                    .build();
            final long[][] keys = new long[t.kvs.length][];
            for (int i = 0; i < keys.length; i++) {
                keys[i] = t.kvs[i].getKey();
            }
            final long[] hashes = t.writeKeyHashes.clone();
            DbException e = null;
            try {
                db.execute(t);
            } catch (DbException x) {
                e = x;
            }
            Assert.assertTrue("refused", e != null);
            Assert.assertTrue("the cause: " + e.getCause(), e.getCause() == thrown);
            Assert.assertTrue(e.getMessage(), e.getMessage().contains(
                    "The key transformation of \"/k2\" threw (the cause)"));
            for (int i = 0; i < keys.length; i++) {
                Assert.assertTrue("the key as written " + i, t.kvs[i].getKey() == keys[i]);
                Assert.assertEquals("the write hash " + i, hashes[i], t.writeKeyHashes[i]);
            }
            Assert.assertFalse("no value transformation ran", vtRan[0]);
            Assert.assertTrue("active", db.internal().isActive());
            Assert.assertEquals("a0", new String(DbUtil.get(db, "/a")));
            Assert.assertNull(DbUtil.get(db, "/b"));
            Assert.assertNull(DbUtil.get(db, "/c"));
            Assert.assertNull(DbUtil.get(db, "/v"));
            Assert.assertEquals("the transactions", count, db.getTransactionCount());
            db.sync(SyncLevel.ORDINARY);
            Assert.assertEquals("nothing appended", length, stream.getLength());
            Trans t2 = db.trans().put("/d", "d2").build();
            db.execute(t2);
            Assert.assertEquals("the refused one's time", times[0], t2.tt);
        } finally {
            db.close();
        }
    }
}
