package bergdb.core;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.DbException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * Deletes through Db: the upward unlink, the take-back and root collapse at the delete
 * (bergdb 023-07, sections 5.1 to 5.3; 023-09), with restarts that rerun the records.
 *
 * @author Frans Lundberg
 */
public class DbTesterDelete {

    /** Turns the key "/prefix/$..." into "/prefix/z...", which sorts after "/prefix/b...". */
    private static final KeyTransformation DOLLAR_TO_Z = new KeyTransformation() {
        public void transform(Trans trans, int index) {
            String s = Keys.toString(trans.kvs[index].getKey()).replace("/prefix/$", "/prefix/z");
            long[] key = Keys.toSegments(s);
            trans.kvs[index].setKey(key);
            trans.writeKeyHashes[index] = Keys.hash(key);
        }
    };

    private static String key(String segment, int i) {
        return "/prefix/" + segment + String.format("%04d", i);
    }

    private static Db start(MemoryStream stream) {
        return start(stream, 10);
    }
    
    private static Db start(MemoryStream stream, int startupDistance) {
        Db db = Db.builder().testSetup(stream).maxNodeSize8().start();
        db.setStartupDistance(startupDistance);      // nothing written if in force (bergdb 028-13)
        return db;
    }
    
    private static void assertValue(String about, String expected, String actual) {
        if (expected == null ? actual != null : !expected.equals(actual)) {
            throw new AssertionError(about + ", expected " + expected + ", got " + actual + ".");
        }
    }
    
    /** Startup distances: 10 bytes, so a start reruns little; 10 MB, so it reruns all. */
    private static final int[] DISTANCES = {10, 10 * 1000 * 1000};

    /**
     * Deletes and puts through a KeyTransformation in one transaction, with restarts (bergdb
     * 023-08, review C; the check of fault 12, section 3.1, DbShadowProbe): a history of b
     * keys, then one transaction that puts z keys through a KeyTransformation and deletes
     * every b key, then a restart and more transactions, and another restart; the values at
     * each step, at a startup distance of 10 bytes, which writes each record at once. Before
     * the sort of a transaction's keys after their transformation (Db.putKvs, 023-09) this was
     * fault 12's case, reached at iterations 7 and 11 without the fix in
     * Dag.spaceSplitInPlace; since then the z keys are put after the deletes, and
     * DagTester.testNoKlongNamesATakenBackNode reaches that order through the Dag (bergdb
     * 023-11, review B, B4: the name was testTakeBackAfterSpaceSplitInPlace).
     */
    @Nano
    public static void testTransformedPutsAndDeletesWithRestarts() {
        Random r = new Random(1);
        for (int iter = 0; iter < 16; iter++) {
            int nb = 1 + r.nextInt(60);
            int hist = 1 + r.nextInt(4);
            List<List<Integer>> hs = new ArrayList<List<Integer>>();
            for (int h = 0; h < hist; h++) {
                List<Integer> s = new ArrayList<Integer>();
                for (int i = 0; i < nb; i++) {
                    if (h == 0 || r.nextInt(3) == 0) s.add(i);
                }
                hs.add(s);
            }
            int nz = 1 + r.nextInt(120);
            String at = "iter " + iter + ", nb " + nb + ", hist " + hist + ", nz " + nz + ": ";

            MemoryStream ms = new MemoryStream();
            Db db = start(ms);
            for (int h = 0; h < hist; h++) {
                Trans.Builder tb = db.trans();
                for (int i : hs.get(h)) tb.put(key("b", i), "v" + h + "-" + i);
                db.execute(tb.build());
            }
            Trans.Builder tb = db.trans();
            for (int i = 0; i < nz; i++) {
                tb.put(Keys.toSegments(key("$", i)), DOLLAR_TO_Z, ("z" + i).getBytes(), null);
            }
            for (int i = 0; i < nb; i++) tb.delete(key("b", i));
            db.execute(tb.build());
            Trans t2 = db.trans().put("/other/key00001", "x").build();
            db.execute(t2);
            db.sync(t2.lastPos, SyncLevel.ORDINARY);
            for (int i = 0; i < nz; i++) {
                Assert.assertEquals(at + "z" + i, "z" + i, DbUtil.getString(db, key("z", i)));
            }
            db.close();

            Db db2 = start(ms.copy());
            for (int i = 0; i < nz; i++) {
                Assert.assertEquals(at + "restart, z" + i, "z" + i, DbUtil.getString(db2, key("z", i)));
            }
            for (int i = 0; i < nb; i++) {
                Assert.assertEquals(at + "restart, b" + i, null, DbUtil.get(db2, key("b", i)));
            }
            db2.execute(db2.trans().put("/other/key00002", "y").build());
            db2.execute(db2.trans().put("/other/key00003", "y").build());
            for (int q = 0; q < 30; q++) {
                db2.execute(db2.trans().put("/other/q" + q, "y").delete(key("z", q % nz)).build());
            }
            db2.close();

            Db db3 = start(ms.copy());
            for (int i = 30; i < nz; i++) {
                Assert.assertEquals(at + "restart 2, z" + i, "z" + i, DbUtil.getString(db3, key("z", i)));
            }
            db3.close();
        }
    }
    
    /**
     * Every key deleted (bergdb 023-08, review C, 5.3, item 3): the climbs reach the space
     * root, which root collapse lowers as it loses its children, down to a segment leaf that
     * stays, empty. In one transaction after the fill, and over several transactions, then
     * puts again, at startup distances that rerun little and all; gets after each step and
     * after restarts. An inner space root is never emptied in one delete: Dag.deleteUpward
     * throws Bug for it (bergdb 023-11, review A, S1). Transactions of at most
     * Db.MAX_OPERATIONS (L1, bergdb 024-24): 2,000 keys are deleted in four of 500, not in one,
     * and put again in batches of 500; 500 keys, a deeper tree than 100, are still deleted in
     * one transaction (review rev24, R12).
     */
    @Nano
    public static void testDeleteEveryKey() {
        final long collapses0 = bergdb.dag.Dag.statCollapses;
        for (int sd : DISTANCES) {
            for (int n : new int[] {1, 7, 100, 500, 2000}) {
                for (int per : new int[] {Math.min(n, Db.MAX_OPERATIONS), 13}) {
                    String at = "sd " + sd + ", n " + n + ", deletes a transaction " + per + ": ";
                    MemoryStream ms = new MemoryStream();
                    Db db = start(ms, sd);
                    for (int i = 0; i < n; i += 50) {
                        Trans.Builder tb = db.trans();
                        for (int j = i; j < Math.min(n, i + 50); j++) tb.put("/k/" + j, "v" + j);
                        db.execute(tb.build());
                    }
                    for (int i = 0; i < n; i += per) {
                        Trans.Builder tb = db.trans();
                        for (int j = i; j < Math.min(n, i + per); j++) tb.delete("/k/" + j);
                        db.execute(tb.build());
                    }
                    for (int i = 0; i < n; i++) {
                        Assert.assertEquals(at + "/k/" + i, null, DbUtil.get(db, "/k/" + i));
                    }
                    db.close();
                    
                    ms = ms.copy();
                    db = start(ms, sd);
                    for (int i = 0; i < n; i++) {
                        Assert.assertEquals(at + "restart, /k/" + i, null, DbUtil.get(db, "/k/" + i));
                    }
                    for (int i0 = 0; i0 < n; i0 += 3 * Db.MAX_OPERATIONS) {
                        Trans.Builder tb = db.trans();
                        for (int i = i0; i < Math.min(n, i0 + 3 * Db.MAX_OPERATIONS); i += 3) {
                            tb.put("/k/" + i, "w" + i);
                        }
                        db.execute(tb.build());
                    }
                    db.close();
                    
                    db = start(ms.copy(), sd);
                    for (int i = 0; i < n; i++) {
                        assertValue(at + "restart 2, /k/" + i, i % 3 == 0 ? "w" + i : null,
                                DbUtil.getString(db, "/k/" + i));
                    }
                    db.close();
                }
            }
        }
        Assert.assertTrue("root collapses", bergdb.dag.Dag.statCollapses > collapses0);
    }
    
    /** Turns the key "/c/$x" or "/c/~x" into "/c/x": "$" sorts before letters, "~" after. */
    private static final KeyTransformation TO_C = new KeyTransformation() {
        public void transform(Trans trans, int index) {
            String s = Keys.toString(trans.kvs[index].getKey());
            long[] key = Keys.toSegments("/c/" + s.substring("/c/".length() + 1));
            trans.kvs[index].setKey(key);
            trans.writeKeyHashes[index] = Keys.hash(key);
        }
    };
    
    /** Appends "!" to the value it is given, and counts its calls. */
    private static final class Bang implements ValueTransformation {
        int calls = 0;
        public byte[] transform(long transTime, byte[] inputValue, byte[] previous) {
            calls++;
            return (new String(inputValue, java.nio.charset.StandardCharsets.UTF_8) + "!")
                    .getBytes(java.nio.charset.StandardCharsets.UTF_8);
        }
    }
    
    /**
     * KVs that key transformations make one key: the transaction is refused (bergdb 024-16,
     * Db.transformKeys), and nothing of it is written. One transaction has, on keys that
     * existed: a transformed put and a plain put; a transformed put and a later delete; a
     * delete and a later transformed put; two transformed puts; and a transformed put with a
     * value transformation before a plain put with one (neither runs). Its database writes
     * the same stream, byte for byte, as one not given the transaction, and every key keeps
     * its value, at the latest time and after a restart, at startup distances that rerun
     * little and all. From 2026-11-10 one KV of each key was kept (023-08, section 7): until
     * 024-16 the one called last (024-10), so that the keys held "a2", nothing, "c1", "d2" and
     * "e2!"; until release 2026.4 the last put in the order of the keys as written, or a
     * delete if there was no put, so that "/c/b" held "b1". Until 2026-11-10 both KVs reached
     * the index, and a put and a delete of one key reached X5 (c).
     */
    @Nano
    public static void testOneOperationAKeyAfterTransformations() {
        for (int sd : DISTANCES) {
            byte[][] streams = new byte[2][];
            for (int d = 0; d < 2; d++) {
                MemoryStream ms = new MemoryStream();
                Db db = start(ms, sd);
                Trans.Builder tb = db.trans();
                for (String k : new String[] {"a", "b", "c", "d", "e"}) tb.put("/c/" + k, "old");
                db.execute(tb.build());
                Bang dropped = new Bang(), kept = new Bang();
                tb = db.trans();
                if (d == 0) {
                    tb.put(Keys.toSegments("/c/$a"), TO_C, bytes("a1"), null);
                    tb.put("/c/a", "a2");
                    tb.put(Keys.toSegments("/c/$b"), TO_C, bytes("b1"), null);
                    tb.delete("/c/b");
                    tb.delete("/c/c");
                    tb.put(Keys.toSegments("/c/~c"), TO_C, bytes("c1"), null);
                    tb.put(Keys.toSegments("/c/$d"), TO_C, bytes("d1"), null);
                    tb.put(Keys.toSegments("/c/~d"), TO_C, bytes("d2"), null);
                    tb.put(Keys.toSegments("/c/$e"), TO_C, bytes("e1"), dropped);
                    tb.put(Keys.toSegments("/c/e"), null, bytes("e2"), kept);
                    refused(db, tb.build(), false);
                }
                String at = "sd " + sd + (d == 0 ? ", transformed: " : ", not given: ");
                Assert.assertEquals(at + "a value transformation", 0, dropped.calls);
                Assert.assertEquals(at + "the other value transformation", 0, kept.calls);
                for (int round = 0; round < 2; round++) {
                    String[] expected = {"old", "old", "old", "old", "old"};
                    for (int i = 0; i < expected.length; i++) {
                        String k = "/c/" + (char) ('a' + i);
                        assertValue(at + "round " + round + ", " + k, expected[i],
                                DbUtil.getString(db, k));
                    }
                    db.close();
                    db = start(ms.copy(), sd);
                }
                db.close();
                streams[d] = new byte[(int) ms.getLength()];
                try {
                    ms.read(0, streams[d], 0, streams[d].length);
                } catch (java.io.IOException e) {
                    throw new RuntimeException(e);
                }
            }
            Assert.assertTrue("sd " + sd + ": the same stream, " + streams[0].length + " and "
                    + streams[1].length + " bytes", java.util.Arrays.equals(streams[0], streams[1]));
        }
    }
    
    /**
     * A Trans run twice (its Javadoc allows reuse by one thread) keeps every KV and its slot
     * (bergdb 023-11, review A, F1): Db.putKvs sorts and keeps one operation a key in a copy
     * for each run. Two puts built at "/template/a" and "/template/b", whose transformation
     * gives each slot its key by the slot's index and a switch: in the first run both
     * "/shared" (one put kept, b's), or "/x2" and "/x1" (the sort turns them round); in the
     * second "/later/a" and "/later/b". After the second run, and after a restart, each
     * "/later" key holds its own slot's value. Before the fix the first run dropped a's KV
     * from the Trans, or turned the slots round, and "/later/a" was absent or wrong. Since
     * bergdb 024-16 the first run with "/shared" is refused, and "/shared" has no value; until
     * then it held "2", the KV kept.
     */
    @Nano
    public static void testReusedTransKeepsItsKvs() {
        final boolean[] first = new boolean[1];
        final boolean[] collide = new boolean[1];
        final KeyTransformation bySlot = new KeyTransformation() {
            public void transform(Trans trans, int index) {
                String name = index == 0 ? "a" : "b";
                String k = !first[0] ? "/later/" + name : collide[0] ? "/shared"
                        : index == 0 ? "/x2" : "/x1";
                long[] key = Keys.toSegments(k);
                trans.kvs[index].setKey(key);
                trans.writeKeyHashes[index] = Keys.hash(key);
            }
        };
        for (boolean c : new boolean[] {true, false}) {
            collide[0] = c;
            MemoryStream ms = new MemoryStream();
            Db db = start(ms, DISTANCES[1]);
            Trans t = db.trans()
                    .put(Keys.toSegments("/template/a"), bySlot, bytes("1"), null)
                    .put(Keys.toSegments("/template/b"), bySlot, bytes("2"), null)
                    .build();
            first[0] = true;
            String at = c ? "collision: " : "no collision: ";
            if (c) {
                refused(db, t, false);
                assertValue(at + "/shared", null, DbUtil.getString(db, "/shared"));
            } else {
                db.execute(t);
                assertValue(at + "/x2", "1", DbUtil.getString(db, "/x2"));
                assertValue(at + "/x1", "2", DbUtil.getString(db, "/x1"));
            }
            first[0] = false;
            db.execute(t);
            for (int round = 0; round < 2; round++) {
                assertValue(at + "round " + round + ", /later/a", "1",
                        DbUtil.getString(db, "/later/a"));
                assertValue(at + "round " + round + ", /later/b", "2",
                        DbUtil.getString(db, "/later/b"));
                db.close();
                db = start(ms.copy(), DISTANCES[1]);
            }
            db.close();
        }
    }
    
    /** The calls of a row of bergdb 024-10's table on a builder; x names the row's key. */
    private interface Calls {
        void on(Trans.Builder tb, String x, Bang[] vt);
    }
    
    /** A row of bergdb 024-10, section 4: its calls, and what the rule keeps of them. */
    private static final class Row {
        final String name;
        final String k;             // the value at the row's key "/c/x" after it; null: none
        final String dollar;        // the value at "/c/$x", a key as written
        final Calls calls;          // the row's calls, in order
        final Calls kept;           // the operations kept, alone; null: refused (024-16)
        
        Row(String name, String k, String dollar, Calls calls, Calls kept) {
            this.name = name;
            this.k = k;
            this.dollar = dollar;
            this.calls = calls;
            this.kept = kept;
        }
    }
    
    private static void put(Trans.Builder tb, String x, String value) {
        tb.put("/c/" + x, value);
    }
    
    /** A put at "/c/$x" or "/c/~x" (mark "$" or "~") whose final key is "/c/x". */
    private static void tput(Trans.Builder tb, String mark, String x, String value) {
        tb.put(Keys.toSegments("/c/" + mark + x), TO_C, bytes(value), null);
    }
    
    private static void del(Trans.Builder tb, String x) {
        tb.delete("/c/" + x);
    }
    
    /** Notes a value that is not the expected one, so that a test names every wrong row. */
    private static void check(List<String> wrong, String about, String expected, String got) {
        if (!java.util.Objects.equals(expected, got)) {
            wrong.add(about + " is " + got + ", expected " + expected);
        }
    }
    
    /** The rows B1 to B7 and T1 to T10 of bergdb 024-10, section 4. */
    private static Row[] rows() {
        return new Row[] {
            new Row("B1", "2", "old",
                    (tb, x, vt) -> { put(tb, x, "1"); put(tb, x, "2"); },
                    (tb, x, vt) -> put(tb, x, "2")),
            new Row("B2", "1", "old",
                    (tb, x, vt) -> { del(tb, x); put(tb, x, "1"); },
                    (tb, x, vt) -> put(tb, x, "1")),
            new Row("B3", null, "old",
                    (tb, x, vt) -> { put(tb, x, "1"); del(tb, x); },
                    (tb, x, vt) -> del(tb, x)),
            new Row("B4", "3", "old",
                    (tb, x, vt) -> { put(tb, x, "1"); del(tb, x); put(tb, x, "3"); },
                    (tb, x, vt) -> put(tb, x, "3")),
            new Row("B5", null, "old",
                    (tb, x, vt) -> { del(tb, x); del(tb, x); },
                    (tb, x, vt) -> del(tb, x)),
            new Row("B6", null, "old",
                    (tb, x, vt) -> { put(tb, x, "1"); del(tb, x); put(tb, x, "2"); del(tb, x); },
                    (tb, x, vt) -> del(tb, x)),
            new Row("B7", null, "old",
                    (tb, x, vt) -> { del(tb, x); put(tb, x, "1"); del(tb, x); },
                    (tb, x, vt) -> del(tb, x)),
            new Row("T1", "old", "old",
                    (tb, x, vt) -> { tput(tb, "$", x, "1"); put(tb, x, "2"); }, null),
            new Row("T2", "old", "old",
                    (tb, x, vt) -> { put(tb, x, "2"); tput(tb, "$", x, "1"); }, null),
            new Row("T3", "old", "old",
                    (tb, x, vt) -> { tput(tb, "$", x, "1"); del(tb, x); }, null),
            new Row("T4", "old", "old",
                    (tb, x, vt) -> { del(tb, x); tput(tb, "$", x, "1"); }, null),
            new Row("T5", "old", "old",
                    (tb, x, vt) -> { tput(tb, "$", x, "1"); tput(tb, "~", x, "2"); }, null),
            new Row("T6", "old", "old",
                    (tb, x, vt) -> { tput(tb, "~", x, "2"); tput(tb, "$", x, "1"); }, null),
            new Row("T7", "old", "old",
                    (tb, x, vt) -> { tput(tb, "~", x, "1"); put(tb, x, "2"); }, null),
            new Row("T8", "old", "old",
                    (tb, x, vt) -> { put(tb, x, "2"); tput(tb, "~", x, "1"); }, null),
            new Row("T9", "2", null,
                    (tb, x, vt) -> { put(tb, x, "2"); tput(tb, "$", x, "1"); del(tb, "$" + x); },
                    (tb, x, vt) -> { put(tb, x, "2"); del(tb, "$" + x); }),
            new Row("T10", "old", "old",
                    (tb, x, vt) -> {
                        tb.put(Keys.toSegments("/c/$" + x), TO_C, bytes("1"), vt[0]);
                        tb.put(Keys.toSegments("/c/" + x), null, bytes("2"), vt[1]);
                    }, null),
        };
    }
    
    /**
     * The last operation on a key as written wins, put or delete (bergdb 024-10, section 3,
     * R1), and a transaction whose key transformations make two keys one is refused (bergdb
     * 024-16, section 3, S2): the rows B1 to B7 (calls on one key in Trans.Builder) and T1 to
     * T10 (KVs that key transformations may make one key) of 024-10, section 4, and 024-16,
     * section 6, each a transaction of its own on a key "/c/x" that held "old", as did
     * "/c/$x", a key as written. After a B row the key holds the value of the call made last,
     * or nothing if that was a delete. T1 to T8 and T10 are refused, and both keys hold "old";
     * T9 is not (its put at "/c/$x" is taken away by its own last call, a delete, before the
     * commit): "/c/x" holds 2, "/c/$x" nothing. The database's stream is, byte for byte, that
     * of a database given the kept operations alone, and nothing of a refused row, and the
     * values are the same after a restart, at startup distances that rerun little and all. No
     * value transformation runs (T10). Until 2026-11-11 a delete never replaced a put (B3, B6,
     * B7, T3, T9), and of two puts that transformations made one key, the one whose key as
     * written sorted last was kept; from then until 024-16 the one called last was kept, so
     * that T1 to T8 and T10 gave 2, 1, nothing, 1, 2, 1, 2, 1 and "2!": every wrong row is
     * named in the failure.
     */
    @Nano
    public static void testLastOperationWins() {
        Row[] rows = rows();
        List<String> wrong = new ArrayList<String>();
        for (int sd : DISTANCES) {
            byte[][] streams = new byte[2][];
            for (int d = 0; d < 2; d++) {
                MemoryStream ms = new MemoryStream();
                Db db = start(ms, sd);
                Trans.Builder tb = db.trans();
                for (int i = 0; i < rows.length; i++) {
                    tb.put("/c/r" + i, "old").put("/c/$r" + i, "old");
                }
                db.execute(tb.build());
                Bang[] vt = {new Bang(), new Bang()};
                String at = "sd " + sd + (d == 0 ? ", the calls" : ", the kept alone");
                for (int i = 0; i < rows.length; i++) {
                    Calls calls = d == 0 ? rows[i].calls : rows[i].kept;
                    if (calls == null) {
                        continue;
                    }
                    tb = db.trans();
                    calls.on(tb, "r" + i, vt);
                    try {
                        db.execute(tb.build());
                        if (d == 0 && rows[i].kept == null) {
                            wrong.add(at + ", " + rows[i].name + " is not refused");
                        }
                    } catch (DbException e) {
                        if (rows[i].kept != null) {
                            wrong.add(at + ", " + rows[i].name + " is refused: " + e.getMessage());
                        }
                    }
                }
                if (vt[0].calls != 0 || vt[1].calls != 0) {
                    wrong.add(at + ": the value transformations of T10 ran " + vt[0].calls
                            + " and " + vt[1].calls + " times, expected 0 and 0");
                }
                for (int round = 0; round < 2; round++) {
                    for (int i = 0; i < rows.length; i++) {
                        String row = at + ", round " + round + ", " + rows[i].name;
                        String k = DbUtil.getString(db, "/c/r" + i);
                        String dollar = DbUtil.getString(db, "/c/$r" + i);
                        check(wrong, row + ", k", rows[i].k, k);
                        check(wrong, row + ", $k", rows[i].dollar, dollar);
                    }
                    db.close();
                    db = start(ms.copy(), sd);
                }
                db.close();
                streams[d] = new byte[(int) ms.getLength()];
                try {
                    ms.read(0, streams[d], 0, streams[d].length);
                } catch (java.io.IOException e) {
                    throw new RuntimeException(e);
                }
            }
            if (!java.util.Arrays.equals(streams[0], streams[1])) {
                wrong.add("sd " + sd + ": the stream is not that of the kept operations alone, "
                        + streams[0].length + " and " + streams[1].length + " bytes");
            }
        }
        Assert.assertTrue(wrong.size() + " wrong: " + wrong, wrong.isEmpty());
    }
    
    /**
     * A reused Trans whose key transformations make two keys one in some runs (bergdb 024-10,
     * section 3, R5; rows U1 and U2; 024-16, sections 3 and 6): each such run is refused,
     * and the next run gets the keys as written. Two puts, at "/template/a" (value 1) and
     * "/template/b" (value 2), called in either order; the transformation gives both the key
     * "/shared" in the first and the third run, and "/later/a" and "/later/b" in the second.
     * The first and the third run are refused, and "/shared" has no value; the second run puts
     * both KVs. Until 2026-11-11 "/shared" held 2, the value of the key as written that sorts
     * last, also when a's put was called last (U2); from then until 024-16 the value of the
     * put called last.
     */
    @Nano
    public static void testReusedTransLastCallWins() {
        final boolean[] collide = new boolean[1];
        final KeyTransformation byRun = new KeyTransformation() {
            public void transform(Trans trans, int index) {
                // trans.kvs is in the order of the keys as written: 0 is a's, 1 is b's.
                String name = index == 0 ? "a" : "b";
                long[] key = Keys.toSegments(collide[0] ? "/shared" : "/later/" + name);
                trans.kvs[index].setKey(key);
                trans.writeKeyHashes[index] = Keys.hash(key);
            }
        };
        List<String> wrong = new ArrayList<String>();
        for (boolean aLast : new boolean[] {false, true}) {
            String at = aLast ? "U2, a's put called last: " : "U1, b's put called last: ";
            MemoryStream ms = new MemoryStream();
            Db db = start(ms, DISTANCES[1]);
            Trans.Builder tb = db.trans();
            if (aLast) tb.put(Keys.toSegments("/template/b"), byRun, bytes("2"), null);
            tb.put(Keys.toSegments("/template/a"), byRun, bytes("1"), null);
            if (!aLast) tb.put(Keys.toSegments("/template/b"), byRun, bytes("2"), null);
            Trans t = tb.build();
            collide[0] = true;
            refused(db, t, false);
            check(wrong, at + "run 1, /shared", null, DbUtil.getString(db, "/shared"));
            collide[0] = false;
            db.execute(t);
            check(wrong, at + "run 2, /later/a", "1", DbUtil.getString(db, "/later/a"));
            check(wrong, at + "run 2, /later/b", "2", DbUtil.getString(db, "/later/b"));
            db.execute(db.trans().delete("/shared").build());
            collide[0] = true;
            refused(db, t, false);
            for (int round = 0; round < 2; round++) {
                check(wrong, at + "run 3, round " + round + ", /shared", null,
                        DbUtil.getString(db, "/shared"));
                check(wrong, at + "round " + round + ", /later/a", "1",
                        DbUtil.getString(db, "/later/a"));
                db.close();
                db = start(ms.copy(), DISTANCES[1]);
            }
            db.close();
        }
        Assert.assertTrue(wrong.size() + " wrong: " + wrong, wrong.isEmpty());
    }
    
    /**
     * Executes t, which must be refused (bergdb 024-16), and returns the message, from the
     * calling thread or, if inThread, from a thread of its own.
     */
    private static String refused(final Db db, final Trans t, boolean inThread) {
        final DbException[] e = new DbException[1];
        Runnable run = () -> {
            try {
                db.execute(t);
            } catch (DbException x) {
                e[0] = x;
            }
        };
        if (inThread) {
            Thread thread = new Thread(run);
            thread.start();
            try {
                thread.join(60_000);
                Assert.assertFalse("the execute() thread did not end within 60 s",
                        thread.isAlive());
            } catch (InterruptedException x) {
                throw new RuntimeException(x);
            }
        } else {
            run.run();
        }
        Assert.assertTrue("refused", e[0] != null);
        return e[0].getMessage();
    }
    
    /**
     * A transaction whose key transformations make two of its keys one key is refused
     * (bergdb 024-16, section 3, S2, and section 4) and leaves everything as it was. Two
     * databases at startup distances that rerun little and all; in the first, a Trans with a
     * put at "/c/a", a transformed put at "/c/$b" whose final key is "/c/b" (with a value
     * transformation), a plain put at "/c/b" and a delete of "/c/c" is run twice, from this
     * thread and from a thread of its own, and refused each time with a DbException that
     * names both keys as written and the key they became. After each refusal: the Trans holds
     * the same array of the same KVs, each with its key as written, and the same write hashes,
     * each that of its key as written; t.tt as before; the value transformation has not run;
     * the lookup time and every value are as before.
     * Then both databases run the same transaction, which takes the time the refused one
     * would have had, as the clock stands still; their streams are the same, byte for byte,
     * and so are the values after a restart. A key of 108 characters is shown in the message
     * by its first 100 and its length (of 303 until bergdb 024-24, over L2 since).
     */
    @Nano
    public static void testRefusedTransUnchanged() {
        for (int sd : DISTANCES) {
            byte[][] streams = new byte[2][];
            for (int d = 0; d < 2; d++) {
                MemoryStream ms = new MemoryStream();
                Db db = start(ms, sd);
                Trans.Builder tb = db.trans();
                for (String k : new String[] {"a", "b", "$b", "c"}) tb.put("/c/" + k, "old");
                db.execute(tb.build());
                final long time = db.lookupTime(Long.MAX_VALUE);
                String at = "sd " + sd + ": ";
                if (d == 0) {
                    Bang vt = new Bang();
                    Trans t = db.trans().put("/c/a", "a1")
                            .put(Keys.toSegments("/c/$b"), TO_C, bytes("b1"), vt)
                            .put("/c/b", "b2").delete("/c/c").build();
                    final Kv[] kvs = t.kvs;
                    final Kv[] kvs0 = kvs.clone();
                    final long[][] keys = new long[kvs.length][];
                    for (int i = 0; i < kvs.length; i++) keys[i] = kvs[i].getKey().clone();
                    final long[] hashes = t.writeKeyHashes;
                    final long[] hashes0 = hashes.clone();
                    final long tt0 = t.tt;
                    for (int run = 0; run < 2; run++) {
                        String about = at + "run " + run + ", ";
                        String message = refused(db, t, run == 1);
                        Assert.assertTrue(about + message, message.contains("\"/c/$b\" and "
                                + "\"/c/b\" as written are both \"/c/b\"."));
                        Assert.assertTrue(about + "the same KVs", t.kvs == kvs);
                        for (int i = 0; i < kvs.length; i++) {
                            Assert.assertTrue(about + "KV " + i, kvs[i] == kvs0[i]
                                    && java.util.Arrays.equals(kvs[i].getKey(), keys[i]));
                        }
                        Assert.assertTrue(about + "the write hashes", t.writeKeyHashes == hashes
                                && java.util.Arrays.equals(hashes, hashes0));
                        for (int i = 0; i < kvs.length; i++) {
                            // Each the hash of its key as written: a check of its own, so that
                            // a restore of the keys alone fails twice (the review of 024-16).
                            Assert.assertEquals(about + "the write hash of KV " + i,
                                    Keys.hash(kvs[i].getKey()), hashes[i]);
                        }
                        Assert.assertEquals(about + "t.tt, as before the call", tt0, t.tt);
                        Assert.assertEquals(about + "the value transformation", 0, vt.calls);
                        Assert.assertEquals(about + "the lookup time", time,
                                db.lookupTime(Long.MAX_VALUE));
                        for (String k : new String[] {"a", "b", "$b", "c"}) {
                            assertValue(about + k, "old", DbUtil.getString(db, "/c/" + k));
                        }
                    }
                    
                    String x = "/c/" + new String(new char[105]).replace('\0', 'x');
                    String y = "/c/$" + x.substring("/c/".length());
                    String message = refused(db, db.trans().put(x, "1")
                            .put(Keys.toSegments(y), TO_C, bytes("2"), null).build(), false);
                    Assert.assertTrue(at + message, message.contains("...\" (109 characters)")
                            && message.length() < 600);
                }
                Trans t2 = db.trans().put("/c/a", "a2")
                        .put(Keys.toSegments("/c/$b"), TO_C, bytes("b3"), null).build();
                db.execute(t2);
                Assert.assertEquals(at + "the next transaction's time", time + 1, t2.tt);
                for (int round = 0; round < 2; round++) {
                    String[][] expected = {{"a", "a2"}, {"b", "b3"}, {"$b", "old"}, {"c", "old"}};
                    for (String[] kv : expected) {
                        assertValue(at + "round " + round + ", " + kv[0], kv[1],
                                DbUtil.getString(db, "/c/" + kv[0]));
                    }
                    db.close();
                    db = start(ms.copy(), sd);
                }
                db.close();
                streams[d] = new byte[(int) ms.getLength()];
                try {
                    ms.read(0, streams[d], 0, streams[d].length);
                } catch (java.io.IOException e) {
                    throw new RuntimeException(e);
                }
            }
            Assert.assertTrue("sd " + sd + ": the same stream, " + streams[0].length + " and "
                    + streams[1].length + " bytes", java.util.Arrays.equals(streams[0], streams[1]));
        }
    }
    
    private static byte[] bytes(String s) {
        return s.getBytes(java.nio.charset.StandardCharsets.UTF_8);
    }
}
