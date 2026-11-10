package bergdb.core;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
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
        return Db.builder().testSetup(stream).maxNodeSize8().startupDistance(startupDistance)
                .start();
    }
    
    private static void assertValue(String about, String expected, String actual) {
        if (expected == null ? actual != null : !expected.equals(actual)) {
            throw new AssertionError(about + ", expected " + expected + ", got " + actual + ".");
        }
    }
    
    /** Startup distances: 10 bytes, so a start reruns little; 10 MB, so it reruns all. */
    private static final int[] DISTANCES = {10, 10 * 1000 * 1000};

    /**
     * Fault 12 (bergdb 023-08, review C; the check of it, section 3.1, DbShadowProbe): a
     * history of b keys, then one transaction that puts z keys through a KeyTransformation and
     * deletes every b key, then a restart and more transactions, and another restart. The
     * segment root of "/prefix" that the transaction made is split in place under a new root;
     * its segment leaf's klong of tt to it was shadowed by a second klong, and when the
     * transaction emptied and took the root back, the shadowed klong named a node never
     * written: with -ea the store failed (StoredTrans' stream pointer check), without it the
     * next start ("Unexpected stream pointer"). The startup distance of 10 bytes writes the
     * leaf at once. Failed at iterations 7 and 11 without the fix in Dag.spaceSplitInPlace.
     * Since the sort of a transaction's keys after their transformation (Db.putKvs, 023-09),
     * the z keys are put after the deletes, and this test no longer reaches that order through
     * Db; DagTester.testNoKlongNamesATakenBackNode still does, through the Dag.
     */
    @Nano
    public static void testTakeBackAfterSpaceSplitInPlace() {
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
     * after restarts. An inner space root emptied in one delete is replaced by an empty
     * segment leaf: DagTester.testEmptiedSpaceRootReplacedByALeaf.
     */
    @Nano
    public static void testDeleteEveryKey() {
        final long collapses0 = bergdb.dag.Dag.statCollapses;
        for (int sd : DISTANCES) {
            for (int n : new int[] {1, 7, 100, 2000}) {
                for (int per : new int[] {n, 13}) {
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
                    Trans.Builder tb = db.trans();
                    for (int i = 0; i < n; i += 3) tb.put("/k/" + i, "w" + i);
                    db.execute(tb.build());
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
     * KVs that key transformations make one key reach the index as one operation (Db.putKvs,
     * Db.sortByKey; bergdb 023-08, section 7, Frans's decision of 2026-11-10): of them the
     * last put in the order of the keys as written is kept, or a delete if there is no put; a
     * delete never replaces a put, as Trans.Builder.build's rule for the calls on one key
     * (bergdb 015-40). One transaction has, on keys that existed: a transformed put and a
     * plain put (the plain one, later, is kept); a transformed put and a later delete (the
     * put); a delete and a later transformed put (the put); two transformed puts (the later);
     * and a transformed put with a value transformation before a plain put with one (only
     * the kept one's runs). Its database writes the same stream, byte for byte, as one given
     * the kept operations alone, and gives their values at the latest time and after a
     * restart, at startup distances that rerun little and all. Until 2026-11-10 both KVs
     * reached the index, and a put and a delete of one key reached X5 (c).
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
                } else {
                    tb.put("/c/a", "a2").put("/c/b", "b1").put("/c/c", "c1").put("/c/d", "d2");
                    tb.put(Keys.toSegments("/c/e"), null, bytes("e2"), kept);
                }
                db.execute(tb.build());
                String at = "sd " + sd + (d == 0 ? ", transformed: " : ", plain: ");
                Assert.assertEquals(at + "the dropped KV's value transformation", 0, dropped.calls);
                Assert.assertEquals(at + "the kept KV's value transformation", 1, kept.calls);
                for (int round = 0; round < 2; round++) {
                    String[] expected = {"a2", "b1", "c1", "d2", "e2!"};
                    for (int i = 0; i < expected.length; i++) {
                        String k = "/c/" + (char) ('a' + i);
                        Assert.assertEquals(at + "round " + round + ", " + k, expected[i],
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
     * from the Trans, or turned the slots round, and "/later/a" was absent or wrong.
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
            db.execute(t);
            String at = c ? "collision: " : "no collision: ";
            if (c) {
                assertValue(at + "/shared", "2", DbUtil.getString(db, "/shared"));
            } else {
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
    
    private static byte[] bytes(String s) {
        return s.getBytes(java.nio.charset.StandardCharsets.UTF_8);
    }
}
