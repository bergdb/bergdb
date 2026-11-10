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
        return Db.builder().testSetup(stream).maxNodeSize8().startupDistance(10).start();
    }

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
}
