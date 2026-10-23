package bergdb.core;

import java.util.Random;

import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.storage.RecoverableStream;
import bergdb.stream.MemoryStream;

/**
 * Probe of bergdb 005-34 (found in 005-30): the transaction position that a get gives
 * (GetData.tpos, from ValueNode.getTpos()) for the values of a record that crosses a meta
 * block, and what Db.getTrans, the Pub API's Connection.transactionInfo(), does with it.
 * Transactions of 20 values of 500 bytes, zeros or random bytes, until three records have
 * crossed a meta block (every 200,000 bytes).
 *
 * Usage: java -cp bergdb.jar:. bergdb.core.TposProbe zeros|SEED
 */
public class TposProbe {
    public static void main(String[] args) throws Exception {
        final boolean zeros = args[0].equals("zeros");
        final Random rnd = new Random(zeros ? 0 : Long.parseLong(args[0]));
        final int d = RecoverableStream.META_BLOCK_DISTANCE;
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).start();
        int found = 0;
        try {
            for (int i = 0; i < 2000 && found < 3; i++) {
                Trans.Builder b = db.trans();
                for (int j = 0; j < 20; j++) {
                    byte[] v = new byte[500];
                    if (!zeros) {
                        rnd.nextBytes(v);
                    }
                    b.put("/k" + i + "/" + j, v);
                }
                Trans t = b.build();
                db.execute(t);
                if (t.tpos / d == t.lastPos / d) {
                    continue;
                }
                found++;
                System.out.println("transaction " + i + " at " + t.tpos + " to " + t.lastPos
                        + ", across the meta block at " + (t.lastPos / d) * d);
                int wrong = 0;
                for (int j = 0; j < 20; j++) {
                    GetData gd = db.newGetData();
                    db.getOne(Long.MAX_VALUE, Keys.toSegments("/k" + i + "/" + j), gd);
                    if (gd.tpos == t.tpos) {
                        continue;
                    }
                    wrong++;
                    String r;
                    try {
                        StoredTrans st = db.getTrans(gd.tpos);
                        r = "gives the transaction at " + st.tpos;
                    } catch (Throwable e) {
                        r = "throws " + e;
                    }
                    System.out.println("  value " + j + ": tpos " + gd.tpos + ", "
                            + (gd.tpos - t.tpos) + " too far; getTrans " + r);
                }
                System.out.println("  " + wrong + " of 20 values with a wrong tpos");
            }
        } catch (Throwable e) {
            System.out.println("the probe stopped: " + e);
        }
        db.stop();
    }
}
