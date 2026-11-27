package bergdb.core;

import java.util.Random;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * Review probe (031-06, review-main): at a lowered record limit (StoredTrans.recordLimit, the
 * tests' hook), an ordinary workload of single small puts, with a startup distance larger
 * than the record limit, and optionally a large value now and then and maintain() calls.
 * Does a record's got-dirty set, its own nodes and those that its take keeps dirty, pass
 * StoredTrans.takeRoom(), so that Db.checkTakeable fails the database?
 *
 * args: limit sd keys actions maintainEvery seed node8(0|1) valueBytes [bigEvery bigBytes]
 * (maintainEvery 0: no maintain() call; = actions: one call, after the last commit)
 */
public class RmRoomProbe {
    static Trans last;
    static long records, maxSetNodes, maxSetBytes, maxRecord, maxIndexWritten;

    public static void main(String[] a) {
        final long limit = Long.parseLong(a[0]);
        final int sd = Integer.parseInt(a[1]);
        final int keys = Integer.parseInt(a[2]);
        final int actions = Integer.parseInt(a[3]);
        final int maintainEvery = Integer.parseInt(a[4]);
        final long seed = Long.parseLong(a[5]);
        final boolean node8 = a[6].equals("1");
        final int valueBytes = Integer.parseInt(a[7]);
        final int bigEvery = a.length > 8 ? Integer.parseInt(a[8]) : 0;
        final int bigBytes = a.length > 9 ? Integer.parseInt(a[9]) : 0;
        final long SEC = Clock.UNITS_PER_SEC;
        StoredTrans.recordLimit = limit;
        final long nodeBytes = 32 + 16L * ((node8 ? 8 : 30) + 1) + 16;
        Db.testHooks = new Db.TestHooks() {
            public void beforePlan(Db.ExecuteData x) { last = x.trans; }
            public void beforeApply(Db.ExecuteData x) {
                long bytes = 0;
                for (Node n : x.transInfo.gotDirtyNodes) {
                    bytes += n.getType() == Node.TYPE_TOP_NODE ? StoredTrans.TOP_BYTES / 2 : nodeBytes;
                }
                records++;
                maxSetBytes = Math.max(maxSetBytes, bytes);
                maxSetNodes = Math.max(maxSetNodes, x.transInfo.gotDirtyNodes.size());
                maxRecord = Math.max(maxRecord, x.trans.nextPos - x.trans.tpos);
                maxIndexWritten = Math.max(maxIndexWritten, x.transNodes.keyCount);
            }
            public void transExecuted(Db.ExecuteData x) {}
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) {}
        };
        final CutStream stream = new CutStream();
        final CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        DbBuilder b = Db.builder().testSetup(stream).clock(clock);
        if (node8) b.maxNodeSize8();
        final Db db = b.start();
        db.setStartupDistance(sd);
        db.setRetainDuration(SEC);
        final Random r = new Random(seed);
        System.out.println("record limit " + limit + " (dirtyLimit " + StoredTrans.dirtyLimit()
                + ", takeRoom " + StoredTrans.takeRoom() + ", recordCap " + StoredTrans.recordCap()
                + "), node size " + (node8 ? 8 : 30) + ", startup distance " + sd + ", " + keys
                + " keys, values of " + valueBytes + " bytes" + (bigEvery > 0 ? ", every " + bigEvery
                + "th of " + bigBytes : "") + (maintainEvery > 0 ? ", maintain(100000) every "
                + maintainEvery + " actions" : ", no maintain() call"));
        int i = 0;
        String what = "a commit";
        byte[] v = null;
        try {
            for (i = 0; i < actions; i++) {
                time += SEC / 50;
                clock.setTime(time);
                final int k = r.nextInt(keys);
                v = new byte[bigEvery > 0 && i % bigEvery == bigEvery - 1 ? bigBytes : valueBytes];
                r.nextBytes(v);
                final String key = "/d" + (k % 37) + "/e" + (k % 1009) + "/f" + k;
                what = "a commit (one put of " + v.length + " bytes)";
                db.execute(db.trans().put(key, v).build());
                if (maintainEvery > 0 && i % maintainEvery == maintainEvery - 1) {
                    what = "a part of maintain()";
                    db.maintain(100000);
                }
            }
            System.out.println("  NO FAILURE in " + actions + " actions: " + records + " records, the "
                    + "largest got-dirty set " + maxSetNodes + " nodes, " + maxSetBytes + " bytes "
                    + "at the largest sizes, the largest record " + maxRecord + " bytes, at most "
                    + maxIndexWritten + " key nodes written in a record");
        } catch (Throwable e) {
            System.out.println("  THE DATABASE FAILED at action " + i + ", in " + what + " whose record "
                    + (last.recordCap > 0 ? "carried maintenance (its cap " + last.recordCap + ")"
                    : "carried none (its cap the record limit)") + ": " + e.getClass().getSimpleName()
                    + ": " + e.getMessage());
            System.out.println("  before it: " + records + " records, the largest got-dirty set "
                    + maxSetNodes + " nodes, " + maxSetBytes + " bytes, the largest record "
                    + maxRecord + " bytes, at most " + maxIndexWritten + " key nodes written in a record");
        }
        Db.testHooks = null;
        try { db.close(); } catch (RuntimeException e) { }
    }
}
