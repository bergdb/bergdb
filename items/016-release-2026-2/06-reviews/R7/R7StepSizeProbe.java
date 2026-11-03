package bergdb.core;

import bergdb.dag.Keys;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbFailedException;

/**
 * 016-06/R7, F1: a reclaim step rewrites old values in one internal transaction, and
 * checkSize (bergdb 005-17) refuses it with a DbException when its values together pass
 * StoredTrans.valueLimit(), although each was committed by the user within the limit.
 * The DbException comes from inside a user transaction's go point
 * (Reclaim.transactionCompleted), so the database fails.
 *
 * The record limit is lowered to 100 kB, as StoredTrans's own test does, so that the
 * values are small. Run: java -ea -cp probe-classes:build/bergdb.jar bergdb.core.R7StepSizeProbe
 */
public class R7StepSizeProbe {
    public static void main(String[] args) {
        final long saved = StoredTrans.recordLimit;
        StoredTrans.recordLimit = 100 * 1000;
        Db db = null;
        try {
            long time = Clock.UNITS_PER_SEC;
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(time);
            bergdb.stream.MemoryStream stream = new bergdb.stream.MemoryStream();
            db = Db.builder().testSetup(stream).clock(clock).startupDistance(2000).start();
            db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
            
            long limit = StoredTrans.valueLimit();
            final long SLACK = Long.getLong("slack", 60);
            // Ten old values of 4000 bytes, under /a/, committed one by one, never updated.
            for (int i = 0; i < 10; i++) {
                time += Clock.UNITS_PER_SEC / 20; clock.setTime(time);
                db.execute(db.trans().put("/a/" + i, new byte[4000]).build());
            }
            // One value whose node takes limit - 10,000 bytes, alone in its transaction.
            long[] key = Keys.toSegments("/b");
            int n = (int) (limit - SLACK);
            while (StoredValueNode.getByteSizeLong(new byte[n], key) > limit - SLACK) n--;
            time += Clock.UNITS_PER_SEC / 20; clock.setTime(time);
            db.execute(db.trans().put("/b", new byte[n]).build());
            System.out.println("valueLimit " + limit + "; /b's node "
                    + StoredValueNode.getByteSizeLong(new byte[n], key) + " bytes; /a's ten nodes "
                    + 10 * StoredValueNode.getByteSizeLong(new byte[4000], Keys.toSegments("/a/0")));
            
            java.util.Random r = new java.util.Random(1);
            for (int i = 0; i < 4000; i++) {
                time += Clock.UNITS_PER_SEC / 20; clock.setTime(time);
                try {
                    db.execute(db.trans().put("/k/" + r.nextInt(50), new byte[1 + r.nextInt(60)])
                            .build());
                } catch (DbFailedException e) {
                    System.out.println("FAULT at put " + i + ": " + e.getMessage());
                    System.out.println("  cause: " + e.getCause());
                    System.out.println("  iterations completed: " + db.getReclaimIterationCount());
                    db.close();
                    // A restart, with retention forever: the iteration resumes anyway.
                    clock = new CoreTestClock(); clock.setTime(time);
                    db = Db.builder().testSetup(stream.copy()).clock(clock).start();
                    for (int j = 0; j < 50; j++) {
                        time += Clock.UNITS_PER_SEC / 20; clock.setTime(time);
                        try {
                            db.execute(db.trans().put("/k/" + j, new byte[10]).build());
                        } catch (DbFailedException e2) {
                            System.out.println("AFTER RESTART (retain forever), put " + j
                                    + " fails again: " + e2.getCause());
                            return;
                        }
                    }
                    System.out.println("after restart: 50 puts taken");
                    return;
                }
            }
            System.out.println("no failure; iterations " + db.getReclaimIterationCount()
                    + ", first available pos " + db.getFirstAvailablePos());
        } finally {
            StoredTrans.recordLimit = saved;
            if (db != null) db.close();
        }
    }
}
