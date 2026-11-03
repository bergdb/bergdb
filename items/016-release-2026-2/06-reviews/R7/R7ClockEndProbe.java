package bergdb.core;

import bergdb.pub.util.Clock;
import bergdb.pub.util.DbFailedException;

/**
 * 016-06/R7: a user transaction at the last database time, Klong.MAX_TIME, is taken; the
 * reclaim step it allows then needs a later time, transactionBegin refuses it ("No database
 * time is left") inside the user transaction's go point, and the database fails. A user
 * transaction there is refused cleanly; the top node ordinals keep a margin for reclaim's
 * internal transactions (Db.TOP_ORDINAL_MARGIN, bergdb 005-02), the times none.
 */
public class R7ClockEndProbe {
    public static void main(String[] args) {
        long time = Clock.UNITS_PER_SEC;
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(time);
        Db db = Db.builder().testSetup().clock(clock).startupDistance(2000).start();
        db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
        Reclaim rc = db.internal().reclaim();
        java.util.Random r = new java.util.Random(1);
        try {
            for (int i = 0; i < 4000; i++) {
                time += Clock.UNITS_PER_SEC / 20; clock.setTime(time);
                Reclaim.IterationInfo cur = rc.currentIteration();
                boolean last = cur != null && Reclaim.fractionOf(db.getStreamLength() + 150
                        - cur.pStart, 16384) - cur.rewritten > 10000;
                if (last) clock.setTime(bergdb.dag.Klong.MAX_TIME);
                try {
                    db.execute(db.trans().put("/k/" + r.nextInt(50),
                            new byte[1 + r.nextInt(60)]).build());
                } catch (DbFailedException e) {
                    System.out.println("put " + i + " (clock at Klong.MAX_TIME: " + last
                            + ") FAILED THE DATABASE: " + e.getCause());
                    return;
                } catch (RuntimeException e) {
                    System.out.println("put " + i + " refused, database goes on: " + e);
                    return;
                }
                if (last) {
                    System.out.println("put " + i + " at Klong.MAX_TIME taken; next one:");
                    try {
                        db.execute(db.trans().put("/x", "1").build());
                    } catch (RuntimeException e) {
                        System.out.println("  " + e.getClass().getSimpleName() + ": "
                                + e.getMessage());
                    }
                    return;
                }
            }
            System.out.println("no step was armed");
        } finally {
            db.close();
        }
    }
}
