package bergdb.core;

import bergdb.pub.util.Clock;

/**
 * 016-06/R7, doubt: Reclaim.markSafePositions says pSafe is "the stream length now", but
 * transactionCompleted passes streamSize = t.nextPos, the user record's end, read before the
 * same call's iteration start (storeTable) and step. Counts the markings of pSafe made in a
 * call that appended internal records before the marking, where pSafe is then less than the
 * stream length at the marking; and how far the startup pos was at the marking.
 */
public class R7SafePosProbe {
    @SuppressWarnings("unchecked")
    static java.util.List<Reclaim.IterationInfo> rows(Reclaim rc) {
        try {
            java.lang.reflect.Field f = Reclaim.class.getDeclaredField("table");
            f.setAccessible(true);
            Object table = f.get(rc);
            java.lang.reflect.Field g = table.getClass().getDeclaredField("rows");
            g.setAccessible(true);
            return new java.util.ArrayList<Reclaim.IterationInfo>(
                    (java.util.List<Reclaim.IterationInfo>) g.get(table));
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    public static void main(String[] args) {
        long time = Clock.UNITS_PER_SEC;
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(time);
        Db db = Db.builder().testSetup().clock(clock).startupDistance(Integer.getInteger("sd", 2000))
                .start();
        db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
        Reclaim rc = db.internal().reclaim();
        java.util.Random r = new java.util.Random(1);
        int markings = 0, stale = 0, cutSameCall = 0, cutEarly = 0, staleCut = 0;
        java.util.IdentityHashMap<Reclaim.IterationInfo, Long> trueSafe =
                new java.util.IdentityHashMap<Reclaim.IterationInfo, Long>();
        Reclaim.IterationInfo lastCut = null;
        final int vmax = Integer.getInteger("v", 60);
        java.util.IdentityHashMap<Reclaim.IterationInfo, Boolean> marked =
                new java.util.IdentityHashMap<Reclaim.IterationInfo, Boolean>();
        for (int i = 0; i < 4000; i++) {
            time += Clock.UNITS_PER_SEC / Integer.getInteger("rate", 20); clock.setTime(time);
            Trans t = db.trans().put("/k/" + r.nextInt(50), new byte[1 + r.nextInt(vmax)]).build();
            db.execute(t);
            Reclaim.IterationInfo cutNow = rc.lastCutRow();
            if (cutNow != null && cutNow != lastCut) {
                lastCut = cutNow;
                Long ts = trueSafe.get(cutNow);
                if (ts != null) {
                    staleCut++;
                    long sp = db.internal().getStartupPosForEvict();
                    if (sp < ts) {
                        cutEarly++;
                        System.out.println("put " + i + ": CUT DECIDED at startup pos " + sp
                                + ", before the stream length at its marking, " + ts
                                + " (pSafe " + cutNow.pSafe + ")");
                    }
                }
            }
            for (Reclaim.IterationInfo row : rows(rc)) {
                if (row.pSafe != -1 && !marked.containsKey(row)) {
                    marked.put(row, true);
                    markings++;
                    if (row.pSafe == t.nextPos && db.getStreamLength() > t.nextPos) {
                        // Internal records may come after the marking too (a cut's table); count
                        // only calls whose internal records came before it: a step or a start.
                        Reclaim.IterationInfo cur = rc.currentIteration();
                        if (cur != null && cur.pStart >= t.nextPos) {
                            stale++;
                            trueSafe.put(row, db.getStreamLength());
                            if (rc.lastCutRow() == row) {
                                cutSameCall++;
                                System.out.println("put " + i + ": the row was cut in the same call,"
                                        + " at startup pos " + db.internal().getStartupPosForEvict()
                                        + ", before the call's internal records (to "
                                        + db.getStreamLength() + ") were taken");
                            }
                            if (stale <= 3) {
                                System.out.println("put " + i + ": pSafe " + row.pSafe
                                        + " = the user record's end; the same call then started an "
                                        + "iteration at pStart " + cur.pStart + " (its table and "
                                        + "step before the marking); stream now "
                                        + db.getStreamLength() + "; startup pos "
                                        + db.internal().getStartupPosForEvict());
                            }
                        }
                    }
                }
            }
        }
        System.out.println("pSafe markings " + markings + ", in a call that had appended internal "
                + "records before the marking: " + stale + ", of them cut in the same call: " + cutSameCall
                + "; such rows cut later: " + staleCut + ", of them at a startup pos before the "
                + "length at the marking: " + cutEarly);
        db.close();
    }
}
