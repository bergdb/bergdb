package bergdb.core;

import java.util.Random;

/**
 * bergdb 007-07, a probe: how often the deadline takes a transaction that the share would not,
 * in the second half before a decrease of the startup distance, while the span comes down
 * after it, and after. Needs a build with dlprobe.diff (TransSeq.PROBE_*), the class first on
 * the class path. -Dsd0 -Dsd -Dkeys -Dvsize -Dper -Dn (transactions before) -Dn2 (after).
 */
public class DlProbe {
    public static void main(String[] a) {
        int sd0 = Integer.getInteger("sd0", 8000000), sd = Integer.getInteger("sd", 1000000);
        int keys = Integer.getInteger("keys", 2000), vsize = Integer.getInteger("vsize", 1000);
        int per = Integer.getInteger("per", 1), n = Integer.getInteger("n", 20000), n2 = Integer.getInteger("n2", 20000);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).startupDistance(sd0).start();
        Random r = new Random(1);
        long time = 10;
        int forcedBefore = 0;
        for (int i = 0; i < n + n2 + 1; i++) {
            if (i == n) {
                TransSeq.PROBE_FORCED_NOW = false;
                db.setStartupDistance(sd);
                System.out.println("dummy: deadline forced a take: " + TransSeq.PROBE_FORCED_NOW);
                continue;
            }
            clock.setTime(time++);
            Trans.Builder tb = db.trans();
            for (int k = 0; k < per; k++) { byte[] v = new byte[vsize]; r.nextBytes(v); tb.put("/k/" + r.nextInt(keys), v); }
            TransSeq.PROBE_FORCED_NOW = false;
            db.execute(tb.build());
            if (i < n) { if (i >= n / 2 && TransSeq.PROBE_FORCED_NOW) forcedBefore++; continue; }
            if (TransSeq.PROBE_FORCED_NOW) forced[db.internal().transSeq().span() >= 2L * sd && !below ? 0 : 1]++;
            commits[below ? 1 : 0]++;
            if (!below && db.internal().transSeq().span() < 2L * sd) below = true;
        }
        System.out.printf("second half before: %d of %d commits forced; catch-up: %d of %d commits forced; after: %d of %d%n",
                forcedBefore, n / 2, forced[0], commits[0], forced[1], commits[1]);
        db.close();
    }
    static int[] forced = new int[2], commits = new int[2];
    static boolean below;
}
