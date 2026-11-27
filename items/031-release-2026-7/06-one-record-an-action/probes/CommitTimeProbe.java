package bergdb.core;

import java.util.*;

import bergdb.pub.util.Clock;

/**
 * bergdb 031-06: an indicative figure, not a gate: the time of a commit whose call makes a
 * reclaim step, on this prototype (the step in the commit's own record) and on 031-05's
 * (c315, run with -Dproto315.eager=true: the step a record of its own after the commit's, in
 * its call, as on main). The same workload on both, with a test clock: K keys of V bytes,
 * then N commits of one overwrite each, 1 ms of database time apart (R = 1 s), after W
 * commits of warm-up. A commit makes a step if the running iteration's row moved (kvCount,
 * lastKey or done) in its call. Only API that both prototypes have.
 *
 * Usage: java -cp OUT:JAR [-Dproto315.eager=true] bergdb.core.CommitTimeProbe K V N W
 */
public class CommitTimeProbe {
    public static void main(String[] args) {
        int k = Integer.parseInt(args[0]), v = Integer.parseInt(args[1]);
        int n = Integer.parseInt(args[2]), w = Integer.parseInt(args[3]);
        CoreTestClock clock = new CoreTestClock();
        long time = Clock.UNITS_PER_SEC;
        clock.setTime(time);
        Db db = Db.builder().testSetup().clock(clock).start();
        try {
            db.setStartupDistance(100000);
            Random r = new Random(1);
            for (int i = 0; i < k; i += 100) {
                time += Clock.UNITS_PER_SEC / 1000; clock.setTime(time);
                Trans.Builder b = db.trans();
                for (int j = i; j < i + 100 && j < k; j++) b.put("/k/" + j, new byte[v]);
                db.execute(b.build());
            }
            db.setRetainDuration(Clock.UNITS_PER_SEC);
            Reclaim rc = db.internal().reclaim();
            long[] withStep = new long[n], without = new long[n];
            int ws = 0, wo = 0;
            for (int i = 0; i < w + n; i++) {
                time += Clock.UNITS_PER_SEC / 1000; clock.setTime(time);
                byte[] val = new byte[v];
                r.nextBytes(val);
                Trans t = db.trans().put("/k/" + r.nextInt(k), val).build();
                Reclaim.IterationInfo cur = rc.currentIteration();
                long kv = cur == null ? -1 : cur.kvCount, ps = cur == null ? -1 : cur.pStart;
                long[] lk = cur == null ? null : cur.lastKey;
                long t0 = System.nanoTime();
                db.execute(t);
                long dt = System.nanoTime() - t0;
                Reclaim.IterationInfo after = rc.currentIteration();
                boolean step = cur != null && (after == null || after.pStart != ps
                        || after.kvCount != kv || !Arrays.equals(after.lastKey, lk));
                if (i < w) continue;
                if (step) withStep[ws++] = dt; else without[wo++] = dt;
            }
            System.out.println("K " + k + ", V " + v + ", " + n + " commits: " + ws
                    + " made a step (" + String.format("%.1f", 100.0 * ws / n) + " %)");
            System.out.println("  with a step:    " + stats(withStep, ws));
            System.out.println("  without a step: " + stats(without, wo));
        } finally {
            db.close();
        }
    }

    static String stats(long[] a, int n) {
        if (n == 0) return "none";
        long[] s = Arrays.copyOf(a, n);
        Arrays.sort(s);
        return String.format("median %.1f us, p90 %.1f us, p99 %.1f us, max %.1f us",
                s[n / 2] / 1000.0, s[n * 9 / 10] / 1000.0, s[Math.min(n - 1, n * 99 / 100)] / 1000.0,
                s[n - 1] / 1000.0);
    }
}
