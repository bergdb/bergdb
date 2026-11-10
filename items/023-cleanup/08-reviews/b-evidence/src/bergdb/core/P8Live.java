package bergdb.core;

import java.io.File;
import java.util.ArrayList;
import java.util.Random;
import bergdb.pub.util.Clock;
import bergdb.stream.FileStream;

/**
 * Probe (2026-11-10, review of bergdb 023-07 K5 / P8): does a reclaim iteration end under a
 * growing random-key workload? Each transaction: puts of new hashed keys and deletes of
 * existing ones; prints reclaim's progress every 500 transactions and each iteration's
 * length in transactions when it ends.
 *
 * Args: T opsPerTrans dir [sdBytes] [retainMs] [dtMs] [budgetMb]
 */
public class P8Live {
    public static void main(String[] args) throws Exception {
        final int T = Integer.parseInt(args[0]);
        final int ops = Integer.parseInt(args[1]);
        final File dir = new File(args[2]);
        final int sd = args.length > 3 ? Integer.parseInt(args[3]) : 100 * 1000;
        final long retain = (args.length > 4 ? Long.parseLong(args[4]) : 1000) * (Clock.UNITS_PER_SEC / 1000);
        final long dt = (args.length > 5 ? Long.parseLong(args[5]) : 10) * (Clock.UNITS_PER_SEC / 1000);
        final long budget = (args.length > 6 ? Long.parseLong(args[6]) : 1024) * 1024L * 1024L;
        rm(dir);
        dir.mkdirs();

        CoreTestClock clock = new CoreTestClock();
        long time = 10 * Clock.UNITS_PER_SEC;
        clock.setTime(time);
        DbBuilder b = Db.builder().mainStream(new FileStream(dir)).testId()
                .clock(clock).startupDistance(sd).cacheSizeIndicator(budget);
        Db db = b.start();
        Reclaim reclaim = db.internal().reclaim();
        Reclaim.Stats stats = reclaim.enableStats();
        db.setRetainDuration(retain);

        Random rnd = new Random(1);
        ArrayList<String> live = new ArrayList<String>();
        byte[] value = new byte[100];
        rnd.nextBytes(value);
        final int puts = ops * 9 / 10;
        final int dels = ops - puts;

        // Per iteration: the transaction index at its first step, live keys then.
        ArrayList<long[]> iterStart = new ArrayList<long[]>();   // {transAtFirstStep, liveThen}
        int reportedDone = 0;
        long t0 = System.nanoTime();
        System.out.println("# T=" + T + " ops=" + ops + " sd=" + sd + " retainMs=" + retain / (Clock.UNITS_PER_SEC / 1000)
                + " dtMs=" + dt / (Clock.UNITS_PER_SEC / 1000) + " budgetMB=" + budget / (1024 * 1024));
        final long lo = bergdb.dag.Keys.toSegments("/h/0000000000000000")[0];
        final long hi = bergdb.dag.Keys.toSegments("/h/ffffffffffffffff")[0];
        System.out.println("# trans  live     streamMB  itStarted itDone steps   cuts  lagMs    curSteps curKvs  wallS  curPos%");

        for (int tr = 1; tr <= T; tr++) {
            time += dt;
            clock.setTime(time);
            Trans.Builder tb = db.trans();
            for (int i = 0; i < puts; i++) {
                String k = "/h/" + Long.toHexString(rnd.nextLong());
                tb.put(k, value);
                live.add(k);
            }
            for (int i = 0; i < dels && live.size() > puts; i++) {
                int j = rnd.nextInt(live.size());
                String k = live.get(j);
                live.set(j, live.get(live.size() - 1));
                live.remove(live.size() - 1);
                tb.delete(k);
            }
            db.execute(tb.build());

            // Track iterations: a Stats.Iteration appears at its first step.
            while (iterStart.size() < stats.iterations.size()) {
                iterStart.add(new long[] {tr, live.size()});
            }
            for (int i = reportedDone; i < stats.iterations.size(); i++) {
                Reclaim.Stats.Iteration it = stats.iterations.get(i);
                if (it.pEnd == -1) break;
                long[] s = iterStart.get(i);
                System.out.println("ITER " + i + " done: trans " + s[0] + " to " + tr + " = " + (tr - s[0] + 1)
                        + " trans; steps " + it.steps + " kvs " + it.kvs + " values " + it.values
                        + " liveAtFirstStep " + s[1] + " liveNow " + live.size()
                        + " (main's rule would scan ~liveAtStart KVs)");
                reportedDone = i + 1;
            }

            if (tr % 500 == 0 || tr == T) {
                long steps = 0;
                for (Reclaim.Stats.Iteration it : stats.iterations) steps += it.steps;
                Reclaim.Stats.Iteration cur = stats.iterations.isEmpty() ? null
                        : stats.iterations.get(stats.iterations.size() - 1);
                boolean curOpen = cur != null && cur.pEnd == -1;
                long f = db.getFirstAvailableLookupTime();
                String lag = f == 0 ? "none" : "" + (time - f) / (Clock.UNITS_PER_SEC / 1000);
                Reclaim.IterationInfo ci = reclaim.currentIteration();
                String pos = ci == null || ci.lastKey == null ? "-"
                        : String.format("%.1f", 100.0 * (ci.lastKey[0] - lo) / (double) (hi - lo));
                System.out.printf("%6d %9d %8.1f %8d %6d %7d %5d %8s %8s %7s %6.0f %7s%n",
                        tr, live.size(), db.getStreamLength() / 1e6, stats.iterations.size(),
                        reclaim.getIterationCount(), steps, stats.cuts.size(), lag,
                        curOpen ? "" + cur.steps : "-", curOpen ? "" + cur.kvs : "-",
                        (System.nanoTime() - t0) / 1e9, pos);
            }
        }
        Reclaim.IterationInfo c = reclaim.currentIteration();
        if (c != null) {
            System.out.println("# iteration in progress at the end: pStart " + c.pStart + " lastKey "
                    + (c.lastKey == null ? "null" : java.util.Arrays.toString(c.lastKey))
                    + " endKey " + (c.endKey == null ? "null" : java.util.Arrays.toString(c.endKey))
                    + " kvCount " + c.kvCount + " rewritten " + c.rewritten);
        }
        db.close();
        System.out.println("# wall " + (System.nanoTime() - t0) / 1e9 + " s");
    }

    static void rm(File f) {
        if (f.isDirectory()) for (File c : f.listFiles()) rm(c);
        f.delete();
    }
}
