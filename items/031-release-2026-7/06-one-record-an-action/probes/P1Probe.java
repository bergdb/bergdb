package bergdb.core;

import java.io.File;
import java.util.*;

import bergdb.pub.util.Clock;
import bergdb.stream.FileStream;

/**
 * bergdb 031-06, landing step 3: P1 (010-01: no stop-the-world, about 20 ms for BergDB's own
 * code) with the pace of step 3 (the after-row charge, a commit's step sized by its
 * allowance, the warm-up of a step's reads before the lock), on a database larger than its
 * cache budget, on disk (FileStream, every append forced as by default). Kind: timing (the
 * times are the result; run on a quiet machine).
 *
 * The load: KEYS keys of VALSIZE bytes, 500 puts a transaction. Then COMMITS commits by one
 * writer, 1 ms of database time apart (a test clock, so that reclaim's pace is the same in
 * every run), retain duration RETAIN seconds of database time: an overwrite of a random key
 * (one put of VALSIZE bytes), and every BIG-th commit one put of BIGSIZE bytes at one of 8
 * keys of their own; READERS threads get random keys at the latest time meanwhile. The
 * commits run in 10 blocks, the warm-up off in the odd ones (Db.TestHooks.stepWarmup) and on
 * in the even ones, so that both meet the same database in turn.
 *
 * Printed, for the commits that carry a step and for the others, with the warm-up and
 * without: the time of execute(), the time under the write lock from the plan to the end of
 * the record (Db.TestHooks.beforePlan to transExecuted), the plan's time before the go point
 * (beforePlan to the first kvApplied: a commit is readable only after it), each as the
 * median, the 99th and 99.9th percentiles and the longest; the versions that the plan's
 * scans loaded from the stream (RecordPlan.loads); the gets' times; the five longest commits
 * with their JVM uptimes, so that a GC log (-Xlog:gc*,safepoint) tells the collector's stops
 * from BergDB's. The cache budget is well under the data: the database is larger than the
 * cache budget, and the stream's files may still be in the OS page cache (dropping it,
 * "sudo purge" on macOS, needs root; a database larger than the machine's memory is the
 * other way).
 *
 * Usage: java -Xmx4g [-XX:+UseZGC] -cp OUT:JAR bergdb.core.P1Probe
 * Properties: keys=N (default 2,000,000), valsize=N (200), budget=MB (100), dir=D
 * (build/p1probe, emptied first), commits=N (200,000), big=N (50), bigsize=N (200,000),
 * retain=S (10), sd=N (the startup distance, default 20,000,000), readers=N (2).
 * Prints P1 PROBE DONE.
 */
public class P1Probe {
    static final long SEC = Clock.UNITS_PER_SEC;
    final int keys = Integer.getInteger("keys", 2000 * 1000);
    final int valsize = Integer.getInteger("valsize", 200);
    final long budget = Long.getLong("budget", 100) * 1000 * 1000;
    final File dir = new File(System.getProperty("dir", "build/p1probe"));
    final int commits = Integer.getInteger("commits", 200 * 1000);
    final int big = Integer.getInteger("big", 50);
    final int bigsize = Integer.getInteger("bigsize", 200 * 1000);
    final long retain = Long.getLong("retain", 10);
    final int sd = Integer.getInteger("sd", 20 * 1000 * 1000);
    final int readers = Integer.getInteger("readers", 2);

    static volatile boolean warm = true;
    static long planStart, planNanos, loads0;
    static boolean lastStep;
    static long lastLock, lastPlan, lastLoads;

    /** Times of one kind: [warm][step]. */
    final long[][][] exec = new long[2][2][], lock = new long[2][2][], plan = new long[2][2][];
    final int[][] count = new int[2][2];
    final long[][] scanLoads = new long[2][2];
    final long[] topNs = new long[5], topAt = new long[5];
    volatile boolean stop;
    Db db;

    public static void main(String[] args) throws Exception {
        new P1Probe().run();
    }

    void run() throws Exception {
        for (int w = 0; w < 2; w++) {
            for (int s = 0; s < 2; s++) {
                exec[w][s] = new long[commits];
                lock[w][s] = new long[commits];
                plan[w][s] = new long[commits];
            }
        }
        Db.testHooks = new Db.TestHooks() {
            public boolean stepWarmup() {
                return warm;
            }

            public void beforePlan(Db.ExecuteData x) {
                planStart = System.nanoTime();
                planNanos = -1;
            }

            public void kvApplied(long[] key, byte[] value) {
                if (planNanos == -1) planNanos = System.nanoTime() - planStart;
            }

            public void transExecuted(Db.ExecuteData x) {
                lastStep = x.plan != null && x.plan.touchKeys != null;
                lastLock = System.nanoTime() - planStart;
                lastPlan = planNanos;
                lastLoads = x.plan instanceof Reclaim.RecordPlan
                        ? ((Reclaim.RecordPlan) x.plan).loads : 0;
            }

            public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}
            public void nodeTouched(bergdb.dag.Node node) {}
            public void nodeReplaced(bergdb.dag.Node node) {}
        };
        dir.mkdirs();
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) f.delete();
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        db = Db.builder().stream("main", new FileStream(dir)).testId().clock(clock)
                .cacheSizeIndicator(budget).evictionSchedule(Eviction.Schedule.BUDGET, 1).build();
        db.start();
        try {
            db.setStartupDistance(sd);
            Random r = new Random(1);
            long t0 = System.nanoTime();
            for (int i = 0; i < keys; i += 500) {
                time += SEC / 1000;
                clock.setTime(time);
                Trans.Builder tb = db.trans();
                for (int j = i; j < Math.min(keys, i + 500); j++) {
                    tb.put(key(j), value(r, valsize));
                }
                db.execute(tb.build());
            }
            db.sync(bergdb.pub.util.SyncLevel.ORDINARY);
            System.out.println("P1Probe: " + keys + " keys of " + valsize + " bytes, a stream of "
                    + db.getStreamLength() / 1000000 + " MB, cache budget " + budget / 1000000
                    + " MB, loaded in " + (System.nanoTime() - t0) / 1000000 + " ms; " + commits
                    + " commits, every " + big + "th of " + bigsize + " bytes, retain " + retain
                    + " s, sd " + sd + ", " + readers + " readers");
            db.setRetainDuration(retain * SEC);
            final long[] gets = new long[1 << 22];
            final int[] ng = new int[1];
            final long getMax[] = new long[1];
            Thread[] ts = new Thread[readers];
            for (int k = 0; k < readers; k++) {
                final Random rr = new Random(100 + k);
                ts[k] = new Thread(() -> {
                    GetDataHolder h = new GetDataHolder(db);
                    while (!stop) {
                        long a = System.nanoTime();
                        db.getOne(Long.MAX_VALUE, bergdb.dag.Keys.toSegments(key(rr.nextInt(keys))),
                                h.gd);
                        long d = System.nanoTime() - a;
                        synchronized (gets) {
                            if (ng[0] < gets.length) gets[ng[0]++] = d;
                            if (d > getMax[0]) getMax[0] = d;
                        }
                    }
                });
                ts[k].setDaemon(true);
                ts[k].start();
            }
            final int block = Math.max(1, commits / 10);
            long t1 = System.nanoTime();
            for (int i = 0; i < commits; i++) {
                warm = (i / block) % 2 == 1;
                time += SEC / 1000;
                clock.setTime(time);
                Trans t = i % big == big - 1
                        ? db.trans().put("/b/" + r.nextInt(8), value(r, bigsize)).build()
                        : db.trans().put(key(r.nextInt(keys)), value(r, valsize)).build();
                long a = System.nanoTime();
                db.execute(t);
                long d = System.nanoTime() - a;
                final int w = warm ? 1 : 0, s = lastStep ? 1 : 0;
                final int c = count[w][s]++;
                exec[w][s][c] = d;
                lock[w][s][c] = lastLock;
                plan[w][s][c] = lastPlan;
                scanLoads[w][s] += lastLoads;
                top(d);
            }
            stop = true;
            for (Thread th : ts) th.join();
            System.out.println("  " + commits + " commits in " + (System.nanoTime() - t1) / 1000000
                    + " ms; the stream kept " + (db.getStreamLength() - db.getFirstAvailablePos())
                    / 1000000 + " MB of " + db.getStreamLength() / 1000000 + " MB");
            for (int w = 0; w < 2; w++) {
                for (int s = 1; s >= 0; s--) {
                    final int c = count[w][s];
                    System.out.println("  warm-up " + (w == 1 ? "on " : "off") + ", "
                            + (s == 1 ? "with a step:   " : "without a step:") + " " + c
                            + " commits; execute " + pct(exec[w][s], c) + "; under the lock "
                            + pct(lock[w][s], c) + "; the plan " + pct(plan[w][s], c)
                            + "; loads by the plans' scans " + scanLoads[w][s]);
                }
            }
            System.out.println("  gets: " + pct(gets, ng[0]) + ", longest " + getMax[0] / 1000
                    + " us");
            StringBuilder b = new StringBuilder("  the five longest commits (ms at uptime s):");
            for (int k = 0; k < 5; k++) {
                b.append(String.format(" %.2f at %.1f", topNs[k] / 1e6, topAt[k] / 1000.0));
            }
            System.out.println(b);
            System.out.println("  " + db.internal().cacheStats());
        } finally {
            stop = true;
            db.close();
            Db.testHooks = null;
        }
        System.out.println("P1 PROBE DONE");
    }

    void top(long d) {
        int k = 4;
        if (d <= topNs[k]) return;
        while (k > 0 && d > topNs[k - 1]) {
            topNs[k] = topNs[k - 1];
            topAt[k] = topAt[k - 1];
            k--;
        }
        topNs[k] = d;
        topAt[k] = java.lang.management.ManagementFactory.getRuntimeMXBean().getUptime();
    }

    static String pct(long[] a, int n) {
        if (n == 0) return "-";
        long[] c = Arrays.copyOf(a, n);
        Arrays.sort(c);
        return String.format("median %.3f, p99 %.3f, p99.9 %.3f, max %.3f ms",
                c[n / 2] / 1e6, c[Math.min(n - 1, (int) (n * 0.99))] / 1e6,
                c[Math.min(n - 1, (int) (n * 0.999))] / 1e6, c[n - 1] / 1e6);
    }

    static String key(int j) {
        return String.format("/k/%08d", j);
    }

    static byte[] value(Random r, int n) {
        byte[] v = new byte[n];
        r.nextBytes(v);
        return v;
    }

    /** A reader's GetData (Db.newGetData()), one a thread. */
    static final class GetDataHolder {
        final bergdb.dag.GetData gd;

        GetDataHolder(Db db) {
            gd = db.newGetData();
        }
    }
}
