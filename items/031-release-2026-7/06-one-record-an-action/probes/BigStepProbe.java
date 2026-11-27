package bergdb.core;

import java.io.File;
import java.util.*;

import bergdb.pub.util.Clock;
import bergdb.stream.FileStream;

/**
 * bergdb 031-06, review 3, section 5, point 2: the time under the write lock of a commit
 * whose record carries a step of up to 128 KiB of small values (Reclaim.commitStepSize,
 * since 031-06's landing, step 3; 16 kB before), against P1 (010-01, about 20 ms for
 * BergDB's own code). Kind: timing (the times are the result; run on a quiet machine). It
 * runs on main's jar too (16 kB steps), for the comparison.
 *
 * The load: KEYS cold keys of 20 to 30 bytes, 500 puts a transaction, on disk (FileStream,
 * every append forced, as by default), a cache budget well under the data. Then COMMITS
 * commits by one writer, 1 ms of database time apart (a test clock, so that reclaim's pace
 * is the same in every run), retain duration RETAIN seconds of database time: an overwrite
 * of a random cold key with 20 to 30 bytes, and every BIG-th commit one put of BIGSIZE bytes
 * (default 600,000) at one of 8 keys of its own. A large commit adds about a quarter of its
 * size to the allowance, so the commit after it carries a step of up to 128 KiB: 900 to
 * 1,200 copies of the cold values (their touch, their puts and the charge's walk under the
 * lock).
 *
 * Printed, for the commits that carry a step and for the others: the time of execute() and
 * the time under the write lock from the plan to the end of the record (Db.TestHooks
 * beforePlan to transExecuted), each as the median, the 99th and 99.9th percentiles and the
 * longest; the copies a step (touchKeys); the commit with the longest time under the lock
 * and its copies; the five longest commits with their JVM uptimes for the GC log
 * (-Xlog:gc*,safepoint); the stream kept; and the longest under the lock and the longest
 * commit against 20 ms, as figures only (no pass or fail).
 *
 * Usage: java -Xmx4g [-XX:+UseZGC] -cp OUT:JAR bergdb.core.BigStepProbe
 * Properties: keys=N (default 2,000,000), budget=MB (50), dir=D (build/bigstep, emptied
 * first), commits=N (100,000), big=N (50), bigsize=N (600,000), retain=S (10), sd=N (the
 * startup distance, default 20,000,000). Prints BIG STEP PROBE DONE.
 */
public class BigStepProbe {
    static final long SEC = Clock.UNITS_PER_SEC;
    final int keys = Integer.getInteger("keys", 2000 * 1000);
    final long budget = Long.getLong("budget", 50) * 1000 * 1000;
    final File dir = new File(System.getProperty("dir", "build/bigstep"));
    final int commits = Integer.getInteger("commits", 100 * 1000);
    final int big = Integer.getInteger("big", 50);
    final int bigsize = Integer.getInteger("bigsize", 600 * 1000);
    final long retain = Long.getLong("retain", 10);
    final int sd = Integer.getInteger("sd", 20 * 1000 * 1000);

    static long planStart;
    static boolean lastStep;
    static long lastLock;
    static int lastCopies;

    /** [step]: the times of execute() and under the lock, the copies. */
    final long[][] exec = new long[2][], lock = new long[2][];
    final int[] count = new int[2];
    final long[] copies = new long[1 << 20];
    final long[] topNs = new long[5], topAt = new long[5];
    long lockMax, lockMaxCopies, execMax;
    Db db;

    public static void main(String[] args) throws Exception {
        new BigStepProbe().run();
    }

    void run() throws Exception {
        for (int s = 0; s < 2; s++) {
            exec[s] = new long[commits];
            lock[s] = new long[commits];
        }
        Db.testHooks = new Db.TestHooks() {
            public void beforePlan(Db.ExecuteData x) {
                planStart = System.nanoTime();
            }

            public void transExecuted(Db.ExecuteData x) {
                lastStep = x.plan != null && x.plan.touchKeys != null;
                lastLock = System.nanoTime() - planStart;
                lastCopies = lastStep ? x.plan.touchKeys.length - 1 : 0;
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
                    tb.put(key(j), value(r, 20 + r.nextInt(11)));
                }
                db.execute(tb.build());
            }
            db.sync(bergdb.pub.util.SyncLevel.ORDINARY);
            System.out.println("BigStepProbe: " + keys + " keys of 20 to 30 bytes, a stream of "
                    + db.getStreamLength() / 1000000 + " MB, cache budget " + budget / 1000000
                    + " MB, loaded in " + (System.nanoTime() - t0) / 1000000 + " ms; " + commits
                    + " commits, every " + big + "th of " + bigsize + " bytes, retain " + retain
                    + " s, sd " + sd);
            db.setRetainDuration(retain * SEC);
            long t1 = System.nanoTime();
            int nc = 0;
            for (int i = 0; i < commits; i++) {
                time += SEC / 1000;
                clock.setTime(time);
                Trans t = i % big == big - 1
                        ? db.trans().put("/b/" + r.nextInt(8), value(r, bigsize)).build()
                        : db.trans().put(key(r.nextInt(keys)), value(r, 20 + r.nextInt(11)))
                                .build();
                long a = System.nanoTime();
                db.execute(t);
                long d = System.nanoTime() - a;
                final int s = lastStep ? 1 : 0;
                final int c = count[s]++;
                exec[s][c] = d;
                lock[s][c] = lastLock;
                if (lastStep && nc < copies.length) copies[nc++] = lastCopies;
                if (lastLock > lockMax) {
                    lockMax = lastLock;
                    lockMaxCopies = lastStep ? lastCopies : -1;
                }
                execMax = Math.max(execMax, d);
                top(d);
            }
            System.out.println("  " + commits + " commits in " + (System.nanoTime() - t1) / 1000000
                    + " ms; the stream kept " + (db.getStreamLength() - db.getFirstAvailablePos())
                    / 1000000 + " MB of " + db.getStreamLength() / 1000000 + " MB");
            for (int s = 1; s >= 0; s--) {
                final int c = count[s];
                System.out.println("  " + (s == 1 ? "with a step:   " : "without a step:") + " "
                        + c + " commits; execute " + pct(exec[s], c) + "; under the lock "
                        + pct(lock[s], c));
            }
            long[] cp = Arrays.copyOf(copies, nc);
            Arrays.sort(cp);
            System.out.println("  copies a step: " + (nc == 0 ? "-" : "median " + cp[nc / 2]
                    + ", p99 " + cp[Math.min(nc - 1, (int) (nc * 0.99))] + ", most "
                    + cp[nc - 1]) + "; the longest under the lock had "
                    + (lockMaxCopies < 0 ? "no step" : lockMaxCopies + " copies"));
            StringBuilder b = new StringBuilder("  the five longest commits (ms at uptime s):");
            for (int k = 0; k < 5; k++) {
                b.append(String.format(" %.2f at %.1f", topNs[k] / 1e6, topAt[k] / 1000.0));
            }
            System.out.println(b);
            System.out.println(String.format("  P1 (20 ms): the longest under the lock %.3f ms,"
                    + " the longest commit %.3f ms", lockMax / 1e6, execMax / 1e6));
            System.out.println("  " + db.internal().cacheStats());
        } finally {
            db.close();
            Db.testHooks = null;
        }
        System.out.println("BIG STEP PROBE DONE");
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
}
