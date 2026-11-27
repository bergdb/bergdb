package bergdb.core;

import java.util.*;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06, review 3, W1: review-3-probes/MwWarmProbe with two more counts, the
 * warm-ups' scans (the GetMany that Db.newGetMany makes on a thread that does not hold the
 * write lock: a commit's step warm-up; the writers make no other) and all loads of the
 * commits' phase (NodeCollection.loads: the commits' own reads, the plans' scans, the
 * warm-ups), so that the warm-up's share of the steps and its cost are seen together. The
 * records with a step are counted in the commits' phase only (MwWarmProbe counts the
 * cold puts' too). MwWarmProbe's text follows.
 *
 * The warm-up of a step's reads before the write lock
 * (Reclaim.warmup) with more than one writer thread, as counts, not as times. A database
 * larger than its cache budget, as probes/WarmProbe's: COLD keys of VALUE bytes put once,
 * then N commits by WRITERS threads, each one put of COMMIT bytes at one of 8 hot keys, the
 * clock DT_MS on for each; retain duration 1 s. Run without the warm-up
 * (Db.TestHooks.stepWarmup false) and with it. For the records that carry a step: the
 * versions that the plan's scan loaded from the stream under the write lock
 * (RecordPlan.loads, the maintenance follower's count, the plan's own), and how many of the
 * steps' scans loaded any. With several writers the runs' streams are not the same (the
 * lock's order), so only the counts are compared; with one writer the two streams have the
 * same length.
 *
 * With -Dpause=NS each writer waits up to NS ns after a commit (0: none). With -Dhold=NS
 * every commit of the N holds the write lock NS ns longer (a spin in Db.TestHooks.beforePlan),
 * as a commit that takes that long under the lock does: the other writers then come to the
 * lock, make their warm-up and wait, so a writer's warm-up is made before the record before
 * its own is applied.
 *
 * Usage: java -cp OUT:JAR bergdb.core.WarmAheadProbe COLD VALUE N COMMIT DT_MS BUDGET WRITERS
 * Kind: functional (counts; no time is measured).
 */
public class WarmAheadProbe {
    static final long SEC = Clock.UNITS_PER_SEC;
    static volatile boolean warmup;
    static long steps, scanLoads, coldSteps, scanLoadsMax, stepKvs;
    static Db db;
    static final int hold = Integer.getInteger("hold", 0);
    static volatile boolean loading;
    static final AtomicLong warmScans = new AtomicLong();
    static Object writeLock;

    public static void main(String[] args) throws Exception {
        int cold = Integer.parseInt(args[0]), value = Integer.parseInt(args[1]);
        int n = Integer.parseInt(args[2]), commit = Integer.parseInt(args[3]);
        long dt = Long.parseLong(args[4]) * SEC / 1000;
        long budget = Long.parseLong(args[5]);
        int writers = Integer.parseInt(args[6]);
        System.out.println("WarmAheadProbe cold " + cold + " x " + value + ", " + n
                + " commits of " + commit + " bytes, " + args[4] + " ms apart, cache budget "
                + budget + ", writers " + writers + ", pause "
                + Integer.getInteger("pause", 0) + " ns, hold " + hold + " ns:");
        String r0 = run(cold, value, n, commit, dt, budget, writers, false);
        System.out.println("  without the warm-up: " + r0);
        String r1 = run(cold, value, n, commit, dt, budget, writers, true);
        System.out.println("  with the warm-up:    " + r1);
    }

    static String run(int cold, int value, final int n, final int commit, final long dt,
            long budget, int writers, boolean warm) throws Exception {
        warmup = warm;
        steps = scanLoads = coldSteps = scanLoadsMax = stepKvs = 0;
        Db.testHooks = new Db.TestHooks() {
            public boolean stepWarmup() {
                return warmup;
            }

            public void beforePlan(Db.ExecuteData x) {         // under the write lock
                if (hold > 0 && !loading) {
                    final long end = System.nanoTime() + hold;
                    while (System.nanoTime() < end) Thread.onSpinWait();
                }
            }

            public void transExecuted(Db.ExecuteData x) {     // under the write lock
                if (!loading && x.plan instanceof Reclaim.RecordPlan && x.plan.touchKeys != null) {
                    final long l = ((Reclaim.RecordPlan) x.plan).loads;
                    steps++;
                    scanLoads += l;
                    if (l > 0) coldSteps++;
                    scanLoadsMax = Math.max(scanLoadsMax, l);
                    stepKvs += x.plan.touchKeys.length - 1;
                }
            }

            public void getManyCreated(bergdb.dag.GetMany g) {
                if (!loading && writeLock != null && !Thread.holdsLock(writeLock)) {
                    warmScans.incrementAndGet();
                }
            }

            public void valueNodeCreated(bergdb.dag.ValueNode vn, long[] key) {}
            public void nodeTouched(bergdb.dag.Node nd) {}
            public void nodeReplaced(bergdb.dag.Node nd) {}
        };
        final AtomicLong clock = new AtomicLong(SEC);
        CutStream s = new CutStream();
        db = Db.builder().testSetup(s).clock(clock::get).cacheSizeIndicator(budget).start();
        final java.lang.reflect.Field lockField = Db.class.getDeclaredField("writeLock");
        lockField.setAccessible(true);
        writeLock = lockField.get(db);
        warmScans.set(0);
        try {
            db.setStartupDistance(Integer.getInteger("sd", 20000));
            db.setRetainDuration(SEC);
            Random r = new Random(1);
            loading = true;
            final int per = Math.max(1, Math.min(100, 2000000 / (value + 100)));
            for (int i = 0; i < cold; i += per) {
                clock.addAndGet(SEC / 100);
                Trans.Builder tb = db.trans();
                for (int j = i; j < Math.min(cold, i + per); j++) {
                    byte[] v = new byte[value];
                    r.nextBytes(v);
                    tb.put(String.format("/c/%08d", j), v);
                }
                db.execute(tb.build());
            }
            final long loads0 = db.internal().nodeCollection().loads();
            loading = false;
            final AtomicLong left = new AtomicLong(n);
            final int pause = Integer.getInteger("pause", 0);
            final List<Thread> ts = new ArrayList<Thread>();
            final Throwable[] failure = new Throwable[1];
            for (int w = 0; w < writers; w++) {
                final Random rw = new Random(100 + w);
                Thread t = new Thread(() -> {
                    try {
                        while (left.decrementAndGet() >= 0) {
                            clock.addAndGet(dt);
                            byte[] v = new byte[commit];
                            rw.nextBytes(v);
                            db.execute(db.trans().put("/h/" + rw.nextInt(8), v).build());
                            if (pause > 0) {
                                long end = System.nanoTime() + rw.nextInt(pause);
                                while (System.nanoTime() < end) Thread.onSpinWait();
                            }
                        }
                    } catch (Throwable e) {
                        synchronized (failure) {
                            if (failure[0] == null) failure[0] = e;
                        }
                    }
                });
                ts.add(t);
            }
            for (Thread t : ts) t.start();
            for (Thread t : ts) t.join();
            if (failure[0] != null) {
                failure[0].printStackTrace(System.out);
                return "FAILED: " + failure[0];
            }
            db.sync(bergdb.pub.util.SyncLevel.ORDINARY);     // the stream's length then
            return steps + " records with a step, " + stepKvs + " copies; the plans' scans "
                    + "loaded under the lock " + scanLoads + " versions ("
                    + String.format("%.2f", steps == 0 ? 0.0 : scanLoads / (double) steps)
                    + " a step, at most " + scanLoadsMax + "); steps whose scan loaded any: "
                    + coldSteps + " (" + String.format("%.1f", steps == 0 ? 0.0
                    : 100.0 * coldSteps / steps) + " %); warm-up scans " + warmScans.get()
                    + ", loads in all " + (db.internal().nodeCollection().loads() - loads0)
                    + "; stream " + s.getLength();
        } finally {
            db.close();
            Db.testHooks = null;
        }
    }
}
