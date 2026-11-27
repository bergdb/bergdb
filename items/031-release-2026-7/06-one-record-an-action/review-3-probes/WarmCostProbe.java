package bergdb.core;

import java.util.*;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06, review 3 (finding W1): the reads that the warm-up of a step's scan adds
 * (Reclaim.warmup), as counts. COLD keys of VALUE bytes put once, then N commits by WRITERS
 * threads, each one put of COMMIT bytes at one of 8 hot keys, the clock DT_MS on for each;
 * retain duration 1 s; every object evicted after every transaction
 * (Eviction.Schedule.EVERY 1), so that every read of a node or a value is a load from the
 * stream and the count of loads is the count of reads. Run without the warm-up and with it.
 * Printed: the records with a step; all loads of the run (NodeCollection.loads: the
 * commits' own reads, the plans' scans, the warm-ups); the plans' scans' loads; the calls of
 * the warm-up while an iteration ran (Db.TestHooks.stepWarmup, asked once a call).
 *
 * Usage: java -cp OUT:JAR bergdb.core.WarmCostProbe COLD VALUE N COMMIT DT_MS WRITERS
 * Kind: functional (counts; no time is measured).
 */
public class WarmCostProbe {
    static final long SEC = Clock.UNITS_PER_SEC;
    static volatile boolean warmup;
    static final AtomicLong warmCalls = new AtomicLong();
    static long steps, scanLoads;

    public static void main(String[] a) throws Exception {
        System.out.println("WarmCostProbe cold " + a[0] + " x " + a[1] + ", " + a[2]
                + " commits of " + a[3] + " bytes, " + a[4] + " ms apart, writers " + a[5]
                + ", every object evicted after every transaction:");
        System.out.println("  without the warm-up: " + run(a, false));
        System.out.println("  with the warm-up:    " + run(a, true));
    }

    static String run(String[] a, boolean warm) throws Exception {
        int cold = Integer.parseInt(a[0]), value = Integer.parseInt(a[1]);
        final int n = Integer.parseInt(a[2]), commit = Integer.parseInt(a[3]);
        final long dt = Long.parseLong(a[4]) * SEC / 1000;
        int writers = Integer.parseInt(a[5]);
        warmup = warm;
        warmCalls.set(0);
        steps = scanLoads = 0;
        Db.testHooks = new Db.TestHooks() {
            public boolean stepWarmup() {
                warmCalls.incrementAndGet();
                return warmup;
            }

            public void transExecuted(Db.ExecuteData x) {     // under the write lock
                if (x.plan instanceof Reclaim.RecordPlan && x.plan.touchKeys != null) {
                    steps++;
                    scanLoads += ((Reclaim.RecordPlan) x.plan).loads;
                }
            }

            public void valueNodeCreated(bergdb.dag.ValueNode vn, long[] key) {}
            public void nodeTouched(bergdb.dag.Node nd) {}
            public void nodeReplaced(bergdb.dag.Node nd) {}
        };
        final AtomicLong clock = new AtomicLong(SEC);
        CutStream s = new CutStream();
        final Db db = Db.builder().testSetup(s).clock(clock::get)
                .evictionSchedule(Eviction.Schedule.EVERY, 1).start();
        try {
            db.setStartupDistance(Integer.getInteger("sd", 20000));
            db.setRetainDuration(SEC);
            Random r = new Random(1);
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
            final long calls0 = warmCalls.get();
            final AtomicLong left = new AtomicLong(n);
            final List<Thread> ts = new ArrayList<Thread>();
            for (int w = 0; w < writers; w++) {
                final Random rw = new Random(100 + w);
                ts.add(new Thread(() -> {
                    while (left.decrementAndGet() >= 0) {
                        clock.addAndGet(dt);
                        byte[] v = new byte[commit];
                        rw.nextBytes(v);
                        db.execute(db.trans().put("/h/" + rw.nextInt(8), v).build());
                    }
                }));
            }
            steps = scanLoads = 0;
            for (Thread t : ts) t.start();
            for (Thread t : ts) t.join();
            db.sync(bergdb.pub.util.SyncLevel.ORDINARY);
            return steps + " records with a step; loads " 
                    + (db.internal().nodeCollection().loads() - loads0)
                    + ", of them by the plans' scans " + scanLoads + "; warm-up calls while "
                    + "an iteration ran " + (warmCalls.get() - calls0) + "; stream "
                    + s.getLength();
        } finally {
            db.close();
            Db.testHooks = null;
        }
    }
}
