package bergdb.core;

import java.security.MessageDigest;
import java.util.*;

import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06, landing step 3 (the review's F4): the warm-up of a step's reads before the
 * write lock (Maintenance.warmup), as a count of the node versions read from the stream under
 * the lock, not as a time. A database larger than its cache budget (cacheSizeIndicator, the
 * eviction on): COLD keys of VALUE bytes put once, then N commits, DT_MS of database time
 * apart, retain duration 1 s: one put of COMMIT bytes at one of 8 hot keys, or with -Dputs=K,
 * K puts of COMMIT / K bytes at random keys among -Dhot=H hot keys; with -Dmaint=M a
 * maintain(1000) call every M commits. Run twice, without the warm-up
 * (Db.TestHooks.stepWarmup false) and with it. For each record that carries a step:
 * the versions loaded from the stream under the lock, from the plan to the record's end
 * (NodeCollection.loads, the node table's count: the plan's scan, its touch, the batch and
 * the take), and of them the plan's scan's (RecordPlan.loads). The two streams must be the
 * same, byte for byte (a SHA-256 of the stream from its first position, its length and its
 * first position): the warm-up changes only what is in memory.
 *
 * Usage: java -cp OUT:JAR bergdb.core.WarmProbe COLD VALUE N COMMIT DT_MS BUDGET [NODE]
 *   -Dsd=20000 -Dputs=1 -Dhot=8 -Dmaint=0
 * Prints WARM PROBE OK, or WARM PROBE FAILED (other streams) and exits 1.
 * Kind: functional (counts; no time is measured).
 */
public class WarmProbe {
    static final long SEC = Clock.UNITS_PER_SEC;

    static boolean warmup;
    static long loads0, scanLoads0;
    static long steps, lockLoads, scanLoads, stepLockLoadsMax, commitSteps, partSteps;

    public static void main(String[] args) throws Exception {
        int cold = Integer.parseInt(args[0]), value = Integer.parseInt(args[1]);
        int n = Integer.parseInt(args[2]), commit = Integer.parseInt(args[3]);
        long dt = Long.parseLong(args[4]) * SEC / 1000;
        long budget = Long.parseLong(args[5]);
        int node = args.length > 6 ? Integer.parseInt(args[6]) : 0;
        String[] r0 = run(cold, value, n, commit, dt, budget, node, false);
        String[] r1 = run(cold, value, n, commit, dt, budget, node, true);
        System.out.println("WarmProbe cold " + cold + " x " + value + ", " + n + " commits of "
                + commit + " bytes in " + Integer.getInteger("puts", 1) + " put(s), " + args[4]
                + " ms apart, cache budget " + budget + ", node " + node + ", maint "
                + Integer.getInteger("maint", 0) + ":");
        System.out.println("  without the warm-up: " + r0[1]);
        System.out.println("  with the warm-up:    " + r1[1]);
        if (!r0[0].equals(r1[0])) {
            System.out.println("  streams: " + r0[0] + " against " + r1[0]);
            System.out.println("WARM PROBE FAILED");
            System.exit(1);
        }
        System.out.println("  the same stream: " + r0[0]);
        System.out.println("WARM PROBE OK");
    }

    static String[] run(int cold, int value, int n, int commit, long dt, long budget, int node,
            boolean warm) throws Exception {
        warmup = warm;
        steps = lockLoads = scanLoads = stepLockLoadsMax = commitSteps = partSteps = 0;
        Db.testHooks = new Db.TestHooks() {
            public boolean stepWarmup() {
                return warmup;
            }

            public void beforePlan(Db.ExecuteData x) {
                loads0 = x.trans == null ? 0 : nodes().loads();
            }

            public void transExecuted(Db.ExecuteData x) {
                if (x.plan instanceof Reclaim.RecordPlan && x.plan.touchKeys != null) {
                    final long d = nodes().loads() - loads0;
                    steps++;
                    if (x.trans.part) partSteps++; else commitSteps++;
                    lockLoads += d;
                    stepLockLoadsMax = Math.max(stepLockLoadsMax, d);
                    scanLoads += ((Reclaim.RecordPlan) x.plan).loads;
                }
            }

            public void valueNodeCreated(bergdb.dag.ValueNode vn, long[] key) {}
            public void nodeTouched(bergdb.dag.Node nd) {}
            public void nodeReplaced(bergdb.dag.Node nd) {}
        };
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        CutStream s = new CutStream();
        DbBuilder b = Db.builder().testSetup(s).clock(clock).cacheSizeIndicator(budget);
        if (node == 8) b.maxNodeSize8();
        if (node == 30) b.maxNodeSize30();
        db = b.start();
        try {
            db.setStartupDistance(Integer.getInteger("sd", 20000));
            db.setRetainDuration(SEC);
            Random r = new Random(1);
            final int per = Math.max(1, Math.min(100, 2000000 / (value + 100)));
            for (int i = 0; i < cold; i += per) {
                time += SEC / 100;
                clock.setTime(time);
                Trans.Builder tb = db.trans();
                for (int j = i; j < Math.min(cold, i + per); j++) {
                    byte[] v = new byte[value];
                    r.nextBytes(v);
                    tb.put(String.format("/c/%08d", j), v);
                }
                db.execute(tb.build());
            }
            final int puts = Integer.getInteger("puts", 1);
            final int hot = Integer.getInteger("hot", 8);
            final int maint = Integer.getInteger("maint", 0);
            for (int i = 0; i < n; i++) {
                time += dt;
                clock.setTime(time);
                Trans.Builder tb = db.trans();
                if (puts == 1) {
                    byte[] v = new byte[commit];
                    r.nextBytes(v);
                    tb.put("/h/" + r.nextInt(hot), v);
                } else {
                    final TreeSet<Integer> ks = new TreeSet<Integer>();
                    while (ks.size() < Math.min(puts, hot)) ks.add(r.nextInt(hot));
                    for (int k : ks) {
                        byte[] v = new byte[Math.max(1, commit / puts)];
                        r.nextBytes(v);
                        tb.put(String.format("/h/%07d", k), v);
                    }
                }
                db.execute(tb.build());
                if (maint > 0 && i % maint == maint - 1) {
                    db.maintain(1000);
                }
            }
            db.sync(bergdb.pub.util.SyncLevel.ORDINARY);
            final long first = s.getFirstPos(), length = s.getLength();
            MessageDigest md = MessageDigest.getInstance("SHA-256");
            byte[] buf = new byte[1 << 20];
            for (long p = first; p < length; p += buf.length) {
                int k = (int) Math.min(buf.length, length - p);
                s.read(p, buf, 0, k);
                md.update(buf, 0, k);
            }
            StringBuilder h = new StringBuilder();
            for (byte x : md.digest()) h.append(String.format("%02x", x));
            final String image = "length " + length + ", first " + first + ", sha256 "
                    + h.substring(0, 16);
            final String figures = steps + " records with a step (" + commitSteps
                    + " commits', " + partSteps + " parts'); loaded under the lock " + lockLoads
                    + " (" + String.format("%.2f", steps == 0 ? 0.0 : lockLoads / (double) steps)
                    + " a step, at most " + stepLockLoadsMax + "), of them by the plan's scan "
                    + scanLoads;
            return new String[] {image, figures};
        } finally {
            db.close();
            Db.testHooks = null;
        }
    }

    static Db db;

    static NodeCollection nodes() {
        return db.internal().nodeCollection();
    }
}
