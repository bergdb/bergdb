package bergdb.core;

import java.security.MessageDigest;
import java.util.*;

import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06, review 3: whether a record that carries a step depends on what is in memory
 * (landing step 3: the charge after the batch, Db.chargeStep; a commit's step up to 128 KiB,
 * Reclaim.commitStepSize; the warm-up). One workload, one thread, a test clock: COLD keys of
 * VALUE bytes put once, then N commits DT_MS apart, retain duration 1 s; commit i is one put
 * of COMMIT bytes at one of 8 hot keys, or, every third, 50 puts of 40 bytes at random cold
 * keys (so that the action's paths and the step's share nodes), or, every seventh, deletes of
 * 20 cold keys; maintain(300) every 40 commits; a stop and a start every RESTART commits (0:
 * none). Run with: no eviction (the Core's test setup, every object stays in memory), a cache
 * budget of BUDGET bytes, every object evicted after every transaction
 * (Eviction.Schedule.EVERY 1), and the budget without the warm-up. The streams must be the
 * same: their length, first position and SHA-256. Prints the steps and the largest step's
 * copies' bytes of each run.
 *
 * Usage: java -ea -cp OUT:JAR bergdb.core.EvictChargeProbe COLD VALUE N COMMIT DT_MS BUDGET
 *     NODE RESTART
 * Prints EVICT CHARGE PROBE OK, or FAILED and exits 1. Kind: functional.
 */
public class EvictChargeProbe {
    static final long SEC = Clock.UNITS_PER_SEC;
    static long steps, maxStepBytes, copies;
    static volatile boolean warm = true;

    public static void main(String[] a) throws Exception {
        String[] modes = {"none", "budget", "every1", "budget-nowarm"};
        String first = null;
        boolean ok = true;
        for (String m : modes) {
            String r = run(a, m);
            System.out.println("  " + m + ": " + r + "; steps " + steps + ", copies " + copies
                    + ", largest step's copies " + maxStepBytes + " bytes");
            if (first == null) first = r;
            else if (!first.equals(r)) ok = false;
        }
        System.out.println(ok ? "EVICT CHARGE PROBE OK" : "EVICT CHARGE PROBE FAILED");
        if (!ok) System.exit(1);
    }

    static Db start(CutStream s, CoreTestClock clock, String mode, long budget, int node) {
        DbBuilder b = Db.builder().testSetup(s).clock(clock);
        if (mode.startsWith("budget")) b.cacheSizeIndicator(budget);
        if (mode.equals("every1")) b.evictionSchedule(Eviction.Schedule.EVERY, 1);
        if (node == 8) b.maxNodeSize8();
        if (node == 30) b.maxNodeSize30();
        return b.start();
    }

    static String run(String[] a, String mode) throws Exception {
        int cold = Integer.parseInt(a[0]), value = Integer.parseInt(a[1]);
        int n = Integer.parseInt(a[2]), commit = Integer.parseInt(a[3]);
        long dt = Long.parseLong(a[4]) * SEC / 1000;
        long budget = Long.parseLong(a[5]);
        int node = Integer.parseInt(a[6]), restart = Integer.parseInt(a[7]);
        steps = maxStepBytes = copies = 0;
        warm = !mode.endsWith("nowarm");
        Db.testHooks = new Db.TestHooks() {
            public boolean stepWarmup() {
                return warm;
            }

            public void transExecuted(Db.ExecuteData x) {
                if (x.plan instanceof Reclaim.RecordPlan && x.plan.touchKeys != null) {
                    Reclaim.RecordPlan p = (Reclaim.RecordPlan) x.plan;
                    steps++;
                    copies += p.stepValues;
                    maxStepBytes = Math.max(maxStepBytes, p.stepValueBytes);
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
        Db db = start(s, clock, mode, budget, node);
        try {
            db.setStartupDistance(Integer.getInteger("sd", 20000));
            db.setRetainDuration(SEC);
            Random r = new Random(7);
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
            for (int i = 0; i < n; i++) {
                time += dt;
                clock.setTime(time);
                Trans.Builder tb = db.trans();
                if (i % 7 == 6) {
                    TreeSet<Integer> ks = new TreeSet<Integer>();
                    while (ks.size() < 20) ks.add(r.nextInt(cold));
                    for (int k : ks) tb.delete(String.format("/c/%08d", k));
                } else if (i % 3 == 2) {
                    TreeSet<Integer> ks = new TreeSet<Integer>();
                    while (ks.size() < 50) ks.add(r.nextInt(cold));
                    for (int k : ks) {
                        byte[] v = new byte[40];
                        r.nextBytes(v);
                        tb.put(String.format("/c/%08d", k), v);
                    }
                } else {
                    byte[] v = new byte[commit];
                    r.nextBytes(v);
                    tb.put("/h/" + r.nextInt(8), v);
                }
                db.execute(tb.build());
                if (i % 40 == 39) {
                    db.maintain(300);
                }
                if (restart > 0 && i % restart == restart - 1) {
                    db.close();
                    s = s.copy();       // db.close() closes the stream
                    db = start(s, clock, mode, budget, node);
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
            return "length " + length + ", first " + first + ", sha256 " + h.substring(0, 16);
        } finally {
            db.close();
            Db.testHooks = null;
        }
    }
}
