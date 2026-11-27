package bergdb.core;

import java.util.*;

import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * Review probe of bergdb 031-06 (2026-11-27), a figure for P1: the time between a commit's
 * time being taken and its writes being given to the index (Db.TestHooks.beforePlan to the
 * first kvApplied: the plan with its scan, before the go point; the commit's writes are not
 * readable before it ends), and the whole execute(), for the commits that carry a step.
 * Case "walk": COLD keys put once; when an iteration runs, NEW keys are put ahead of its scan
 * in transactions of 500, in -Dgaps=1 gaps between cold keys (stored after pStart: the scan walks them, counts none toward its
 * 16 kB, and ends at the step reserve's count of index nodes). Case "big": cold values of
 * VALUE bytes (a step copies one). EVICT > 0: a cache of that many bytes (cacheSizeIndicator)
 * instead of none.
 *
 * Usage: java -cp OUT:JAR bergdb.core.RvP1 COLD VALUE NEW COMMITS [EVICT]
 */
public class RvP1 {
    static final long SEC = Clock.UNITS_PER_SEC;
    static long planStart, planNanos;

    public static void main(String[] args) throws Exception {
        int cold = Integer.parseInt(args[0]), value = Integer.parseInt(args[1]);
        int fresh = Integer.parseInt(args[2]), n = Integer.parseInt(args[3]);
        long evict = args.length > 4 ? Long.parseLong(args[4]) : 0;
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {}
            public void beforePlan(Db.ExecuteData x) { planStart = System.nanoTime(); planNanos = -1; }
            public void kvApplied(long[] key, byte[] v) {
                if (planNanos == -1) planNanos = System.nanoTime() - planStart;
            }
            public void valueNodeCreated(ValueNode node, long[] k) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) {}
        };
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        DbBuilder b = Db.builder().testSetup(new CutStream()).clock(clock);
        if (evict > 0) b.cacheSizeIndicator(evict);
        if (Long.getLong("reserve", 0) > 0) b.reclaimStepReserve(Long.getLong("reserve"));
        Db db = b.start();
        db.setStartupDistance(100000);
        Random r = new Random(1);
        final int per = Math.max(1, Math.min(100, 20000000 / (value + 100)));
        for (int i = 0; i < cold; i += per) {
            time += SEC / 1000; clock.setTime(time);
            Trans.Builder tb = db.trans();
            for (int j = i; j < i + per && j < cold; j++) {
                byte[] v = new byte[value];
                r.nextBytes(v);
                tb.put(String.format("/c/%07d", j), v);
            }
            db.execute(tb.build());
        }
        db.setRetainDuration(SEC);
        Reclaim rc = db.internal().reclaim();
        final Reclaim.Stats rcStats = rc.enableStats();
        long[] plan = new long[n], whole = new long[n];
        int steps = 0, put = 0;
        long maxKv = 0;
        for (int i = 0; i < n; i++) {
            time += SEC / 100; clock.setTime(time);
            Reclaim.IterationInfo cur = rc.currentIteration();
            if (cur != null && put < fresh && cur.lastKey != null) {
                // New keys ahead of the scan, in one transaction.
                Trans.Builder tb = db.trans();
                for (int j = 0; j < 500 && put < fresh; j++, put++) {
                    tb.put(String.format("/c/%07d/n%07d", cold * 2 / 5 + put % Integer.getInteger("gaps", 1), put), new byte[4]);
                }
                db.execute(tb.build());
                continue;
            }
            if (Boolean.getBoolean("dbg") && i % 500 == 0) System.out.println("  i " + i + " put " + put + " cur "
                    + (cur == null ? "none" : bergdb.dag.Keys.toString(cur.lastKey == null ? new long[0] : cur.lastKey) + " kv " + cur.kvCount + " pStart " + cur.pStart + " rewritten " + cur.rewritten)
                    + " length " + db.getStreamLength() + " first " + db.getFirstAvailablePos());
            byte[] val = new byte[2000];
            r.nextBytes(val);
            long kv = cur == null ? -1 : cur.kvCount, ps = cur == null ? -1 : cur.pStart;
            long t0 = System.nanoTime();
            db.execute(db.trans().put("/h/" + r.nextInt(100), val).build());
            long dt = System.nanoTime() - t0;
            Reclaim.IterationInfo after = rc.currentIteration();
            boolean step = cur != null && (after == null || after.pStart != ps || after.kvCount != kv);
            if (step) {
                if (after != null && after.pStart == ps) maxKv = Math.max(maxKv, after.kvCount - kv);
                plan[steps] = planNanos; whole[steps] = dt; steps++;
            }
        }
        long splits = 0;
        Reclaim.Stats rs = rcStats;
        for (Reclaim.Stats.Iteration st : rs.iterations) splits += st.splitSteps;
        System.out.println("  step reserve " + rc.getStepReserve() + ": " + splits + " steps split by it; the stream's length " + db.getStreamLength());
        System.out.println("RvP1 cold " + cold + " x " + value + ", " + put + " new keys ahead of the scan, cache "
                + (evict > 0 ? evict + " bytes" : "none (all in memory)") + ": " + steps + " commits carried a step; "
                + "the most KVs one scan met " + maxKv);
        System.out.println("  the plan (before the go point): " + stats(plan, steps));
        System.out.println("  the whole execute():            " + stats(whole, steps));
        db.close();
    }

    static String stats(long[] a, int n) {
        if (n == 0) return "none";
        long[] s = Arrays.copyOf(a, n);
        Arrays.sort(s);
        return String.format("median %.2f ms, p99 %.2f ms, max %.2f ms", s[n / 2] / 1e6,
                s[Math.min(n - 1, n * 99 / 100)] / 1e6, s[n - 1] / 1e6);
    }
}
