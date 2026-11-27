package bergdb.core;

import java.util.Random;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * Review probe (031-06, review-main): a Trans whose execution failed the database after its
 * go point, with a plan that carried a step, keeps the plan's fields (Trans.touch, recordCap,
 * touchCount): Db.executeLocked sets them only when the execution has a plan, and clears them
 * only after a record that worked. Executed again on the restarted database, when its record
 * carries no plan, the same Trans object runs the touch of a test (Db.touchPaths over its own
 * keys). Is its record the record of a new Trans with the same KVs at the same time?
 *
 * args: seed node8(0|1) [after|before]   (the failure after the record's append, or before it)
 */
public class RmReuseProbe {
    static final long SEC = Clock.UNITS_PER_SEC;
    static final class Crash extends RuntimeException { Crash() { super("crash"); } }
    static boolean armed, before;
    static boolean lastPlanNull, lastTouch;

    static Db start(CutStream s, CoreTestClock clock, boolean node8) {
        DbBuilder b = Db.builder().testSetup(s).clock(clock);
        if (node8) b.maxNodeSize8();
        return b.start();
    }

    static Trans build(Db db, int i, byte[] v) {
        return db.trans().put("/k" + (i % 150), v).put("/n/new" + i, new byte[] {1, 2, 3})
                .delete("/missing/" + i).build();
    }

    public static void main(String[] a) throws Exception {
        final long seed = Long.parseLong(a[0]);
        final boolean node8 = a[1].equals("1");
        before = a.length > 2 && a[2].equals("before");
        Db.testHooks = new Db.TestHooks() {
            public void kvApplied(long[] key, byte[] value) {
                // before the append: in putKvs, after the go point (the touch has run)
                if (armed && before && fire) { armed = false; throw new Crash(); }
            }
            boolean fire;
            public void beforePlan(Db.ExecuteData x) { fire = false; }
            public void nodeTouched(Node n) { fire = true; }    // the record has a touch: a step
            public void beforeApply(Db.ExecuteData x) {
                lastPlanNull = x.plan == null;
                lastTouch = x.trans.touch;
            }
            public void transExecuted(Db.ExecuteData x) {
                if (armed && !before && x.plan != null && x.trans.touch && !x.trans.part) {
                    armed = false;
                    throw new Crash();
                }
            }
            public void valueNodeCreated(ValueNode n, long[] k) {}
            public void nodeReplaced(Node n) {}
        };
        final CutStream s = new CutStream();
        final CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        Db db = start(s, clock, node8);
        db.setStartupDistance(2000);
        db.setRetainDuration(SEC);
        final Random r = new Random(seed);
        Trans failed = null;
        byte[] failedValue = null;
        int failedAt = -1;
        for (int i = 0; i < 20000 && failed == null; i++) {
            time += SEC / 100;
            clock.setTime(time);
            final byte[] v = new byte[100 + r.nextInt(400)];
            r.nextBytes(v);
            final Trans t = build(db, i, v);
            armed = i > 300;
            try {
                db.execute(t);
            } catch (RuntimeException e) {
                failed = t;
                failedValue = v;
                failedAt = i;
                System.out.println("action " + i + ": the database failed " + (before ? "before"
                        : "after") + " the record of a commit that carried a step ("
                        + e.getClass().getSimpleName() + "); the Trans keeps touch=" + t.touch
                        + ", recordCap=" + t.recordCap + ", dirtiedNodes=" + t.dirtiedNodes);
            }
        }
        armed = false;
        if (failed == null) { System.out.println("no commit carried a step"); return; }
        try { db.close(); } catch (RuntimeException e) { }
        // Another commit takes the step that is due (as another thread's would), then the
        // action again: with the Trans that failed, and with a new Trans of the same KVs.
        // Third, the control: the Trans that failed, with the plan's fields cleared by hand.
        final byte[][] images = new byte[3][];
        final boolean[] planNull = new boolean[3], touch = new boolean[3];
        for (int run = 0; run < 3; run++) {
            final CutStream c = s.copy();
            final CoreTestClock clock2 = new CoreTestClock();
            clock2.setTime(time);
            final Db d = start(c, clock2, node8);
            clock2.setTime(time + SEC / 100);
            d.execute(d.trans().put("/other", new byte[] {7}).build());
            clock2.setTime(time + 2 * SEC / 100);
            final Trans again = run == 1 ? build(d, failedAt, failedValue) : failed;
            if (run == 2) {
                failed.touch = false;
                failed.touchCount = null;
                failed.maintainTakeTo = -1;
                failed.recordCap = 0;
            }
            d.execute(again);
            planNull[run] = lastPlanNull;
            touch[run] = lastTouch;
            clock2.setTime(time + 3 * SEC / 100);
            d.execute(d.trans().put("/after", new byte[] {8}).build());
            d.close();
            images[run] = new byte[(int) (c.getLength() - c.getFirstPos())];
            c.read(c.getFirstPos(), images[run], 0, images[run].length);
            System.out.println((run == 0 ? "the Trans that failed, again" : run == 1 ? "a new Trans, the same KVs  "
                    : "the failed one, fields cleared")
                    + ": its record carried " + (planNull[run] ? "no plan" : "a plan") + ", touch="
                    + touch[run] + "; stream length " + c.getLength() + ", first pos " + c.getFirstPos());
        }
        int diff = -1;
        final int n = Math.min(images[0].length, images[1].length);
        for (int i = 0; i < n && diff == -1; i++) if (images[0][i] != images[1][i]) diff = i;
        System.out.println("control (the failed Trans with its plan's fields cleared, against a new Trans): "
                + (java.util.Arrays.equals(images[2], images[1]) ? "the same stream" : "DIFFERENT"));
        if (images[0].length == images[1].length && diff == -1) {
            System.out.println("SAME STREAM (" + images[0].length + " bytes)");
        } else {
            System.out.println("DIFFERENT STREAMS: lengths " + images[0].length + " and "
                    + images[1].length + ", first different byte at offset " + diff);
        }
    }
}
