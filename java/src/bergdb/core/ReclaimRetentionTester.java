package bergdb.core;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.CutStream;

/**
 * Tests of changing the retain duration while the database runs, and across restarts
 * (2026-10-13, bergdb 011-04, W2). Database.setRetainDuration() promises that
 * the retain duration can be changed at any time: a larger one makes the available span
 * grow until it reaches the new duration; a smaller one is allowed.
 *
 * <p>What must hold, whatever the changes: (1) every cut keeps the guarantee of the retain
 * duration that was in force when it was decided: first available lookup time &lt;
 * decision time - retain duration; (2) the first available lookup time never moves back, also
 * not over a restart, and what a decided cut has removed is not expected back; (3) every
 * lookup from the first available lookup time on gives what the model says, before and after
 * a restart; (4) a lookup before it throws LookupTimeNotAvailableException.</p>
 */
public class ReclaimRetentionTester {
    private static final long SEC = Clock.UNITS_PER_SEC;
    private static final long FOREVER = Long.MAX_VALUE;

    private ReclaimRetentionTester() {}

    /** A database on a CutStream with a model of all it was given. */
    private static final class Run {
        final Random r;
        final Map<String, TreeMap<Long, byte[]>> model =
                new HashMap<String, TreeMap<Long, byte[]>>();
        CutStream stream = new CutStream();
        CoreTestClock clock;
        long time = SEC;
        Db db;
        Reclaim.Stats stats;
        long maxFirst;      // The largest first available lookup time seen, over restarts.

        Run(long seed, long retain) {
            r = new Random(seed);
            start(retain);
        }

        void start(long retain) {
            clock = new CoreTestClock();
            clock.setTime(time);
            db = Db.builder().testSetup(stream).clock(clock).maxNodeSize8()
                    .startupDistance(2000).start();
            db.setRetainDuration(retain);
            stats = db.internal().reclaim().enableStats();
            Assert.assertTrue("the first available lookup time moved back over a restart: "
                    + db.getFirstAvailableLookupTime() + " < " + maxFirst,
                    db.getFirstAvailableLookupTime() >= maxFirst);
        }

        void restart(long retain) {
            db.sync(SyncLevel.STRONG);
            db.stop();
            stream = stream.copy();
            start(retain);
        }

        void put() {
            time += SEC / 20;
            clock.setTime(time);
            String k = "/k/" + r.nextInt(50);
            byte[] v = new byte[1 + r.nextInt(30)];
            r.nextBytes(v);
            Trans t = db.trans().put(k, v).build();
            db.execute(t);
            TreeMap<Long, byte[]> h = model.get(k);
            if (h == null) {
                model.put(k, h = new TreeMap<Long, byte[]>());
            }
            h.put(t.tt, v);
            if (r.nextInt(10) == 0) {
                db.sync(SyncLevel.ORDINARY);
            }
        }

        void puts(int n) {
            for (int i = 0; i < n; i++) {
                put();
            }
        }

        /** Puts until at least 'cuts' cuts were decided in this session; at most 'max' puts. */
        void putUntilCuts(int cuts, int max) {
            for (int i = 0; i < max && stats.cuts.size() < cuts; i++) {
                put();
            }
            Assert.assertTrue("cuts: " + stats.cuts.size() + ", wanted " + cuts,
                    stats.cuts.size() >= cuts);
        }

        /** Checks (1) to (4) above. */
        void check(String where) {
            for (Reclaim.Stats.Cut c : stats.cuts) {
                Assert.assertTrue(where + ": the cut at " + c.decidedTime + " (tEnd " + c.tEnd
                        + ") breaks its retain duration, " + c.retain,
                        c.retain == FOREVER ? false : c.tEnd < c.decidedTime - c.retain);
            }
            long first = db.getFirstAvailableLookupTime();
            Assert.assertTrue(where + ": the first available lookup time moved back, " + first
                    + " < " + maxFirst, first >= maxFirst);
            maxFirst = first;

            for (Map.Entry<String, TreeMap<Long, byte[]>> e : model.entrySet()) {
                Assert.assertArrayEquals(where + ": " + e.getKey(),
                        e.getValue().lastEntry().getValue(), DbUtil.get(db, e.getKey()));
                for (long lt = Math.max(first, 1); lt <= time; lt += SEC / 7) {
                    Map.Entry<Long, byte[]> x = e.getValue().floorEntry(lt);
                    byte[] expected = x == null ? null : x.getValue();
                    Assert.assertArrayEquals(where + ": " + e.getKey() + " at " + lt, expected,
                            DbUtil.get(db, lt, e.getKey()));
                }
            }

            if (first > 0) {
                try {
                    DbUtil.get(db, first - 1, "/k/0");
                    throw new AssertionError(where + ": a lookup before the first available "
                            + "lookup time did not throw");
                } catch (LookupTimeNotAvailableException ex) {
                    // Expected.
                }
            }
        }

        void stop() {
            db.stop();
        }
    }

    /**
     * A smaller retain duration while an iteration runs. The cut that follows is decided with
     * the new duration.
     */
    @Nano
    public static void testShrinkDuringIteration() {
        Run run = new Run(1, 4 * SEC);
        for (int i = 0; i < 5000 && run.db.internal().reclaim().currentIteration() == null; i++) {
            run.put();
        }
        Assert.assertTrue("no iteration started",
                run.db.internal().reclaim().currentIteration() != null);
        Assert.assertEquals(0, run.stats.cuts.size());

        run.db.setRetainDuration(1 * SEC);
        run.putUntilCuts(1, 20000);
        Assert.assertEquals(1 * SEC, run.stats.cuts.get(0).retain);
        run.check("after the shrink");
        run.restart(1 * SEC);
        run.check("after the restart");
        run.stop();
    }

    /**
     * Several done iterations wait for the cut under a long duration; a short one makes them
     * all cuttable at once. The newest is chosen, and its conditions still hold.
     */
    @Nano("f")
    public static void testShrinkMakesSeveralRowsCuttable() {
        Run run = new Run(2, 40 * SEC);
        for (int i = 0; i < 6000 && run.db.getReclaimIterationCount() < 3; i++) {
            run.put();
        }
        Assert.assertTrue("iterations: " + run.db.getReclaimIterationCount(),
                run.db.getReclaimIterationCount() >= 3);
        Assert.assertEquals(0, run.stats.cuts.size());

        run.db.setRetainDuration(1 * SEC);
        run.putUntilCuts(1, 20000);
        run.check("after the shrink");
        run.restart(1 * SEC);
        run.puts(500);
        run.check("after the restart");
        run.stop();
    }

    /**
     * A larger retain duration after a cut was decided, before it is made. The decided cut is
     * made; the first available lookup time does not move back.
     */
    @Nano("f")
    public static void testGrowWithPendingCut() {
        Run run = new Run(3, 1 * SEC);
        for (int i = 0; i < 20000 && run.stream.getCut() == 0; i++) {
            run.put();
            run.db.sync(SyncLevel.ORDINARY);
        }
        Assert.assertTrue("no first cut", run.stream.getCut() > 0);

        // The next cut: stop right after the transaction that decides it.
        run.putUntilCuts(2, 20000);
        long first = run.db.getFirstAvailableLookupTime();
        long cutNow = run.stream.getCut();
        run.db.setRetainDuration(100 * SEC);

        for (int i = 0; i < 2000 && run.stream.getCut() == cutNow; i++) {
            run.put();
            run.db.sync(SyncLevel.ORDINARY);
        }
        Assert.assertTrue("the decided cut was not made", run.stream.getCut() > cutNow);
        Assert.assertEquals(first, run.db.getFirstAvailableLookupTime());
        run.check("after the growth");

        // With the longer duration, no new cut for a while, and the data stays.
        int cuts = run.stats.cuts.size();
        run.puts(500);
        Assert.assertEquals(cuts, run.stats.cuts.size());
        run.check("later");
        run.restart(100 * SEC);
        run.check("after the restart");
        run.stop();
    }

    /**
     * A restart with another retain duration: the same as changing it. After cuts, forever,
     * and then a short one again.
     */
    @Nano("f")
    public static void testRestartWithOtherRetention() {
        Run run = new Run(4, 1 * SEC);
        run.putUntilCuts(2, 20000);
        run.check("session 1");
        long first = run.db.getFirstAvailableLookupTime();
        Assert.assertTrue(first > 0);

        run.restart(FOREVER);
        Assert.assertEquals(first, run.db.getFirstAvailableLookupTime());
        run.check("forever, after the restart");
        run.puts(1000);
        Assert.assertEquals(0, run.stats.cuts.size());
        Assert.assertEquals(first, run.db.getFirstAvailableLookupTime());
        run.check("forever, later");

        run.restart(2 * SEC);
        Assert.assertEquals(first, run.db.getFirstAvailableLookupTime());
        run.putUntilCuts(1, 30000);
        Assert.assertTrue(run.db.getFirstAvailableLookupTime() > first);
        run.check("2 s");

        run.restart(5 * SEC);
        run.puts(300);
        run.check("5 s");
        run.stop();
    }

    /** A long history is made with forever; then a finite duration starts reclaim. */
    @Nano("f")
    public static void testForeverThenFinite() {
        Run run = new Run(5, FOREVER);
        run.puts(3000);
        Assert.assertEquals(0, run.db.getFirstAvailableLookupTime());
        Assert.assertEquals(0, run.db.getReclaimIterationCount());

        run.db.setRetainDuration(1 * SEC);
        run.putUntilCuts(1, 30000);
        run.check("after the first cut");
        run.restart(1 * SEC);
        run.check("after the restart");
        run.stop();
    }

    /**
     * A finite duration, then forever while an iteration runs: it ends, no new one starts.
     * Back to a finite duration, the cuts go on.
     */
    @Nano("f")
    public static void testFiniteThenForeverMidIteration() {
        Run run = new Run(6, 4 * SEC);
        for (int i = 0; i < 5000 && run.db.internal().reclaim().currentIteration() == null; i++) {
            run.put();
        }
        Assert.assertTrue("no iteration started",
                run.db.internal().reclaim().currentIteration() != null);

        run.db.setRetainDuration(FOREVER);
        run.puts(2000);
        long done = run.db.getReclaimIterationCount();
        Assert.assertTrue("the iteration did not end", done >= 1);
        Assert.assertTrue("no iteration in progress",
                run.db.internal().reclaim().currentIteration() == null);
        run.puts(2000);
        Assert.assertEquals(done, run.db.getReclaimIterationCount());
        Assert.assertEquals(0, run.stats.cuts.size());
        run.check("forever");

        run.db.setRetainDuration(1 * SEC);
        run.putUntilCuts(1, 30000);
        run.check("finite again");
        run.restart(1 * SEC);
        run.check("after the restart");
        run.stop();
    }

    /** A duration below one second is refused and changes nothing. */
    @Nano
    public static void testRetainDurationTooSmall() {
        Run run = new Run(7, 3 * SEC);
        try {
            run.db.setRetainDuration(SEC - 1);
            throw new AssertionError("a retain duration below 1 s was accepted");
        } catch (IllegalArgumentException e) {
            // Expected.
        }
        Assert.assertEquals(3 * SEC, run.db.getRetainDuration());
        run.stop();
    }
}
