package bergdb.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbException;
import bergdb.stream.CutStream;

/**
 * Tests of a record's room (bergdb 031-06, the review's F5 and F6): every record, its
 * action's KVs and the maintenance it carries together, makes dirty index nodes within
 * StoredTrans.dirtyLimit(), so that a later record takes them whole (Db.recordDirtyFits,
 * Reclaim.plan); an action alone is admitted within StoredTrans.actionDirtyLimit(); and a
 * record whose index nodes no later record could take fails the database before it is
 * appended (Db.checkTakeable), where before nothing failed and the startup pos stood before
 * it for good; the take keeps every record's set within the room that the check counts
 * (TransSeq.SetRoom; review-main, R2). At lowered record limits (StoredTrans.recordLimit, a test hook), with actions
 * near their limit, long keys of BergDB's own prefix and the largest values: the startup pos
 * moves, cuts are decided, the stream kept stays bounded, and the values are right, also
 * after a restart.
 */
public class ReclaimRoomTester {
    private static final long SEC = Clock.UNITS_PER_SEC;

    private ReclaimRoomTester() {}

    /** A key of 'segments' segments under BergDB's prefix "/#", as the review's RvLong. */
    static long[] longKey(String prefix, int segments) {
        StringBuilder k = new StringBuilder(prefix);
        for (int i = 0; i < segments - 1; i++) {
            k.append("/s").append(String.format("%04d", i % 10000));
        }
        return Keys.toSegments(k.toString());
    }

    /** What the hook saw of the records. */
    static final class Seen {
        long records;
        long maxSetBytes;           // a record's got-dirty set, as Db.checkTakeable counts it
        long maxSetNodes;
        long overDirtyLimit;        // records whose set passed dirtyLimit() (kept-dirty nodes)
        long maxRecord;             // bytes
        long overCap;               // records over StoredTrans.recordCap()
    }

    /** Installs a hook that measures every record (Db.TestHooks.beforeApply). */
    static Seen measure(final int maxNodeSize) {
        final Seen s = new Seen();
        final long nodeBytes = 32 + 16L * (maxNodeSize + 1) + 16;
        Db.testHooks = new Db.TestHooks() {
            public void beforeApply(Db.ExecuteData x) {
                long bytes = 0;
                for (Node n : x.transInfo.gotDirtyNodes) {
                    bytes += n.getType() == Node.TYPE_TOP_NODE ? StoredTrans.TOP_BYTES / 2
                            : nodeBytes;
                }
                s.records++;
                s.maxSetBytes = Math.max(s.maxSetBytes, bytes);
                s.maxSetNodes = Math.max(s.maxSetNodes, x.transInfo.gotDirtyNodes.size());
                if (bytes > StoredTrans.dirtyLimit()) s.overDirtyLimit++;
                final long size = x.trans.nextPos - x.trans.tpos;
                s.maxRecord = Math.max(s.maxRecord, size);
                if (size > StoredTrans.recordCap()) s.overCap++;
            }
            public void transExecuted(Db.ExecuteData x) {}
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) {}
        };
        return s;
    }

    /** A database at node size 8 or the default, on a CutStream, with its clock and model. */
    static final class Run {
        final boolean node8;
        CutStream stream = new CutStream();
        final CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        Db db;
        Reclaim.Stats stats;
        final Map<String, byte[]> model = new HashMap<String, byte[]>();
        final Map<String, long[]> keys = new HashMap<String, long[]>();

        Run(boolean node8, int sd) {
            this.node8 = node8;
            clock.setTime(time);
            start();
            db.setStartupDistance(sd);
            db.setRetainDuration(SEC);
        }

        void start() {
            DbBuilder b = Db.builder().testSetup(stream).clock(clock);
            if (node8) b.maxNodeSize8();
            db = b.start();
            synchronized (db.internal().getWriteLock()) {
                stats = db.internal().reclaim().enableStats();
            }
        }

        void restart() {
            db.close();
            stream = stream.copy();
            start();
        }

        void tick(long dt) {
            time += dt;
            clock.setTime(time);
        }

        /** Executes b, and on success puts its KVs in the model. */
        boolean exec(Trans.Builder b, Map<String, byte[]> puts) {
            try {
                db.execute(b.build());
            } catch (DbException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("005-31"));
                return false;
            }
            model.putAll(puts);
            return true;
        }

        /** Every key of the model at the latest time has its value. */
        void check(String at) {
            for (Map.Entry<String, byte[]> e : model.entrySet()) {
                final long[] k = keys.containsKey(e.getKey()) ? keys.get(e.getKey())
                        : Keys.toSegments(e.getKey());
                final byte[] got = db.getOne(Long.MAX_VALUE, k, db.newGetData());
                Assert.assertTrue(at + ": the value of " + e.getKey(),
                        Arrays.equals(e.getValue(), got));
            }
        }

        long kept() {
            return db.getStreamLength() - db.getFirstAvailablePos();
        }

        long section() {
            return db.getStreamLength() - db.internal().getStartupPosForEvict();
        }
    }

    /**
     * A sustained run at a lowered record limit: 3,000 cold keys and 20 long ones of 60
     * segments under "/#" (put by Trans.Builder.putLongKey), then actions of which a third
     * put kMin to kMax of 'hot' keys, many near or over the action's limit (the refused ones, by
     * 005-31, change nothing), the rest one to three, and a maintain() call every 100
     * actions. Every record's own index nodes are within dirtyLimit() by the counts before the
     * go point; the record's room cuts steps to their first KV to copy, or leaves them out of a
     * commit's record. Checked: no failure, so no record over StoredTrans.takeRoom(); the
     * startup pos moves in every window of 300 actions; cuts are decided; the stream kept in
     * the run's last third is at most 1.3 times its largest in the middle third; the values
     * are the model's, also after a restart.
     */
    static void sustained(boolean node8, long limit, int seed, int kMin, int kMax,
            int hot) {
        final long saved = StoredTrans.recordLimit;
        StoredTrans.recordLimit = limit;
        final Seen seen = measure(node8 ? 8 : 30);
        final Run run = new Run(node8, 20000);
        try {
            final Random r = new Random(seed);
            for (int i = 0; i < 3000; i += 100) {
                Trans.Builder b = run.db.trans();
                Map<String, byte[]> puts = new HashMap<String, byte[]>();
                for (int j = i; j < i + 100; j++) {
                    final byte[] v = new byte[50];
                    r.nextBytes(v);
                    final String k = String.format("/c/%05d", j);
                    b.put(k, v);
                    puts.put(k, v);
                }
                run.tick(SEC / 20);
                Assert.assertTrue("cold keys", run.exec(b, puts));
            }
            for (int j = 0; j < 20; j++) {
                final long[] k = longKey("/#t" + j, 60);
                final byte[] v = new byte[40];
                r.nextBytes(v);
                final String name = "long" + j;
                run.keys.put(name, k);
                Map<String, byte[]> puts = new HashMap<String, byte[]>();
                puts.put(name, v);
                run.tick(SEC / 20);
                Assert.assertTrue("a long key", run.exec(
                        run.db.trans().putLongKey(k, null, v, null), puts));
            }
            final int n = 3000;
            final long[] sp = new long[n / 300 + 1];
            long maxMiddle = 0, maxLast = 0, refused = 0, large = 0;
            for (int i = 0; i < n; i++) {
                run.tick(SEC / 20);
                if (i % 300 == 0) {
                    sp[i / 300] = run.db.internal().getStartupPosForEvict();
                }
                if (i % 100 == 99) {
                    run.db.maintain(Reclaim.MAINTAIN_MIN_BUDGET);
                }
                Trans.Builder b = run.db.trans();
                Map<String, byte[]> puts = new HashMap<String, byte[]>();
                final int k = r.nextInt(3) == 0 ? kMin + r.nextInt(kMax - kMin + 1)
                        : 1 + r.nextInt(3);
                for (int j = 0; j < k; j++) {
                    final String key = String.format("/h/%05d", r.nextInt(hot));
                    final byte[] v = new byte[20];
                    r.nextBytes(v);
                    b.put(key, v);
                    puts.put(key, v);
                }
                if (run.exec(b, puts)) {
                    if (k >= kMin) large++;
                } else {
                    refused++;
                }
                if (i >= n / 3 && i < 2 * n / 3) maxMiddle = Math.max(maxMiddle, run.kept());
                if (i >= 2 * n / 3) maxLast = Math.max(maxLast, run.kept());
            }
            sp[n / 300] = run.db.internal().getStartupPosForEvict();
            final String at = "node " + (node8 ? 8 : 30) + ", limit " + limit + ", seed " + seed;
            if (Boolean.getBoolean("roomtester.print")) {
                System.out.println(at + ": " + seen.records + " records, large actions taken "
                        + large + ", refused " + refused + "; steps cut to their first copy "
                        + run.stats.roomFirstCopy + ", left out " + run.stats.roomNoStep
                        + "; the largest set " + seen.maxSetNodes + " nodes, " + seen.maxSetBytes
                        + " bytes (dirtyLimit " + StoredTrans.dirtyLimit() + ", takeRoom "
                        + StoredTrans.takeRoom() + "), over dirtyLimit " + seen.overDirtyLimit
                        + "; cuts " + run.stats.cuts.size() + "; kept at most " + maxMiddle
                        + " (middle third), " + maxLast + " (last); the startup pos "
                        + Arrays.toString(sp) + ", section at the end " + run.section());
            }
            for (int w = 1; w < sp.length; w++) {
                Assert.assertTrue(at + ": the startup pos moves in window " + w + ": "
                        + Arrays.toString(sp), sp[w] > sp[w - 1]);
            }
            Assert.assertTrue(at + ": large actions taken " + large + ", refused " + refused,
                    large > 100);
            Assert.assertTrue(at + ": the record's room cut steps: " + run.stats.roomFirstCopy
                    + ", " + run.stats.roomNoStep, run.stats.roomFirstCopy > 0
                    && run.stats.roomNoStep > 0);
            Assert.assertTrue(at + ": cuts " + run.stats.cuts.size(), run.stats.cuts.size() >= 3);
            Assert.assertTrue(at + ": the stream kept, " + maxLast + " in the last third, "
                    + maxMiddle + " in the middle", maxLast <= maxMiddle * 13 / 10);
            Assert.assertTrue(at + ": no record over its cap", seen.overCap == 0);
            Assert.assertTrue(at + ": sets within takeRoom " + seen.maxSetBytes,
                    seen.maxSetBytes <= StoredTrans.takeRoom());
            run.check(at);
            run.restart();
            run.check(at + ", after a restart");
        } finally {
            Db.testHooks = null;
            StoredTrans.recordLimit = saved;
            run.db.close();
        }
    }

    /**
     * Seed 3 since 2026-11-27: with the take bounded by the room of the record's set
     * (TransSeq.SetRoom; review-main, R2) the run of seed 1 cut 252 steps to their first copy
     * and left none out of a commit's record, which the run must show; seed 3 cuts 117 and
     * leaves 2 out. Seed 2 since 031-06's landing, step 3 (the charge after the batch, a
     * commit's step up to twice the last record's allowance): seed 3 cut 93 and left none
     * out; seed 2 cuts 66 and leaves 2 out.
     */
    @Nano("f")
    public static void testSustainedLargeActionsNode8() {
        sustained(true, 100 * 1000, 2, 10, 80, 2000);
    }

    /**
     * Seed 6 since 031-06's landing, step 3: seed 2 cut 94 steps to their first copy and left
     * none out; seed 6 cuts 96 and leaves 5 out.
     */
    @Nano("f")
    public static void testSustainedLargeActionsNode30() {
        sustained(false, 200 * 1000, 6, 60, 250, 20000);
    }

    /**
     * A record whose index nodes no later record could take fails the database before it is
     * appended (Db.checkTakeable). A key of 600 segments under "/#": at a record limit of
     * 100 kB its transaction is refused by 005-31, with nothing written; admitted at the
     * release's limit, and the limit lowered to 100 kB after the admission (in the hook before
     * the plan), its record's set passes StoredTrans.takeRoom(): the database fails with the
     * check's Bug, nothing of the record is in the stream, and a restart has the database as
     * before it. Until 031-06 nothing failed: the take stopped at that record for good (the
     * review's RvLong with the limit lowered under such a record).
     */
    @Nano
    public static void testUntakeableRecordFails() {
        final long saved = StoredTrans.recordLimit;
        final Run run = new Run(true, 2000);
        try {
            run.tick(SEC / 20);
            run.exec(run.db.trans().put("/a", new byte[] {1}), new HashMap<String, byte[]>());
            final long[] k = longKey("/#u", 600);
            StoredTrans.recordLimit = 100 * 1000;
            final long length = run.stream.getLength();
            run.tick(SEC / 20);
            try {
                run.db.execute(run.db.trans().putLongKey(k, null, new byte[] {2}, null).build());
                throw new AssertionError("taken: a key whose index nodes pass the limit");
            } catch (DbException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("005-31"));
            }
            Assert.assertEquals("refused: nothing appended", length, run.stream.getLength());
            StoredTrans.recordLimit = saved;

            Db.testHooks = new Db.TestHooks() {
                public void beforePlan(Db.ExecuteData x) {
                    StoredTrans.recordLimit = 100 * 1000;
                }
                public void transExecuted(Db.ExecuteData x) {}
                public void valueNodeCreated(ValueNode node, long[] key) {}
                public void nodeTouched(Node node) {}
                public void nodeReplaced(Node node) {}
            };
            Throwable failure = null;
            try {
                run.db.execute(run.db.trans().putLongKey(k, null, new byte[] {2}, null).build());
            } catch (Throwable e) {
                failure = e;
            }
            Db.testHooks = null;
            StoredTrans.recordLimit = saved;
            Assert.assertTrue("failed", failure != null);
            Throwable c = failure;
            while (c.getCause() != null && !String.valueOf(c.getMessage()).contains("F5")) {
                c = c.getCause();
            }
            Assert.assertTrue(String.valueOf(failure), String.valueOf(c.getMessage())
                    .contains("more than a later record can take") && c instanceof bergdb.common.Bug);
            Assert.assertEquals("failed: nothing appended", length, run.stream.getLength());
            run.restart();
            Assert.assertTrue("not put", run.db.getOne(Long.MAX_VALUE, k, run.db.newGetData())
                    == null);
            Assert.assertTrue("/a", run.db.getOne(Long.MAX_VALUE, Keys.toSegments("/a"),
                    run.db.newGetData()) != null);
            run.tick(SEC / 20);
            run.db.execute(run.db.trans().putLongKey(k, null, new byte[] {2}, null).build());
            Assert.assertTrue("put after the restart", Arrays.equals(new byte[] {2},
                    run.db.getOne(Long.MAX_VALUE, k, run.db.newGetData())));
        } finally {
            Db.testHooks = null;
            StoredTrans.recordLimit = saved;
            run.db.close();
        }
    }

    /**
     * bergdb 031-06 (review-main, R2): at a lowered record limit, 100 kB at node size 8, with
     * a startup distance above it, 2 MB, 3,000 commits of one put of 30 bytes among 2,000
     * keys, then maintain() calls until they rest: the take of each record keeps its
     * got-dirty set within StoredTrans.takeRoom() by the take itself (TransSeq.SetRoom), so no
     * record fails the database at Db.checkTakeable(). Until 2026-11-27 the first call failed
     * it: its record took 596 index nodes smaller than the largest, many of which it kept
     * dirty, 119,552 bytes at the largest sizes against a room of 98,288 (the review's
     * RmRoomProbe). Checked: the first call moves the startup pos, the calls rest, a cut is
     * decided, every set is within takeRoom(), and the values are right, also after a restart.
     */
    @Nano
    public static void testTakeWithinTheSetRoom() {
        final long saved = StoredTrans.recordLimit;
        StoredTrans.recordLimit = 100 * 1000;
        final Seen seen = measure(8);
        final Run run = new Run(true, 2000 * 1000);
        try {
            Assert.assertTrue("a startup distance above the record limit",
                    run.db.getStartupDistance() > StoredTrans.recordLimit);
            final Random r = new Random(1);
            for (int i = 0; i < 3000; i++) {
                run.tick(SEC / 50);
                final int k = r.nextInt(2000);
                final byte[] v = new byte[30];
                r.nextBytes(v);
                final String key = "/d" + (k % 37) + "/e" + (k % 1009) + "/f" + k;
                final Map<String, byte[]> puts = new HashMap<String, byte[]>();
                puts.put(key, v);
                Assert.assertTrue("a commit", run.exec(run.db.trans().put(key, v), puts));
            }
            final long sp0 = run.db.internal().getStartupPosForEvict();
            int calls = 0, rest = 0;
            long sp1 = -1;
            while (calls < 100 && rest < 5) {
                run.tick(SEC / 2);
                final long length = run.db.getStreamLength();
                run.db.maintain(Reclaim.MAINTAIN_MAX_BUDGET);
                if (calls == 0) sp1 = run.db.internal().getStartupPosForEvict();
                calls++;
                rest = run.db.getStreamLength() == length ? rest + 1 : 0;
            }
            final String at = "after " + calls + " calls";
            Assert.assertTrue(at + ": the first call moves the startup pos, " + sp0 + " to "
                    + sp1, sp1 > sp0);
            Assert.assertTrue(at + ": they rest", rest == 5);
            Assert.assertTrue(at + ": cuts " + run.stats.cuts.size(), run.stats.cuts.size() >= 1);
            Assert.assertTrue(at + ": sets within takeRoom, " + seen.maxSetBytes,
                    seen.maxSetBytes <= StoredTrans.takeRoom());
            Assert.assertTrue(at + ": no record over its cap", seen.overCap == 0);
            run.check(at);
            run.restart();
            run.check(at + ", after a restart");
        } finally {
            Db.testHooks = null;
            StoredTrans.recordLimit = saved;
            run.db.close();
        }
    }

    /**
     * The review's F6: a key of 6,000 segments (42 kB) under "/#", which the Core accepts
     * through Trans.Builder.putLongKey (L2 is not checked for BergDB's own keys; L3 bounds
     * it), at the release's limits and node size 8, is copied by a commit's step: its record
     * makes more than 5,000 index nodes dirty, counted from the actual key (Db.recordDirtyFits),
     * within dirtyLimit(); the startup pos passes it, cuts are decided and cut the original
     * record away, and the value is right, also after a restart.
     */
    @Nano("f")
    public static void testLongKeyCopiedByAStep() {
        final Seen seen = measure(8);
        final Run run = new Run(true, 2000);
        try {
            final long[] k = longKey("/#u", 6000);
            final byte[] v = new byte[100];
            new Random(1).nextBytes(v);
            run.keys.put("long", k);
            final Map<String, byte[]> puts = new HashMap<String, byte[]>();
            puts.put("long", v);
            run.tick(SEC);
            Assert.assertTrue("the long key", run.exec(run.db.trans().putLongKey(k, null, v,
                    null), puts));
            final long first = run.db.getStreamLength();
            boolean copied = false;
            final Random r = new Random(2);
            for (int i = 0; i < 400; i++) {
                run.tick(SEC / 20);
                final byte[] val = new byte[3000];
                r.nextBytes(val);
                final Map<String, byte[]> p = new HashMap<String, byte[]>();
                p.put("/h/" + (i % 5), val);
                run.exec(run.db.trans().put("/h/" + (i % 5), val), p);
                final bergdb.dag.GetData gd = run.db.newGetData();
                run.db.getOne(Long.MAX_VALUE, k, gd);
                for (StoredNode sn : run.db.getTrans(gd.tpos).nodes) {
                    if (sn instanceof StoredValueNode
                            && Arrays.equals(k, ((StoredValueNode) sn).getKey())
                            && ((StoredValueNode) sn).isCopy()) {
                        copied = true;
                    }
                }
            }
            Assert.assertTrue("copied by a step", copied);
            long stepDirtied = 0;
            for (Reclaim.Stats.Iteration it : run.stats.iterations) {
                stepDirtied = Math.max(stepDirtied, it.maxStepDirtied);
            }
            Assert.assertTrue("a step's record made the key's nodes dirty: " + stepDirtied,
                    stepDirtied >= 5000);
            Assert.assertTrue("within dirtyLimit: " + seen.overDirtyLimit, seen.overDirtyLimit == 0);
            Assert.assertTrue("the original record cut away: " + run.db.getFirstAvailablePos(),
                    run.db.getFirstAvailablePos() >= first);
            Assert.assertTrue("the startup pos follows: " + run.section(),
                    run.section() < 4 * 2000 + 2 * 3100 + 100 * 1000);
            run.check("the long key");
            run.restart();
            run.check("the long key, after a restart");
        } finally {
            Db.testHooks = null;
            run.db.close();
        }
    }

    /**
     * The largest action next to the largest old value, at a record limit of 200 kB: two cold
     * values of 170,000 bytes, near StoredTrans.valueLimit() (175,000), each put alone, then
     * actions each of a value of 160,000 bytes and 40 small puts. A step carries an old value
     * of the largest size as its first KV (015-50's rule), in the record of such an action:
     * every record within StoredTrans.recordCap(), the big values copied, cuts decided, and the
     * values right, also after a restart.
     */
    @Nano("f")
    public static void testLargestActionNextToLargestOldValue() {
        final long saved = StoredTrans.recordLimit;
        StoredTrans.recordLimit = 200 * 1000;
        final Seen seen = measure(30);
        final Run run = new Run(false, 100 * 1000);
        try {
            final Random r = new Random(3);
            for (int j = 0; j < 2; j++) {
                final byte[] v = new byte[170 * 1000];
                r.nextBytes(v);
                final Map<String, byte[]> puts = new HashMap<String, byte[]>();
                puts.put("/big/" + j, v);
                run.tick(SEC / 10);
                Assert.assertTrue("a big value", run.exec(run.db.trans().put("/big/" + j, v),
                        puts));
            }
            long bigCopies = 0;
            for (int i = 0; i < 250; i++) {
                run.tick(SEC / 10);
                Trans.Builder b = run.db.trans();
                final Map<String, byte[]> puts = new HashMap<String, byte[]>();
                final byte[] v = new byte[160 * 1000];
                r.nextBytes(v);
                b.put("/hv/" + (i % 3), v);
                puts.put("/hv/" + (i % 3), v);
                for (int j = 0; j < 40; j++) {
                    final byte[] w = new byte[8];
                    r.nextBytes(w);
                    b.put("/s/" + r.nextInt(5000), w);      // not in the model
                }
                run.exec(b, puts);
            }
            for (Reclaim.Stats.Iteration it : run.stats.iterations) {
                bigCopies += it.valueBytes >= 170 * 1000 ? 1 : 0;
            }
            Assert.assertTrue("no record over its cap: " + seen.maxRecord + ", "
                    + StoredTrans.recordCap(), seen.overCap == 0);
            Assert.assertTrue("a record with a big copy and a big action: " + seen.maxRecord,
                    seen.maxRecord > 330 * 1000);
            Assert.assertTrue("iterations that copied a big value: " + bigCopies, bigCopies > 0);
            Assert.assertTrue("cuts " + run.stats.cuts.size(), run.stats.cuts.size() >= 2);
            run.check("big values");
            run.restart();
            run.check("big values, after a restart");
        } finally {
            Db.testHooks = null;
            StoredTrans.recordLimit = saved;
            run.db.close();
        }
    }
}
