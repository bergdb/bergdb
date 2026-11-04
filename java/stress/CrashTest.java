package bergdb.core;

import java.util.*;

import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.RecoverableStream;
import bergdb.stream.CutStream;

/**
 * Crash test, written 2026-10-13: INV-CRASH in bergdb 011-01. Cutting
 * the stream at any position must give the database state after the last
 * complete transaction before the cut, and the database must work on from
 * there.
 *
 * Writes random transactions (puts and deletes, 1 to 3 keys, now and then
 * up to 40) with a small startup distance, so that index nodes are written
 * and the startup pos moves (level 2). Then, for each cut: copies the
 * stream, cuts it, starts the database from it, and checks every key at the
 * latest time and random keys at earlier times against a model. Then it
 * runs more transactions, restarts once more without a cut, and checks
 * again.
 *
 * In package bergdb.core to reach Db internals.
 *
 * Usage: java [-Dprop=value ...] -cp bergdb.jar:. bergdb.core.CrashTest firstSeed rounds
 *
 * Properties:
 *   trans=N    Transactions before the cuts (default 2000).
 *   keys=N     Distinct keys /k/0 to /k/N-1 (default 300).
 *   cuts=N     Cuts per round (default 100); a third of them at or next to
 *              the end of a transaction.
 *   metacuts=N More cuts per round, at or next to a meta block's position
 *              (default 20): at it, 1 byte before it, in the block (1 and 127
 *              bytes after) and just after it (128 and 129). Also a cut at the
 *              end of each transaction that ends exactly at a meta block's
 *              position, where a crash can come between the transaction and
 *              the meta block (bergdb 005-27); such transactions are rare.
 *   sd=N       Startup distance in bytes (default 2000; 0: Db default).
 *   maxnode=N  Max node size: 8, 14, 30 or 62 (default: Db default).
 *   after=N    Transactions after each cut (default 50).
 *   retain=S   Reclaim on, with a retain duration of S seconds (level 3); transactions
 *              are then 0.01 to 0.2 s apart, the stream is a CutStream, which refuses
 *              reads below the front cut, and the tail is cut only after the last front
 *              cut was made (bytes a crash can lose). Lookups are checked from the
 *              first available lookup time.
 */
public class CrashTest {
    static final byte[] DELETED = new byte[0];
    final int transCount = Integer.getInteger("trans", 2000);
    final int keyCount = Integer.getInteger("keys", 300);
    final int cuts = Integer.getInteger("cuts", 100);
    final int metaCuts = Integer.getInteger("metacuts", 20);
    final int sd = Integer.getInteger("sd", 2000);
    final int maxNode = Integer.getInteger("maxnode", 0);
    final int after = Integer.getInteger("after", 50);
    final int retain = Integer.getInteger("retain", 0);
    final long timeScale = retain > 0 ? Clock.UNITS_PER_SEC / 100 : 1;

    final long seed;
    final Random rnd;

    // Per transaction i of the first run.
    final List<Map<String, byte[]>> ops = new ArrayList<Map<String, byte[]>>();
    final List<Long> times = new ArrayList<Long>();
    final List<Long> lastPos = new ArrayList<Long>();

    /** A metacut's offset from a meta block's position. */
    static final int[] META_OFFSETS = {-1, 0, 1, 127, 128, 129};
    /** Cuts at the end of a transaction that ends at a meta block's position. */
    int edgeCuts;

    CrashTest(long seed) {
        this.seed = seed;
        this.rnd = new Random(seed);
    }

    Db start(CutStream ms, CoreTestClock clock) {
        DbBuilder b = Db.builder().testSetup(ms).clock(clock);
        if (sd > 0) b.startupDistance(sd);
        if (maxNode == 8) b.maxNodeSize8();
        if (maxNode == 14) b.maxNodeSize14();
        if (maxNode == 30) b.maxNodeSize30();
        if (maxNode == 62) b.maxNodeSize62();
        Db db = b.start();
        if (retain > 0) db.setRetainDuration(retain * Clock.UNITS_PER_SEC);
        return db;
    }

    Map<String, byte[]> randomOps(Random r) {
        Map<String, byte[]> m = new LinkedHashMap<String, byte[]>();
        int n = 1 + r.nextInt(r.nextInt(10) == 0 ? 40 : 3);
        for (int o = 0; o < n; o++) {
            String k = "/k/" + r.nextInt(keyCount);
            if (r.nextInt(5) == 0) {
                m.put(k, DELETED);
            } else {
                byte[] v = new byte[1 + r.nextInt(60)];
                r.nextBytes(v);
                m.put(k, v);
            }
        }
        return m;
    }

    /** Executes the ops; returns {tt, lastPos}. */
    long[] execute(Db db, Map<String, byte[]> m) {
        Trans.Builder b = db.trans();
        for (Map.Entry<String, byte[]> e : m.entrySet()) {
            if (e.getValue() == DELETED) b.delete(e.getKey());
            else b.put(e.getKey(), e.getValue());
        }
        Trans t = b.build();
        final long[] pos = new long[1];
        t.listener = new Trans.Listener() {
            public void transExecuted(Db.ExecuteData x) { pos[0] = x.trans.lastPos; }
            public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}
        };
        db.execute(t);
        return new long[] {t.tt, pos[0]};
    }

    /** Model: key -> (time -> value), for the given list of ops and times. */
    static TreeMap<String, TreeMap<Long, byte[]>> model(List<Map<String, byte[]>> ops, List<Long> times) {
        TreeMap<String, TreeMap<Long, byte[]>> model = new TreeMap<String, TreeMap<Long, byte[]>>();
        for (int i = 0; i < ops.size(); i++) {
            for (Map.Entry<String, byte[]> e : ops.get(i).entrySet()) {
                TreeMap<Long, byte[]> h = model.get(e.getKey());
                if (h == null) model.put(e.getKey(), h = new TreeMap<Long, byte[]>());
                h.put(times.get(i), e.getValue());
            }
        }
        return model;
    }

    void verify(Db db, List<Map<String, byte[]>> ops, List<Long> times, Random r, String where) {
        TreeMap<String, TreeMap<Long, byte[]>> model = model(ops, times);
        for (int k = 0; k < keyCount; k++) {
            check(db, model, "/k/" + k, Long.MAX_VALUE, where);
        }
        for (int j = 0; j < 200 && !times.isEmpty(); j++) {
            long lt = times.get(r.nextInt(times.size())) - (r.nextBoolean() ? 0 : 1);
            if (lt < db.getFirstAvailableLookupTime()) continue;     // Cut by reclaim.
            check(db, model, "/k/" + r.nextInt(keyCount), lt, where);
        }
    }

    void check(Db db, TreeMap<String, TreeMap<Long, byte[]>> model, String k, long lt, String where) {
        byte[] exp = null;
        TreeMap<Long, byte[]> h = model.get(k);
        if (h != null) {
            Map.Entry<Long, byte[]> e = h.floorEntry(lt);
            if (e != null && e.getValue() != DELETED) exp = e.getValue();
        }
        byte[] act;
        try {
            act = DbUtil.get(db, lt, k);
        } catch (RuntimeException e) {
            throw new RuntimeException(where + ": get(" + k + ", " + lt + ") failed, first "
                    + "available lookup time " + db.getFirstAvailableLookupTime() + ": " + e, e);
        }
        if (!Arrays.equals(exp, act)) {
            throw new AssertionError(where + ": key " + k + " at time " + lt + ": expected "
                    + (exp == null ? "null" : exp.length + " bytes") + ", got "
                    + (act == null ? "null" : act.length + " bytes"));
        }
    }

    void run() {
        CutStream ms = new CutStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = start(ms, clock);
        long time = 1000;
        for (int i = 0; i < transCount; i++) {
            time += (1 + rnd.nextInt(20)) * timeScale;
            clock.setTime(time);
            Map<String, byte[]> m = randomOps(rnd);
            long[] r = execute(db, m);
            ops.add(m);
            times.add(r[0]);
            lastPos.add(r[1]);
        }
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        long length = ms.getLength();
        long first = Math.max(lastPos.get(0) + 1, ms.getLengthAtCut());

        for (int c = 0; c < cuts; c++) {
            long cut;
            int kind = rnd.nextInt(3);
            if (kind == 0) {
                // At, just before or just after the end of a transaction.
                cut = lastPos.get(rnd.nextInt(transCount)) + rnd.nextInt(3);
            } else {
                cut = first + (long) (rnd.nextDouble() * (length - first));
            }
            cut = Math.max(first, Math.min(length, cut));
            cutAndCheck(ms, cut, time);
        }

        // At the end of each transaction that ends at a meta block's position, then at or
        // next to meta block positions (metacuts).
        final long dist = RecoverableStream.META_BLOCK_DISTANCE;
        for (long p : lastPos) {
            if ((p + 1) % dist == 0 && p + 1 >= first) {
                edgeCuts++;
                cutAndCheck(ms, p + 1, time);
            }
        }
        long firstBlock = (first + dist - 1) / dist;
        long blocks = length / dist - firstBlock + 1;
        for (int c = 0; c < metaCuts && blocks > 0; c++) {
            long cut = (firstBlock + (long) (rnd.nextDouble() * blocks)) * dist
                    + META_OFFSETS[rnd.nextInt(META_OFFSETS.length)];
            cut = Math.max(first, Math.min(length, cut));
            cutAndCheck(ms, cut, time);
        }
    }

    void cutAndCheck(CutStream full, long cut, long lastTime) {
        String where = "seed " + seed + ", cut at " + cut + " of " + full.getLength()
                + (full.getCut() > 0 ? ", front cut at " + full.getCut() : "");
        CutStream ms = full.copy();
        ms.truncate(cut);

        // The transactions complete before the cut.
        int complete = 0;
        while (complete < transCount && lastPos.get(complete) < cut) complete++;
        List<Map<String, byte[]>> o = new ArrayList<Map<String, byte[]>>(ops.subList(0, complete));
        List<Long> t = new ArrayList<Long>(times.subList(0, complete));

        CoreTestClock clock = new CoreTestClock();
        clock.setTime(lastTime + 1);
        Db db;
        try {
            db = start(ms, clock);
        } catch (RuntimeException e) {
            throw new RuntimeException(where + ", " + complete + " complete transactions: startup failed: " + e, e);
        }
        Random r = new Random(seed * 1000003 + cut);
        verify(db, o, t, r, where + ", after the cut (" + complete + " transactions)");

        // Work on, restart, check.
        long time = lastTime + 1;
        for (int i = 0; i < after; i++) {
            time += (1 + r.nextInt(20)) * timeScale;
            clock.setTime(time);
            Map<String, byte[]> m = randomOps(r);
            long[] x = execute(db, m);
            o.add(m);
            t.add(x[0]);
        }
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        CoreTestClock clock2 = new CoreTestClock();
        clock2.setTime(time + 1);
        Db db2;
        try {
            db2 = start(ms.copy(), clock2);     // db.stop() closed ms.
        } catch (RuntimeException e) {
            throw new RuntimeException(where + ": restart after more transactions failed: " + e, e);
        }
        verify(db2, o, t, r, where + ", restarted after " + after + " more transactions");
        db2.stop();
    }

    public static void main(String[] args) {
        long firstSeed = Long.parseLong(args[0]);
        int rounds = Integer.parseInt(args[1]);
        int fails = 0;
        int edgeCuts = 0;
        long t0 = System.currentTimeMillis();
        for (long seed = firstSeed; seed < firstSeed + rounds; seed++) {
            CrashTest c = new CrashTest(seed);
            try {
                c.run();
            } catch (Throwable e) {
                fails++;
                System.out.println("FAIL seed " + seed + ": " + e);
                StackTraceElement[] st = e.getStackTrace();
                for (int i = 0; i < Math.min(8, st.length); i++) {
                    System.out.println("       at " + st[i]);
                }
                Throwable cause = e.getCause();
                if (cause != null && cause != e) {
                    System.out.println("     cause: " + cause);
                    st = cause.getStackTrace();
                    for (int i = 0; i < Math.min(8, st.length); i++) {
                        System.out.println("       at " + st[i]);
                    }
                }
            }
            edgeCuts += c.edgeCuts;
        }
        if (Audit.EVERY > 0) System.out.println(Audit.summary());   // -Daudit=N (WP J1)
        System.out.println("Done: " + rounds + " rounds, " + fails + " failures, "
                + (System.currentTimeMillis() - t0) / 1000 + " s. Cuts where a transaction "
                + "ends at a meta block's position: " + edgeCuts + ".");
    }
}
