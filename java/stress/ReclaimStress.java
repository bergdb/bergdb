package bergdb.core;

import java.util.*;

import bergdb.pub.util.Clock;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;

/**
 * Randomized stress test of reclaim (level 3, docs/levels.md), written
 * 2026-10-13, modeled on RestartStress. Reclaim is on (a retain duration of
 * 1 to 5 s), the stream is a CutStream, which refuses reads below the cut,
 * and the database is restarted between sessions. Before and after every
 * restart it checks, against a model with the full history:
 *
 *   - every key at the latest time;
 *   - random lookups at times from the first available lookup time
 *     (Db.getFirstAvailableLookupTime()) to now, and in the retention window
 *     [now - R, now];
 *   - the retention guarantee: first available lookup time <= now - R (with changes of the
 *     retain duration, see rchange below: every cut keeps the guarantee of the duration in
 *     force when it was decided, and the first available lookup time never moves back);
 *   - a lookup below the first available lookup time throws
 *     LookupTimeNotAvailableException.
 *
 * In package bergdb.core to reach Db internals.
 *
 * Usage: java [-Dprop=value ...] -cp bergdb.jar:. bergdb.core.ReclaimStress firstSeed rounds
 *
 * Properties:
 *   sessions=N, keys=N, sd=N, maxnode=N, retain=SECONDS  Override the random choice.
 *   trans=N     Up to N transactions per session (default 400).
 *   exhaustive=0  No exhaustive check. By default (2026-10-13, W5a), when there are at most 50
 *               keys and at most 200,000 (key, time) pairs, every key is checked at every
 *               transaction time from the first available lookup time, after each restart too
 *               (a cold cache: every surviving old version is read from the stream, which
 *               refuses reads below the cut), instead of 300 random lookups.
 *   rchange=0   Keep the retain duration of the round fixed. By default (2026-10-13,
 *               bergdb 011-04, W2) it is changed at restarts and during sessions, to 1,
 *               2, 5 s or forever (no reclaim), at random.
 *   del=0       No deletes.
 *   verbose=1   Print a line per session: stream length, cut, first available time.
 */
public class ReclaimStress {
    static final byte[] DELETED = new byte[0];
    static final boolean DEL = !"0".equals(System.getProperty("del"));
    static final boolean VERBOSE = "1".equals(System.getProperty("verbose"));
    static final long SEC = Clock.UNITS_PER_SEC;

    final long seed;
    final Random rnd;
    final String config;
    CutStream stream = new CutStream();
    CoreTestClock clock = new CoreTestClock();
    long time = SEC;
    final int startupDistance, maxNode, keyCount, sessions, retainSec;
    final boolean longKeys, stopBeforeRestart;
    final Map<String, TreeMap<Long, byte[]>> model = new HashMap<String, TreeMap<Long, byte[]>>();
    final List<Long> times = new ArrayList<Long>();
    final List<String> keys = new ArrayList<String>();
    long maxCut;
    static final boolean RCHANGE = !"0".equals(System.getProperty("rchange"));
    static final long FOREVER = Long.MAX_VALUE;
    static final boolean EXHAUSTIVE = !"0".equals(System.getProperty("exhaustive"));
    long exhaustiveChecks;          // Verifications that were exhaustive (statistics).
    long curRetain;                 // The retain duration now, in time units.
    boolean retainChanged;          // Whether it was ever changed from the round's retainSec.
    long maxFirst;                  // The largest first available lookup time seen so far.
    Reclaim.Stats stats;            // Of the current database.

    ReclaimStress(long seed) {
        this.seed = seed;
        rnd = new Random(seed);
        int[] sds = {1000, 3000, 10 * 1000, 20 * 1000};
        int[] mns = {0, 8, 14, 30, 62};
        int[] kcs = {5, 50, 500, 3000};
        int[] rs = {1, 2, 5};
        startupDistance = Integer.getInteger("sd", sds[rnd.nextInt(sds.length)]);
        maxNode = Integer.getInteger("maxnode", mns[rnd.nextInt(mns.length)]);
        keyCount = Integer.getInteger("keys", kcs[rnd.nextInt(kcs.length)]);
        sessions = Integer.getInteger("sessions", 5 + rnd.nextInt(26));
        retainSec = Integer.getInteger("retain", rs[rnd.nextInt(rs.length)]);
        longKeys = rnd.nextBoolean();
        stopBeforeRestart = rnd.nextBoolean();
        for (int i = 0; i < keyCount; i++) {
            keys.add(longKeys && i % 2 == 1 ? "/long/" + i : "/k/" + i);
        }
        config = "seed=" + seed + " sd=" + startupDistance + " maxnode=" + maxNode
                + " keys=" + keyCount + " sessions=" + sessions + " retain=" + retainSec
                + " long=" + longKeys + " stop=" + stopBeforeRestart;
    }

    Db start() {
        clock = new CoreTestClock();
        clock.setTime(time);
        DbBuilder b = Db.builder().testSetup(stream).clock(clock);
        b.startupDistance(startupDistance);
        if (maxNode == 8) b.maxNodeSize8();
        if (maxNode == 14) b.maxNodeSize14();
        if (maxNode == 30) b.maxNodeSize30();
        if (maxNode == 62) b.maxNodeSize62();
        Db db = b.build();
        db.start();
        if (curRetain == 0) {
            curRetain = retainSec * SEC;
        }
        if (RCHANGE && sessionCount > 0 && rnd.nextInt(2) == 0) {
            setRetain(db, randomRetain());
        }
        db.setRetainDuration(curRetain);
        stats = db.internal().reclaim().enableStats();
        if (db.getFirstAvailableLookupTime() < maxFirst) {
            throw new AssertionError("the first available lookup time moved back over a "
                    + "restart: " + db.getFirstAvailableLookupTime() + " < " + maxFirst);
        }
        return db;
    }

    int sessionCount;

    long randomRetain() {
        int[] rs = {1, 2, 5, 0};
        int r = rs[rnd.nextInt(rs.length)];
        return r == 0 ? FOREVER : r * SEC;
    }

    void setRetain(Db db, long retain) {
        curRetain = retain;
        retainChanged |= retain != retainSec * SEC;
        db.setRetainDuration(retain);
    }

    void session(Db db) {
        int transCount = 1 + rnd.nextInt(Integer.getInteger("trans", 400));
        for (int t = 0; t < transCount; t++) {
            if (RCHANGE && rnd.nextInt(80) == 0) {
                setRetain(db, randomRetain());
            }
            time += SEC / 100 + rnd.nextInt((int) (SEC / 10));
            clock.setTime(time);
            Map<String, byte[]> ops = new LinkedHashMap<String, byte[]>();
            int opCount = 1 + rnd.nextInt(rnd.nextInt(10) < 8 ? 3 : 40);
            for (int o = 0; o < opCount; o++) {
                String k = keys.get(rnd.nextInt(keyCount));
                if (DEL && rnd.nextInt(5) == 0) {
                    ops.put(k, DELETED);
                } else {
                    byte[] v = new byte[1 + rnd.nextInt(rnd.nextInt(10) == 0 ? 2000 : 60)];
                    rnd.nextBytes(v);
                    ops.put(k, v);
                }
            }
            Trans.Builder b = db.trans();
            for (Map.Entry<String, byte[]> e : ops.entrySet()) {
                if (e.getValue() == DELETED) b.delete(e.getKey());
                else b.put(e.getKey(), e.getValue());
            }
            Trans trans = b.build();
            db.execute(trans);
            times.add(trans.tt);
            for (Map.Entry<String, byte[]> e : ops.entrySet()) {
                TreeMap<Long, byte[]> h = model.get(e.getKey());
                if (h == null) model.put(e.getKey(), h = new TreeMap<Long, byte[]>());
                h.put(trans.tt, e.getValue());
            }
        }
    }

    byte[] expected(String k, long lookupTime) {
        TreeMap<Long, byte[]> h = model.get(k);
        if (h == null) return null;
        Map.Entry<Long, byte[]> e = h.floorEntry(lookupTime);
        if (e == null || e.getValue() == DELETED) return null;
        return e.getValue();
    }

    void dumpKey(String k) {
        TreeMap<Long, byte[]> h = model.get(k);
        StringBuilder b = new StringBuilder();
        if (h != null) {
            for (Map.Entry<Long, byte[]> e : h.entrySet()) {
                b.append(e.getKey()).append(e.getValue() == DELETED ? " delete, " : " put, ");
            }
        }
        System.out.println("DEBUG model history of " + k + ": " + b);
    }

    void verify(Db db, String where) {
        long now = times.get(times.size() - 1);
        long first = db.getFirstAvailableLookupTime();
        long windowStart = now - retainSec * SEC;
        if (!retainChanged && first > windowStart && first > times.get(0)) {
            throw new AssertionError(where + ": first available lookup time " + first
                    + " is inside the retention window, which starts at " + windowStart);
        }
        // With changes of the retain duration: every cut keeps the guarantee of the duration
        // in force when it was decided, and the first available lookup time never moves back.
        for (Reclaim.Stats.Cut c : stats.cuts) {
            if (c.retain != FOREVER && c.tEnd >= c.decidedTime - c.retain) {
                throw new AssertionError(where + ": the cut at time " + c.decidedTime
                        + " (first available lookup time " + c.tEnd + ") breaks its retain "
                        + "duration, " + c.retain);
            }
        }
        if (first < maxFirst) {
            throw new AssertionError(where + ": the first available lookup time moved back: "
                    + first + " < " + maxFirst);
        }
        maxFirst = first;
        for (String k : keys) {
            check(db, k, Long.MAX_VALUE, where + ", latest");
        }
        long lo = Math.max(first, times.get(0));
        for (int j = 0; j < 300; j++) {
            long lt = lo + (long) (rnd.nextDouble() * (now - lo));
            check(db, keys.get(rnd.nextInt(keyCount)), lt, where + ", from first available");
        }
        if (EXHAUSTIVE && keyCount <= 50) {
            int from = 0;
            while (from < times.size() && times.get(from) < first) from++;
            if ((long) (times.size() - from) * keyCount <= 200000) {
                exhaustiveChecks++;
                for (String k : keys) {
                    check(db, k, first, where + ", exhaustive, at the first available time");
                    for (int i = from; i < times.size(); i++) {
                        check(db, k, times.get(i), where + ", exhaustive");
                    }
                }
            }
        }
        if (!retainChanged) {
            long wlo = Math.max(windowStart, times.get(0));
            for (int j = 0; j < 100; j++) {
                long lt = wlo + (long) (rnd.nextDouble() * (now - wlo));
                check(db, keys.get(rnd.nextInt(keyCount)), lt, where + ", in retention window");
            }
        }
        if (first > 0) {
            try {
                DbUtil.get(db, first - 1, keys.get(0));
                throw new AssertionError(where + ": a lookup below the first available time "
                        + first + " did not throw");
            } catch (LookupTimeNotAvailableException e) {
                // Expected.
            }
        }
    }

    void check(Db db, String k, long lt, String where) {
        byte[] exp = expected(k, lt);
        byte[] act;
        try {
            act = DbUtil.get(db, lt, k);
        } catch (RuntimeException e) {
            throw new RuntimeException(where + ": get(" + k + ", " + lt + ") failed: " + e, e);
        }
        if (!Arrays.equals(exp, act)) {
            throw new AssertionError(where + ": key " + k + " at time " + lt + ": expected "
                    + (exp == null ? "null" : exp.length + " bytes") + ", got "
                    + (act == null ? "null" : act.length + " bytes"));
        }
    }

    void run() {
        Db db = start();
        for (int s = 0; s < sessions; s++) {
            session(db);
            verify(db, "session " + s + " before restart");
            maxCut = Math.max(maxCut, stream.getCut());
            if (VERBOSE) {
                System.out.println("  session " + s + ": stream " + stream.getLength()
                        + ", cut " + stream.getCut() + ", first available "
                        + db.getFirstAvailableLookupTime() + ", now " + time
                        + ", iterations " + db.getReclaimIterationCount());
            }
            long sum1 = DbUtil.checksum(db);
            db.sync(SyncLevel.STRONG);
            if (stopBeforeRestart) db.stop();
            stream = stream.copy();
            sessionCount++;
            Db before = db;
            try {
                db = start();
            } catch (RuntimeException e) {
                throw new RuntimeException("restart after session " + s + " (cut "
                        + stream.getCut() + "): startup failed: " + e, e);
            }
            if (!stopBeforeRestart) before.close();     // nothing else closes it (bergdb 005-55)
            long sum2 = DbUtil.checksum(db);
            if (sum1 != sum2) {
                throw new AssertionError("restart " + s + ": checksum differs");
            }
            verify(db, "after restart " + s);
        }
        db.stop();
    }

    public static void main(String[] args) {
        long first = Long.parseLong(args[0]);
        int rounds = Integer.parseInt(args[1]);
        int fails = 0, withCut = 0;
        long exhaustive = 0;
        long t0 = System.currentTimeMillis();
        for (long seed = first; seed < first + rounds; seed++) {
            ReclaimStress r = new ReclaimStress(seed);
            if (VERBOSE) System.out.println(r.config);
            try {
                r.run();
                if (r.maxCut > 0) withCut++;
                exhaustive += r.exhaustiveChecks;
            } catch (Throwable e) {
                fails++;
                exhaustive += r.exhaustiveChecks;
                if (r.maxCut > 0) withCut++;
                if (System.getProperty("dump") != null) r.dumpKey(System.getProperty("dump"));
                System.out.println("FAIL " + r.config);
                for (Throwable c = e; c != null; c = c.getCause() == c ? null : c.getCause()) {
                    System.out.println("     " + c);
                    StackTraceElement[] st = c.getStackTrace();
                    for (int i = 0; i < Math.min(Integer.getInteger("stack", 6), st.length); i++) {
                        System.out.println("       at " + st[i]);
                    }
                }
            }
        }
        if (Audit.EVERY > 0) System.out.println(Audit.summary());   // -Daudit=N (WP J1)
        System.out.println("Done: " + rounds + " rounds, " + fails + " failures, "
                + withCut + " rounds with a cut, "
                + (System.currentTimeMillis() - t0) / 1000 + " s, " + exhaustive
                + " exhaustive verifications.");
    }
}
