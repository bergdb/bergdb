import java.io.File;
import java.io.IOException;
import java.util.*;

import bergdb.core.*;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

/**
 * Randomized restart stress test for BergDB, using the core API (2017 source;
 * eviction settings were removed from the API in 2016-2017).
 * Written 2026-10-12 to reproduce ISSUE151111 ("occurs when restarting the
 * database several times under certain conditions"). Each round writes
 * random transactions in a number of sessions, restarts the database between
 * sessions, and compares it to an in-memory model with the full history,
 * before and after every restart.
 *
 * Usage: java [-Dprop=value ...] -cp bergdb.jar:. RestartStress firstSeed rounds
 *
 * Properties:
 *   defaults=true  Default Db settings: startupDistance 50 MB, no eviction,
 *                  default node size; 3000 keys.
 *   file=true      FileStream on disk (dir/db-SEED, dir from "dir", default ".")
 *                  instead of MemoryStream. Always stops before a restart.
 *   sessions=N     Number of sessions (restarts) per round.
 *   keys=N         Number of distinct keys, named /k/0 to /k/N-1. Keys of 7 or
 *                  more bytes (N > 1000) have two key segments.
 *   trans=N        Up to N transactions per session (default 400).
 *   valsize=N      Value size 1..N bytes.
 *   sd=N, maxnode=N  Override startupDistance and max node size (8, 14, 30, 62).
 *   del=0, big=0, multi=0     No deletes, no big values, one key per transaction.
 *   verbose=1      Print stream length after each session.
 *   restart=0      Do not restart between sessions (a baseline).
 *   history=count  Count wrong historical lookups instead of failing on the
 *                  first one; a round with only those is reported as HIST.
 *                  Lookups of the latest values still fail the round.
 */
public class RestartStress {
    static final byte[] DELETED = new byte[0];
    static final boolean FILE = Boolean.getBoolean("file");
    static final boolean DEL = !"0".equals(System.getProperty("del"));
    static final boolean BIG = !"0".equals(System.getProperty("big"));
    static final boolean MULTI = !"0".equals(System.getProperty("multi"));
    static final boolean VERBOSE = "1".equals(System.getProperty("verbose"));
    static final boolean RESTART = !"0".equals(System.getProperty("restart"));
    static final boolean HIST_COUNT = "count".equals(System.getProperty("history"));

    final long seed;
    final Random rnd;
    final String config;
    MemoryStream memStream = new MemoryStream();
    AppendOnlyStream fileStream;
    File dir;
    CoreTestClock clock = new CoreTestClock();
    long time = 10;
    int startupDistance, maxNode, keyCount, sessions;   // 0 means default
    boolean stopBeforeRestart, strongSync;
    Map<String, TreeMap<Long, byte[]>> model = new HashMap<String, TreeMap<Long, byte[]>>();
    List<Long> times = new ArrayList<Long>();
    int histBad;                // wrong historical lookups (history=count)
    String firstHist;

    RestartStress(long seed) {
        this.seed = seed;
        rnd = new Random(seed);
        int[] sds = {0, 100, 1000, 10 * 1000, 100 * 1000};
        startupDistance = sds[rnd.nextInt(sds.length)];
        int[] mns = {0, 8, 14, 30, 62};
        maxNode = mns[rnd.nextInt(mns.length)];
        rnd.nextInt(5);         // Was eviction setting; keeps the seeds of 2026-10-12.
        int[] kcs = {5, 50, 500, 3000};
        keyCount = kcs[rnd.nextInt(kcs.length)];
        sessions = 2 + rnd.nextInt(25);
        rnd.nextBoolean();      // Unused; keeps the seeds of 2026-10-12 reproducible.
        stopBeforeRestart = rnd.nextBoolean() || FILE;
        strongSync = rnd.nextBoolean();

        if (Boolean.getBoolean("defaults")) {
            startupDistance = 0;
            maxNode = 0;
            keyCount = 3000;
        }
        sessions = Integer.getInteger("sessions", sessions);
        keyCount = Integer.getInteger("keys", keyCount);
        startupDistance = Integer.getInteger("sd", startupDistance);
        maxNode = Integer.getInteger("maxnode", maxNode);

        config = "seed=" + seed + " startupDistance=" + startupDistance + " maxNode=" + maxNode
                + " keys=" + keyCount + " sessions=" + sessions
                + " stop=" + stopBeforeRestart + " strong=" + strongSync;
    }

    Db start(boolean create) {
        AppendOnlyStream stream = memStream;
        if (FILE) {
            if (create) {
                dir = new File(System.getProperty("dir", "."), "db-" + seed);
                dir.mkdirs();
            }
            try {
                fileStream = new FileStream(dir);
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
            stream = fileStream;
        }
        DbBuilder b = Db.builder().testSetup(stream).clock(clock);
        if (startupDistance > 0) b.startupDistance(startupDistance);
        if (maxNode == 8) b.maxNodeSize8();
        if (maxNode == 14) b.maxNodeSize14();
        if (maxNode == 30) b.maxNodeSize30();
        if (maxNode == 62) b.maxNodeSize62();
        return b.start();
    }

    String key(int i) {
        return "/k/" + i;
    }

    void session(Db db) {
        int transCount = 1 + rnd.nextInt(Integer.getInteger("trans", 400));
        int valsize = Integer.getInteger("valsize", 0);
        for (int t = 0; t < transCount; t++) {
            time += 1 + rnd.nextInt(20);
            clock.setTime(time);
            Map<String, byte[]> ops = new LinkedHashMap<String, byte[]>();
            int opCount = 1 + rnd.nextInt(rnd.nextInt(10) < 8 ? 3 : 40);
            if (!MULTI) opCount = 1;
            for (int o = 0; o < opCount; o++) {
                String k = key(rnd.nextInt(keyCount));
                if (rnd.nextInt(5) == 0 && DEL) {
                    ops.put(k, DELETED);
                } else {
                    int size = rnd.nextInt(10) == 0 && BIG ? rnd.nextInt(5000) : 1 + rnd.nextInt(60);
                    if (valsize > 0) size = 1 + rnd.nextInt(valsize);
                    byte[] v = new byte[size];
                    rnd.nextBytes(v);
                    if (size == 0) v = new byte[]{1};   // Empty array means DELETED.
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

    /** Checks the latest value of every key, then 300 random historical lookups. */
    void verify(Db db, String where) {
        for (int i = 0; i < keyCount; i++) {
            check(db, key(i), Long.MAX_VALUE, where);
        }
        for (int j = 0; j < 300 && !times.isEmpty(); j++) {
            long lt = times.get(rnd.nextInt(times.size())) + (rnd.nextBoolean() ? 0 : -1);
            String k = key(rnd.nextInt(keyCount));
            if (!HIST_COUNT) {
                check(db, k, lt, where);
                continue;
            }
            try {
                check(db, k, lt, where);
            } catch (Throwable e) {
                histBad++;
                if (firstHist == null) firstHist = e.toString();
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
        Db db = start(true);
        for (int s = 0; s < sessions; s++) {
            session(db);
            if (VERBOSE) {
                long length = FILE ? fileStream.getLength() : memStream.getLength();
                System.out.println("session " + s + " done, time " + time
                        + ", trans " + times.size() + ", stream " + length);
            }
            verify(db, "session " + s + " before restart");
            long sum1 = DbUtil.checksum(db);
            db.sync(strongSync ? SyncLevel.STRONG : SyncLevel.ORDINARY);
            if (!RESTART) continue;
            if (stopBeforeRestart) db.stop();
            if (!FILE) memStream = memStream.copy();    // Without stop: like a crash after sync.
            Db before = db;
            db = start(false);
            if (!stopBeforeRestart) before.close();     // nothing else closes it (bergdb 005-55)
            long sum2 = DbUtil.checksum(db);
            if (sum1 != sum2) {
                throw new AssertionError("restart " + s + ": checksum differs " + sum1 + " != " + sum2);
            }
            verify(db, "after restart " + s);
        }
        db.stop();
    }

    public static void main(String[] args) {
        long first = Long.parseLong(args[0]);
        int rounds = Integer.parseInt(args[1]);
        int fails = 0, histOnly = 0;
        long t0 = System.currentTimeMillis();
        for (long seed = first; seed < first + rounds; seed++) {
            RestartStress r = new RestartStress(seed);
            try {
                r.run();
                if (r.histBad > 0) {
                    histOnly++;
                    System.out.println("HIST " + r.config + ": " + r.histBad
                            + " wrong historical lookups, first: " + r.firstHist);
                }
            } catch (Throwable e) {
                fails++;
                System.out.println("FAIL " + r.config);
                System.out.println("     " + e);
                StackTraceElement[] st = e.getStackTrace();
                for (int i = 0; i < Math.min(6, st.length); i++) {
                    System.out.println("       at " + st[i]);
                }
            }
        }
        System.out.println("Done: " + rounds + " rounds, " + fails + " failures"
                + (HIST_COUNT ? ", " + histOnly + " with only historical errors" : "")
                + ", " + (System.currentTimeMillis() - t0) / 1000 + " s.");
    }
}
