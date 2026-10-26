package bergdb.core;

import java.io.File;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentSkipListMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.Clock;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.FileStream;
import bergdb.stream.ReadBelowFirstPosException;

/**
 * Concurrent readers while reclaim cuts the stream (level 3, bergdb 011-04, W1),
 * written 2026-10-13, modeled on ReclaimStress. Reader threads do random get and scan
 * operations at lookup times from the first available lookup time (mostly its old end) to
 * the last completed transaction, while the writer thread, the main thread, drives reclaim.
 * Each session starts from a restart, so that the cache is cold and reads go to the stream.
 *
 * The rule (decision D1 = A): an operation returns what the model says at its lookup time,
 * or throws LookupTimeNotAvailableException, because the lookup time was already before the
 * first available lookup time (expired at admission) or the cut overtook the operation
 * (expired during, with a ReadBelowFirstPosException as the cause). Nothing else is allowed,
 * and the writer must never fail. After each session, with the readers stopped, the same
 * checks as in ReclaimStress (every key, the retention guarantee) run, then a restart.
 *
 * The model is shared: the writer publishes its model frontier after execute() and all
 * model updates. Historical readers choose times up to that frontier. A latest request
 * may observe a newer database commit first; it waits for model publication at its actual
 * snapshot before comparing. The published frontier includes internal reclaim transactions.
 *
 * In package bergdb.core to reach Db internals.
 *
 * Usage: java [-Dprop=value ...] -cp bergdb.jar:. bergdb.core.ReclaimReaders firstSeed rounds
 *
 * Properties:
 *   disk=1      A FileStream (files are deleted) instead of a CutStream (exact cut).
 *   readers=N   Reader threads (default random, 2 to 4).
 *   sessions=N, keys=N, sd=N, maxnode=N, retain=SECONDS, trans=N, valsize=N  As in
 *               ReclaimStress; valsize is the largest value size (default 60, 1500 on disk).
 *   verbose=1   Print a line per session.
 *   evict=S     An eviction schedule (values, every or random; evictseed=N its seed), as for
 *               every stress program (Eviction; bergdb item 001, WP J5): slots change between
 *               memory and stream while the readers run.
 */
public class ReclaimReaders {
    static final byte[] DELETED = new byte[0];
    static final boolean DISK = "1".equals(System.getProperty("disk"));
    static final boolean VERBOSE = "1".equals(System.getProperty("verbose"));
    static final long SEC = Clock.UNITS_PER_SEC;

    final long seed;
    final Random rnd;
    final String config;
    final int startupDistance, maxNode, keyCount, sessions, retainSec, readerCount, valSize;
    final List<String> keys = new ArrayList<String>();
    final Map<String, long[]> segments = new HashMap<String, long[]>();
    final Map<String, String> keyOfSegments = new HashMap<String, String>();
    final ConcurrentHashMap<String, ConcurrentSkipListMap<Long, byte[]>> model =
            new ConcurrentHashMap<String, ConcurrentSkipListMap<Long, byte[]>>();
    final List<Long> times = new ArrayList<Long>();     // The writer thread only.

    volatile long lastCompleted;
    volatile boolean stopReaders;
    final AtomicReference<Throwable> failure = new AtomicReference<Throwable>();
    final AtomicLong okGets = new AtomicLong(), okScans = new AtomicLong();
    final AtomicLong expiredAtAdmission = new AtomicLong(), expiredDuring = new AtomicLong();
    long maxFirstPos;

    CutStream cutStream;
    File dir;
    AppendOnlyStream stream;
    CoreTestClock clock = new CoreTestClock();
    long time = SEC;

    ReclaimReaders(long seed) {
        this.seed = seed;
        rnd = new Random(seed * 0x9E3779B97F4A7C15L + 12345);
        int[] sds = {1000, 3000, 10 * 1000, 20 * 1000};
        int[] mns = {0, 8, 14, 30, 62};
        int[] kcs = {5, 50, 500};
        int[] rs = {1, 2, 5};
        startupDistance = Integer.getInteger("sd", sds[rnd.nextInt(sds.length)]);
        maxNode = Integer.getInteger("maxnode", mns[rnd.nextInt(mns.length)]);
        keyCount = Integer.getInteger("keys", kcs[rnd.nextInt(kcs.length)]);
        sessions = Integer.getInteger("sessions", 10 + rnd.nextInt(30));
        retainSec = Integer.getInteger("retain", rs[rnd.nextInt(rs.length)]);
        readerCount = Integer.getInteger("readers", 2 + rnd.nextInt(3));
        valSize = Integer.getInteger("valsize", DISK ? 1500 : 60);
        boolean longKeys = rnd.nextBoolean();
        for (int i = 0; i < keyCount; i++) {
            String k = longKeys && i % 2 == 1 ? "/long/" + i : "/k/" + i;
            keys.add(k);
            long[] segs = Keys.toSegments(k);
            segments.put(k, segs);
            keyOfSegments.put(Arrays.toString(segs), k);
        }
        config = "seed=" + seed + " sd=" + startupDistance + " maxnode=" + maxNode
                + " keys=" + keyCount + " sessions=" + sessions + " retain=" + retainSec
                + " readers=" + readerCount + " long=" + longKeys + " disk=" + DISK;
    }

    // ---- Database ----

    Db start(boolean first) throws Exception {
        if (DISK) {
            if (first) {
                dir = new File("build/readers-" + seed + "-" + System.nanoTime());
                dir.mkdirs();
            }
            stream = new FileStream(dir);
        } else {
            cutStream = cutStream == null ? new CutStream() : cutStream.copy();
            stream = cutStream;
        }
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
        db.setRetainDuration(retainSec * SEC);
        return db;
    }

    long firstPos() {
        return DISK ? ((FileStream) stream).getFirstPos() : cutStream.getCut();
    }

    // ---- Model ----

    byte[] expected(String k, long lookupTime) {
        ConcurrentSkipListMap<Long, byte[]> h = model.get(k);
        if (h == null) return null;
        Map.Entry<Long, byte[]> e = h.floorEntry(lookupTime);
        if (e == null || e.getValue() == DELETED) return null;
        return e.getValue();
    }

    // ---- Writer ----

    void session(Db db) {
        int transCount = 10 + rnd.nextInt(Integer.getInteger("trans", 300));
        for (int t = 0; t < transCount && failure.get() == null; t++) {
            time += SEC / 100 + rnd.nextInt((int) (SEC / 10));
            clock.setTime(time);
            Map<String, byte[]> ops = new LinkedHashMap<String, byte[]>();
            int opCount = 1 + rnd.nextInt(rnd.nextInt(10) < 8 ? 3 : 20);
            for (int o = 0; o < opCount; o++) {
                String k = keys.get(rnd.nextInt(keyCount));
                if (rnd.nextInt(5) == 0) {
                    ops.put(k, DELETED);
                } else {
                    byte[] v = new byte[1 + rnd.nextInt(valSize)];
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
            for (Map.Entry<String, byte[]> e : ops.entrySet()) {
                ConcurrentSkipListMap<Long, byte[]> h = model.get(e.getKey());
                if (h == null) {
                    model.putIfAbsent(e.getKey(), new ConcurrentSkipListMap<Long, byte[]>());
                    h = model.get(e.getKey());
                }
                h.put(trans.tt, e.getValue());
            }
            times.add(trans.tt);
            lastCompleted = db.lookupTime(Long.MAX_VALUE);  // Publishes the model updates above.
            if (t % 10 == 0) {
                db.sync(SyncLevel.ORDINARY);
            }
        }
    }

    // ---- Readers ----

    void fail(String what, Throwable e) {
        failure.compareAndSet(null, e == null ? new AssertionError(what)
                : new RuntimeException(what + ": " + e, e));
    }

    /** Wait for the oracle, not the database: a latest read can precede model publication. */
    boolean awaitModel(long actualLookupTime, String what) {
        long deadline = System.nanoTime() + 60L * 1000 * 1000 * 1000;
        while (actualLookupTime > lastCompleted) {
            if (failure.get() != null || stopReaders) {
                fail(what + ": model was not published through " + actualLookupTime, null);
                return false;
            }
            if (System.nanoTime() >= deadline) {
                fail(what + ": timed out waiting for model through " + actualLookupTime, null);
                return false;
            }
            java.util.concurrent.locks.LockSupport.parkNanos(100000);
        }
        return true;
    }

    /**
     * Classifies an exception from an operation at the requested 'lookupTime' (Long.MAX_VALUE:
     * the latest state, whose snapshot is the last transaction at the start of the
     * operation); false if it is a failure.
     */
    boolean expired(Db db, long lookupTime, Throwable e, String what) {
        if (!(e instanceof LookupTimeNotAvailableException)) {
            fail(what + " failed", e);
            return false;
        }
        boolean during = false;
        for (Throwable t = e; t != null; t = t.getCause() == t ? null : t.getCause()) {
            during |= t instanceof ReadBelowFirstPosException;
        }
        long first = db.getFirstAvailableLookupTime();
        if (lookupTime != Long.MAX_VALUE && lookupTime >= first) {
            fail(what + " expired although the lookup time is not before the first "
                    + "available lookup time " + first, e);
            return false;
        }
        if (lookupTime == Long.MAX_VALUE && !during) {
            fail(what + " expired at admission, which a read of the latest state cannot", e);
            return false;
        }
        (during ? expiredDuring : expiredAtAdmission).incrementAndGet();
        return true;
    }

    void getOne(Db db, Random rr, long lookupTime) {
        String k = keys.get(rr.nextInt(keyCount));
        String what = "get(" + k + ", " + lookupTime + ")";
        byte[] act;
        GetData gd = db.newGetData();
        gd.actualLookupTime = -1;
        try {
            act = db.getOne(lookupTime, segments.get(k), gd);
        } catch (Throwable e) {
            expired(db, gd.actualLookupTime >= 0 ? gd.actualLookupTime : lookupTime, e, what);
            return;
        }
        if (!awaitModel(gd.actualLookupTime, what)) {
            return;
        }
        byte[] exp = expected(k, gd.actualLookupTime);
        if (!Arrays.equals(exp, act)) {
            fail(what + " (actual lookup time " + gd.actualLookupTime + "): expected "
                    + (exp == null ? "null" : exp.length + " bytes")
                    + ", got " + (act == null ? "null" : act.length + " bytes"), null);
            return;
        }
        okGets.incrementAndGet();
    }

    void scan(final Db db, Random rr, long requested, final int limit, final long parkNanos) {
        String start = keys.get(rr.nextInt(keyCount));
        String what = "scan(" + start + ", " + requested + ")";
        GetMany g = db.newGetMany();
        g.actualLookupTime = -1;
        g.lookupTime = requested;
        g.startKey = segments.get(start);
        g.inclusive = true;     // [start, ...]; before 2026-10-13 the start key was not
                                // returned in a deep tree (GetMany.eqMatch, bergdb 011-04, "Level 3 follow-up").
        final int[] added = new int[1];
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                if (parkNanos > 0) {
                    java.util.concurrent.locks.LockSupport.parkNanos(parkNanos);
                }
                return ++added[0] >= limit ? ADD_AND_STOP : ADD;
            }
            public void eod() {}
        };
        boolean stoppedEarly;
        try {
            db.getMany(g);
        } catch (Throwable e) {
            expired(db, g.actualLookupTime >= 0 ? g.actualLookupTime : requested, e, what);
            return;
        }
        final long lookupTime = g.actualLookupTime;
        if (!awaitModel(lookupTime, what)) {
            return;
        }
        stoppedEarly = added[0] >= limit;
        Set<String> returned = new HashSet<String>();
        Kvt last = null;
        for (Kvt kvt : g.result) {
            last = kvt;
            String k = keyOfSegments.get(Arrays.toString(kvt.key));
            if (k == null) continue;        // An internal key.
            returned.add(k);
            byte[] exp = expected(k, lookupTime);
            if (exp == null || !Arrays.equals(exp, kvt.value)) {
                fail(what + ": key " + k + " returned, expected "
                        + (exp == null ? "no value" : exp.length + " bytes"), null);
                return;
            }
        }
        for (String k : keys) {
            long[] ks = segments.get(k);
            boolean inRange = Keys.compareKeys(g.startKey, ks) <= 0
                    && (!stoppedEarly || Keys.compareKeys(ks, last.key) <= 0);
            if (inRange && expected(k, lookupTime) != null && !returned.contains(k)) {
                fail(what + ": key " + k + " is missing from the result (" + g.result.size()
                        + " KVs, first " + (g.result.isEmpty() ? "-" : Arrays.toString(g.result.get(0).key))
                        + ", start " + Arrays.toString(g.startKey) + ")", null);
                return;
            }
        }
        okScans.incrementAndGet();
    }

    Thread startReader(final Db db, final int id) {
        Thread t = new Thread(new Runnable() {
            public void run() {
                Random rr = new Random(seed * 1000 + id + System.nanoTime() % 7);
                try {
                    while (!stopReaders && failure.get() == null) {
                        long last = lastCompleted;
                        long first = db.getFirstAvailableLookupTime();
                        if (last <= 0 || last < first) {
                            Thread.yield();
                            continue;
                        }
                        long span = last - first;
                        long lookupTime;
                        int r = rr.nextInt(10);
                        if (r < 5) {
                            lookupTime = first + (long) (rr.nextDouble() * span * 0.1);
                        } else if (r < 9) {
                            lookupTime = first + (long) (rr.nextDouble() * span);
                        } else if (r == 9 && rr.nextBoolean()) {
                            lookupTime = Long.MAX_VALUE;    // The latest state, a finite snapshot.
                        } else {
                            lookupTime = last;
                        }
                        if (id % 2 == 1) {
                            // A slow reader: a long scan, so that a cut can overtake it.
                            scan(db, rr, lookupTime, 200, 200 * 1000);
                        } else if (rr.nextInt(4) == 0) {
                            scan(db, rr, lookupTime, 40, 0);
                        } else {
                            getOne(db, rr, lookupTime);
                        }
                    }
                } catch (Throwable e) {
                    fail("reader " + id, e);
                }
            }
        });
        t.setName("reader-" + id);
        t.setDaemon(true);
        t.start();
        return t;
    }

    // ---- After a session: the checks of ReclaimStress, readers stopped ----

    void verify(Db db, String where) {
        long now = times.get(times.size() - 1);
        long first = db.getFirstAvailableLookupTime();
        long windowStart = now - retainSec * SEC;
        if (first > windowStart && first > times.get(0)) {
            throw new AssertionError(where + ": first available lookup time " + first
                    + " is inside the retention window, which starts at " + windowStart);
        }
        for (String k : keys) {
            check(db, k, Long.MAX_VALUE, where + ", latest");
        }
        long lo = Math.max(first, times.get(0));
        for (int j = 0; j < 300; j++) {
            long lt = lo + (long) (rnd.nextDouble() * (now - lo));
            check(db, keys.get(rnd.nextInt(keyCount)), lt, where + ", from first available");
        }
        for (int j = 0; j < Integer.getInteger("verifyscans", 100); j++) {
            long lt = lo + (long) (rnd.nextDouble() * (now - lo));
            scan(db, rnd, lt, 40, 0);
            if (failure.get() != null) {
                throw new AssertionError(where + ": " + failure.get(), failure.get());
            }
        }
    }

    void check(Db db, String k, long lt, String where) {
        byte[] exp = expected(k, lt);
        byte[] act = DbUtil.get(db, lt, k);
        if (!Arrays.equals(exp, act)) {
            throw new AssertionError(where + ": key " + k + " at time " + lt + ": expected "
                    + (exp == null ? "null" : exp.length + " bytes") + ", got "
                    + (act == null ? "null" : act.length + " bytes"));
        }
    }

    void run() throws Exception {
        Db db = start(true);
        try {
            for (int s = 0; s < sessions; s++) {
                stopReaders = false;
                List<Thread> readers = new ArrayList<Thread>();
                if (!times.isEmpty()) {
                    for (int i = 0; i < readerCount; i++) readers.add(startReader(db, i));
                }
                // The first session has nothing to read yet; its readers start after it.
                session(db);
                stopReaders = true;
                for (Thread t : readers) t.join(60 * 1000);
                for (Thread t : readers) {
                    if (t.isAlive()) fail("a reader did not end", null);
                }
                if (failure.get() != null) {
                    throw new RuntimeException("session " + s + ": " + failure.get(), failure.get());
                }
                maxFirstPos = Math.max(maxFirstPos, firstPos());
                verify(db, "session " + s + " before restart");
                if (VERBOSE) {
                    System.out.println("  session " + s + ": first pos " + firstPos()
                            + ", first available " + db.getFirstAvailableLookupTime()
                            + ", now " + time + ", gets " + okGets + ", scans " + okScans
                            + ", expired at admission " + expiredAtAdmission
                            + ", during " + expiredDuring);
                }
                db.sync(SyncLevel.STRONG);
                db.stop();
                db = start(false);
                verify(db, "after restart " + s);
            }
        } finally {
            stopReaders = true;
        }
        db.stop();
        if (DISK) {
            for (File f : dir.listFiles()) f.delete();
            dir.delete();
        }
    }

    public static void main(String[] args) throws Exception {
        long first = Long.parseLong(args[0]);
        int rounds = Integer.parseInt(args[1]);
        int fails = 0, withCut = 0;
        long gets = 0, scans = 0, atAdmission = 0, during = 0;
        long t0 = System.currentTimeMillis();
        for (long seed = first; seed < first + rounds; seed++) {
            ReclaimReaders r = new ReclaimReaders(seed);
            if (VERBOSE) System.out.println(r.config);
            try {
                r.run();
            } catch (Throwable e) {
                fails++;
                System.out.println("FAIL " + r.config);
                for (Throwable c = e; c != null; c = c.getCause() == c ? null : c.getCause()) {
                    System.out.println("     " + c);
                    StackTraceElement[] st = c.getStackTrace();
                    for (int i = 0; i < Math.min(Integer.getInteger("stack", 6), st.length); i++) {
                        System.out.println("       at " + st[i]);
                    }
                }
            }
            if (r.maxFirstPos > 0) withCut++;
            gets += r.okGets.get();
            scans += r.okScans.get();
            atAdmission += r.expiredAtAdmission.get();
            during += r.expiredDuring.get();
        }
        System.out.println("Done: " + rounds + " rounds, " + fails + " failures, "
                + withCut + " rounds with a cut, " + gets + " gets and " + scans
                + " scans correct, expired at admission " + atAdmission + ", expired during "
                + during + ", " + (System.currentTimeMillis() - t0) / 1000 + " s.");
        System.exit(fails == 0 ? 0 : 1);
    }
}
