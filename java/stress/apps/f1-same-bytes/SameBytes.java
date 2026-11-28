import bergdb.core.DatabaseId;
import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

/**
 * App f1 of 031-08 (part B): the README's "One stream" taken at its word, with the Core API.
 * "What is appended is decided by the stream so far and the transactions that follow, with
 * their times and order, and by nothing else. A restart or a stop changes no byte."
 *
 * A list of actions is made from the seed: transactions of puts and deletes over a universe
 * of keys of several shapes (large and small commits mixed, overwrites, deletes of runs of
 * keys), setRetainDuration() (1 to 3 s), setStartupDistance() (20 to 400 kB, so that reclaim
 * works hard), setReclaimInternalFraction(), maintain(budget), each at a time of a clock
 * that the app sets before the action (the same times in every run). The same list is run
 * in several ways, each on a new database made with the same DatabaseId (DbBuilder.id(), the
 * Pub API's builder method, so that two creations can give the same bytes) and the same
 * clock:
 *   ref      one start, every action, a file stream that forces each append;
 *   restart  a stop (half by stop() then close(), half close()) and a start after random
 *            actions, 1 in RESTART_EVERY;
 *   every    a stop and a start after every action;
 *   cache    a cache budget of 1 MB (eviction all the time) and three reader threads that
 *            scan and get at the latest and at older times (checked against the oracle) all
 *            through the run;
 *   nosync   a file stream that does not force appends, sync() after random actions, and
 *            random pauses of 0 to 120 ms (the buffer time, 50 ms, passes or not);
 *   quiet    each maintain(budget) replaced by calls of maintain(100), at the same clock,
 *            until a call writes nothing, with a stop and a start after one call in six;
 *            compared with quietbig, the same with calls of maintain(100000): the same parts
 *            in other calls (Db.maintain(): each part is an action of its own, with its time
 *            from the clock and one record, "planned under the write lock from the stream
 *            before the record"; "with the application idle, the calls then go quiet");
 *   stoptx   one transaction in three executed in another thread, a stop() 0 to 2 ms after it
 *            begins, a start; the transaction is in the stream whole (its commit had begun)
 *            or not at all (refused), and then executed again at the same clock;
 *   stopmid  each maintain(budget) a call of maintain(100000) in another thread, a stop()
 *            0 to 3 ms after it begins, a start, and calls of maintain(100) until quiet;
 *            compared with quietbig too;
 *   copy     at a random action the database is closed, its files copied to a new directory
 *            in the order of their names, and the run goes on in the copy;
 *   memory   a MemoryStream in place of the file stream.
 * Each run's stream must be byte for byte the ref's: the stream from the larger first
 * position to the end, the lengths, the first available position and time; and for the file
 * runs, the files (names, lengths, bytes). On a difference the first differing position is
 * printed with the action whose record holds it (the ref's stream length after each action).
 * Every run's latest state is checked against the oracle (a full scan), also after each
 * restart.
 *
 * Usage: java -cp bergdb-release.jar:out SameBytes SEED ACTIONS DIR [VARIANTS] [KEYS]
 *   VARIANTS: a comma list of the runs above but ref (ref always runs first), or "all"
 *   (default). Prints OK, or a FAILED line with the seed.
 */
public class SameBytes {
    static final long T0 = 1_780_000_000_000L * 10_000L;  // clock units, 100 ns
    static final long MS = Clock.UNITS_PER_SEC / 1000;
    static final int RESTART_EVERY = 25;
    static final boolean DEBUG = Boolean.getBoolean("f1.debug");
    static int fileNotes;
    static long stopRefused, stopCommitted;

    static long seed;
    static int nKeys;
    static List<byte[]> universe = new ArrayList<>();
    static List<Act> acts = new ArrayList<>();
    static long[] refLen;          // the ref's stream length after each action
    static File base;

    static final class Act {
        char kind;                 // T transaction, R retain, S startup distance, F fraction, M maintain
        long time;                 // the clock before the action
        List<byte[]> keys = new ArrayList<>();
        List<byte[]> vals = new ArrayList<>();   // null: a delete
        long arg;
        double frac;
        public String toString() {
            switch (kind) {
                case 'T': return "transaction of " + keys.size() + " KVs";
                case 'R': return "setRetainDuration(" + arg + ")";
                case 'S': return "setStartupDistance(" + arg + ")";
                case 'F': return "setReclaimInternalFraction(" + frac + ")";
                default: return "maintain(" + arg + ")";
            }
        }
    }

    public static void main(String[] a) throws Exception {
        seed = Long.parseLong(a[0]);
        int nActs = Integer.parseInt(a[1]);
        base = new File(a[2]);
        String vs = a.length > 3 ? a[3] : "all";
        nKeys = a.length > 4 ? Integer.parseInt(a[4]) : 1200;
        List<String> variants = vs.equals("all")
                ? Arrays.asList("restart", "cache", "nosync", "stoptx", "quiet", "stopmid", "copy", "memory", "every")
                : Arrays.asList(vs.split(","));
        Common.rmrf(base);
        base.mkdirs();
        makeUniverse();
        makeActs(nActs);
        long t0 = System.currentTimeMillis();
        try {
            Result ref = run("ref");
            log("ref: " + acts.size() + " actions, stream length " + ref.length + ", first available pos "
                    + ref.firstPos + ", files " + ref.files.size() + ", kept " + (ref.length - ref.firstPos)
                    + " bytes, reclaim iterations " + ref.iterations + ", " + ref.liveKeys + " live keys");
            Result quietRef = null;
            for (String v : variants) {
                // "every" (a stop and a start after each action) runs the first 400 actions only.
                // "quiet" is compared with "quietbig", not with the ref.
                if ((v.equals("quiet") || v.equals("stopmid")) && quietRef == null) {
                    quietRef = run("quietbig");
                    Common.rmrf(new File(base, "quietbig"));
                }
                Result r = run(v);
                compare(v, r, v.equals("quiet") || v.equals("stopmid") ? quietRef : ref);
                Common.rmrf(new File(base, v));
                Common.rmrf(new File(base, v + "-copy"));
            }
        } catch (Common.Fail e) {
            System.out.println("FAILED seed " + seed + ": " + e.getMessage());
            System.exit(1);
        }
        Common.rmrf(base);
        System.out.println("OK SameBytes seed " + seed + ", " + acts.size() + " actions, variants " + variants
                + ", " + fileNotes + " with other files (NOTE), stoptx: " + stopCommitted + " transactions committed at a stop, "
                + stopRefused + " refused and executed again"
                + ", " + (System.currentTimeMillis() - t0) / 1000 + " s");
    }

    // ------------------------------------------------------------------ the actions

    static void makeUniverse() {
        Random r = new Random(seed * 31 + 7);
        Set<Common.K> seen = new HashSet<>();
        byte[] shared = new byte[20];
        r.nextBytes(shared);
        shared[0] = 0x30;
        while (universe.size() < nKeys) {
            byte[] k;
            int s = r.nextInt(10);
            if (s < 3) {
                k = ("k" + r.nextInt(nKeys * 4)).getBytes();
            } else if (s < 5) {
                k = new byte[7 * (1 + r.nextInt(3))];
                r.nextBytes(k);
            } else if (s < 7) {
                k = new byte[22 + r.nextInt(90)];
                r.nextBytes(k);
                System.arraycopy(shared, 0, k, 0, 20);
            } else if (s < 9) {
                k = new byte[1 + r.nextInt(12)];
                r.nextBytes(k);
            } else {
                k = new byte[111];
                r.nextBytes(k);
            }
            if ((k[0] & 0xff) < 0x10) k[0] = (byte) (0x10 + (k[0] & 0x0f));   // never BergDB's 01 25
            if (seen.add(new Common.K(k))) universe.add(k);
        }
        universe.sort(Arrays::compareUnsigned);
    }

    static byte[] value(Random r) {
        int p = r.nextInt(1000);
        int len;
        if (p < 600) len = r.nextInt(61);
        else if (p < 880) len = 60 + r.nextInt(940);
        else if (p < 970) len = 1000 + r.nextInt(19_000);
        else if (p < 997) len = 20_000 + r.nextInt(180_000);
        else len = 300_000 + r.nextInt(700_000);
        byte[] v = new byte[len];
        r.nextBytes(v);
        return v;
    }

    /**
     * -Df1.big=true: one transaction in 25 is large, values of 1 to 8 MiB up to 30 MB a
     * transaction (the limits are 8 MiB a value and 32 MiB a transaction), so that records
     * cross many meta blocks and files and a kill tears them in the middle.
     */
    static final boolean BIG = Boolean.getBoolean("f1.big");

    static byte[] smallValue(Random r) {
        byte[] v = new byte[r.nextInt(101)];
        r.nextBytes(v);
        return v;
    }

    static void makeActs(int n) {
        Random r = new Random(seed);
        long t = T0;
        for (int i = 0; i < n; i++) {
            Act x = new Act();
            int p = r.nextInt(1000);
            int dt = r.nextInt(100);
            if (dt < 8) t += 0;                                   // the same clock: the next unit
            else if (dt < 75) t += MS * r.nextInt(20);
            else if (dt < 95) t += MS * (20 + r.nextInt(300));
            else t += MS * (1000 + r.nextInt(2500));               // past the retain duration
            x.time = t;
            if (i == 0 || (p < 6 && i > 10)) {
                x.kind = 'R';
                x.arg = (1000 + r.nextInt(2001)) * MS;
            } else if (i == 1 || p < 14) {
                x.kind = 'S';
                x.arg = 20_000 + r.nextInt(380_000);
            } else if (p < 17) {
                x.kind = 'F';
                x.frac = 0.1 + r.nextInt(8) / 10.0;
            } else if (p < 90) {
                x.kind = 'M';
                x.arg = r.nextInt(4) == 0 ? 100 + r.nextInt(400) : 100 + r.nextInt(5000);
            } else {
                x.kind = 'T';
                int q = r.nextInt(100);
                int ops = q < 65 ? 1 + r.nextInt(3) : q < 88 ? 4 + r.nextInt(46) : q < 97 ? 50 + r.nextInt(250)
                        : 300 + r.nextInt(201);
                boolean run = r.nextInt(10) == 0;                  // a run of keys in key order
                int start = r.nextInt(nKeys);
                boolean delRun = run && r.nextBoolean();
                boolean smallOnly = ops >= 50;                     // a large commit of small values
                boolean big = BIG && r.nextInt(25) == 0;
                if (big) { ops = 1 + r.nextInt(6); run = false; delRun = false; smallOnly = false; }
                Set<Common.K> inTx = new HashSet<>();
                long bytes = 0;
                for (int j = 0; j < ops; j++) {
                    byte[] k = run ? universe.get((start + j) % nKeys) : universe.get(r.nextInt(nKeys));
                    if (!inTx.add(new Common.K(k))) continue;
                    byte[] v;
                    if (big) {
                        v = new byte[1_000_000 + r.nextInt(7_388_608)];
                        r.nextBytes(v);
                        if (bytes + v.length > 30_000_000) v = null;
                    } else {
                        v = delRun || r.nextInt(100) < 30 ? null : smallOnly ? smallValue(r) : value(r);
                        if (v != null && bytes + v.length > 6_000_000) v = null;
                    }
                    if (v != null) bytes += v.length;
                    x.keys.add(k);
                    x.vals.add(v);
                }
            }
            acts.add(x);
        }
    }

    // ------------------------------------------------------------------ a run

    static final class Result {
        String name;
        long length, firstPos, firstTime, iterations, createdLen;
        int liveKeys;
        TreeMap<String, byte[]> files = new TreeMap<>();   // name -> bytes (file runs)
        byte[] mem;                                       // the memory stream's bytes from memFirst
        long memFirst;
        byte[] stream;                                    // every byte appended, from 0
        Tap tap;
        long[] lens;
    }

    /**
     * Every byte appended in a run, read from the storage after each action (a file storage's
     * files up to the durable length, so bytes that never change) and at the end, before a
     * cut can delete them; so the whole stream is compared, not only the files kept.
     */
    static final class Tap {
        long h;                                   // the next position to read
        List<long[]> at = new ArrayList<>();      // each chunk's position
        List<byte[]> chunks = new ArrayList<>();
        long gapBytes;                            // bytes cut before the tap read them (not the ref's)
        byte[] all(long len) {
            byte[] out = new byte[(int) len];
            for (int i = 0; i < chunks.size(); i++) {
                byte[] c = chunks.get(i);
                System.arraycopy(c, 0, out, (int) at.get(i)[0], c.length);
            }
            return out;
        }
        void add(byte[] b) { if (b.length > 0) { at.add(new long[] {h}); chunks.add(b); } h += b.length; }
    }

    static void tap(Run x, long durable) throws IOException {
        for (int k = 0; ; k++) {
            try {
                tap0(x, durable);
                return;
            } catch (java.io.FileNotFoundException gone) {
                // A cut's thread deleted a listed file: list again (the gap is then skipped).
                if (x.name.equals("ref") || k > 100) throw new Common.Fail(x.name + ": the tap missed bytes: " + gone);
            }
        }
    }

    static void tap0(Run x, long durable) throws IOException {
        Tap t = x.tap;
        long h0 = t.h, g0 = t.gapBytes;
        try {
            tap1(x, durable);
        } catch (java.io.FileNotFoundException e) {
            t.h = h0;
            t.gapBytes = g0;
            throw e;
        }
    }

    static void tap1(Run x, long durable) throws IOException {
        Tap t = x.tap;
        if (x.mem != null) {
            long len = Math.min(x.mem.getLength(), durable);
            if (len > t.h) {
                if (x.mem.getFirstPos() > t.h) {
                    if (x.name.equals("ref")) throw new Common.Fail("ref: the tap missed bytes " + t.h + " to " + x.mem.getFirstPos());
                    t.gapBytes += x.mem.getFirstPos() - t.h;
                    t.h = x.mem.getFirstPos();
                }
                byte[] b = new byte[(int) (len - t.h)];
                x.mem.read(t.h, b, 0, b.length);
                t.add(b);
            }
            return;
        }
        List<File> fs = listStreamFiles(x.dir);
        if (fs.isEmpty()) return;
        File last = fs.get(fs.size() - 1);
        long end = Math.min(durable, fileStart(last.getName()) + last.length());
        if (end <= t.h) return;
        long first = fileStart(fs.get(0).getName());
        if (first > t.h) {
            if (x.name.equals("ref")) throw new Common.Fail("ref: the tap missed bytes " + t.h + " to " + first + " (cut first)");
            t.gapBytes += first - t.h;
            t.h = first;
        }
        byte[] b = new byte[(int) (end - t.h)];
        long covered = t.h;
        for (int i = 0; i < fs.size(); i++) {
            File f = fs.get(i);
            long s0 = fileStart(f.getName());
            long s1 = i + 1 < fs.size() ? fileStart(fs.get(i + 1).getName()) : end;
            long a = Math.max(s0, t.h), e = Math.min(end, s1);
            if (a >= e) continue;
            if (a != covered) throw new java.io.FileNotFoundException("a hole at " + covered);
            try (java.io.RandomAccessFile raf = new java.io.RandomAccessFile(f, "r")) {
                raf.seek(a - s0);
                raf.readFully(b, (int) (a - t.h), (int) (e - a));
            } catch (java.io.EOFException eof) {
                throw new java.io.FileNotFoundException(f.getName() + " shorter than its place");
            }
            covered = e;
        }
        if (covered != end) throw new java.io.FileNotFoundException("read to " + covered + " of " + end);
        t.add(b);
    }

    static final class Run {
        Tap tap = new Tap();
        String name;
        Random r;
        Db db;
        File dir;
        Common.ManualClock clock = new Common.ManualClock(T0);
        boolean force = true;
        long cache = 0;
        MemoryStream mem;
        Common.Model m = new Common.Model();
        long restarts, readerChecks, maintainCalls;
    }

    static final DatabaseId ID;
    static {
        byte[] b = new byte[16];
        for (int i = 0; i < 16; i++) b[i] = (byte) (0x31 + i);
        ID = DatabaseId.createFromBytes(b);
    }

    static void start(Run x) throws IOException {
        AppendOnlyStream s;
        if (x.mem != null) {
            s = x.mem;
        } else {
            s = new FileStream(x.dir, x.force);
        }
        DbBuilder b = Db.builder().mainStream(s).clock(x.clock).id(ID);
        if (x.cache > 0) b.cacheSizeIndicator(x.cache);
        x.db = b.start();
    }

    static void close(Run x) throws IOException {
        if (x.r.nextBoolean()) x.db.stop();
        x.db.close();
        tap(x, Long.MAX_VALUE);
    }

    static Result run(String name) throws Exception {
        Run x = new Run();
        x.name = name;
        x.r = new Random(seed * 1000 + name.hashCode());
        x.dir = new File(base, name);
        Common.rmrf(x.dir);
        if (name.equals("memory")) x.mem = new MemoryStream();
        if (name.equals("nosync")) x.force = false;
        if (name.equals("cache")) x.cache = 1_000_000;
        x.clock.t.set(T0);
        start(x);
        x.db.sync(SyncLevel.ORDINARY);
        long createdLen = x.db.getStreamLength();
        tap(x, x.db.getDurableLength());
        int n = name.equals("every") ? Math.min(400, acts.size()) : acts.size();
        long[] lens = new long[n];
        int copyAt = name.equals("copy") ? 1 + x.r.nextInt(n - 1) : -1;
        AtomicBoolean stopReaders = new AtomicBoolean();
        AtomicReference<Throwable> readerFail = new AtomicReference<>();
        List<Thread> readers = new ArrayList<>();
        AtomicReference<Db> dbRef = new AtomicReference<>(x.db);
        AtomicLong readerChecks = new AtomicLong();
        if (name.equals("cache")) {
            for (int k = 0; k < 3; k++) {
                final int kk = k;
                Thread th = new Thread(() -> reader(x, dbRef, kk, stopReaders, readerFail, readerChecks));
                th.setDaemon(true);
                th.start();
                readers.add(th);
            }
        }
        for (int i = 0; i < n; i++) {
            Act act = acts.get(i);
            x.clock.t.set(act.time);
            if (name.equals("stoptx") && act.kind == 'T' && x.r.nextInt(3) == 0) {
                // A stop from another thread while the transaction runs: "a transaction whose commit
                // has begun completes", one that has not is refused and writes nothing (Database.stop());
                // after a start, a refused one is executed again at the same clock (RB-013's case).
                final Db d = x.db;
                long len0 = x.db.getStreamLength();
                AtomicReference<Trans> done = new AtomicReference<>();
                Thread th = new Thread(() -> {
                    try {
                        Trans.Builder b = d.trans();
                        for (int j = 0; j < act.keys.size(); j++) {
                            if (act.vals.get(j) == null) b.delete(act.keys.get(j)); else b.put(act.keys.get(j), act.vals.get(j));
                        }
                        Trans t = b.build();
                        d.execute(t);
                        done.set(t);
                    } catch (Throwable e) { /* refused by the stop */ }
                });
                th.start();
                if (x.r.nextBoolean()) Thread.sleep(x.r.nextInt(3));
                x.db.stop();
                th.join();
                x.db.close();
                tap(x, Long.MAX_VALUE);
                start(x);
                x.restarts++;
                long len1 = x.db.getStreamLength();
                if (len1 == len0) {
                    Common.check(done.get() == null, name + ": action " + i + " returned, and its record is not in the stream");
                    apply(x, act);
                    stopRefused++;
                } else {
                    Common.check(len1 == refLen[i], name + ": a stop during action " + i + " (" + act + ") left the stream at " + len1
                            + ", from " + len0 + "; the ref's after the action " + refLen[i]);
                    Map<Common.K, byte[]> ops = new LinkedHashMap<>();
                    for (int j = 0; j < act.keys.size(); j++) {
                        ops.put(new Common.K(act.keys.get(j)), act.vals.get(j) == null ? Common.DELETED : act.vals.get(j));
                    }
                    long tt = done.get() != null ? done.get().tt : act.time;
                    x.m.apply(ops, Math.max(tt, x.m.lastTime + 1));
                    stopCommitted++;
                }
            } else if (name.equals("stopmid") && act.kind == 'M') {
                // A stop from another thread while a call of maintain(100000) runs its parts, a
                // start, and then calls of maintain(100) until quiet: "a call that a crash or a
                // stop interrupts ... counts with the work it wrote" (031-05); compared with quietbig.
                final Db d = x.db;
                Thread th = new Thread(() -> {
                    try { d.maintain(100_000); } catch (Throwable e) { /* refused or stopped: as documented */ }
                });
                th.start();
                Thread.sleep(x.r.nextInt(4));
                long len0 = x.db.getStreamLength();
                x.db.stop();
                th.join();
                x.db.close();
                tap(x, Long.MAX_VALUE);
                start(x);
                x.restarts++;
                Common.check(x.db.getStreamLength() >= len0, name + ": a start after the stop in maintain() at action " + i
                        + " has a shorter stream");
                int calls = 0;
                while (true) {
                    long before = x.db.getStreamLength();
                    x.db.maintain(100);
                    if (x.db.getStreamLength() == before) break;
                    if (++calls > 20_000) throw new Common.Fail(name + ": action " + i + ": maintain() does not go quiet");
                }
                x.maintainCalls += calls;
            } else if (name.startsWith("quiet") && act.kind == 'M') {
                // maintain(budget) until a call writes nothing ("the calls then go quiet"),
                // in calls of 100 (with stops and starts between some) or of 100,000.
                int budget = name.equals("quietbig") ? 100_000 : 100;
                int calls = 0;
                while (true) {
                    long before = x.db.getStreamLength();
                    x.db.maintain(budget);
                    calls++;
                    if (x.db.getStreamLength() == before) break;
                    if (calls > 20_000) {
                        throw new Common.Fail(name + ": action " + i + ": 20,000 calls of maintain(" + budget
                                + ") at one clock time, and still writing, at length " + x.db.getStreamLength());
                    }
                    if (name.equals("quiet") && x.r.nextInt(6) == 0) {
                        long len = x.db.getStreamLength();
                        close(x);
                        start(x);
                        x.restarts++;
                        Common.check(x.db.getStreamLength() == len, name + ": the start between two calls of maintain() at action "
                                + i + " changed the stream length from " + len + " to " + x.db.getStreamLength());
                    }
                }
                x.maintainCalls += calls;
            } else {
                apply(x, act);
            }
            lens[i] = x.db.getStreamLength();
            if (name.equals("ref") || name.equals("quietbig")) x.db.sync(SyncLevel.ORDINARY);   // the reference taps all
            tap(x, x.db.getDurableLength());
            if (refLen != null && !name.startsWith("quiet") && !name.equals("stopmid") && lens[i] != refLen[i]) {
                throw new Common.Fail(name + ": after action " + i + " (" + act + ") the stream length is " + lens[i]
                        + ", the ref's " + refLen[i] + (i > 0 ? " (both " + refLen[i - 1] + " before? this run "
                        + lens[i - 1] + ")" : ""));
            }
            if (name.equals("nosync")) {
                int p = x.r.nextInt(10);
                if (p == 0) x.db.sync(SyncLevel.ORDINARY);
                else if (p < 3) Thread.sleep(x.r.nextInt(121));
            }
            if (DEBUG && x.mem == null) {
                List<File> fs = listStreamFiles(x.dir);
                System.out.println("D " + name + " " + i + " fap " + x.db.getFirstAvailablePos() + " file0 "
                        + (fs.isEmpty() ? -1 : fileStart(fs.get(0).getName())) + " files " + fs.size() + " len " + lens[i]);
            }
            boolean restart = name.equals("every") || (name.equals("restart") && x.r.nextInt(RESTART_EVERY) == 0);
            if (restart && i < n - 1) {
                close(x);
                start(x);
                x.restarts++;
                if (DEBUG) {
                    List<File> fs = listStreamFiles(x.dir);
                    System.out.println("D " + name + " " + i + " RESTART fap " + x.db.getFirstAvailablePos() + " file0 "
                            + (fs.isEmpty() ? -1 : fileStart(fs.get(0).getName())) + " files " + fs.size());
                }
                Common.check(x.db.getStreamLength() == lens[i], name + ": the start after action " + i
                        + " changed the stream length from " + lens[i] + " to " + x.db.getStreamLength());
                if (x.restarts % 10 == 1) Common.verifyFull(x.db, x.m, Long.MAX_VALUE, name + " after restart at " + i);
            }
            if (i == copyAt) {
                x.db.close();
                tap(x, Long.MAX_VALUE);
                File to = new File(base, name + "-copy");
                copyFiles(x.dir, to);
                x.dir = to;
                start(x);
                log("copy: the database copied after action " + i + " and continued in the copy");
            }
            dbRef.set(x.db);
            if (readerFail.get() != null) throw new Common.Fail(name + ": reader: " + readerFail.get());
        }
        stopReaders.set(true);
        for (Thread th : readers) th.join();
        if (readerFail.get() != null) {
            Throwable t = readerFail.get();
            t.printStackTrace(System.out);
            throw new Common.Fail(name + ": reader: " + t);
        }
        Common.verifyFull(x.db, x.m, Long.MAX_VALUE, name + " at the end");
        Result res = new Result();
        res.name = name;
        res.length = x.db.getStreamLength();
        res.firstPos = x.db.getFirstAvailablePos();
        res.firstTime = x.db.getFirstAvailableLookupTime();
        res.iterations = x.db.getReclaimIterationCount();
        res.liveKeys = x.m.liveCount();
        res.lens = lens;
        res.createdLen = createdLen;
        if (x.mem != null) {
            x.db.close();
            tap(x, Long.MAX_VALUE);
            res.memFirst = x.mem.getFirstPos();
            long len = x.mem.getLength();
            res.mem = new byte[(int) (len - res.memFirst)];
            x.mem.read(res.memFirst, res.mem, 0, res.mem.length);
        } else {
            close(x);
            for (File f : listStreamFiles(x.dir)) res.files.put(f.getName(), Files.readAllBytes(f.toPath()));
            // The closed database's files before the file that holds its first available position.
            long before = deadFileBytes(x.dir, res.firstPos);
            if (before > 0) {
                System.out.println("NOTE " + name + ": closed, the files hold " + before + " bytes before the file of the"
                        + " first available position " + res.firstPos);
            }
            // A start and a close with no action: the stream as it was, and the files then begin with
            // the file that holds the first available position (FileStream, "The files and the disk").
            start(x);
            Common.check(x.db.getStreamLength() == res.length && x.db.getFirstAvailablePos() == res.firstPos,
                    name + ": a start after the end changed the stream: length " + x.db.getStreamLength() + ", first pos "
                    + x.db.getFirstAvailablePos());
            x.db.close();
            long after = deadFileBytes(x.dir, res.firstPos);
            Common.check(after == 0, name + ": after a start and a close the files hold " + after + " bytes before the file of"
                    + " the first available position " + res.firstPos + ": " + summary(readAll(x.dir)));
            for (File f : listStreamFiles(x.dir)) {
                byte[] b = Files.readAllBytes(f.toPath());
                byte[] was = res.files.get(f.getName());
                Common.check(was != null && Arrays.equals(b, was), name + ": a start and a close changed file " + f.getName());
            }
        }
        Common.check(x.tap.h == res.length, name + ": the tap read to " + x.tap.h + " of a stream of " + res.length);
        res.stream = x.tap.all(res.length);
        res.tap = x.tap;
        if (name.equals("ref")) {
            refLen = lens;
        }
        log(name + ": done, " + x.restarts + " restarts, " + readerChecks.get() + " reader checks, "
                + x.maintainCalls + " maintain calls, stream "
                + res.length + ", " + res.files.size() + " files");
        return res;
    }

    static void apply(Run x, Act act) {
        Db db = x.db;
        switch (act.kind) {
            case 'R': db.setRetainDuration(act.arg); break;
            case 'S': db.setStartupDistance((int) act.arg); break;
            case 'F': db.setReclaimInternalFraction(act.frac); break;
            case 'M': db.maintain((int) act.arg); break;
            default:
                Trans.Builder b = db.trans();
                Map<Common.K, byte[]> ops = new LinkedHashMap<>();
                for (int j = 0; j < act.keys.size(); j++) {
                    byte[] v = act.vals.get(j);
                    if (v == null) b.delete(act.keys.get(j));
                    else b.put(act.keys.get(j), v);
                    ops.put(new Common.K(act.keys.get(j)), v == null ? Common.DELETED : v);
                }
                Trans t = b.build();
                db.execute(t);
                x.m.apply(ops, t.tt);
        }
    }

    /** Reads at the latest time and at older ones, each checked against the oracle. */
    static void reader(Run x, AtomicReference<Db> dbRef, int k, AtomicBoolean stop, AtomicReference<Throwable> fail,
            AtomicLong checks) {
        Random r = new Random(seed * 77 + k);
        while (!stop.get() && fail.get() == null) {
            Db db = dbRef.get();
            try {
                long last = x.m.lastTime;
                if (last < 0) { Thread.sleep(1); continue; }
                long t;
                if (r.nextBoolean()) t = Long.MAX_VALUE;
                else {
                    Long f = x.m.times.floorKey(last - r.nextInt(3000) * MS);
                    t = f == null ? last : f;
                }
                if (r.nextInt(3) == 0) {
                    GetMany g = db.newGetMany();
                    g.lookupTime = t;
                    db.getMany(g);
                    long actual = g.actualLookupTime;
                    if (actual > x.m.lastTime) continue;           // a commit not yet in the oracle
                    List<Kvt> got = new ArrayList<>();
                    for (Kvt kv : g.result) if (!Common.isBergKey(Keys.toBytes(kv.key))) got.add(kv);
                    Common.compareScan("reader full scan", got, x.m, actual, true);
                } else {
                    for (int j = 0; j < 20; j++) {
                        byte[] key = universe.get(r.nextInt(nKeys));
                        GetData gd = db.newGetData();
                        byte[] v = db.getOne(t, Keys.toSegments(key), gd);
                        long actual = gd.actualLookupTime;
                        if (actual > x.m.lastTime) continue;
                        byte[] exp = x.m.valueAt(new Common.K(key), actual);
                        if (!Arrays.equals(v, exp)) {
                            throw new Common.Fail("reader get of " + Common.hex(key) + " at " + actual + ": "
                                    + Common.hex(v) + ", the oracle " + Common.hex(exp));
                        }
                    }
                }
                checks.incrementAndGet();
            } catch (Throwable e) {
                if (Common.isNotAvailable(e)) continue;
                if (stop.get()) return;
                String s = String.valueOf(e);
                if (s.contains("IllegalDbState") || s.contains("Stopping") || s.contains("stopp")) continue;
                fail.compareAndSet(null, e);
                return;
            }
        }
    }

    // ------------------------------------------------------------------ files and comparison

    static List<File> listStreamFiles(File dir) {
        File[] fs = dir.listFiles((d, n) -> n.endsWith(".bergdb"));
        List<File> l = new ArrayList<>(fs == null ? List.of() : Arrays.asList(fs));
        l.sort(Comparator.comparing(File::getName));
        return l;
    }

    static void copyFiles(File from, File to) throws IOException {
        Common.rmrf(to);
        to.mkdirs();
        File[] fs = from.listFiles();
        Arrays.sort(fs, Comparator.comparing(File::getName));
        for (File f : fs) {
            if (f.getName().equals("bergdb.lock")) continue;
            Files.copy(f.toPath(), new File(to, f.getName()).toPath(), StandardCopyOption.COPY_ATTRIBUTES);
        }
    }

    /** The bytes of the files that end at or before pos (wholly before the file that holds pos). */
    static long deadFileBytes(File dir, long pos) {
        long n = 0;
        for (File f : listStreamFiles(dir)) {
            if (fileStart(f.getName()) + f.length() <= pos) n += f.length();
        }
        return n;
    }

    static TreeMap<String, byte[]> readAll(File dir) throws IOException {
        TreeMap<String, byte[]> m = new TreeMap<>();
        for (File f : listStreamFiles(dir)) m.put(f.getName(), new byte[(int) f.length()]);
        return m;
    }

    static long fileStart(String name) {
        return Long.parseLong(name.substring(0, name.indexOf('.'))) * 100_000L;
    }

    /** The bytes of a run's stream from position p to q (exclusive). */
    static byte[] streamBytes(Result r, long p, long q) {
        byte[] out = new byte[(int) (q - p)];
        if (r.mem != null) {
            System.arraycopy(r.mem, (int) (p - r.memFirst), out, 0, out.length);
            return out;
        }
        for (Map.Entry<String, byte[]> e : r.files.entrySet()) {
            long s = fileStart(e.getKey());
            long end = s + e.getValue().length;
            long a = Math.max(s, p), b = Math.min(end, q);
            if (a < b) System.arraycopy(e.getValue(), (int) (a - s), out, (int) (a - p), (int) (b - a));
        }
        return out;
    }

    static long streamFirst(Result r) {
        return r.mem != null ? r.memFirst : fileStart(r.files.firstKey());
    }

    static void compare(String name, Result r, Result ref) {
        List<String> diffs = new ArrayList<>();
        int n = r.lens.length;
        if (n == ref.lens.length) {
            if (r.length != ref.length) diffs.add("stream length " + r.length + ", the ref's " + ref.length);
            if (r.firstPos != ref.firstPos) diffs.add("first available pos " + r.firstPos + ", the ref's " + ref.firstPos);
            if (r.firstTime != ref.firstTime) diffs.add("first available time " + r.firstTime + ", the ref's " + ref.firstTime);
        }
        long end = r.lens[n - 1];
        long p = 0;
        if (end > ref.lens[n - 1]) diffs.add("length after the last action " + end + ", the ref's " + ref.lens[n - 1]);
        // Every byte appended (the taps), from 0 to the end of the shorter run.
        long diffAt = -1;
        long compared = 0;
        for (int c = 0; c < r.tap.chunks.size() && diffAt < 0; c++) {
            int a0 = (int) r.tap.at.get(c)[0];
            int m = (int) Math.min(r.tap.chunks.get(c).length, Math.min(end, ref.stream.length) - a0);
            if (m <= 0) continue;
            int mm = Arrays.mismatch(r.stream, a0, a0 + m, ref.stream, a0, a0 + m);
            if (mm >= 0) diffAt = a0 + mm;
            compared += m;
        }
        // And the files kept at the end, from the larger first position.
        long fp = Math.max(streamFirst(r), streamFirst(ref));
        if (diffAt < 0 && fp < end) {
            byte[] x = streamBytes(r, fp, end), y = streamBytes(ref, fp, end);
            int mm = Arrays.mismatch(x, y);
            if (mm >= 0) diffAt = fp + mm;
        }
        if (diffAt >= 0) {
            int act = 0;
            while (act < ref.lens.length && ref.lens[act] <= diffAt) act++;
            long recStart = act == 0 ? 0 : ref.lens[act - 1];
            diffs.add("the stream differs first at position " + diffAt + ", in the record(s) of action " + act + " ("
                    + (act < acts.size() ? acts.get(act).toString() : "?") + ", from " + recStart + " to "
                    + (act < ref.lens.length ? ref.lens[act] : -1) + ")");
            int a0 = (int) Math.max(0, diffAt - 16), b0 = (int) Math.min(Math.min(r.stream.length, ref.stream.length), diffAt + 48);
            System.out.println("  this run: " + Common.hex(Arrays.copyOfRange(r.stream, a0, b0)) + "\n  the ref:  "
                    + Common.hex(Arrays.copyOfRange(ref.stream, a0, b0)) + " (from " + a0 + ")");
            long nd = 0, firstSame = -1;
            long recEnd = act < ref.lens.length ? ref.lens[act] : diffAt + 1;
            for (long q = diffAt; q < Math.min(recEnd, Math.min(r.stream.length, ref.stream.length)); q++) {
                if (r.stream[(int) q] != ref.stream[(int) q]) nd++;
            }
            System.out.println("  bytes that differ in the action's records: " + nd + " of " + (recEnd - diffAt));
            int chunk = -1;
            for (int c = 0; c < r.tap.chunks.size(); c++) {
                long at = r.tap.at.get(c)[0];
                if (at <= diffAt && diffAt < at + r.tap.chunks.get(c).length) chunk = c;
            }
            if (chunk >= 0) System.out.println("  the tap's chunk " + chunk + " from " + r.tap.at.get(chunk)[0] + ", "
                    + r.tap.chunks.get(chunk).length + " bytes");
        }
        // The files, for file runs of the whole list: their split and the files kept after a cut
        // follow the timing of the writes (UB-1, 031-08 apps-b.md), so a difference is a NOTE.
        if (r.mem == null && n == ref.lens.length) {
            String fd = null;
            if (!r.files.keySet().equals(ref.files.keySet())) {
                fd = "the files differ: " + summary(r.files) + "; the ref's " + summary(ref.files);
            } else {
                for (String f : r.files.keySet()) {
                    if (!Arrays.equals(r.files.get(f), ref.files.get(f))) {
                        fd = "file " + f + " differs: " + r.files.get(f).length + " bytes, the ref's " + ref.files.get(f).length;
                        break;
                    }
                }
            }
            if (fd != null) {
                fileNotes++;
                System.out.println("NOTE " + name + ": the same stream, other files: " + (fd.length() > 600
                        ? fd.substring(0, 600) + "..." : fd));
            }
        }
        if (!diffs.isEmpty()) throw new Common.Fail(name + ": " + String.join("; ", diffs));
        log(name + ": the same bytes as the ref (" + compared + " bytes of stream compared, "
                + r.tap.gapBytes + " cut before the tap read them"
                + (r.mem == null ? ", " + r.files.size() + " files" : "") + ")");
    }

    static String summary(TreeMap<String, byte[]> files) {
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<String, byte[]> e : files.entrySet()) {
            if (sb.length() > 0) sb.append(' ');
            sb.append(e.getKey().replaceFirst("^0+(?=.)", "").replace(".bergdb", "")).append(':').append(e.getValue().length);
        }
        return sb.toString();
    }

    static void log(String s) {
        Common.log(s);
    }
}
