package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.pub.Connection;
import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.util.Clock;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.StorageInfo;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.FileStream;

/**
 * Probes of replication, bergdb item 005-11 (2026-10-22). Each probe runs the code as it
 * is (no change to java/) and prints what it finds; nothing here is a test of the build.
 * In package bergdb.core to reach Db internals (Reclaim.Stats, the cut decisions).
 *
 * Usage: tools/run.sh PROBE [args], or
 *   java -ea -da:bergdb.stream.MemoryStream -cp bergdb.jar:CLASSES bergdb.core.ReplicaProbe ...
 *
 *   identity              P1: replicas are byte copies; restart from a replica
 *   cuts SEEDS BT GATE [TRANS]
 *                         P2: a replica with reclaim's cuts; crash images at each cut.
 *                         BT: the replica's buffer time; GATE 1: its disk stalls for a
 *                         while. Properties: sd (startup distance, 2000), retain (s, 1),
 *                         step (ms between transactions, 50), value (max bytes, 30)
 *   addafter              P3: a replica added after cuts, also while writing
 *   restore               P4: an empty main with a replica (cut and not cut)
 *   crashsync DIR         P5: a crash (halt) in the middle of addReplica's copy
 *   fail                  P6: a replica whose writes fail; the Job of a failed add
 *   evict                 P7: a replica with eviction
 *   slow DIR              P8: sync levels with a replica; a slow and a hung replica
 *   diverge               P9: a restart without the replica, then with it
 *   pubapi                P10: the Pub API: order of replica() and dir(), encryption,
 *                         the main's own directory as a replica
 *   metaedge              P11 (not replication, found by P2): a crash image that ends
 *                         exactly at a meta block's position. Properties: trans (30000),
 *                         value (max bytes, 60)
 *
 * Temporary files go to java.io.tmpdir, or to the directory in the property tmp.
 */
public class ReplicaProbe {
    static final byte[] DELETED = new byte[0];
    static final long SEC = Clock.UNITS_PER_SEC;
    /** testSetup's main stream. */
    static final int MAIN_BS = 100 * 1000, MAIN_BT = 10;
    /** A replica of DbBuilder.stream(name, aos) and of Database.addReplica. */
    static final int REP_BS = 20 * 1000 * 1000, REP_BT = 2000;
    static File tmpRoot;

    public static void main(String[] args) throws Exception {
        tmpRoot = new File(System.getProperty("tmp", System.getProperty("java.io.tmpdir")),
                "replicaprobe-" + Long.toHexString(System.nanoTime()));
        String p = args[0];
        long t0 = System.nanoTime();
        if (p.equals("identity")) identity();
        else if (p.equals("cuts")) cuts(args);
        else if (p.equals("addafter")) addAfter();
        else if (p.equals("restore")) restore();
        else if (p.equals("crashsync")) crashSync(new File(args[1]));
        else if (p.equals("crashsync-child")) crashSyncChild(new File(args[1]));
        else if (p.equals("fail")) fail();
        else if (p.equals("evict")) evict();
        else if (p.equals("slow")) slow(new File(args[1]));
        else if (p.equals("diverge")) diverge();
        else if (p.equals("pubapi")) pubApi();
        else if (p.equals("metaedge")) metaEdge();
        else throw new IllegalArgumentException("probe " + p);
        System.out.printf("DONE %s in %.1f s%n", p, (System.nanoTime() - t0) * 1e-9);
        deleteTree(tmpRoot);
        System.exit(0);     // Threads of failed or hung streams may remain.
    }


    // ======== The history of a run, its model, and checks ========

    /** Per user transaction of a run: its operations, time and the position of its last byte. */
    static class History {
        final int keyCount;
        final List<Map<String, byte[]>> ops = new ArrayList<Map<String, byte[]>>();
        final List<Long> times = new ArrayList<Long>();
        final List<Long> lastPos = new ArrayList<Long>();

        History(int keyCount) {
            this.keyCount = keyCount;
        }

        /** The number of transactions complete in a stream of this length. */
        int completeIn(long length) {
            int n = 0;
            while (n < lastPos.size() && lastPos.get(n) < length) n++;
            return n;
        }

        /** Key to (time to value) after the first n transactions. */
        TreeMap<String, TreeMap<Long, byte[]>> model(int n) {
            TreeMap<String, TreeMap<Long, byte[]>> m = new TreeMap<String, TreeMap<Long, byte[]>>();
            for (int i = 0; i < n; i++) {
                for (Map.Entry<String, byte[]> e : ops.get(i).entrySet()) {
                    TreeMap<Long, byte[]> h = m.get(e.getKey());
                    if (h == null) m.put(e.getKey(), h = new TreeMap<Long, byte[]>());
                    h.put(times.get(i), e.getValue());
                }
            }
            return m;
        }
    }

    static Map<String, byte[]> randomOps(Random r, int keyCount, int maxValue) {
        Map<String, byte[]> m = new LinkedHashMap<String, byte[]>();
        int n = 1 + r.nextInt(r.nextInt(10) == 0 ? 40 : 3);
        for (int o = 0; o < n; o++) {
            String k = "/k/" + r.nextInt(keyCount);
            if (r.nextInt(5) == 0) {
                m.put(k, DELETED);
            } else {
                byte[] v = new byte[1 + r.nextInt(maxValue)];
                r.nextBytes(v);
                m.put(k, v);
            }
        }
        return m;
    }

    /**
     * Executes the operations and records them. A transaction that throws after it was
     * stored (the writer called transExecuted) is recorded too, and the exception rethrown.
     */
    static void execute(Db db, History h, Map<String, byte[]> m) {
        Trans.Builder b = db.trans();
        for (Map.Entry<String, byte[]> e : m.entrySet()) {
            if (e.getValue() == DELETED) b.delete(e.getKey());
            else b.put(e.getKey(), e.getValue());
        }
        Trans t = b.build();
        final long[] pos = new long[] {-1};
        t.listener = new Trans.Listener() {
            public void transExecuted(Db.ExecuteData x) { pos[0] = x.trans.lastPos; }
            public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}
        };
        try {
            db.execute(t);
        } finally {
            if (pos[0] >= 0) {
                h.ops.add(m);
                h.times.add(t.tt);
                h.lastPos.add(pos[0]);
            }
        }
    }

    /** What a check of a database against the model found. */
    static class Check {
        int checked, wrong, unavailable, errors;
        int latestBad;      // of them, lookups at the latest time
        String first;

        void problem(String s) {
            if (first == null) first = s;
        }

        boolean ok() {
            return wrong == 0 && unavailable == 0 && errors == 0;
        }

        public String toString() {
            return checked + " lookups, " + wrong + " wrong, " + unavailable
                    + " not available at a time from the first available lookup time on, "
                    + errors + " other errors (" + latestBad + " of the failed at the latest "
                    + "time)" + (first == null ? "" : "; first: " + first);
        }
    }

    /**
     * Checks every key at the latest time and at the first available lookup time, and 300
     * random lookups at times from it on, against the model of the first n transactions.
     */
    static Check verify(Db db, History h, int n, Random r, String where) {
        Check c = new Check();
        TreeMap<String, TreeMap<Long, byte[]>> model = h.model(n);
        for (int k = 0; k < h.keyCount; k++) {
            check(db, model, "/k/" + k, Long.MAX_VALUE, c, where);
        }
        c.latestBad = c.wrong + c.unavailable + c.errors;
        if (n == 0) return c;
        long first = Math.max(db.getFirstAvailableLookupTime(), h.times.get(0));
        long last = h.times.get(n - 1);
        if (first <= last) {
            for (int k = 0; k < h.keyCount; k++) {
                check(db, model, "/k/" + k, first, c, where);
            }
        }
        for (int j = 0; j < 300; j++) {
            long lt = h.times.get(r.nextInt(n)) - (r.nextBoolean() ? 0 : 1);
            if (lt < first) continue;
            check(db, model, "/k/" + r.nextInt(h.keyCount), lt, c, where);
        }
        return c;
    }

    static void check(Db db, TreeMap<String, TreeMap<Long, byte[]>> model, String k, long lt,
            Check c, String where) {
        byte[] exp = null;
        TreeMap<Long, byte[]> hist = model.get(k);
        if (hist != null) {
            Map.Entry<Long, byte[]> e = hist.floorEntry(lt);
            if (e != null && e.getValue() != DELETED) exp = e.getValue();
        }
        c.checked++;
        byte[] act;
        try {
            act = DbUtil.get(db, lt, k);
        } catch (LookupTimeNotAvailableException e) {
            c.unavailable++;
            c.problem(where + ": " + k + " at " + lt + ", first available "
                    + db.getFirstAvailableLookupTime() + ": " + e);
            return;
        } catch (RuntimeException e) {
            c.errors++;
            c.problem(where + ": " + k + " at " + lt + ": " + e);
            return;
        }
        if (!Arrays.equals(exp, act)) {
            c.wrong++;
            c.problem(where + ": " + k + " at " + lt + ": expected "
                    + (exp == null ? "null" : exp.length + " bytes") + ", got "
                    + (act == null ? "null" : act.length + " bytes"));
        }
    }


    // ======== Streams and starting ========

    /** A stream and its buffer, for DbBuilder.stream. */
    static class Spec {
        final String name;
        final AppendOnlyStream stream;
        final int bufferSize, bufferTime;

        Spec(String name, AppendOnlyStream stream, int bufferSize, int bufferTime) {
            this.name = name;
            this.stream = stream;
            this.bufferSize = bufferSize;
            this.bufferTime = bufferTime;
        }
    }

    static Spec spec(String name, AppendOnlyStream s, int bs, int bt) {
        return new Spec(name, s, bs, bt);
    }

    /**
     * Starts a database as the reclaim tests do: test clock, no eviction, nodes of 8, the
     * given startup distance; a retain duration of retainSec seconds if > 0.
     */
    static Db start(CoreTestClock clock, int sd, long retainSec, Spec... specs) {
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        for (Spec s : specs) b.stream(s.name, s.stream, s.bufferSize, s.bufferTime);
        b.clock(clock).maxNodeSize8().startupDistance(sd);
        Db db = b.start();
        if (retainSec > 0) db.setRetainDuration(retainSec * SEC);
        return db;
    }

    static Db startAt(long time, int sd, Spec... specs) {
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(time);
        return start(clock, sd, 0, specs);
    }

    /**
     * A test stream that keeps a copy of itself at each cut: what a crash at that moment
     * leaves (the bytes it has are the ones appended to it, as a FileStream's are forced).
     */
    static class SnapCutStream extends CutStream {
        final List<CutStream> images = new ArrayList<CutStream>();
        volatile boolean snap = true;

        public synchronized void pretruncate(long position) throws IOException {
            super.pretruncate(position);
            if (snap) images.add(copy());
        }
    }

    /**
     * A stream wrapper: appends can be held (a disk that stalls), fail, be slow or limited
     * in bandwidth. pretruncate is passed on at once.
     */
    static class GateStream implements AppendOnlyStream {
        final AppendOnlyStream inner;
        private boolean open = true;
        volatile long failAfter = Long.MAX_VALUE;   // bytes; the append that would pass it throws
        volatile int delayMs = 0;                   // per append
        volatile long bytesPerSec = 0;              // 0: no limit
        volatile long appended = 0;
        volatile int waiting = 0;                   // appends waiting at a hold

        GateStream(AppendOnlyStream inner) {
            this.inner = inner;
            this.appended = inner.getLength();
        }

        synchronized void hold() {
            open = false;
        }

        synchronized void release() {
            open = true;
            notifyAll();
        }

        public void append(byte[] source, int offset, int length) throws IOException {
            synchronized (this) {
                while (!open) {
                    waiting++;
                    try {
                        wait();
                    } catch (InterruptedException e) {
                        throw new IOException("interrupted");
                    } finally {
                        waiting--;
                    }
                }
            }
            if (appended + length > failAfter) {
                throw new IOException("GateStream: injected write failure at " + appended);
            }
            try {
                if (delayMs > 0) Thread.sleep(delayMs);
                if (bytesPerSec > 0) Thread.sleep(length * 1000L / bytesPerSec);
            } catch (InterruptedException e) {
                throw new IOException("interrupted");
            }
            inner.append(source, offset, length);
            appended += length;
        }

        public long getLength() { return inner.getLength(); }
        public long getFirstPos() { return inner.getFirstPos(); }
        public void read(long p, byte[] d, int o, int n) throws IOException { inner.read(p, d, o, n); }
        public void pretruncate(long p) throws IOException { inner.pretruncate(p); }
        public void seekFirstPos(long p) throws IOException { inner.seekFirstPos(p); appended = p; }
        public void close() throws IOException { inner.close(); }
    }

    /** The first position in [from, to) where a and b differ, or -1. */
    static long firstDifference(AppendOnlyStream a, AppendOnlyStream b, long from, long to)
            throws IOException {
        byte[] x = new byte[64 * 1024];
        byte[] y = new byte[64 * 1024];
        for (long p = from; p < to; ) {
            int n = (int) Math.min(x.length, to - p);
            a.read(p, x, 0, n);
            b.read(p, y, 0, n);
            for (int i = 0; i < n; i++) {
                if (x[i] != y[i]) return p + i;
            }
            p += n;
        }
        return -1;
    }

    /** Compares two streams over the range both have; prints and returns the result. */
    static long compare(String what, AppendOnlyStream a, AppendOnlyStream b) throws IOException {
        long from = Math.max(a.getFirstPos(), b.getFirstPos());
        long to = Math.min(a.getLength(), b.getLength());
        long d = firstDifference(a, b, from, to);
        System.out.println("  " + what + ": lengths " + a.getLength() + " and " + b.getLength()
                + ", first positions " + a.getFirstPos() + " and " + b.getFirstPos() + "; bytes "
                + from + " to " + to + (d == -1 ? " equal" : " DIFFER first at " + d));
        return d;
    }

    static File dir(String name) {
        File d = new File(tmpRoot, name);
        deleteTree(d);
        d.mkdirs();
        return d;
    }

    static void deleteTree(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File g : fs) deleteTree(g);
        f.delete();
    }

    static void sleep(long ms) {
        try {
            Thread.sleep(ms);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    static String infos(StorageInfo[] infos) {
        StringBuilder b = new StringBuilder();
        for (StorageInfo s : infos) {
            if (b.length() > 0) b.append("; ");
            String st = s.getStatus() == StorageInfo.STATUS_ACTIVE ? "ACTIVE"
                    : s.getStatus() == StorageInfo.STATUS_ERROR ? "ERROR" : "INITIALIZING";
            b.append(s.getName()).append(" ").append(st).append(" (").append(s.getStatusString())
                    .append(")");
        }
        return b.toString();
    }

    static String ex(Throwable e) {
        return e.getClass().getSimpleName() + ": " + e.getMessage();
    }

    /** Runs n random transactions, dt time units apart. Returns the last time. */
    static long run(Db db, CoreTestClock clock, History h, Random r, long time, int n, long dt,
            int maxValue) {
        for (int i = 0; i < n; i++) {
            time += dt;
            clock.setTime(time);
            execute(db, h, randomOps(r, h.keyCount, maxValue));
        }
        return time;
    }


    // ======== P1: byte copies ========

    static void identity() throws Exception {
        System.out.println("P1. Replicas are byte copies of the main stream; restart from one.");
        for (int bt : new int[] {MAIN_BT, REP_BT}) {
            CutStream main = new CutStream();
            CutStream rep = new CutStream();
            CoreTestClock clock = new CoreTestClock();
            long time = 1000;
            clock.setTime(time);
            Db db = start(clock, 2000, 0, spec("main", main, MAIN_BS, MAIN_BT),
                    spec("r", rep, REP_BS, bt));
            History h = new History(300);
            Random r = new Random(1);
            time = run(db, clock, h, r, time, 3000, 13, 60);
            long t1 = System.nanoTime();
            db.sync(SyncLevel.STRONG);
            double strongMs = (System.nanoTime() - t1) * 1e-6;
            db.close();
            System.out.printf("Core, replica buffer time %d ms; 3000 transactions, no reclaim; a "
                    + "STRONG sync took %.0f ms; close():%n", bt, strongMs);
            compare("main and replica", main.copy(), rep.copy());
            Db db2 = startAt(time + 1, 2000, spec("main", rep.copy(), MAIN_BS, MAIN_BT));
            Check c = verify(db2, h, h.ops.size(), new Random(2), "replica alone");
            System.out.println("  started from the replica alone: " + c);
            db2.close();
        }

        // The Pub API, FileStreams: dir() and replica(), then addReplica() while running.
        File d = dir("p1");
        String md = new File(d, "main").getPath();
        String rd = new File(d, "r").getPath();
        String ad = new File(d, "added").getPath();
        Database db = Factory.database().dir(md).replica("r", rd).start();
        Connection c = db.connection();
        Map<String, String> expect = new TreeMap<String, String>();
        for (int i = 0; i < 2000; i++) {
            c.put("/k/" + (i % 300), "value " + i);
            expect.put("/k/" + (i % 300), "value " + i);
        }
        Job job = db.addReplica("added", ad);
        JobStatus st = job.join();
        for (int i = 2000; i < 4000; i++) {
            c.put("/k/" + (i % 300), "value " + i);
            expect.put("/k/" + (i % 300), "value " + i);
        }
        long t1 = System.nanoTime();
        db.sync(SyncLevel.STRONG);
        double strongMs = (System.nanoTime() - t1) * 1e-6;
        String inf = infos(db.getStorageInfos());
        db.stop();
        sleep(3000);        // stop() does not wait for the storage threads.
        System.out.printf("Pub API, dir() and replica(), addReplica() after 2000 puts (job: %d, "
                + "'%s'), 4000 puts, STRONG sync %.0f ms, stop(); storages: %s%n",
                st.progress(), st.note(), strongMs, inf);
        FileStream m = new FileStream(new File(md));
        FileStream r = new FileStream(new File(rd));
        FileStream a = new FileStream(new File(ad));
        compare("main and replica()", m, r);
        compare("main and addReplica()", m, a);
        m.close();
        r.close();
        a.close();
        for (String which : new String[] {rd, ad}) {
            Database dr = Factory.database().dir(which).start();
            Connection cr = dr.connection();
            int same = 0, other = 0;
            for (Map.Entry<String, String> e : expect.entrySet()) {
                if (e.getValue().equals(cr.get(e.getKey(), String.class))) same++;
                else other++;
            }
            dr.stop();
            sleep(500);
            System.out.println("  started from " + new File(which).getName() + " alone (Pub API): "
                    + same + " keys as expected, " + other + " not");
        }
    }


    // ======== P2: cuts ========

    /**
     * cuts SEEDS BT GATE [TRANS]. A main and a replica, both SnapCutStreams (the replica behind
     * a GateStream), reclaim with a retain duration of 1 s by default (the reclaim tests'
     * setup: startup distance 2000, nodes of 8). With GATE 1, the replica's appends are held
     * for a while from transaction 3000 on: a replica disk that stalls. Every image a cut left
     * on either stream (what a crash at that moment leaves) is started and checked against
     * the model of the transactions complete in it, and its length compared with the stream
     * length when reclaim decided the cut (Reclaim.Stats.Cut.decidedAt).
     */
    static void cuts(String[] args) throws Exception {
        int seeds = Integer.parseInt(args[1]);
        int bt = Integer.parseInt(args[2]);
        boolean gate = args[3].equals("1");
        int trans = args.length > 4 ? Integer.parseInt(args[4]) : 12000;
        final int sd = Integer.getInteger("sd", 2000);
        final int retain = Integer.getInteger("retain", 1);
        final long step = SEC * Integer.getInteger("step", 50) / 1000;
        final int maxValue = Integer.getInteger("value", 30);
        System.out.println("P2. Cuts: replica buffer time " + bt + " ms, gate " + gate + ", "
                + seeds + " seeds of " + trans + " transactions; startup distance " + sd
                + ", retain " + retain + " s, " + step * 1000 / SEC + " ms apart, values up to "
                + maxValue + " bytes" + (sd == 2000 ? ", nodes of 8" : "") + ".");
        int[] tot = new int[14];
        for (int seed = 1; seed <= seeds; seed++) {
            SnapCutStream main = new SnapCutStream();
            SnapCutStream repInner = new SnapCutStream();
            GateStream rep = new GateStream(repInner);
            CoreTestClock clock = new CoreTestClock();
            long time = SEC;
            clock.setTime(time);
            Db db = startCuts(clock, sd, retain, spec("main", main, MAIN_BS, MAIN_BT),
                    spec("r", rep, REP_BS, bt));
            Reclaim.Stats stats = db.internal().reclaim().enableStats();
            History h = new History(300);
            Random r = new Random(seed);
            boolean held = false;
            int releaseAt = -1;
            for (int i = 0; i < trans; i++) {
                if (gate && i == 3000) {
                    rep.hold();
                    held = true;
                    releaseAt = 3000 + 500 + r.nextInt(2500);
                }
                if (held && (i == releaseAt
                        || db.getStreamLength() - repInner.getLength() > REP_BS / 2)) {
                    rep.release();
                    held = false;
                }
                time += step;
                clock.setTime(time);
                execute(db, h, randomOps(r, h.keyCount, maxValue));
            }
            rep.release();
            db.sync(SyncLevel.STRONG);
            db.close();
            main.snap = false;
            repInner.snap = false;
            compare("seed " + seed + ", main and replica at the end", main.copy(), repInner.copy());

            int[] m = images("main", main.images, stats, h, time, seed, sd);
            int[] q = images("replica", repInner.images, stats, h, time, seed, sd);
            for (int k = 0; k < 7; k++) {
                tot[k] += m[k];
                tot[7 + k] += q[k];
            }
        }
        System.out.println("Total, main: " + summary(tot, 0));
        System.out.println("Total, replica: " + summary(tot, 7));
    }

    static String summary(int[] t, int o) {
        return t[o] + " images at cuts, " + t[o + 1] + " shorter than the cut's decision; "
                + "started and checked: " + t[o + 2] + " failed to start, " + t[o + 3]
                + " with wrong values, " + t[o + 4] + " with lookups not available at "
                + "times from their first available lookup time on, " + t[o + 5] 
                + " with other errors; " + t[o + 6] + " of the started with a failed lookup at "
                + "the latest time";
    }

    /**
     * Starts each image and checks it. Returns {images, shorter than the decision, start
     * failed, wrong, unavailable, errors}.
     */
    /** As start(), with nodes of 8 for the reclaim tests' startup distance of 2000 only. */
    static Db startCuts(CoreTestClock clock, int sd, long retainSec, Spec... specs) {
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        for (Spec s : specs) b.stream(s.name, s.stream, s.bufferSize, s.bufferTime);
        b.clock(clock).startupDistance(sd);
        if (sd == 2000) b.maxNodeSize8();
        Db db = b.start();
        if (retainSec > 0) db.setRetainDuration(retainSec * SEC);
        return db;
    }

    static int[] images(String which, List<CutStream> images, Reclaim.Stats stats, History h,
            long time, int seed, int sd) {
        int[] res = new int[7];
        String[] example = new String[7];
        for (CutStream image : images) {
            res[0]++;
            long decidedAt = -1;
            for (Reclaim.Stats.Cut c : stats.cuts) {
                if (c.pos == image.getCut()) decidedAt = c.decidedAt;
            }
            boolean shorter = image.getLength() < decidedAt;
            if (shorter) res[1]++;
            int n = h.completeIn(image.getLength());
            String where = which + " image cut at " + image.getCut() + ", length " 
                    + image.getLength() + ", decided at " + decidedAt;
            Db db;
            try {
                CoreTestClock clock = new CoreTestClock();
                clock.setTime(time + 1);
                db = startCuts(clock, sd, 0, spec("main", image.copy(), MAIN_BS, MAIN_BT));
            } catch (RuntimeException e) {
                res[2]++;
                if (example[2] == null) example[2] = where + ": startup failed: " + ex(e);
                continue;
            }
            Check c = verify(db, h, n, new Random(seed * 31 + res[0]), where);
            db.close();
            if (c.wrong > 0) {
                res[3]++;
                if (example[3] == null) example[3] = c.first;
            }
            if (c.unavailable > 0) {
                res[4]++;
                if (example[4] == null) example[4] = c.first;
            }
            if (c.errors > 0) {
                res[5]++;
                if (example[5] == null) example[5] = c.first;
            }
            if (c.latestBad > 0) res[6]++;
        }
        StringBuilder b = new StringBuilder();
        for (int k = 2; k < 6; k++) {
            if (example[k] != null) b.append("\n    example: ").append(example[k]);
        }
        System.out.println("  seed " + seed + ", " + which + ": " + summary(res, 0) + b);
        return res;
    }


    // ======== P3: a replica added after cuts ========

    /**
     * A main with cuts (FileStream, retain 1 s), then addReplica of an empty FileStream:
     * case 0, nothing else writes during the copy; case 1, a writer runs during the copy,
     * with reclaim off until the job is done; case 2, a writer runs and reclaim cuts.
     */
    static void addAfter() throws Exception {
        System.out.println("P3. A replica added after cuts (FileStreams).");
        String[] names = {"No writes during the copy", 
                "A writer during the copy, no cuts during it", 
                "A writer during the copy, with cuts",
                "A writer at full speed during the copy, with cuts"};
        for (int k = 0; k < 4; k++) {
            File d = dir("p3-" + k);
            final FileStream main = new FileStream(new File(d, "main"));
            final CoreTestClock clock = new CoreTestClock();
            long time = SEC;
            clock.setTime(time);
            final Db db = start(clock, 2000, 1, spec("main", main, MAIN_BS, MAIN_BT));
            final History h = new History(300);
            final Random r = new Random(7);
            int n = 0;
            while (main.getFirstPos() < 2 * 1000 * 1000) {
                time = run(db, clock, h, r, time, 100, SEC / 20, 200);
                n += 100;
            }
            db.sync(SyncLevel.STRONG);
            System.out.println(names[k] + ": " + n + " transactions first; main first "
                    + "position " + main.getFirstPos() + ", length " + main.getLength());
            if (k == 1) db.setRetainDuration(Long.MAX_VALUE);
            final long[] tm = new long[] {time};
            final boolean[] stop = new boolean[1];
            final int[] wrote = new int[2];
            final String[] wex = new String[1];
            // About 1000 transactions a second (a sleep of 1 ms after each); case 3 writes at
            // full speed. A first version of this probe held the write lock from one
            // transaction to the next; the copy, which takes the lock for every 50 kB, then
            // never ended, and the heap ran out (no eviction here).
            final boolean paced = k < 3;
            Thread writer = new Thread() {
                public void run() {
                    while (!stop[0]) {
                        tm[0] += SEC / 20;
                        clock.setTime(tm[0]);
                        try {
                            execute(db, h, randomOps(r, h.keyCount, 200));
                            wrote[0]++;
                        } catch (RuntimeException e) {
                            wrote[1]++;
                            if (wex[0] == null) wex[0] = ex(e) + " at " + e.getStackTrace()[0];
                        }
                        if (paced) ReplicaProbe.sleep(1);
                    }
                }
            };
            if (k > 0) writer.start();
            FileStream rep = new FileStream(new File(d, "r"));
            long t1 = System.nanoTime();
            Job job = db.addReplica("r", rep, REP_BS, REP_BT);
            JobStatus st = job.join(30000);
            double ms = (System.nanoTime() - t1) * 1e-6;
            String inf = infos(db.getStorageInfos());
            if (k > 0) {
                sleep(500);
                stop[0] = true;
                writer.join();
                time = tm[0];
            }
            if (k == 1) db.setRetainDuration(SEC);
            System.out.printf("  addReplica: %.0f ms, the job ended with %d '%s'; storages then: "
                    + "%s%n", ms, st.progress(), st.note(), inf);
            if (k > 0) {
                System.out.println("  the writer: " + wrote[0] + " transactions returned, " 
                        + wrote[1] + " threw" + (wex[0] == null ? "" : ", first: " + wex[0]));
            }
            int ok = 0, threw = 0;
            String first = null;
            for (int i = 0; i < 2000; i++) {
                time += SEC / 20;
                clock.setTime(time);
                try {
                    execute(db, h, randomOps(r, h.keyCount, 200));
                    ok++;
                } catch (RuntimeException e) {
                    threw++;
                    if (first == null) first = ex(e);
                }
            }
            System.out.println("  then 2000 transactions: " + ok + " returned, " + threw 
                    + " threw" + (first == null ? "" : " (" + first + ")") + "; " 
                    + h.ops.size() + " stored in all");
            db.sync(SyncLevel.STRONG);
            db.close();
            FileStream m2 = new FileStream(new File(d, "main"));
            FileStream r2 = new FileStream(new File(d, "r"));
            compare("main and replica", m2, r2);
            m2.close();
            r2.close();
            try {
                Db dr = startAt(time + 1, 2000, spec("main", new FileStream(new File(d, "r")),
                        MAIN_BS, MAIN_BT));
                Check c = verify(dr, h, h.ops.size(), new Random(3), "replica alone");
                System.out.println("  started from the replica alone: " + c);
                dr.close();
            } catch (RuntimeException e) {
                System.out.println("  started from the replica alone: startup failed: " + ex(e));
            }
        }
    }


    // ======== P4: restore the main from a replica ========

    static void restore() throws Exception {
        System.out.println("P4. Restore: a new, empty main directory with the replica.");
        for (int retain = 0; retain < 2; retain++) {
            File d = dir("p4-" + retain);
            CoreTestClock clock = new CoreTestClock();
            long time = SEC;
            clock.setTime(time);
            FileStream main = new FileStream(new File(d, "main"));
            Db db = start(clock, 2000, retain, spec("main", main, MAIN_BS, MAIN_BT),
                    spec("r", new FileStream(new File(d, "r")), MAIN_BS, MAIN_BT));
            History h = new History(300);
            Random r = new Random(4);
            int n = 0;
            while (n < 3000 || (retain == 1 && main.getFirstPos() == 0)) {
                time = run(db, clock, h, r, time, 100, SEC / 20, 200);
                n += 100;
            }
            db.sync(SyncLevel.STRONG);
            long first = main.getFirstPos();
            db.close();
            System.out.println((retain == 1 ? "Reclaim on" : "No reclaim") + ": " + n
                    + " transactions, first position " + first + "; start with an empty main "
                    + "and the replica:");
            try {
                Db db2 = startAt(time + 1, 2000,
                        spec("main", new FileStream(new File(d, "main2")), MAIN_BS, MAIN_BT),
                        spec("r", new FileStream(new File(d, "r")), MAIN_BS, MAIN_BT));
                Check c = verify(db2, h, h.ops.size(), new Random(5), "restored main");
                db2.close();
                System.out.println("  started: " + c);
                Db db3 = startAt(time + 1, 2000,
                        spec("main", new FileStream(new File(d, "main2")), MAIN_BS, MAIN_BT));
                c = verify(db3, h, h.ops.size(), new Random(6), "restored main alone");
                db3.close();
                System.out.println("  the restored main alone: " + c);
            } catch (RuntimeException e) {
                System.out.println("  startup failed: " + ex(e));
            }
        }
    }


    // ======== P5: a crash in the middle of addReplica's copy ========

    static final int P5_TRANS = 20000;

    /** The child: a main of about 60 MB, then addReplica; halts in the middle of the copy. */
    static void crashSyncChild(File d) throws Exception {
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(SEC);
        FileStream main = new FileStream(new File(d, "main"));
        Db db = start(clock, 20 * 1000 * 1000, 0, spec("main", main, 10 * 1000 * 1000, 20));
        History h = new History(3000);
        run(db, clock, h, new Random(9), SEC, P5_TRANS, SEC / 100, 2000);
        db.sync(SyncLevel.STRONG);
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < h.lastPos.size(); i++) {
            b.append(h.lastPos.get(i)).append(' ').append(h.times.get(i)).append('\n');
        }
        Files.write(new File(d, "lastpos.txt").toPath(), b.toString().getBytes("UTF-8"));
        final Job job = db.addReplica("r", new FileStream(new File(d, "r")), REP_BS, REP_BT);
        while (job.getStatus().progress() < 50) {
            Thread.sleep(1);
        }
        System.out.println("child: main length " + main.getLength() + "; halts at progress "
                + job.getStatus().progress() + " (" + job.getStatus().note() + ")");
        System.out.flush();
        Runtime.getRuntime().halt(0);
    }

    static void crashSync(File d) throws Exception {
        System.out.println("P5. A crash (Runtime.halt) in the middle of addReplica's copy.");
        deleteTree(d);
        d.mkdirs();
        ProcessBuilder pb = new ProcessBuilder("java", "-ea", "-cp",
                System.getProperty("java.class.path"), "bergdb.core.ReplicaProbe",
                "crashsync-child", d.getPath());
        pb.inheritIO();
        int exit = pb.start().waitFor();
        System.out.println("child exit " + exit);
        // The model: the child's transactions, again, with its positions and times.
        History h = new History(3000);
        Random r = new Random(9);
        for (int i = 0; i < P5_TRANS; i++) {
            h.ops.add(randomOps(r, h.keyCount, 2000));
        }
        for (String s : new String(Files.readAllBytes(new File(d, "lastpos.txt").toPath()),
                "UTF-8").split("\n")) {
            String[] f = s.split(" ");
            h.lastPos.add(Long.parseLong(f[0]));
            h.times.add(Long.parseLong(f[1]));
        }
        long time = h.times.get(h.times.size() - 1);
        FileStream m = new FileStream(new File(d, "main"));
        FileStream rp = new FileStream(new File(d, "r"));
        System.out.println("After the crash: main " + m.getLength() + " bytes, replica "
                + rp.getFirstPos() + " to " + rp.getLength());
        compare("main and the half-copied replica", m, rp);
        m.close();
        rp.close();
        copyTree(new File(d, "r"), new File(d, "r-copy"));
        // The half-copied replica alone.
        try {
            FileStream rc = new FileStream(new File(d, "r-copy"));
            int n = h.completeIn(rc.getLength());
            Db dr = startAt(time + 1, 20 * 1000 * 1000, spec("main", rc, MAIN_BS, MAIN_BT));
            Check c = verify(dr, h, n, new Random(1), "half-copied replica alone");
            dr.close();
            System.out.println("The half-copied replica alone (" + n + " transactions complete "
                    + "in it): " + c);
        } catch (RuntimeException e) {
            System.out.println("The half-copied replica alone: startup failed: " + ex(e));
        }
        // Main and replica: startup copies the rest.
        Db db = startAt(time + 1, 20 * 1000 * 1000,
                spec("main", new FileStream(new File(d, "main")), MAIN_BS, MAIN_BT),
                spec("r", new FileStream(new File(d, "r")), REP_BS, REP_BT));
        Check c = verify(db, h, h.ops.size(), new Random(2), "main with the replica");
        db.close();
        System.out.println("Restart with main and replica: " + c);
        m = new FileStream(new File(d, "main"));
        rp = new FileStream(new File(d, "r"));
        compare("main and replica after the restart", m, rp);
        m.close();
        rp.close();
        deleteTree(d);
    }

    static void copyTree(File from, File to) throws IOException {
        to.mkdirs();
        for (File f : from.listFiles()) {
            Files.copy(f.toPath(), new File(to, f.getName()).toPath());
        }
    }


    // ======== P6: a replica whose writes fail ========

    static void fail() throws Exception {
        System.out.println("P6. A replica whose writes fail.");
        for (int retain = 0; retain < 2; retain++) {
            CutStream main = new CutStream();
            GateStream rep = new GateStream(new CutStream());
            rep.failAfter = 300 * 1000;
            CoreTestClock clock = new CoreTestClock();
            long time = SEC;
            clock.setTime(time);
            Db db = start(clock, 2000, retain, spec("main", main, MAIN_BS, MAIN_BT),
                    spec("r", rep, 1000 * 1000, MAIN_BT));
            History h = new History(300);
            Random r = new Random(11);
            int failedAt = -1, threw = 0, ok = 0;
            String firstEx = null;
            double strongMs = -1;
            for (int i = 0; i < 6000; i++) {
                time += SEC / 20;
                clock.setTime(time);
                try {
                    execute(db, h, randomOps(r, h.keyCount, 30));
                    ok++;
                } catch (RuntimeException e) {
                    threw++;
                    if (firstEx == null) {
                        firstEx = "transaction " + i + ": " + ex(e) + " at " + e.getStackTrace()[0];
                    }
                }
                if (failedAt == -1
                        && db.getStorageInfos()[1].getStatus() == StorageInfo.STATUS_ERROR) {
                    failedAt = i;
                    long t1 = System.nanoTime();
                    db.sync(SyncLevel.STRONG);
                    strongMs = (System.nanoTime() - t1) * 1e-6;
                }
                if (i % 50 == 0) sleep(1);      // lets the replica's storage thread flush
            }
            System.out.println((retain == 1 ? "Reclaim on (retain 1 s)" : "No reclaim")
                    + ": the replica failed after transaction " + failedAt + "; storages then: "
                    + infos(db.getStorageInfos()));
            System.out.printf("  a STRONG sync after the failure returned in %.1f ms; of 6000 "
                    + "transactions, %d returned and %d threw (stored anyway: %d)%n", strongMs,
                    ok, threw, h.ops.size() - ok);
            if (firstEx != null) System.out.println("  first exception: " + firstEx);
            try {
                db.removeReplica("r");
                System.out.println("  removeReplica(\"r\"): returned");
            } catch (RuntimeException e) {
                System.out.println("  removeReplica(\"r\"): " + ex(e) + " at "
                        + e.getStackTrace()[0]);
            }
            System.out.println("  storages after removeReplica: " + infos(db.getStorageInfos()));
            int ok2 = 0, threw2 = 0;
            for (int i = 0; i < 1000; i++) {
                time += SEC / 20;
                clock.setTime(time);
                try {
                    execute(db, h, randomOps(r, h.keyCount, 30));
                    ok2++;
                } catch (RuntimeException e) {
                    threw2++;
                }
            }
            System.out.println("  1000 more transactions: " + ok2 + " returned, " + threw2
                    + " threw");
            Check c = verify(db, h, h.ops.size(), new Random(12), "the database");
            System.out.println("  the database's content: " + c);
            db.close();
            Db db2 = startAt(time + 1, 2000, spec("main", main.copy(), MAIN_BS, MAIN_BT));
            c = verify(db2, h, h.ops.size(), new Random(13), "restarted");
            db2.close();
            System.out.println("  restarted from the main: " + c);
        }

        // The Job of addReplica (Db.addReplica, as Database.addReplica) when the copy fails.
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(SEC);
        Db db = start(clock, 2000, 0, spec("main", new CutStream(), MAIN_BS, MAIN_BT));
        History h = new History(300);
        run(db, clock, h, new Random(14), SEC, 3000, SEC / 20, 200);
        GateStream bad = new GateStream(new CutStream());
        bad.failAfter = 100 * 1000;
        Job job = db.addReplica("bad", bad, REP_BS, REP_BT);
        JobStatus st = job.join();
        System.out.println("addReplica of a replica whose writes fail after 100 kB: the job "
                + "ended with progress " + st.progress() + ", note '" + st.note()
                + "'; storages: " + infos(db.getStorageInfos()));
        db.close();
    }


    // ======== P7: eviction ========

    static void evict() throws Exception {
        System.out.println("P7. A replica with eviction: a cache budget of 2 MB, about 6 MB "
                + "of live values.");
        CutStream main = new CutStream();
        CutStream rep = new CutStream();
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.stream("main", main, MAIN_BS, MAIN_BT).stream("r", rep, REP_BS, REP_BT);
        b.clock(clock).maxNodeSize8().startupDistance(200 * 1000).cacheSizeIndicator(2 * 1000 * 1000);
        Db db = b.start();
        db.setRetainDuration(30 * SEC);
        History h = new History(5000);
        Random r = new Random(15);
        long[] before = Eviction.totals();
        time = run(db, clock, h, r, time, 20000, SEC / 20, 3000);
        db.sync(SyncLevel.STRONG);
        long[] after = Eviction.totals();
        Check c = verify(db, h, h.ops.size(), new Random(16), "running");
        System.out.println("  20000 transactions; eviction released " + (after[1] - before[1])
                + " objects; first position " + main.getFirstPos() + "; reads while running: " + c);
        db.close();
        compare("main and replica", main.copy(), rep.copy());
        DbBuilder b2 = Db.builder();
        b2.testSetupExceptStream();
        CoreTestClock clock2 = new CoreTestClock();
        clock2.setTime(time + 1);
        b2.stream("main", rep.copy(), MAIN_BS, MAIN_BT).clock(clock2).maxNodeSize8()
                .startupDistance(200 * 1000).cacheSizeIndicator(2 * 1000 * 1000);
        Db db2 = b2.start();
        c = verify(db2, h, h.ops.size(), new Random(17), "replica alone");
        System.out.println("  started from the replica alone, with eviction: " + c);
        db2.close();
    }


    // ======== P8: sync levels, slow and hung replicas ========

    static void slow(File d) throws Exception {
        System.out.println("P8. Syncs with a replica; a slow and a hung replica (FileStreams in "
                + d + ").");
        String[] names = {"no replica", "replica 20 ms (replica())",
                "replica 2000 ms (addReplica())"};
        int[] bts = {-1, 20, 2000};
        for (int k = 0; k < 3; k++) {
            File dd = new File(d, "p8-" + k);
            deleteTree(dd);
            Db db = bts[k] < 0
                    ? Db.builder().stream("main", new FileStream(new File(dd, "main")),
                            REP_BS / 2, 20).build()
                    : Db.builder().stream("main", new FileStream(new File(dd, "main")),
                            REP_BS / 2, 20).stream("r", new FileStream(new File(dd, "r")),
                            REP_BS, bts[k]).build();
            db.start();
            for (String level : new String[] {"ORDINARY", "STRONG"}) {
                SyncLevel sl = SyncLevel.valueOf(level);
                double[] t = new double[40];
                for (int i = 0; i < t.length; i++) {
                    db.execute(db.trans().put("/s/" + (i % 10), "value " + i).build());
                    long t1 = System.nanoTime();
                    db.sync(sl);
                    t[i] = (System.nanoTime() - t1) * 1e-6;
                }
                Arrays.sort(t);
                System.out.printf("  %s, sync %s after each commit: p50 %.1f ms, max %.1f ms%n",
                        names[k], level, t[t.length / 2], t[t.length - 1]);
            }
            db.close();
            deleteTree(dd);
        }

        // Writers without syncs, 1 kB values, 5 s: no replica, and a replica limited to 2 MB/s.
        for (int k = 0; k < 2; k++) {
            File dd = new File(d, "p8-w" + k);
            deleteTree(dd);
            DbBuilder b = Db.builder().stream("main", new FileStream(new File(dd, "main")),
                    REP_BS / 2, 20);
            GateStream rep = new GateStream(new FileStream(new File(dd, "r")));
            rep.bytesPerSec = 2 * 1000 * 1000;
            if (k == 1) b.stream("r", rep, REP_BS, REP_BT);
            Db db = b.start();
            byte[] v = new byte[1000];
            long t0 = System.nanoTime();
            int n = 0;
            double[] perSec = new double[5];
            for (int s = 0; s < 5; s++) {
                int n0 = n;
                long end = t0 + (s + 1) * 1000000000L;
                while (System.nanoTime() < end) {
                    db.execute(db.trans().put("/w/" + (n % 10000), v).build());
                    n++;
                }
                perSec[s] = n - n0;
            }
            System.out.printf("  %s: puts of 1 kB without sync, second 1 to 5: %.0f %.0f %.0f "
                    + "%.0f %.0f%n", k == 0 ? "no replica" : "a replica limited to 2 MB/s",
                    perSec[0], perSec[1], perSec[2], perSec[3], perSec[4]);
            db.stop();
            sleep(500);
            deleteTree(dd);
        }

        // A hung replica: its appends block for ever.
        File dd = new File(d, "p8-hung");
        deleteTree(dd);
        final GateStream rep = new GateStream(new FileStream(new File(dd, "r")));
        final Db db = Db.builder().stream("main", new FileStream(new File(dd, "main")),
                REP_BS / 2, 20).stream("r", rep, 1000 * 1000, 20).start();
        db.execute(db.trans().put("/h/x", "before").build());
        db.sync(SyncLevel.STRONG);
        rep.hold();
        final int[] puts = new int[1];
        final boolean[] blocked = new boolean[1];
        Thread w = new Thread() {
            public void run() {
                byte[] v = new byte[1000];
                while (true) {
                    db.execute(db.trans().put("/h/" + (puts[0] % 1000), v).build());
                    puts[0]++;
                }
            }
        };
        w.setDaemon(true);
        w.start();
        sleep(2000);
        int p1 = puts[0];
        sleep(2000);
        int p2 = puts[0];
        String read = DbUtil.getString(db, "/h/x");
        System.out.println("  a hung replica (1 MB buffer): the writer made " + p1 + " puts, then "
                + (p2 - p1) + " in the next 2 s (thread " + w.getState() + "); a read meanwhile: '"
                + read + "'");
        for (final long pos : new long[] {1, 0}) {
            final boolean[] synced = new boolean[1];
            Thread s = new Thread() {
                public void run() {
                    db.sync(pos, SyncLevel.ORDINARY);
                    synced[0] = true;
                }
            };
            s.setDaemon(true);
            s.start();
            s.join(3000);
            System.out.println("  an ORDINARY sync " + (pos == 1 ? "of the first transaction"
                    : "of the last transaction (Database.sync())") + " returned within 3 s: "
                    + synced[0]);
        }
        long t1 = System.nanoTime();
        db.stop();
        System.out.printf("  stop() returned in %.0f ms; the writer is %s%n",
                (System.nanoTime() - t1) * 1e-6, w.getState());
        rep.release();
        sleep(1000);
        System.out.println("  after the replica was released: the writer is " + w.getState()
                + ", " + puts[0] + " puts");
        deleteTree(dd);
    }


    // ======== P9: a restart without the replica ========

    /**
     * Main and replica; the main loses its last bytes (a crash: the replica's disk kept more);
     * the database starts on the main alone and works; then it starts with both again.
     */
    static void diverge() throws Exception {
        System.out.println("P9. A crash that leaves the replica longer than the main, a restart "
                + "without the replica, then with it.");
        for (int more : new int[] {0, 3, 400}) {
            File d = dir("p9-" + more);
            File md = new File(d, "main");
            File rd = new File(d, "r");
            CoreTestClock clock = new CoreTestClock();
            long time = SEC;
            clock.setTime(time);
            Db db = start(clock, 2000, 0, spec("main", new FileStream(md), MAIN_BS, MAIN_BT),
                    spec("r", new FileStream(rd), MAIN_BS, MAIN_BT));
            History h = new History(300);
            Random r = new Random(20);
            time = run(db, clock, h, r, time, 3000, SEC / 20, 200);
            db.sync(SyncLevel.STRONG);
            db.close();
            // The crash: the main's last file loses 3000 bytes; the replica has them.
            long len = truncateLast(md, 3000);
            int n = h.completeIn(len);
            List<Map<String, byte[]>> ops = new ArrayList<Map<String, byte[]>>(h.ops.subList(0, n));
            List<Long> times = new ArrayList<Long>(h.times.subList(0, n));
            List<Long> lastPos = new ArrayList<Long>(h.lastPos.subList(0, n));
            System.out.println("Main cut to " + len + " bytes (" + n + " of " + h.ops.size()
                    + " transactions complete), the replica " + new FileStream(rd).getLength()
                    + " bytes; the main alone runs " + more + " transactions:");
            // History after the crash: the first n, then the new ones.
            History h2 = new History(300);
            h2.ops.addAll(ops);
            h2.times.addAll(times);
            h2.lastPos.addAll(lastPos);
            CoreTestClock clock2 = new CoreTestClock();
            clock2.setTime(time + 1);
            Db db2 = start(clock2, 2000, 0, spec("main", new FileStream(md), MAIN_BS, MAIN_BT));
            time = run(db2, clock2, h2, r, time + 1, more, SEC / 20, 200);
            db2.sync(SyncLevel.STRONG);
            db2.close();
            FileStream m = new FileStream(md);
            FileStream rp = new FileStream(rd);
            System.out.println("  main now " + m.getLength() + " bytes, replica "
                    + rp.getLength());
            compare("main and replica before the restart with both", m, rp);
            m.close();
            rp.close();
            try {
                Db db3 = startOrHang(time + 1, 60, "  start with main and replica", 
                        spec("main", new FileStream(md), MAIN_BS, MAIN_BT),
                        spec("r", new FileStream(rd), MAIN_BS, MAIN_BT));
                if (db3 != null) {
                    Check c = verify(db3, h2, h2.ops.size(), new Random(21), "main with replica");
                    System.out.println("  start with main and replica: started; " + c);
                    db3.close();
                }
            } catch (RuntimeException e) {
                System.out.println("  start with main and replica: FAILED: " + ex(e));
            }
            m = new FileStream(md);
            rp = new FileStream(rd);
            compare("main and replica after it", m, rp);
            m.close();
            rp.close();
            for (File which : new File[] {md, rd}) {
                try {
                    Db db4 = startOrHang(time + 1, 60, "  " + which.getName() + " alone", 
                            spec("main", new FileStream(which), MAIN_BS, MAIN_BT));
                    if (db4 != null) {
                        Check c = verify(db4, h2, h2.ops.size(), new Random(22), which.getName());
                        System.out.println("  " + which.getName() + " alone: started; against "
                                + "the main's history (" + h2.ops.size() + " transactions): " + c);
                        if (which == rd) {
                            c = verify(db4, h, h.ops.size(), new Random(22), which.getName());
                            System.out.println("    against the history before the crash (" 
                                    + h.ops.size() + " transactions): " + c);
                        }
                        db4.close();
                    }
                } catch (RuntimeException e) {
                    System.out.println("  " + which.getName() + " alone: startup FAILED: " + ex(e));
                }
            }
        }
    }

    /**
     * Starts a database in a daemon thread. Returns null, and prints where it is, if it has
     * not started within the time: it hangs.
     */
    static Db startOrHang(final long time, int seconds, String what, final Spec... specs)
            throws InterruptedException {
        final Db[] db = new Db[1];
        final RuntimeException[] ex = new RuntimeException[1];
        Thread t = new Thread() {
            public void run() {
                try {
                    db[0] = startAt(time, 2000, specs);
                } catch (RuntimeException e) {
                    ex[0] = e;
                }
            }
        };
        t.setDaemon(true);
        t.start();
        t.join(seconds * 1000L);
        if (t.isAlive()) {
            StackTraceElement[] st = t.getStackTrace();
            StringBuilder b = new StringBuilder();
            for (int i = 0; i < Math.min(st.length, 12); i++) {
                if (st[i].getClassName().startsWith("bergdb.core")) {
                    b.append("\n      at ").append(st[i]);
                }
            }
            System.out.println(what + ": HUNG, not started after " + seconds + " s; the startup "
                    + "thread uses the CPU (" + t.getState() + "):" + b);
            return null;
        }
        if (ex[0] != null) throw ex[0];
        return db[0];
    }

    /** Removes the last k bytes of the stream in directory d; returns the new length. */
    static long truncateLast(File d, int k) throws IOException {
        File[] fs = d.listFiles();
        Arrays.sort(fs);
        File last = null;
        for (File f : fs) if (f.getName().endsWith(".bergdb") && f.length() > 0) last = f;
        if (last.length() < k) throw new IllegalStateException("last file too short: " + last);
        RandomAccessFile raf = new RandomAccessFile(last, "rw");
        raf.setLength(raf.length() - k);
        raf.close();
        FileStream s = new FileStream(d);
        long len = s.getLength();
        s.close();
        return len;
    }


    // ======== P10: the Pub API ========

    static void pubApi() throws Exception {
        System.out.println("P10. The Pub API.");
        // replica() before dir().
        File d = dir("p10a");
        String md = new File(d, "main").getPath();
        String rd = new File(d, "r").getPath();
        Database db = Factory.database().replica("r", rd).dir(md).start();
        db.connection().put("/a", "x");
        db.sync(SyncLevel.STRONG);
        System.out.println("replica(\"r\", dir) before dir(main): storages: "
                + infos(db.getStorageInfos()) + "; files in the replica directory: "
                + count(new File(rd)));
        db.stop();
        sleep(500);

        // Encryption: one database with a replica of replica(), one with addReplica() (a
        // STRONG sync covers one replica; with both, the second may have nothing on disk).
        CryptoKey key = CryptoKey.generate();
        String secret = "SECRET-PLAINTEXT-4711";
        for (int k = 0; k < 2; k++) {
            d = dir("p10b-" + k);
            md = new File(d, "main").getPath();
            rd = new File(d, "r").getPath();
            if (k == 0) {
                db = Factory.database().cryptoKey(key).dir(md).replica("r", rd).start();
                db.connection().put("/secret", secret);
            } else {
                db = Factory.database().cryptoKey(key).dir(md).start();
                db.connection().put("/secret", secret);
                db.addReplica("r", rd).join();
            }
            db.connection().put("/secret2", secret);
            db.sync(SyncLevel.STRONG);
            db.stop();
            sleep(3000);
            String how = k == 0 ? "replica()" : "addReplica()";
            System.out.println("An encrypted database (cryptoKey) with a replica of " + how 
                    + ": the plain text '" + secret + "' is in " + grep(new File(md), secret) 
                    + " files of the main and " + grep(new File(rd), secret) + " of the replica");
            for (int withKey = 0; withKey < 2; withKey++) {
                try {
                    Database dr = (withKey == 1 ? Factory.database().cryptoKey(key)
                            : Factory.database()).dir(rd).start();
                    String v = dr.connection().get("/secret", String.class);
                    dr.stop();
                    sleep(300);
                    System.out.println("  started from the replica" + (withKey == 1 ? " with" 
                            : " without") + " the key: /secret = " + v);
                } catch (RuntimeException e) {
                    System.out.println("  started from the replica" + (withKey == 1 ? " with" 
                            : " without") + " the key: " + ex(e));
                }
            }
        }

        // The main's own directory as a replica.
        d = dir("p10c");
        md = new File(d, "main").getPath();
        db = Factory.database().dir(md).start();
        Connection c = db.connection();
        for (int i = 0; i < 1000; i++) c.put("/k/" + (i % 100), "value " + i);
        db.sync();
        String result;
        try {
            JobStatus st = db.addReplica("self", md).join();
            result = "accepted, job '" + st.note() + "'";
        } catch (RuntimeException e) {
            result = ex(e);
        } catch (IOException e) {
            result = ex(e);
        }
        for (int i = 1000; i < 30000; i++) c.put("/k/" + (i % 100), "value " + i);
        db.sync(SyncLevel.STRONG);
        db.stop();
        sleep(3000);
        String restart;
        try {
            Database dr = Factory.database().dir(md).start();
            int same = 0;
            for (int k = 0; k < 100; k++) {
                int last = 29900 + k;
                if (("value " + last).equals(dr.connection().get("/k/" + k, String.class))) same++;
            }
            dr.stop();
            restart = "started, " + same + " of 100 keys as expected";
        } catch (RuntimeException e) {
            restart = "startup FAILED: " + ex(e);
        }
        System.out.println("addReplica(\"self\", the main's own directory): " + result
                + "; after 29000 more puts and a restart: " + restart);
        sleep(500);
    }

    // ======== P11: a stream that ends where a meta block starts ========

    /**
     * Found by P2 (2026-10-22): an image of length 14,400,000 did not start. A transaction
     * that ends exactly at a meta block's position (a multiple of 200,000) is appended in two
     * calls: its bytes, then the meta block (RecoverableStream.append, writeMetaBlock). A
     * flush, and so a crash, can come between them. Each such transaction of a run is cut
     * there, at its end, and the image started; as controls, also just before and after.
     */
    static void metaEdge() throws Exception {
        System.out.println("P11. Images that end exactly at a meta block's position.");
        CutStream s = new CutStream();
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        Db db = start(clock, 2000, 0, spec("main", s, MAIN_BS, MAIN_BT));
        History h = new History(300);
        int trans = Integer.getInteger("trans", 30000);
        time = run(db, clock, h, new Random(30), time, trans, 13, Integer.getInteger("value", 60));
        db.close();
        System.out.println("  " + trans + " transactions, " + s.getLength() + " bytes, "
                + s.getLength() / 200000 + " meta block positions");
        int found = 0;
        int[] failed = new int[3];
        String example = null;
        for (int i = 0; i < h.lastPos.size(); i++) {
            long end = h.lastPos.get(i) + 1;
            if (end % RecoverableStreamConstants.DISTANCE != 0) continue;
            found++;
            long[] cuts = {end, end - 8, end + 128};
            for (int k = 0; k < 3; k++) {
                CutStream c = s.copy();
                c.truncate(cuts[k]);
                int n = h.completeIn(cuts[k]);
                try {
                    Db d = startAt(time + 1, 2000, spec("main", c, MAIN_BS, MAIN_BT));
                    Check ck = verify(d, h, n, new Random(i), "cut at " + cuts[k]);
                    d.close();
                    if (!ck.ok()) {
                        failed[k]++;
                        if (example == null) example = ck.first;
                    }
                } catch (RuntimeException e) {
                    failed[k]++;
                    if (example == null) example = "cut at " + cuts[k] + " (transaction " + i 
                            + " ends there): startup failed: " + ex(e);
                }
            }
        }
        System.out.println("  " + found + " transactions end exactly at a meta block's position."
                + " Images cut there: " + failed[0] + " of " + found + " fail; cut 8 bytes "
                + "before (in the transaction): " + failed[1] + " fail; cut after the meta block: "
                + failed[2] + " fail" + (example == null ? "" : "\n  example: " + example));
    }

    /** RecoverableStream's meta block distance. */
    static class RecoverableStreamConstants {
        static final long DISTANCE = bergdb.storage.RecoverableStream.META_BLOCK_DISTANCE;
    }

    static int count(File d) {
        File[] fs = d.listFiles();
        return fs == null ? 0 : fs.length;
    }

    /** The number of files in d that contain the string. */
    static int grep(File d, String s) throws IOException {
        byte[] p = s.getBytes("UTF-8");
        int n = 0;
        File[] fs = d.listFiles();
        if (fs == null) return 0;
        for (File f : fs) {
            byte[] b = Files.readAllBytes(f.toPath());
            for (int i = 0; i + p.length <= b.length; i++) {
                int j = 0;
                while (j < p.length && b[i + j] == p[j]) j++;
                if (j == p.length) {
                    n++;
                    break;
                }
            }
        }
        return n;
    }
}
