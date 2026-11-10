package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.*;

import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.PointerFollower;
import bergdb.pub.util.Clock;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;
import bergdb.stream.FileStream;

/**
 * A prototype of two tests of bergdb 023-03, written 2026-11-10: T1, the hello-world
 * convergence test (with T2's shapes and orders and T3's R forever), and T4, a steady-state
 * queue. Not a gate: it measures, checks lookups against a model, and prints.
 *
 * T1 (command hello): two databases with the same settings, the twin (only "/a.txt" =
 * "Hello world!") and the emptied database (the same, then N keys put and deleted again, so
 * that only "/a.txt" is left). Both have a retain duration R on a test clock, and both get
 * the same drive, K overwrites of "/a.txt"; then their resources are measured and compared,
 * before and after a restart. Lookups are checked against a model at the latest time and at
 * times within R, after the fill, the deletes, the drive and the restart.
 *
 * T4 (command queue): a queue of L live keys, one put and one delete of the oldest a
 * transaction, M transactions; resources measured every M/10 transactions.
 *
 * Measures, all counts but the bytes: kept, the stream's bytes from the decided cut
 * (getFirstAvailablePos(), a function of the transactions), and phys, from the physical cut
 * (CutStream) or the bytes of the files (FileStream), which waits for durability and so
 * depends on timing; lag, now minus the first available lookup time; reach, the key nodes
 * that a scan of every key at the latest time follows (the nodes reachable at the current
 * time), their KEY klongs and the dead ones (deleted or shadowed); get, the key nodes that a
 * get of "/a.txt" follows; head, those that a scan for the first key after the internal
 * ones follows (qhead: for the queue's first entry); hFill, the most key nodes a get of a
 * key of the fill follows, after the fill; D, the dirty index nodes; res, the resident index
 * objects (Residents); handles, the node table's live handles; loads, versions read from
 * the stream (the measuring scans' included). The counting follower wraps
 * NodeCollection.maintenance(), which loads without installing, so a measure does not
 * change what is resident.
 *
 * Usage, from java/ after build.sh:
 *   java -ea -cp build/bergdb.jar:build/stress bergdb.core.CleanupRule hello [prop=value...]
 *   java -ea -cp build/bergdb.jar:build/stress bergdb.core.CleanupRule queue [prop=value...]
 * Properties (hello): n=1000 shape=after|before|around|inter|long|hashed order=asc|desc|random
 *   batch=100 valsize=100 versions=1 sd=100000 retain=1 (seconds; 0: forever) dt=10000 (time
 *   units a transaction) drive=4000 dvalsize=1000 every=500 stream=cut|file dir=PATH
 *   evict=BYTES twin=1 (0: the emptied database only) pre=0 (more overwrites before the
 *   drive: with n=0, a phase-shifted twin) seed=1
 * Properties (queue): m=100000 live=1000 keys=time|hashed valsize=100 sd=100000 retain=1
 *   dt=10000 stream=cut|file dir=PATH evict=BYTES every=m/10
 */
public class CleanupRule {
    static final long SEC = Clock.UNITS_PER_SEC;
    static final String A_KEY = "/a.txt";
    static final long[] A_SEG = Keys.toSegments(A_KEY);
    static final byte[] HELLO = "Hello world!".getBytes(StandardCharsets.UTF_8);
    static final String INTERNAL = "/#i/";

    final Map<String, String> p = new HashMap<String, String>();

    CleanupRule(String[] args) {
        for (int i = 1; i < args.length; i++) {
            int eq = args[i].indexOf('=');
            p.put(args[i].substring(0, eq), args[i].substring(eq + 1));
        }
    }

    int i(String k, int d) { return p.containsKey(k) ? Integer.parseInt(p.get(k)) : d; }
    long l(String k, long d) { return p.containsKey(k) ? Long.parseLong(p.get(k)) : d; }
    String s(String k, String d) { return p.containsKey(k) ? p.get(k) : d; }

    // ======== Measures ========

    /** Counts the key nodes a read follows, by id, and their KEY klongs, live and dead. */
    static final class Count implements PointerFollower {
        final PointerFollower inner;
        final HashSet<Long> ids = new HashSet<Long>();
        long keyKlongs, live;

        Count(PointerFollower inner) {
            this.inner = inner;
        }

        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node r = inner.followPointer(predecessor, pointerIndex, op);
            if (r instanceof KeyNode && ids.add(r.getId())) {
                KeyNode kn = (KeyNode) r;
                int sz = kn.getSize();
                long del = kn.getDeleteBitmapAtTime(Klong.MAX_TIME, sz);
                for (int i = 0; i < sz; i++) {
                    long k = kn.getKlong(i);
                    if (!Klong.isKey(k)) continue;
                    keyKlongs++;
                    if (Klong.isDeleted(del, i)) continue;
                    long cv = Klong.getCompareValue(k);
                    boolean shadowed = false;
                    for (int j = i + 1; j < sz && !shadowed; j++) {
                        long k2 = kn.getKlong(j);
                        shadowed = Klong.isKey(k2) && Klong.getCompareValue(k2) == cv;
                    }
                    if (!shadowed) live++;
                }
            }
            return r;
        }
    }

    static final class M {
        long len, kept, phys, files, fap, lagMs, iters, cuts, reach, klongs, dead, kvs, userKvs,
                get, head, dirty, resObj, resBytes, handles, loads;

        String line() {
            return String.format("len=%d kept=%d phys=%d files=%d lag=%dms iters=%d cuts=%d reach=%d "
                    + "klongs=%d dead=%d kvs=%d user=%d get=%d head=%d D=%d res=%d resB=%d "
                    + "handles=%d loads=%d", len, kept, phys, files, lagMs, iters, cuts, reach, klongs,
                    dead, kvs, userKvs, get, head, dirty, resObj, resBytes, handles, loads);
        }
    }

    /** One database of a run, with its stream, clock and model. */
    final class Run {
        final String label;
        final boolean file = "file".equals(s("stream", "cut"));
        final int sd = i("sd", 100000);
        final long retain = l("retain", 1) * SEC;
        final long evict = l("evict", 0);
        File dir;
        CutStream cut;
        CoreTestClock clock;
        long time = 10 * SEC;
        Db db;
        Reclaim.Stats stats;
        long maxRecord;                 // the largest record since resetWindow()
        long maxKept, minKept = Long.MAX_VALUE, maxDirty;

        // The model: every key's history, time to value (null: deleted).
        final HashMap<String, TreeMap<Long, byte[]>> model =
                new HashMap<String, TreeMap<Long, byte[]>>();

        Run(String label) throws IOException {
            this.label = label;
            if (file) {
                dir = new File(s("dir", "build/cleanup") + "/" + label);
                rm(dir);
                dir.mkdirs();
            } else {
                cut = new CutStream();
            }
            start();
        }

        void start() throws IOException {
            clock = new CoreTestClock();
            clock.setTime(time);
            DbBuilder b;
            if (file) {
                b = Db.builder().mainStream(new FileStream(dir)).testId();
                if (evict == 0) b.noEvict();
            } else {
                b = Db.builder().testSetup(cut);
            }
            b.clock(clock).startupDistance(sd);
            if (evict > 0) b.cacheSizeIndicator(evict);
            db = b.start();
            stats = db.internal().reclaim().enableStats();
        }

        /** sync, stop, and a start on the same stream (a copy for a CutStream). */
        void restart() throws IOException {
            db.sync(SyncLevel.ORDINARY);
            db.close();
            if (!file) cut = cut.copy();
            start();
        }

        void close() {
            db.close();
        }

        long tick() {
            time += l("dt", 10000);
            clock.setTime(time);
            return time;
        }

        /** Executes puts (value != null) and deletes (null), in one transaction. */
        Trans exec(List<String> keys, List<byte[]> values) {
            tick();
            Trans.Builder b = db.trans();
            for (int k = 0; k < keys.size(); k++) {
                if (values.get(k) == null) b.delete(keys.get(k));
                else b.put(keys.get(k), values.get(k));
            }
            Trans t = b.build();
            db.execute(t);
            for (int k = 0; k < keys.size(); k++) {
                TreeMap<Long, byte[]> h = model.get(keys.get(k));
                if (h == null) model.put(keys.get(k), h = new TreeMap<Long, byte[]>());
                h.put(t.tt, values.get(k));
            }
            maxRecord = Math.max(maxRecord, t.nextPos - t.tpos);
            return t;
        }

        Trans exec1(String key, byte[] value) {
            return exec(Collections.singletonList(key), Collections.singletonList(value));
        }

        void resetWindow() {
            maxRecord = 0;
            maxKept = 0;
            minKept = Long.MAX_VALUE;
            maxDirty = 0;
        }

        /**
         * The stream kept from the decided cut, which is a function of the transactions; the
         * physical cut waits for durability, so its position depends on timing (StreamDigest).
         */
        long kept() {
            return db.getStreamLength() - db.getFirstAvailablePos();
        }

        /** The bytes kept by the stream itself: on a CutStream, from the physical cut. */
        long phys() {
            if (!file) return cut.getLength() - cut.getFirstPos();
            long sum = 0;
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) if (f.getName().endsWith(".bergdb")) sum += f.length();
            return sum;
        }

        int files() {
            if (!file) return 0;
            int c = 0;
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) if (f.getName().endsWith(".bergdb")) c++;
            return c;
        }

        long dirty() {
            final Set<Node> d = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
            synchronized (db.internal().getWriteLock()) {
                db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE,
                        (node, tpos, last) -> { if (node.isDirty()) d.add(node); });
            }
            return d.size();
        }

        /** Called after every drive transaction: the window's extremes. */
        void sample() {
            long k = kept();
            maxKept = Math.max(maxKept, k);
            minKept = Math.min(minKept, k);
        }

        M measure() {
            M m = new M();
            m.len = db.getStreamLength();
            m.kept = kept();
            m.phys = phys();
            m.files = files();
            m.fap = db.getFirstAvailablePos();
            long f = db.getFirstAvailableLookupTime();
            m.lagMs = (time - f) / (SEC / 1000);
            m.iters = db.getReclaimIterationCount();
            m.cuts = stats.cuts.size();
            synchronized (db.internal().getWriteLock()) {
                Count c = new Count(db.internal().nodeCollection().maintenance());
                GetMany g = db.newGetMany();
                g.gd.pointerFollower = c;
                db.getMany(g);
                m.reach = c.ids.size();
                m.klongs = c.keyKlongs;
                m.dead = c.keyKlongs - c.live;
                m.kvs = g.result.size();
                for (Kvt kvt : g.result) {
                    if (!Keys.toString(kvt.key).startsWith(INTERNAL)) m.userKvs++;
                }

                Count c2 = new Count(db.internal().nodeCollection().maintenance());
                GetData gd = db.newGetData();
                gd.pointerFollower = c2;
                db.getOne(Long.MAX_VALUE, A_SEG, gd);
                m.get = c2.ids.size();

                Count c3 = new Count(db.internal().nodeCollection().maintenance());
                GetMany h = db.newGetMany();
                h.gd.pointerFollower = c3;
                h.startKey = Keys.toSegments("/");     // the user's keys: after "/#i/..."
                h.inclusive = true;
                h.stopCondition = new FirstUser();
                db.getMany(h);
                m.head = c3.ids.size();
            }
            m.dirty = dirty();
            m.resObj = db.internal().cache().residents().objects();
            m.resBytes = db.internal().cache().residents().bytes();
            m.handles = db.internal().cache().handles().size();
            m.loads = db.internal().cacheStats().loads;
            return m;
        }

        /** A full scan and a get of "/a.txt" through the ordinary follower (they load). */
        void probe() {
            GetMany g = db.newGetMany();
            db.getMany(g);
            db.getOne(Long.MAX_VALUE, A_SEG, db.newGetData());
        }

        // ---- Checks against the model ----

        byte[] expected(String k, long t) {
            TreeMap<Long, byte[]> h = model.get(k);
            if (h == null) return null;
            Map.Entry<Long, byte[]> e = h.floorEntry(t);
            return e == null ? null : e.getValue();
        }

        /**
         * Every key of a sample at the latest time and at times within the retain duration;
         * a scan of the user's keys at the oldest time the guarantee promises and at a random
         * time in the window, against the model; a lookup below the first available time
         * refused.
         */
        void verify(String where, Random rnd) {
            long now = time;
            long first = db.getFirstAvailableLookupTime();
            if (first > now - retain && first > 10 * SEC + retain) {
                throw new AssertionError(label + " " + where + ": first available time " + first
                        + " is inside the retention window [" + (now - retain) + ", " + now + "]");
            }
            long from = Math.max(first, now - retain);
            List<String> keys = new ArrayList<String>(model.keySet());
            Collections.sort(keys);
            int samples = Math.min(keys.size(), 300);
            for (int j = 0; j < samples; j++) {
                String k = keys.get(rnd.nextInt(keys.size()));
                long[] ts = {Long.MAX_VALUE, from, from + (long) (rnd.nextDouble() * (now - from))};
                for (long t : ts) {
                    byte[] act = db.getOne(t, Keys.toSegments(k), db.newGetData());
                    byte[] exp = expected(k, Math.min(t, now));
                    if (!Arrays.equals(exp, act)) {
                        throw new AssertionError(label + " " + where + ": " + k + " at " + t
                                + ": expected " + (exp == null ? "null" : exp.length + " bytes")
                                + ", got " + (act == null ? "null" : act.length + " bytes"));
                    }
                }
            }
            for (long t : new long[] {from, from + (long) (rnd.nextDouble() * (now - from)),
                    Long.MAX_VALUE}) {
                GetMany g = db.newGetMany();
                g.lookupTime = t;
                g.startKey = Keys.toSegments("/");
                db.getMany(g);
                int act = 0;
                for (Kvt kvt : g.result) {
                    String k = Keys.toString(kvt.key);
                    if (k.startsWith(INTERNAL)) continue;
                    act++;
                    if (!Arrays.equals(expected(k, Math.min(t, now)), kvt.value)) {
                        throw new AssertionError(label + " " + where + ": scan at " + t + ": "
                                + k + " has another value than the model's");
                    }
                }
                int exp = 0;
                for (String k : keys) if (expected(k, Math.min(t, now)) != null) exp++;
                if (exp != act) {
                    throw new AssertionError(label + " " + where + ": scan at " + t + ": "
                            + act + " keys, the model has " + exp);
                }
            }
            if (first > 0) {
                try {
                    db.getOne(first - 1, A_SEG, db.newGetData());
                    throw new AssertionError(label + " " + where + ": a lookup below the first "
                            + "available time was not refused");
                } catch (LookupTimeNotAvailableException e) {
                    // as it must
                }
            }
        }
    }

    /** Stops at the first key that is not internal (the user's first key). */
    static final class FirstUser implements GetMany.StopCondition {
        public int handleKvt(Kvt kvt) {
            return Keys.toString(kvt.key).startsWith(INTERNAL) ? CONTINUE : ADD_AND_STOP;
        }

        public void eod() {}
    }

    // ======== Keys of the shapes ========

    static final String ALPHABET;
    static {
        StringBuilder b = new StringBuilder();
        for (char c = '!'; c <= '~'; c++) if (c != '/') b.append(c);
        ALPHABET = b.toString();
    }

    /** Key i of N in the shape. */
    static String key(String shape, int i, int n) {
        switch (shape) {
        case "after":  return String.format("/k/%010d", i);
        case "before": return String.format("/0/%010d", i);
        case "around": return i % 2 == 0 ? String.format("/0/%010d", i)
                : String.format("/k/%010d", i);
        case "inter": {
            // Keys of 6 bytes in "/a.txt"'s own segment tree, spread over the range.
            long span = 1;
            for (int j = 0; j < 4; j++) span *= ALPHABET.length();
            long x = (long) i * (span / Math.max(1, n));
            char[] cs = new char[4];
            for (int j = 3; j >= 0; j--) {
                cs[j] = ALPHABET.charAt((int) (x % ALPHABET.length()));
                x /= ALPHABET.length();
            }
            String k = "/a" + new String(cs);
            return k.equals(A_KEY) ? "/a" + new String(cs, 0, 3) + "!" : k;
        }
        case "long":   return String.format("/L/%010d", i) + "-0123456789-0123456789-0123456789-01234";
        case "hashed": return String.format("/h/%016x", (i * 0x9E3779B97F4A7C15L) >>> 4);
        default: throw new IllegalArgumentException("shape " + shape);
        }
    }

    static int[] order(String order, int n, long seed) {
        int[] o = new int[n];
        for (int i = 0; i < n; i++) o[i] = order.equals("desc") ? n - 1 - i : i;
        if (order.equals("random")) {
            Random r = new Random(seed);
            for (int i = n - 1; i > 0; i--) {
                int j = r.nextInt(i + 1);
                int t = o[i]; o[i] = o[j]; o[j] = t;
            }
        }
        return o;
    }

    static byte[] value(int size, long tag) {
        byte[] v = new byte[size];
        for (int j = 0; j < size; j++) v[j] = (byte) ('a' + (tag + j) % 26);
        for (int j = 0; j < 8 && j < size; j++) v[j] = (byte) (tag >>> (8 * j));
        return v;
    }

    static void rm(File dir) {
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) f.delete();
        dir.delete();
    }

    // ======== T1, hello ========

    void hello() throws IOException {
        final int n = i("n", 1000);
        final String shape = s("shape", "after");
        final String order = s("order", "asc");
        final int batch = i("batch", 100);
        final int valsize = i("valsize", 100);
        final int versions = i("versions", 1);
        final int drive = i("drive", 4000);
        final int dvalsize = i("dvalsize", 1000);
        final int every = i("every", 500);
        final long seed = l("seed", 1);
        System.out.println("CleanupRule hello " + p);

        List<Run> runs = new ArrayList<Run>();
        if (i("twin", 1) == 1) runs.add(new Run("twin"));     // first: the twin
        runs.add(new Run("n" + n));
        long[] ms = new long[runs.size()];
        M[] end = new M[runs.size()], afterStart = new M[runs.size()], afterProbe = new M[runs.size()];
        long[] maxKept = new long[runs.size()], minKept = new long[runs.size()];
        long[] maxRec = new long[runs.size()], maxD = new long[runs.size()];

        for (int r = 0; r < runs.size(); r++) {
            Run run = runs.get(r);
            long t0 = System.nanoTime();
            Random rnd = new Random(seed);
            if (run.retain > 0) run.db.setRetainDuration(run.retain);   // 0: forever
            run.exec1(A_KEY, HELLO);
            int nn = run.label.equals("twin") ? 0 : n;

            // Fill: versions rounds of puts of every key, in key order, batch keys a transaction.
            for (int v = 0; v < versions; v++) {
                for (int i = 0; i < nn; i += batch) {
                    List<String> ks = new ArrayList<String>();
                    List<byte[]> vs = new ArrayList<byte[]>();
                    for (int j = i; j < Math.min(nn, i + batch); j++) {
                        ks.add(key(shape, j, nn));
                        vs.add(value(valsize, j + (long) v * nn));
                    }
                    run.exec(ks, vs);
                }
            }
            if (nn > 0) {
                System.out.println(run.label + " filled:  " + run.measure().line());
                run.verify("after the fill", rnd);
                // h_fill: the most key nodes that a get of a key of the fill follows (a sample).
                int hFill = 0;
                synchronized (run.db.internal().getWriteLock()) {
                    for (int j = 0; j < Math.min(nn, 200); j++) {
                        Count c = new Count(run.db.internal().nodeCollection().maintenance());
                        GetData gd = run.db.newGetData();
                        gd.pointerFollower = c;
                        run.db.getOne(Long.MAX_VALUE,
                                Keys.toSegments(key(shape, (int) ((long) j * nn / Math.min(nn, 200)), nn)), gd);
                        hFill = Math.max(hFill, c.ids.size());
                    }
                }
                System.out.println(run.label + " hFill=" + hFill);
            }
            long deleteStart = run.time;

            // Delete, in the order given.
            int[] o = order(order, nn, seed);
            for (int i = 0; i < nn; i += batch) {
                List<String> ks = new ArrayList<String>();
                List<byte[]> vs = new ArrayList<byte[]>();
                for (int j = i; j < Math.min(nn, i + batch); j++) {
                    ks.add(key(shape, o[j], nn));
                    vs.add(null);
                }
                run.exec(ks, vs);
            }
            if (nn > 0) {
                M m = run.measure();
                System.out.println(run.label + " deleted: " + m.line());
                run.verify("after the deletes", rnd);
                // The history within R must still be there: the keys at the time before the
                // first delete, when that is within the window.
                if (run.time - deleteStart < run.retain) {
                    GetMany g = run.db.newGetMany();
                    g.lookupTime = deleteStart;
                    g.startKey = Keys.toSegments("/");
                    run.db.getMany(g);
                    int user = 0;
                    for (Kvt kvt : g.result) {
                        if (!Keys.toString(kvt.key).startsWith(INTERNAL)) user++;
                    }
                    System.out.println(run.label + " a scan at the time before the deletes, "
                            + "within R: " + (user - 1) + " keys of " + nn);
                }
            }

            // A phase shift for a second twin (n=0 pre=K): K more overwrites before the drive.
            if (!run.label.equals("twin")) {
                for (int k = 0; k < i("pre", 0); k++) run.exec1(A_KEY, value(dvalsize, -1 - k));
            }

            // Drive: overwrites of "/a.txt".
            // The window: the drive's last R of time (at least 'every' transactions).
            final int window = Math.min(drive, Math.max(every, (int) (run.retain / l("dt", 10000))));
            for (int d = 1; d <= drive; d++) {
                run.exec1(A_KEY, value(dvalsize, d));
                if (d == drive - window + 1) run.resetWindow();
                if (d > drive - window) {
                    run.sample();
                    if (d % 50 == 0) run.maxDirty = Math.max(run.maxDirty, run.dirty());
                }
                if (d % every == 0) {
                    System.out.println(run.label + " drive " + d + ": " + run.measure().line()
                            + " maxRecord=" + run.maxRecord);
                }
            }
            run.verify("after the drive", rnd);
            end[r] = run.measure();
            maxKept[r] = run.maxKept;
            minKept[r] = run.minKept;
            maxRec[r] = run.maxRecord;
            maxD[r] = run.maxDirty;
            Reclaim.Stats.Iteration it = null;
            for (Reclaim.Stats.Iteration x : run.stats.iterations) if (x.pEnd != -1) it = x;
            if (it != null) {
                System.out.println(run.label + " last done iteration: steps=" + it.steps
                        + " kvs=" + it.kvs + " touchVisited=" + it.touch.visited
                        + " touchDirtied=" + it.touch.dirtied + " dirtiedNodes=" + it.dirtiedNodes
                        + " dirtiedBytes=" + it.dirtiedBytes + " maxStepNodes=" + it.maxStepNodes
                        + " recordBytes=" + it.recordBytes);
            }

            Reclaim.Stats.Iteration cur = run.stats.iterations.isEmpty() ? null
                    : run.stats.iterations.get(run.stats.iterations.size() - 1);
            if (cur != null && cur.pEnd == -1) {
                System.out.println(run.label + " iteration in progress: steps=" + cur.steps
                        + " kvs=" + cur.kvs + " touchVisited=" + cur.touch.visited
                        + " dirtiedNodes=" + cur.dirtiedNodes + " dirtiedBytes=" + cur.dirtiedBytes
                        + " maxStepDirtied=" + cur.maxStepDirtied + " maxStepNodes="
                        + cur.maxStepNodes);
            }
            run.restart();
            afterStart[r] = run.measure();
            run.probe();
            afterProbe[r] = run.measure();
            run.verify("after the restart", rnd);
            run.close();
            ms[r] = (System.nanoTime() - t0) / 1000000;
            System.out.println(run.label + " end:     " + end[r].line());
            System.out.println(run.label + " started: " + afterStart[r].line());
            System.out.println(run.label + " probed:  " + afterProbe[r].line());
            System.out.println(run.label + " window: kept " + minKept[r] + " to " + maxKept[r]
                    + ", max record " + maxRec[r] + ", max D " + maxD[r] + "; " + ms[r] + " ms");
        }
        if (runs.size() == 1) {
            System.out.println(String.format("RESULT1 n=%d shape=%s: kept %d (window max %d), "
                    + "reach %d, dead %d, get %d, head %d, maxD %d, maxRecord %d, lagMs %d, res "
                    + "after start %d, after probe %d, loads after probe %d, files %d; %d ms", n,
                    shape, end[0].kept, maxKept[0], end[0].reach, end[0].dead, end[0].get,
                    end[0].head, maxD[0], maxRec[0], end[0].lagMs, afterStart[0].resObj,
                    afterProbe[0].resObj, afterProbe[0].loads, end[0].files, ms[0]));
        }
        if (runs.size() == 2) {
            System.out.println(String.format("RESULT hello n=%d shape=%s order=%s versions=%d: "
                    + "keptMax %d/%d, reach %d/%d, dead %d/%d, get %d/%d, head %d/%d, "
                    + "maxD %d/%d, maxRecord %d/%d, lagMs %d/%d, res after start %d/%d, "
                    + "after probe %d/%d, handles %d/%d, loads after probe %d/%d, files %d/%d "
                    + "(twin/B); %d ms", n, shape, order, versions, maxKept[0], maxKept[1],
                    end[0].reach, end[1].reach, end[0].dead, end[1].dead, end[0].get, end[1].get,
                    end[0].head, end[1].head, maxD[0], maxD[1], maxRec[0], maxRec[1],
                    end[0].lagMs, end[1].lagMs, afterStart[0].resObj, afterStart[1].resObj,
                    afterProbe[0].resObj, afterProbe[1].resObj, afterProbe[0].handles,
                    afterProbe[1].handles, afterProbe[0].loads, afterProbe[1].loads,
                    end[0].files, end[1].files, ms[1]));
        }
    }

    // ======== T5, a queue ========

    void queue() throws IOException {
        final int m = i("m", 100000);
        final int live = i("live", 1000);
        final boolean hashed = "hashed".equals(s("keys", "time"));
        final int valsize = i("valsize", 100);
        final int every = i("every", m / 10);
        System.out.println("CleanupRule queue " + p);
        Run run = new Run("queue");
        Random rnd = new Random(l("seed", 1));
        run.db.setRetainDuration(run.retain);
        run.exec1(A_KEY, HELLO);
        long t0 = System.nanoTime();
        for (int i = 0; i < m; i++) {
            List<String> ks = new ArrayList<String>(2);
            List<byte[]> vs = new ArrayList<byte[]>(2);
            ks.add(qkey(i, hashed));
            vs.add(value(valsize, i));
            if (i >= live) {
                ks.add(qkey(i - live, hashed));
                vs.add(null);
            }
            run.exec(ks, vs);
            if (i >= live) run.model.remove(qkey(i - live - 1, hashed));  // keep the model small
            if ((i + 1) % every == 0) {
                M x = run.measure();
                // The queue's head: the key nodes that a scan for the first entry follows.
                int qhead;
                synchronized (run.db.internal().getWriteLock()) {
                    Count c = new Count(run.db.internal().nodeCollection().maintenance());
                    GetMany h = run.db.newGetMany();
                    h.gd.pointerFollower = c;
                    h.startKey = Keys.toSegments("/q/");
                    h.stopCondition = new GetMany.GetN(1);
                    run.db.getMany(h);
                    qhead = c.ids.size();
                }
                System.out.println(String.format("queue %8d: %s qhead=%d maxRecord=%d wall=%dms",
                        i + 1, x.line(), qhead, run.maxRecord,
                        (System.nanoTime() - t0) / 1000000));
                run.maxRecord = 0;
            }
        }
        run.close();
    }

    static String qkey(int i, boolean hashed) {
        return hashed ? String.format("/q/%016x", (i * 0x9E3779B97F4A7C15L) >>> 4)
                : String.format("/q/%012d", i);
    }

    public static void main(String[] args) throws Exception {
        CleanupRule c = new CleanupRule(args);
        if (args[0].equals("hello")) c.hello();
        else if (args[0].equals("queue")) c.queue();
        else throw new IllegalArgumentException(args[0]);
    }
}
