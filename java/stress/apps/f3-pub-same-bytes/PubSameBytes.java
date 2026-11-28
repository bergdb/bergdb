import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.WBuilder;
import bergdb.pub.util.LookupTimeNotAvailableException;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

/**
 * App f3 of 031-08 (part B): the README's "One stream" for a user of the Pub API, whose
 * clock is a TestClock (DatabaseBuilder.clock(): "Use this method together with a TestClock
 * to do deterministic testing"). A database is created at a fixed time and closed; each run
 * starts on a copy of its files (the Pub API has no way to give two creations one ID) and
 * makes the same actions at the same times: puts of objects (long, string and bytes fields),
 * texts and bytes, w() batches of up to 200 puts and deletes, deletes, rw() counters,
 * setRetainDuration() (1 to 3 s), setStartupDistanceInMb() (5 to 7), maintain(budget), an
 * index on the objects' long field created (start().join()), with "delete" also deleted,
 * setCacheSizeInMb() (a setting that changes no byte). The runs:
 *   ref      a sync after every action, the stream read after each;
 *   fast     no sync, no pause;
 *   slow     pauses of 0 to 150 ms after half the actions;
 *   restart  stop() or close() and a start after one action in 20;
 *   cache    a cache budget of 4 MB, and two reader threads that hold iterators of the
 *            objects and of the index across commits, at frozen lookup times;
 *   copy     the database closed at a random action, its files copied, the run goes on in
 *            the copy.
 * Each run's getStreamSize() after each action, and its stream, every byte (read from the
 * files after each action and at the end, as in f1), must be the ref's; the latest state
 * against the oracle at the end (a listing of each directory, and the index's scan).
 *
 * Without "delete" the index is created once and never deleted: deleteIndex() removes the
 * entries in the background (its Javadoc), on a thread whose commits come among the user's
 * as the threads' timing has it (UB-2, 031-08 apps-b.md); with "delete", the index is
 * created and deleted again and again, and a run then differs from the ref.
 *
 * Usage: java -cp bergdb-release.jar:out PubSameBytes SEED ACTIONS DIR [VARIANTS] [delete]
 */
public class PubSameBytes {
    public static class A {
        public long n;
        public String s;
        public byte[] b;
        public A() {}
    }

    static final long T0 = 1_780_000_000_000L * 10_000L;
    static final long MS = 10_000L;
    static long seed;
    static File base;
    static List<Act> acts = new ArrayList<>();
    static Ref ref;
    static long diffNotes;
    static boolean withDelete;           // deleteIndex() actions too (UB-2: its cleanup commits on its own)

    static final class Act {
        char kind;      // P put, W batch, D delete, X rw counter, R retain, S startup, M maintain, I index, J delete index, C cache
        long time;
        List<String> keys = new ArrayList<>();
        List<Object> vals = new ArrayList<>();    // null: a delete
        long arg;
        public String toString() { return kind + "(" + keys.size() + " keys, arg " + arg + ")"; }
    }

    public static void main(String[] a) throws Exception {
        seed = Long.parseLong(a[0]);
        int n = Integer.parseInt(a[1]);
        base = new File(a[2]);
        String vs = a.length > 3 ? a[3] : "all";
        withDelete = a.length > 4 && a[4].equals("delete");
        List<String> variants = vs.equals("all") ? Arrays.asList("fast", "slow", "restart", "cache", "copy")
                : Arrays.asList(vs.split(","));
        Common.rmrf(base);
        base.mkdirs();
        makeActs(n);
        long t0 = System.currentTimeMillis();
        try {
            File created = new File(base, "created");
            TestClock tc = new TestClock();
            tc.setTime(Time.units(T0));
            try (Database db = Factory.database().create(created.getPath()).clock(tc).start()) {
                db.sync();
            }
            ref = new Ref();
            Out r = run("ref");
            ref.out = r;
            log("ref: " + n + " actions, stream " + r.stream.length + " bytes, kept " + r.sizes[n - 1] + ", files "
                    + r.files.size());
            for (String v : variants) {
                Out o = run(v);
                compare(v, o);
                Common.rmrf(new File(base, v));
                Common.rmrf(new File(base, v + "-copy"));
            }
        } catch (Common.Fail e) {
            System.out.println("FAILED seed " + seed + ": " + e.getMessage());
            System.exit(1);
        }
        Common.rmrf(base);
        System.out.println("OK PubSameBytes seed " + seed + ", " + n + " actions, variants " + variants + ", " + diffNotes
                + " with other files (NOTE), " + (System.currentTimeMillis() - t0) / 1000 + " s");
    }

    static void makeActs(int n) {
        Random r = new Random(seed);
        long t = T0 + 10 * MS;
        boolean index = false;
        for (int i = 0; i < n; i++) {
            Act x = new Act();
            int dt = r.nextInt(100);
            if (dt < 8) t += 0;
            else if (dt < 75) t += MS * r.nextInt(20);
            else if (dt < 95) t += MS * (20 + r.nextInt(300));
            else t += MS * (1000 + r.nextInt(2500));
            x.time = t;
            int p = r.nextInt(1000);
            if (i == 0 || p < 5) { x.kind = 'R'; x.arg = 1000 + r.nextInt(2001); }
            else if (i == 1 || p < 10) { x.kind = 'S'; x.arg = 5 + r.nextInt(3); }
            else if (p < 70) { x.kind = 'M'; x.arg = 100 + r.nextInt(r.nextBoolean() ? 400 : 5000); }
            else if (p < 76 && (!index || withDelete)) {
                x.kind = index ? 'J' : 'I';
                index = !index;
            } else if (p < 80) { x.kind = 'C'; x.arg = 4 + r.nextInt(200); }
            else if (p < 120) { x.kind = 'X'; x.keys.add("/c/n" + r.nextInt(5) + ".txt"); }
            else if (p < 200) { x.kind = 'D'; x.keys.add(key(r)); x.vals.add(null); }
            else if (p < 700) { x.kind = 'P'; String k = key(r); x.keys.add(k); x.vals.add(value(r, k)); }
            else {
                x.kind = 'W';
                int ops = r.nextInt(10) < 8 ? 2 + r.nextInt(20) : 20 + r.nextInt(180);
                Set<String> seen = new HashSet<>();
                for (int j = 0; j < ops; j++) {
                    String k = key(r);
                    if (!seen.add(k)) continue;
                    x.keys.add(k);
                    x.vals.add(r.nextInt(4) == 0 ? null : value(r, k));
                }
            }
            acts.add(x);
        }
    }

    static String key(Random r) {
        int d = r.nextInt(3);
        int k = r.nextInt(600);
        if (d == 0) return "/a/o" + k;
        if (d == 1) return "/t/x" + k + ".txt";
        return "/b/y" + k + ".bin";
    }

    static Object value(Random r, String key) {
        int p = r.nextInt(1000);
        int len = p < 600 ? r.nextInt(80) : p < 900 ? 80 + r.nextInt(2000) : p < 985 ? 2000 + r.nextInt(60_000)
                : 100_000 + r.nextInt(900_000);
        if (key.startsWith("/a/")) {
            A o = new A();
            o.n = r.nextInt(1000) - 500;
            o.s = "s" + r.nextInt(100000);
            o.b = new byte[len];
            r.nextBytes(o.b);
            return o;
        }
        if (key.endsWith(".txt")) {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < Math.min(len, 20_000); i++) sb.append((char) ('a' + r.nextInt(26)));
            return sb.toString();
        }
        byte[] b = new byte[len];
        r.nextBytes(b);
        return b;
    }

    // ------------------------------------------------------------------ a run

    static final class Ref { Out out; }

    static final class Out {
        long[] sizes;
        long[] ends;                                  // the ref's stream end after each action
        byte[] stream;
        List<long[]> chunks = new ArrayList<>();      // {pos, length} the tap read
        TreeMap<String, byte[]> files = new TreeMap<>();
        long gap;
        long restarts, readerChecks;
    }

    static final class Run {
        String name;
        File dir;
        Database db;
        TestClock tc = new TestClock();
        Random r;
        int cache;
        long h;
        TreeMap<Long, byte[]> tapped = new TreeMap<>();
        long gap;
        TreeMap<String, Object> model = new TreeMap<>();
        boolean index;
    }

    static void start(Run x) {
        DatabaseBuilder b = Factory.database().create(x.dir.getPath()).clock(x.tc);
        if (x.cache > 0) b.cacheSizeInMb(x.cache);
        x.db = b.start();
    }

    static void close(Run x) throws IOException {
        if (x.r.nextBoolean()) x.db.stop();
        x.db.close();
        tap(x, true);
    }

    static Out run(String name) throws Exception {
        Run x = new Run();
        x.name = name;
        x.r = new Random(seed * 1009 + name.hashCode());
        x.dir = new File(base, name);
        SameBytes.copyFiles(new File(base, "created"), x.dir);
        x.tc.setTime(Time.units(T0 + 5 * MS));
        if (name.equals("cache")) x.cache = 4;
        start(x);
        int n = acts.size();
        Out out = new Out();
        out.sizes = new long[n];
        out.ends = new long[n];
        int copyAt = name.equals("copy") ? 1 + x.r.nextInt(n - 1) : -1;
        AtomicBoolean stop = new AtomicBoolean();
        AtomicReference<Throwable> fail = new AtomicReference<>();
        AtomicReference<Database> dbRef = new AtomicReference<>(x.db);
        AtomicLong checks = new AtomicLong();
        List<Thread> readers = new ArrayList<>();
        if (name.equals("cache")) {
            for (int k = 0; k < 2; k++) {
                final int kk = k;
                Thread th = new Thread(() -> reader(dbRef, kk, stop, fail, checks));
                th.setDaemon(true);
                th.start();
                readers.add(th);
            }
        }
        tap(x, false);
        for (int i = 0; i < n; i++) {
            Act act = acts.get(i);
            if (act.time > x.tc.getTime()) x.tc.setTime(Time.units(act.time));
            apply(x, act);
            out.sizes[i] = x.db.getStreamSize();
            if (name.equals("ref")) {
                x.db.sync();
                tap(x, true);
                out.ends[i] = x.h;
            } else {
                tap(x, false);
                if (ref.out != null && out.sizes[i] != ref.out.sizes[i]) {
                    throw new Common.Fail(name + ": after action " + i + " (" + act + ") getStreamSize() is " + out.sizes[i]
                            + ", the ref's " + ref.out.sizes[i] + (i > 0 ? " (before: " + out.sizes[i - 1] + ", the ref's "
                            + ref.out.sizes[i - 1] + ")" : ""));
                }
            }
            if (name.equals("slow") && x.r.nextBoolean()) Thread.sleep(x.r.nextInt(151));
            if (name.equals("restart") && x.r.nextInt(20) == 0 && i < n - 1) {
                close(x);
                start(x);
                out.restarts++;
            }
            if (i == copyAt) {
                x.db.close();
                tap(x, true);
                File to = new File(base, name + "-copy");
                SameBytes.copyFiles(x.dir, to);
                x.dir = to;
                start(x);
            }
            dbRef.set(x.db);
            if (fail.get() != null) break;
        }
        stop.set(true);
        for (Thread th : readers) th.join();
        if (fail.get() != null) {
            fail.get().printStackTrace(System.out);
            throw new Common.Fail(name + ": a reader: " + fail.get());
        }
        verify(x, name + " at the end");
        out.readerChecks = checks.get();
        close(x);
        for (File f : SameBytes.listStreamFiles(x.dir)) out.files.put(f.getName(), Files.readAllBytes(f.toPath()));
        long end = x.h;
        out.stream = new byte[(int) end];
        for (Map.Entry<Long, byte[]> e : x.tapped.entrySet()) {
            System.arraycopy(e.getValue(), 0, out.stream, (int) (long) e.getKey(), e.getValue().length);
            out.chunks.add(new long[] {e.getKey(), e.getValue().length});
        }
        out.gap = x.gap;
        log(name + ": done, " + out.restarts + " restarts, " + out.readerChecks + " reader checks, stream " + end + ", "
                + out.files.size() + " files, " + x.gap + " bytes cut before the tap read them");
        return out;
    }

    static void apply(Run x, Act act) {
        Database db = x.db;
        Connection c = db.connection();
        switch (act.kind) {
            case 'R': db.setRetainDuration(Duration.units(act.arg * MS)); break;
            case 'S': db.setStartupDistanceInMb((int) act.arg); break;
            case 'M': db.maintain((int) act.arg); break;
            case 'C': db.setCacheSizeInMb(x.cache > 0 ? x.cache : (int) act.arg); break;
            case 'I':
                db.indexBuilder("by-n").dir("/a/").type("long").field("n").start().join();
                x.index = true;
                break;
            case 'J':
                db.deleteIndex("by-n");
                x.index = false;
                break;
            case 'X': {
                String k = act.keys.get(0);
                c.rw(env -> {
                    String v = env.get(k, String.class);
                    long m = v == null ? 0 : Long.parseLong(v);
                    env.put(k, Long.toString(m + 1));
                });
                String v = (String) x.model.get(k);
                x.model.put(k, Long.toString((v == null ? 0 : Long.parseLong(v)) + 1));
                break;
            }
            case 'D':
                c.delete(act.keys.get(0));
                x.model.remove(act.keys.get(0));
                break;
            case 'P':
                c.put(act.keys.get(0), act.vals.get(0));
                x.model.put(act.keys.get(0), act.vals.get(0));
                break;
            default: {
                WBuilder w = c.w();
                for (int j = 0; j < act.keys.size(); j++) {
                    if (act.vals.get(j) == null) w.delete(act.keys.get(j)); else w.put(act.keys.get(j), act.vals.get(j));
                }
                w.execute();
                for (int j = 0; j < act.keys.size(); j++) {
                    if (act.vals.get(j) == null) x.model.remove(act.keys.get(j)); else x.model.put(act.keys.get(j), act.vals.get(j));
                }
            }
        }
    }

    static void verify(Run x, String what) {
        Connection c = x.db.newConnection();
        for (String dir : new String[] {"/a/", "/t/", "/b/", "/c/"}) {
            Iterator<Map.Entry<String, Object>> it = x.model.tailMap(dir).entrySet().iterator();
            for (Kv<Object> kv : c.usePrimary(Object.class).dir(dir).kvs()) {
                Map.Entry<String, Object> e = it.hasNext() ? it.next() : null;
                if (e == null || !e.getKey().startsWith(dir) || !e.getKey().equals(kv.key())) {
                    throw new Common.Fail(what + ": the listing of " + dir + " has " + kv.key() + ", the oracle "
                            + (e == null ? "nothing" : e.getKey()));
                }
                checkValue(c, e.getKey(), e.getValue(), what);
            }
            if (it.hasNext()) {
                Map.Entry<String, Object> e = it.next();
                if (e.getKey().startsWith(dir)) throw new Common.Fail(what + ": the listing of " + dir + " lacks " + e.getKey());
            }
        }
        if (x.index) {
            List<String> exp = new ArrayList<>();
            for (Map.Entry<String, Object> e : x.model.tailMap("/a/").entrySet()) {
                if (!e.getKey().startsWith("/a/")) break;
                exp.add(e.getKey());
            }
            exp.sort(Comparator.comparingLong((String k) -> ((A) x.model.get(k)).n).thenComparing(Comparator.naturalOrder()));
            List<String> got = new ArrayList<>();
            for (Kv<A> kv : c.useIndex("by-n", A.class).kvs()) got.add(kv.key());
            if (!got.equals(exp)) throw new Common.Fail(what + ": the index scan has " + got.size() + " keys, the oracle "
                    + exp.size() + (got.isEmpty() || exp.isEmpty() ? "" : "; first " + got.get(0) + " / " + exp.get(0)));
        }
    }

    static void checkValue(Connection c, String key, Object exp, String what) {
        if (exp instanceof A) {
            A got = c.get(key, A.class);
            A e = (A) exp;
            if (got == null || got.n != e.n || !Objects.equals(got.s, e.s) || !Arrays.equals(got.b, e.b)) {
                throw new Common.Fail(what + ": " + key + " is not the oracle's object");
            }
        } else if (exp instanceof String) {
            if (!exp.equals(c.get(key, String.class))) throw new Common.Fail(what + ": " + key + " is not the oracle's text");
        } else {
            if (!Arrays.equals((byte[]) exp, c.get(key, byte[].class))) throw new Common.Fail(what + ": " + key
                    + " is not the oracle's bytes");
        }
    }

    /** A reader that holds iterators across commits, at a frozen lookup time. */
    static void reader(AtomicReference<Database> dbRef, int k, AtomicBoolean stop, AtomicReference<Throwable> fail,
            AtomicLong checks) {
        Random r = new Random(seed * 3 + k);
        while (!stop.get()) {
            Database db = dbRef.get();
            try {
                Connection c = db.newConnection();
                c.freezeLookupTime();
                int seen = 0;
                if (k == 0) {
                    String last = null;
                    for (Kv<Object> kv : c.usePrimary(Object.class).dir("/a/").kvs()) {
                        if (last != null && kv.key().compareTo(last) <= 0) throw new Common.Fail("reader: listing out of order");
                        last = kv.key();
                        if (++seen % 50 == 0) Thread.sleep(1 + r.nextInt(5));
                        if (stop.get()) break;
                    }
                } else {
                    long lastN = Long.MIN_VALUE;
                    try {
                        for (A o : c.useIndex("by-n", A.class).objects()) {
                            if (o.n < lastN) throw new Common.Fail("reader: index scan out of order");
                            lastN = o.n;
                            if (++seen % 50 == 0) Thread.sleep(1 + r.nextInt(5));
                            if (stop.get()) break;
                        }
                    } catch (bergdb.pub.NoSuchIndexException e) {
                        Thread.sleep(2);
                    }
                }
                checks.incrementAndGet();
            } catch (Throwable e) {
                if (e instanceof Common.Fail) { fail.compareAndSet(null, e); return; }
                if (stop.get()) return;
                String s = String.valueOf(e);
                boolean expected = false;
                for (Throwable t = e; t != null; t = t.getCause()) {
                    if (t instanceof LookupTimeNotAvailableException || t instanceof bergdb.pub.util.IllegalDbStateException
                            || String.valueOf(t).contains("Storage is closing")) expected = true;
                }
                if (!expected) { fail.compareAndSet(null, e); return; }
            }
        }
    }

    // ------------------------------------------------------------------ the tap and the comparison

    /** Reads the stream's new bytes from the files: all of them (all), or the files but the last. */
    static void tap(Run x, boolean all) throws IOException {
        for (int k = 0; k < 100; k++) {
            try {
                tap0(x, all);
                return;
            } catch (java.io.FileNotFoundException | java.io.EOFException gone) {
                // a cut's thread deleted a file: list again
            }
        }
        throw new Common.Fail(x.name + ": the tap could not read the files");
    }

    static void tap0(Run x, boolean all) throws IOException {
        List<File> fs = SameBytes.listStreamFiles(x.dir);
        if (fs.isEmpty()) return;
        int m = all ? fs.size() : fs.size() - 1;
        if (m <= 0) return;
        long first = SameBytes.fileStart(fs.get(0).getName());
        long h = x.h, gap = x.gap;
        if (first > h) {
            if (x.name.equals("ref")) throw new Common.Fail("ref: the tap missed bytes " + h + " to " + first);
            gap += first - h;
            h = first;
        }
        TreeMap<Long, byte[]> add = new TreeMap<>();
        for (int i = 0; i < m; i++) {
            File f = fs.get(i);
            long s0 = SameBytes.fileStart(f.getName());
            long s1 = i + 1 < fs.size() ? SameBytes.fileStart(fs.get(i + 1).getName()) : Long.MAX_VALUE;
            long len = f.length();
            long e = Math.min(s0 + len, s1);
            if (i + 1 < fs.size() && s0 + len != s1) {
                if (len == 0) throw new java.io.FileNotFoundException(f.getName());
            }
            long a = Math.max(s0, h);
            if (a >= e) continue;
            if (a != h) throw new java.io.FileNotFoundException("hole");
            byte[] b = new byte[(int) (e - a)];
            try (RandomAccessFile raf = new RandomAccessFile(f, "r")) {
                raf.seek(a - s0);
                raf.readFully(b);
            }
            add.put(a, b);
            h = e;
        }
        x.tapped.putAll(add);
        x.h = h;
        x.gap = gap;
    }

    static void compare(String name, Out o) {
        Out r = ref.out;
        if (o.stream.length != r.stream.length) throw new Common.Fail(name + ": the stream ends at " + o.stream.length
                + ", the ref's at " + r.stream.length);
        long compared = 0;
        for (long[] c : o.chunks) {
            int a = (int) c[0], n = (int) c[1];
            int mm = Arrays.mismatch(o.stream, a, a + n, r.stream, a, a + n);
            if (mm >= 0) {
                long pos = a + mm;
                throw new Common.Fail(name + ": the stream differs first at " + pos + " (" + actionAt(pos) + ")");
            }
            compared += n;
        }
        String fd = KillBytes.diffFiles(o.files, r.files);
        if (fd != null) {
            diffNotes++;
            System.out.println("NOTE " + name + ": the same stream, other files: " + (fd.length() > 400 ? fd.substring(0, 400) : fd));
        }
        log(name + ": the same bytes as the ref (" + compared + " bytes compared, " + o.gap + " cut before the tap read them)");
    }

    static String actionAt(long pos) {
        long[] e = ref.out.ends;
        int i = 0;
        while (i < e.length && e[i] <= pos) i++;
        return "in the records of action " + i + (i < acts.size() ? ", " + acts.get(i) : "") + ", from "
                + (i == 0 ? 0 : e[i - 1]) + " to " + (i < e.length ? e[i] : -1);
    }

    static void log(String s) {
        Common.log(s);
    }
}
