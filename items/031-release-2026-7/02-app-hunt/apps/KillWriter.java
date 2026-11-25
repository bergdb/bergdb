import bergdb.pub.*;
import bergdb.pub.util.*;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.concurrent.*;

/**
 * KillWriter (031-02, e4). A child JVM writes a sequence of transactions, each a function of
 * the seed and its number j alone (or of the state, for its rw() part, which the oracle
 * computes the same way): w() batches of byte values with deletes, objects in a directory
 * with two indexes, rw() counters that also write a value made from keys they read, large
 * values that make the stream grow, transactions of 501 operations that must be refused
 * and leave nothing, and maintain() calls; a short retain duration (1 s) and a startup
 * distance of 5 MB make reclaim run and cut. Each committed transaction puts its number at
 * /meta/seq.txt; the child prints "C j time" after each commit and "S j" after each sync.
 * The parent kills the child (destroyForcibly) at random moments, starts the database
 * itself, and checks: the recovered number k is at least the last synced one; the whole
 * state (every key, object, index scan forward and backward, counter) equals the oracle's
 * after transactions 1 to k; states at older times printed by the child, when still
 * available, equal the oracle's at those transactions. Then it closes the database and
 * starts the next child, which goes on from k + 1.
 *
 * The child writes its lines to DIR.out, one write each: the pipe of its stdout loses the
 * last ones, as Process.destroyForcibly() closes the parent's end (031-02, section 8). Before
 * each start the parent notes a zeroed tail of the last stream file (031-02, F1).
 *
 * Options (system properties of the parent, passed to the child): -DearlyKill=true, half
 * the kills 50 to 750 ms after the spawn, while the child starts; -Didle=true, pauses of over
 * 2 s in the child, so that its write buffer shrinks; -DnoSd=true, no change of the startup
 * distance; -Dsnap=true, a copy of the files as each kill left them in DIR.snap.
 *
 * Usage: java KillWriter parent DIR SEED KILLS
 *        java KillWriter child DIR SEED
 */
public class KillWriter {
    public static class Obj {
        public long v;
        public String s;
        public long j;
        public Obj() {}
    }

    static void fail(String m) {
        System.out.println("KILLWRITER FAILED: " + m);
        System.out.flush();
        System.exit(1);
    }

    static final int KEYS = 3000, OBJS = 1500, CTRS = 5, BIGS = 12;

    // ---- The deterministic transaction j ----

    static final class Op { String key; Object value; }   // value null: delete

    static char type(long seed, long j) {
        Random r = rnd(seed, j);
        int t = r.nextInt(100);
        if (t < 40) return 'W';
        if (t < 65) return 'O';
        if (t < 88) return 'R';
        if (t < 93) return 'X';
        return 'D';
    }

    static Random rnd(long seed, long j) { return new Random(seed * 1_000_003L + j * 7919L); }

    static byte[] bytes(Random r, int n) { byte[] b = new byte[n]; r.nextBytes(b); return b; }

    // The ops of a W, O, X or D transaction, in order; the marker is added by the caller.
    static List<Op> ops(long seed, long j) {
        Random r = rnd(seed, j);
        r.nextInt(100);
        char t = type(seed, j);
        List<Op> ops = new ArrayList<>();
        if (t == 'W') {
            int n = 1 + r.nextInt(r.nextInt(5) == 0 ? 450 : 60);
            for (int i = 0; i < n; i++) {
                Op o = new Op();
                o.key = "/k/" + r.nextInt(KEYS) + ".bin";
                o.value = r.nextInt(4) == 0 ? null : bytes(r, r.nextInt(8) == 0 ? 2000 + r.nextInt(6000) : r.nextInt(50));
                ops.add(o);
            }
        } else if (t == 'O') {
            int n = 1 + r.nextInt(r.nextInt(5) == 0 ? 70 : 30);   // 3 indexes: up to 7 operations each
            for (int i = 0; i < n; i++) {
                Op o = new Op();
                o.key = "/o/" + r.nextInt(OBJS);
                if (r.nextInt(5) == 0) o.value = null;
                else {
                    Obj x = new Obj();
                    x.v = r.nextInt(500) - 250;
                    x.s = r.nextInt(10) == 0 ? null : "s" + r.nextInt(300);
                    x.j = j;
                    o.value = x;
                }
                ops.add(o);
            }
        } else if (t == 'X') {
            for (int i = 0; i < 501; i++) {
                Op o = new Op();
                o.key = "/k/" + i + ".bin";
                o.value = i % 2 == 0 ? null : bytes(r, 5);
                ops.add(o);
            }
        } else if (t == 'D') {
            Op o = new Op();
            o.key = "/big/b" + r.nextInt(BIGS) + ".bin";
            o.value = bytes(r, 100_000 + r.nextInt(1_500_000));
            ops.add(o);
        }
        return ops;
    }

    // The rw() of an R transaction: counter m, delta, two keys read.
    static int[] rwParams(long seed, long j) {
        Random r = rnd(seed, j);
        r.nextInt(100);
        return new int[] {r.nextInt(CTRS), 1 + r.nextInt(9), r.nextInt(KEYS), r.nextInt(KEYS)};
    }

    static long hashOf(byte[] b) { return b == null ? -1 : Arrays.hashCode(b); }

    // ---- The child ----

    static void child(String dir, long seed) throws Exception {
        // Each line a write of its own to a file, which a kill does not lose: the pipe of
        // stdout does, as Process.destroyForcibly() closes the parent's end (031-02).
        PrintStream out = new PrintStream(new FileOutputStream(dir + ".out", true), true);
        Database db = Factory.database().create(dir).start();
        Connection c = db.connection();
        String m = c.get("/meta/seq.txt", String.class);
        long j = m == null ? 0 : Long.parseLong(m);
        if (j == 0) {
            db.setStartupDistanceInMb(5);
            db.setRetainDuration(Duration.seconds(1));
            if (!exists(db, "by-v")) db.indexBuilder("by-v").dir("/o/").type("long").field("v").start().join();
            if (!exists(db, "by-s")) db.indexBuilder("by-s").dir("/o/").type("string").field("s")
                    .type("long").field("v").start().join();
            db.sync();
        }
        out.println("START " + j);
        Random r = new Random(System.nanoTime());
        while (true) {
            j++;
            char t = type(seed, j);
            Transaction tr;
            if (t == 'R') {
                int[] p = rwParams(seed, j);
                final long jj = j;
                tr = c.rw(env -> {
                    String cv = env.get("/ctr/c" + p[0] + ".txt", String.class);
                    long v = (cv == null ? 0 : Long.parseLong(cv)) + p[1];
                    byte[] a = env.get("/k/" + p[2] + ".bin", byte[].class);
                    byte[] b = env.get("/k/" + p[3] + ".bin", byte[].class);
                    env.put("/ctr/c" + p[0] + ".txt", Long.toString(v));
                    env.put("/sum/s" + p[0] + ".txt", v + ":" + hashOf(a) + ":" + hashOf(b));
                    env.put("/meta/seq.txt", Long.toString(jj));
                });
            } else {
                WBuilder w = c.w();
                for (Op o : ops(seed, j)) {
                    if (o.value == null) w.delete(o.key); else w.put(o.key, o.value);
                }
                w.put("/meta/seq.txt", Long.toString(j));
                try {
                    tr = w.execute();
                    if (t == 'X') { out.println("BAD " + j + " a transaction of 502 operations was taken"); return; }
                } catch (DbException e) {
                    if (t != 'X') { out.println("BAD " + j + " refused: " + e); return; }
                    continue;
                }
            }
            out.println("C " + j + " " + tr.getTime().units());
            // An index whose build kills may interrupt: created and deleted again and again.
            if (j % 2000 == 1000 && !exists(db, "by-j")) db.indexBuilder("by-j").dir("/o/").type("long").field("j").start();
            if (j % 2000 == 0 && exists(db, "by-j")) db.deleteIndex("by-j");
            // The startup distance changed now and then, up and down (kept in the stream).
            if (j % 700 == 350 && !Boolean.getBoolean("noSd")) db.setStartupDistanceInMb(5 + r.nextInt(r.nextBoolean() ? 10 : 80));
            // With -Didle=true, pauses of over 2 s now and then, so that the write buffer
            // shrinks to its smallest and grows again at the next burst (Database.stop()).
            if (Boolean.getBoolean("idle") && r.nextInt(400) == 0) Thread.sleep(2100 + r.nextInt(1000));
            int x = r.nextInt(100);
            if (x < 8) { c.sync(); out.println("S " + j); }
            else if (x < 12) { while (db.maintain()) { } out.println("M " + j); }
        }
    }

    static boolean exists(Database db, String name) {
        try { db.indexJob(name); return true; } catch (NoSuchIndexException e) { return false; }
    }

    // ---- The oracle ----

    static final class Model {
        TreeMap<String, byte[]> k = new TreeMap<>();
        TreeMap<String, Obj> o = new TreeMap<>();
        long[] ctr = new long[CTRS];
        String[] sum = new String[CTRS];
        TreeMap<String, byte[]> big = new TreeMap<>();
        long seq;

        Model copy() {
            Model m = new Model();
            m.k = new TreeMap<>(k); m.o = new TreeMap<>(o); m.ctr = ctr.clone(); m.sum = sum.clone();
            m.big = new TreeMap<>(big); m.seq = seq;
            return m;
        }

        void apply(long seed, long j) {
            char t = type(seed, j);
            if (t == 'X') return;
            if (t == 'R') {
                int[] p = rwParams(seed, j);
                ctr[p[0]] += p[1];
                sum[p[0]] = ctr[p[0]] + ":" + hashOf(k.get("/k/" + p[2] + ".bin")) + ":"
                        + hashOf(k.get("/k/" + p[3] + ".bin"));
            } else {
                // The last op of a key counts.
                for (Op op : ops(seed, j)) {
                    TreeMap map = op.key.startsWith("/k/") ? k : op.key.startsWith("/o/") ? o : big;
                    if (op.value == null) map.remove(op.key); else map.put(op.key, op.value);
                }
            }
            seq = j;
        }
    }

    static long nByJ, nBeyond, nZeroTails;

    static String parentLastName = "";
    static long parentLastLength = 0;

    static File lastFile(File dir) {
        File[] fs = dir.listFiles((d, n) -> n.endsWith(".bergdb"));
        if (fs == null || fs.length == 0) return null;
        Arrays.sort(fs);
        return fs[fs.length - 1];
    }

    static long trailingZeros(File dir) throws IOException {
        File[] fs = dir.listFiles((d, n) -> n.endsWith(".bergdb"));
        if (fs == null || fs.length == 0) return 0;
        Arrays.sort(fs);
        File last = fs[fs.length - 1];
        try (RandomAccessFile f = new RandomAccessFile(last, "r")) {
            long n = f.length();
            long z = 0;
            byte[] b = new byte[65536];
            while (n > 0) {
                int len = (int) Math.min(b.length, n);
                f.seek(n - len);
                f.readFully(b, 0, len);
                for (int i = len - 1; i >= 0; i--) {
                    if (b[i] != 0) return z;
                    z++;
                }
                n -= len;
            }
            return z;
        }
    }
    static final List<String> tail = new ArrayList<>();

    static void deleteTree(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File x : fs) deleteTree(x);
        f.delete();
    }

    static void copyTree(File from, File to) throws IOException {
        to.mkdirs();
        File[] fs = from.listFiles();
        if (fs == null) return;
        for (File f : fs) {
            if (f.isDirectory()) copyTree(f, new File(to, f.getName()));
            else java.nio.file.Files.copy(f.toPath(), new File(to, f.getName()).toPath());
        }
    }

    static void parent(String dir, long seed, int kills) throws Exception {
        String cp = System.getProperty("java.class.path");
        String java = ProcessHandle.current().info().command().orElse("java");
        Model model = new Model();
        Map<Long, Long> times = new HashMap<>();
        Random r = new Random(seed);
        long lastK = 0;
        long checksOld = 0, notAvail = 0;
        for (int kill = 0; kill < kills; kill++) {
            ProcessBuilder pb = new ProcessBuilder(java, "-ea", "-Xmx1g", "-XX:+UseZGC",
                    "-DnoSd=" + Boolean.getBoolean("noSd"), "-Didle=" + Boolean.getBoolean("idle"),
                    "-XX:+ExitOnOutOfMemoryError", "-cp", cp, "KillWriter", "child", dir, Long.toString(seed));
            pb.redirectErrorStream(true);
            new File(dir + ".out").delete();
            Process p = pb.start();
            final long[] lastC = {-1}, lastS = {-1}, start = {-1};
            final List<String> bad = Collections.synchronizedList(new ArrayList<>());
            tail.clear();
            // The pipe carries what the JVM prints itself (an exception's trace); the lines of
            // the protocol are in the file.
            final List<String> pipe = Collections.synchronizedList(new ArrayList<>());
            Thread pr = new Thread(() -> {
                try (BufferedReader br = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
                    String line;
                    while ((line = br.readLine()) != null) pipe.add(line);
                } catch (IOException e) { }
            });
            pr.start();
            Thread rd = new Thread(() -> {
                try { p.waitFor(); } catch (InterruptedException e) { }
                try (BufferedReader br = new BufferedReader(new FileReader(dir + ".out"))) {
                    String line;
                    while ((line = br.readLine()) != null) {
                        if (line.isEmpty()) continue;
                        String[] f = line.split(" ");
                        if (f[0].equals("C") && f.length < 3) continue;   // a line the kill cut
                        if (f[0].equals("C")) {
                            long jj = Long.parseLong(f[1]);
                            synchronized (times) { times.put(jj, Long.parseLong(f[2])); }
                            lastC[0] = jj;
                        } else if (f[0].equals("S")) lastS[0] = Long.parseLong(f[1]);
                        else if (f[0].equals("START")) start[0] = Long.parseLong(f[1]);
                        else if (f[0].equals("M")) { }
                        else bad.add(line);
                        synchronized (tail) { tail.add(line); if (tail.size() > 6) tail.remove(0); }
                    }
                } catch (IOException e) { }
            });
            long wait = 300 + r.nextInt(r.nextInt(4) == 0 ? 8000 : 2500);
            if (Boolean.getBoolean("idle")) wait += r.nextInt(6000);
            // With -DearlyKill=true, half the kills come while the child starts.
            if (Boolean.getBoolean("earlyKill") && r.nextBoolean()) wait = 50 + r.nextInt(700);
            Thread.sleep(wait);
            p.destroyForcibly();
            p.waitFor();
            rd.start();
            rd.join();
            pr.join(10_000);
            for (String line : pipe) bad.add("(stdout) " + line);
            if (!bad.isEmpty()) fail("kill " + kill + ": the child printed " + bad.subList(0, Math.min(5, bad.size())));
            if (start[0] >= 0 && start[0] != lastK) fail("kill " + kill + ": the child started at " + start[0]
                    + ", the parent recovered " + lastK);
            // Recover and check; the files as the kill left them are kept until the next kill.
            File snap = new File(dir + ".snap");
            if (Boolean.getBoolean("snap")) {
                deleteTree(snap);
                copyTree(new File(dir), snap);
            }
            // Zeros at the end of the last stream file, as the kill left it (031-02, F1).
            long zeros = trailingZeros(new File(dir));
            if (zeros >= 4096) {
                File lf = lastFile(new File(dir));
                long from = lf.length() - zeros;
                boolean before = lf.getName().equals(parentLastName) && from < parentLastLength;
                if (!before) nZeroTails++;
                System.out.println("NOTE kill " + kill + ": " + lf.getName() + " ends in " + zeros + " zero bytes, from "
                        + from + (before ? ", there before the child ran (a start's fill)" : ", written while the child ran"));
            }
            Database db;
            try {
                db = Factory.database().open(dir).start();
            } catch (DatabaseNotCreatedException e) {
                // A kill while the database was created: documented; its files are removed.
                if (lastK != 0) fail("kill " + kill + ": DatabaseNotCreatedException after " + lastK + " transactions");
                for (File f : new File(dir).listFiles()) if (f.getName().endsWith(".bergdb") || f.getName().equals("created.txt")) f.delete();
                System.out.println("kill " + kill + ": killed while the database was created; its files removed");
                continue;
            } catch (RuntimeException e) {
                System.out.println("kill " + kill + ": the start after the kill threw: " + e);
                File[] fs = new File(dir).listFiles();
                Arrays.sort(fs);
                for (File f : fs) System.out.println("  " + f.getName() + " " + f.length());
                System.out.println("  the child's last lines: " + tail);
                fail("kill " + kill + ": the database does not start after a kill (files as the kill left them in "
                        + snap.getName() + " with -Dsnap=true)");
                return;
            }
            Connection c = db.connection();
            String m = c.get("/meta/seq.txt", String.class);
            long k = m == null ? 0 : Long.parseLong(m);
            if (k < lastS[0]) fail("kill " + kill + ": recovered " + k + ", but " + lastS[0] + " was synced");
            if (k < lastK) fail("kill " + kill + ": recovered " + k + " < " + lastK + " recovered before");
            if (lastC[0] >= 0) {
                // The next transaction that commits after the last printed one: a refused one
                // (X) takes a number and prints nothing.
                long next = lastC[0] + 1;
                while (type(seed, next) == 'X') next++;
                if (k > next) {
                    if (!Boolean.getBoolean("noteBeyond")) fail("kill " + kill + ": recovered " + k + ", but the last commit "
                            + "that returned is " + lastC[0] + "; the child's last lines: " + tail);
                    // Checked further: the state must still be the oracle's at k.
                    c.get("/meta/seq.txt", String.class);
                    long seqTime = c.transactionInfo().time().units();
                    Long lastTime;
                    synchronized (times) { lastTime = times.get(lastC[0]); }
                    System.out.println("NOTE kill " + kill + ": recovered " + k + " (its time " + seqTime + "), last committed printed "
                            + lastC[0] + " (at " + lastTime + "), started at " + start[0] + ", the previous recovery " + lastK
                            + "; the child's last lines: " + tail);
                    nBeyond++;
                }
            }
            // Advance the model, keeping two snapshots for older reads.
            List<Model> snaps = new ArrayList<>();
            Set<Long> pick = new HashSet<>();
            for (int i = 0; i < 3 && k > lastK; i++) pick.add(lastK + 1 + (long) r.nextInt((int) (k - lastK)));
            for (long j = lastK + 1; j <= k; j++) {
                model.apply(seed, j);
                if (pick.contains(j) && type(seed, j) != 'X') snaps.add(model.copy());
            }
            checkState(c, model, "kill " + kill + " at " + k);
            if (exists(db, "by-j")) {
                JobStatus js = db.indexJob("by-j").join();
                if (js.state() != JobStatus.State.ACTIVE) fail("kill " + kill + ": by-j's build ended " + js.state() + " " + js.reason());
                List<String> exp = new ArrayList<>(model.o.keySet());
                exp.sort((a, b) -> model.o.get(a).j != model.o.get(b).j ? Long.compare(model.o.get(a).j, model.o.get(b).j)
                        : Arrays.compareUnsigned(a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8)));
                List<String> got = new ArrayList<>();
                for (Kv<Obj> kv : c.useIndex("by-j", Obj.class).kvs()) got.add(kv.key());
                if (!got.equals(exp)) fail("kill " + kill + ": by-j lists " + got.size() + ", model " + exp.size());
                nByJ++;
            }
            long fa = db.getFirstAvailableLookupTime().units();
            Connection o = db.newConnection();
            for (Model s : snaps) {
                Long t;
                synchronized (times) { t = times.get(s.seq); }
                if (t == null || t < fa) { notAvail++; continue; }
                o.setLookupTime(Time.units(t));
                try {
                    checkState(o, s, "kill " + kill + " older state " + s.seq);
                    checksOld++;
                } catch (LookupTimeNotAvailableException e) {
                    notAvail++;     // a cut can pass t while the check runs
                }
            }
            db.close();
            File lf0 = lastFile(new File(dir));
            parentLastName = lf0 == null ? "" : lf0.getName();
            parentLastLength = lf0 == null ? 0 : lf0.length();
            // The times printed for transactions that the kill lost are no one's: a later
            // child makes those numbers again, at other times.
            synchronized (times) { times.keySet().removeIf(jj -> jj > k); }
            if (kill % 10 == 0) System.out.println("  kill " + kill + ": recovered " + k + " (synced " + lastS[0]
                    + ", committed " + lastC[0] + "), keys " + model.k.size() + " objects " + model.o.size()
                    + ", older states checked " + checksOld + " (" + notAvail + " cut), by-j checked " + nByJ);
            lastK = k;
        }
        System.out.println("kills " + kills + ", transactions " + lastK + ", older states " + checksOld
                + ", recoveries beyond the last printed commit " + nBeyond + ", zeroed tails " + nZeroTails);
        System.out.println("KILLWRITER OK");
    }

    static void checkState(Connection c, Model m, String what) {
        String seq = c.get("/meta/seq.txt", String.class);
        if (m.seq > 0 && (seq == null || Long.parseLong(seq) != m.seq)) fail(what + ": seq " + seq + ", model " + m.seq);
        // Every byte key.
        int n = 0;
        Iterator<Map.Entry<String, byte[]>> it = m.k.entrySet().iterator();
        List<Kv<byte[]>> got = new ArrayList<>();
        for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/k/").kvs()) got.add(kv);
        List<Map.Entry<String, byte[]>> exp = new ArrayList<>(m.k.entrySet());
        exp.sort((a, b) -> Arrays.compareUnsigned(a.getKey().getBytes(StandardCharsets.UTF_8),
                b.getKey().getBytes(StandardCharsets.UTF_8)));
        if (got.size() != exp.size()) fail(what + ": /k/ lists " + got.size() + ", model " + exp.size());
        for (int i = 0; i < exp.size(); i++) {
            if (!got.get(i).key().equals(exp.get(i).getKey()) || !Arrays.equals(got.get(i).value(), exp.get(i).getValue())) {
                fail(what + ": /k/ entry " + i + " " + got.get(i).key() + " differs from " + exp.get(i).getKey());
            }
        }
        // Objects and their indexes.
        List<Kv<Obj>> objs = new ArrayList<>();
        for (Kv<Obj> kv : c.usePrimary(Obj.class).dir("/o/").kvs()) objs.add(kv);
        List<String> ok = new ArrayList<>(m.o.keySet());
        ok.sort((a, b) -> Arrays.compareUnsigned(a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8)));
        if (objs.size() != ok.size()) fail(what + ": /o/ lists " + objs.size() + ", model " + ok.size());
        for (int i = 0; i < ok.size(); i++) {
            Obj e = m.o.get(ok.get(i)), g = objs.get(i).value();
            if (!objs.get(i).key().equals(ok.get(i)) || e.v != g.v || e.j != g.j || !Objects.equals(e.s, g.s)) {
                fail(what + ": object " + ok.get(i) + " differs");
            }
        }
        if (m.seq > 0) {
            List<String> byV = new ArrayList<>(m.o.keySet());
            byV.sort((a, b) -> m.o.get(a).v != m.o.get(b).v ? Long.compare(m.o.get(a).v, m.o.get(b).v)
                    : Arrays.compareUnsigned(a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8)));
            List<String> gv = new ArrayList<>();
            for (Kv<Obj> kv : c.useIndex("by-v", Obj.class).kvs()) gv.add(kv.key());
            if (!gv.equals(byV)) fail(what + ": index by-v lists " + gv.size() + " keys, model " + byV.size()
                    + (gv.size() == byV.size() ? " (order differs)" : ""));
            List<String> gb = new ArrayList<>();
            for (Kv<Obj> kv : c.useIndex("by-v", Obj.class).backward().kvs()) gb.add(kv.key());
            Collections.reverse(gb);
            if (!gb.equals(byV)) fail(what + ": index by-v backward differs");
            // by-s: string then v, objects without s have no entry; a prefix scan.
            String pre = "s1";
            List<String> bs = new ArrayList<>();
            for (String key : m.o.keySet()) if (m.o.get(key).s != null && m.o.get(key).s.startsWith(pre)) bs.add(key);
            bs.sort((a, b) -> {
                Obj x = m.o.get(a), y = m.o.get(b);
                int cmp = x.s.compareTo(y.s);
                if (cmp != 0) return cmp;
                if (x.v != y.v) return Long.compare(x.v, y.v);
                return Arrays.compareUnsigned(a.getBytes(StandardCharsets.UTF_8), b.getBytes(StandardCharsets.UTF_8));
            });
            List<String> gs = new ArrayList<>();
            for (Kv<Obj> kv : c.useIndex("by-s", Obj.class).prefix(pre).kvs()) gs.add(kv.key());
            if (!gs.equals(bs)) fail(what + ": index by-s prefix " + pre + " lists " + gs.size() + ", model " + bs.size());
        }
        for (int i = 0; i < CTRS; i++) {
            String cv = c.get("/ctr/c" + i + ".txt", String.class);
            long v = cv == null ? 0 : Long.parseLong(cv);
            if (v != m.ctr[i]) fail(what + ": counter " + i + " is " + v + ", model " + m.ctr[i]);
            String sv = c.get("/sum/s" + i + ".txt", String.class);
            if (!Objects.equals(sv, m.sum[i])) fail(what + ": sum " + i + " is " + sv + ", model " + m.sum[i]);
        }
        for (int i = 0; i < BIGS; i++) {
            byte[] b = c.get("/big/b" + i + ".bin", byte[].class);
            if (!Arrays.equals(b, m.big.get("/big/b" + i + ".bin"))) fail(what + ": big value " + i + " differs");
        }
    }

    public static void main(String[] args) throws Exception {
        if (args[0].equals("child")) child(args[1], Long.parseLong(args[2]));
        else parent(args[1], Long.parseLong(args[2]), Integer.parseInt(args[3]));
    }
}
