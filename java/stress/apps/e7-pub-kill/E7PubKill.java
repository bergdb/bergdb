import bergdb.pub.*;
import bergdb.pub.util.JobStatus;

import java.io.*;
import java.nio.ByteBuffer;
import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

/**
 * App e7 of 031-08: SIGKILLs of a child JVM that writes objects in an indexed directory,
 * builds, deletes and makes indexes again, and calls maintain(budget), under a retain
 * duration (Pub API, file databases, a test clock that the child moves).
 *
 * The child's actions are a function of the seed and the action number i and the state
 * before it: transaction i, a w() of 1 to 40 puts and deletes of objects (a long n, a String
 * s) in /e7/obj/ and of byte[] values in /e7/bin/, with the marker /e7/marker.bin holding i
 * and /e7/log/(i mod 32).bin the time of transaction i - 1. Every 97th action deletes the
 * index "by-s" if it exists and starts it again (its build runs while the next transactions
 * commit); "by-n" is made at the start and stays. maintain() calls (budgets 100 to 100,000)
 * follow some transactions, printed "M i" before and "m i" after. Transaction i runs at
 * T0 + i x 50 ms; the retain duration is 1 or 3 s. A child starts the database, joins the
 * builds that the start resumed, reads the marker n, replays the oracle to n and checks: the
 * listing of both directories at the latest state, every object and value; the index "by-n"
 * whole, both ways, and from() a bound, against the oracle's objects in the index's order
 * (n, then the key's name); "by-s" the same if it is active; for 2 logged times at or after
 * the first available time, the listing of /e7/obj/ there against the oracle after that
 * transaction. Then it prints "R n" and goes on, syncing every 11th transaction ("S i"). The
 * parent kills it (SIGKILL) at a random time after "R" and checks each recovery against the
 * syncs as e4 does.
 *
 * Usage: java E7PubKill parent SEED DIR KILLS [DBKILLS] [maxDelayMs]
 *        java E7PubKill child SEED DIR RETAINMS [maxTx]
 */
public class E7PubKill {
    static final long T0 = Time.utc("2026-06-01").units();
    static final long STEP = 500_000L;

    public static class Obj {
        public long n;
        public String s;
        public Obj() {}
    }

    public static void main(String[] a) throws Exception {
        if (a[0].equals("parent")) parent(a);
        else child(a);
    }

    // ---------------- parent ----------------

    static void parent(String[] a) throws Exception {
        long seed = Long.parseLong(a[1]);
        File dir = new File(a[2]);
        int kills = Integer.parseInt(a[3]);
        int dbKills = a.length > 4 ? Integer.parseInt(a[4]) : 20;
        int maxDelay = a.length > 5 ? Integer.parseInt(a[5]) : 2500;
        Random rnd = new Random(seed);
        String java = System.getProperty("java.home") + "/bin/java";
        String cp = System.getProperty("java.class.path");
        int done = 0, cleanExits = 0, dbs = 0, inMaintain = 0, inStart = 0;
        long recoveries = 0, t0 = System.currentTimeMillis();
        while (done < kills) {
            dbs++;
            long dbSeed = seed * 1000 + dbs;
            int retainMs = rnd.nextBoolean() ? 1000 : 3000;
            EOracle.rmrf(dir);
            long maxSynced = -1, lastRecovered = -1;
            for (int k = 0; k < dbKills && done < kills; k++) {
                boolean clean = rnd.nextInt(10) == 0;
                List<String> cmd = new ArrayList<>(List.of(java, "-ea", "-Xmx1g", "-XX:+ExitOnOutOfMemoryError", "-cp", cp, "E7PubKill",
                        "child", "" + dbSeed, dir.getPath(), "" + retainMs));
                if (clean) cmd.add("" + (50 + rnd.nextInt(200)));
                Process p = new ProcessBuilder(cmd).redirectErrorStream(true).start();
                final AtomicLong synced = new AtomicLong(maxSynced), recovered = new AtomicLong(-2), inM = new AtomicLong();
                final StringBuilder fail = new StringBuilder();
                final List<String> tail = Collections.synchronizedList(new ArrayList<>());
                Thread reader = new Thread(() -> {
                    try (BufferedReader br = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
                        String line;
                        while ((line = br.readLine()) != null) {
                            if (line.startsWith("S ")) synced.accumulateAndGet(Long.parseLong(line.substring(2)), Math::max);
                            else if (line.startsWith("R ")) recovered.set(Long.parseLong(line.substring(2)));
                            else if (line.startsWith("M ")) inM.set(1);
                            else if (line.startsWith("m ")) inM.set(0);
                            else {
                                tail.add(line);
                                if (tail.size() > 60) tail.remove(0);
                                if (line.startsWith("FAIL") || line.startsWith("Exception")) synchronized (fail) { fail.append(line).append('\n'); }
                            }
                        }
                    } catch (IOException e) { }
                });
                reader.start();
                int kind = rnd.nextInt(10);
                long delay = kind == 0 ? rnd.nextInt(600) : 200 + rnd.nextInt(maxDelay);
                boolean exited;
                if (clean) exited = p.waitFor(900, TimeUnit.SECONDS);
                else if (kind == 0) exited = p.waitFor(delay, TimeUnit.MILLISECONDS);
                else {
                    long until = System.currentTimeMillis() + 120_000;
                    while (recovered.get() == -2 && p.isAlive() && System.currentTimeMillis() < until) Thread.sleep(2);
                    exited = p.waitFor(delay, TimeUnit.MILLISECONDS);
                }
                boolean wasInM = inM.get() == 1, wasInStart = recovered.get() == -2;
                if (!exited) {
                    if (clean) { System.out.println("FAIL a clean child did not end in 900 s (seed " + dbSeed + ")"); dump(tail); p.destroyForcibly(); System.exit(1); }
                    p.destroyForcibly();
                    p.waitFor();
                    if (wasInM) inMaintain++;
                    if (wasInStart) inStart++;
                }
                reader.join();
                int code = p.exitValue();
                if (fail.length() > 0 || (exited && code != 0)) {
                    System.out.println("FAIL child of db " + dbs + " (seed " + dbSeed + ", retain " + retainMs + ") after kill " + done + ", exit " + code + ":");
                    dump(tail);
                    System.exit(1);
                }
                long r = recovered.get();
                if (r != -2) {
                    if (r < maxSynced) { System.out.println("FAIL db " + dbs + ": recovered " + r + " but " + maxSynced + " was synced (seed " + dbSeed + ")"); dump(tail); System.exit(1); }
                    if (r < lastRecovered) { System.out.println("FAIL db " + dbs + ": recovered " + r + " after " + lastRecovered + " (seed " + dbSeed + ")"); System.exit(1); }
                    lastRecovered = r;
                    recoveries++;
                }
                maxSynced = Math.max(maxSynced, synced.get());
                if (clean) cleanExits++; else done++;
                if ((done + cleanExits) % 25 == 0) EOracle.log("kills " + done + " (" + inMaintain + " in maintain, " + inStart + " in a start), clean "
                        + cleanExits + ", databases " + dbs + ", last recovered " + lastRecovered + ", synced " + maxSynced);
            }
            Process p = new ProcessBuilder(List.of(java, "-ea", "-Xmx1g", "-cp", cp, "E7PubKill", "child", "" + dbSeed, dir.getPath(), "" + retainMs, "0"))
                    .redirectErrorStream(true).start();
            String out = new String(p.getInputStream().readAllBytes());
            p.waitFor();
            if (p.exitValue() != 0 || out.contains("FAIL")) { System.out.println("FAIL final check of db " + dbs + " (seed " + dbSeed + "):\n" + out); System.exit(1); }
        }
        EOracle.rmrf(dir);
        EOracle.log("OK E7PubKill seed " + seed + ": " + done + " kills (" + inMaintain + " in a maintain() call, " + inStart + " in a start), "
                + cleanExits + " clean exits, " + dbs + " databases, " + recoveries + " recoveries checked, " + (System.currentTimeMillis() - t0) / 1000 + " s");
    }

    static void dump(List<String> tail) { synchronized (tail) { for (String s : tail) System.out.println("  | " + s); } }

    // ---------------- child ----------------

    static long seed;
    // key -> (action number -> value: Obj, byte[], or null for a delete)
    static final HashMap<String, TreeMap<Long, Object>> hist = new HashMap<>();
    static final TreeMap<String, Object> live = new TreeMap<>(EOracle.ORDER);

    static void child(String[] a) throws Exception {
        seed = Long.parseLong(a[1]);
        File dir = new File(a[2]);
        int retainMs = Integer.parseInt(a[3]);
        long maxTx = a.length > 4 ? Long.parseLong(a[4]) : Long.MAX_VALUE;
        TestClock clock = new TestClock();
        Database db = null;
        try {
            try {
                db = Factory.database().create(dir.getPath()).clock(clock).cacheSizeInMb(16).start();
            } catch (bergdb.pub.util.DatabaseNotCreatedException e) {
                for (File f : dir.listFiles()) if (f.getName().endsWith(".bergdb") || f.getName().equals("created.txt")) f.delete();
                db = Factory.database().create(dir.getPath()).clock(clock).cacheSizeInMb(16).start();
            }
            Connection c = db.connection();
            byte[] mv = c.get("/e7/marker.bin", byte[].class);
            long n = mv == null ? -1 : ByteBuffer.wrap(mv).getLong();
            clock.setTime(Time.units(Math.max(T0 + (n + 1) * STEP, clock.getTime())));
            if (n < 0) {
                db.setStartupDistanceInMb(5);
                db.setRetainDuration(Duration.units(retainMs * 10_000L));
                try { db.indexBuilder("by-n").dir("/e7/obj/").type("long").field("n").start().join(); }
                catch (IndexAlreadyExistsException e) { db.indexJob("by-n").join(); }
            } else {
                EOracle.check(db.getRetainDuration().equals(Duration.units(retainMs * 10_000L)), "recovered " + n + ": the retain duration " + db.getRetainDuration());
            }
            for (String name : new String[] {"by-n", "by-s"}) {
                try {
                    JobStatus st = db.indexJob(name).join();
                    EOracle.check(st.state() == JobStatus.State.ACTIVE, "recovered " + n + ": the build of " + name + " ended " + st.state());
                } catch (NoSuchIndexException e) {
                    if (name.equals("by-n")) {   // its creation may be lost with the stream's tail only while n < 0
                        EOracle.check(n < 0, "recovered " + n + ": no index by-n");
                        db.indexBuilder("by-n").dir("/e7/obj/").type("long").field("n").start().join();
                    }
                }
            }
            for (long i = 0; i <= n; i++) applyModel(gen(i, null), i);
            check(db, c, n);
            System.out.println("R " + n);
            System.out.flush();
            if (new Random(seed + n).nextInt(3) == 0) {      // maintain() right after the start that recovered
                System.out.println("M " + n); System.out.flush();
                db.maintain(new int[] {100, 100_000}[new Random(seed - n).nextInt(2)]);
                System.out.println("m " + n); System.out.flush();
            }
            long end = maxTx == Long.MAX_VALUE ? Long.MAX_VALUE : n + 1 + maxTx;
            long prevTime = -2;
            for (long i = n + 1; i < end; i++) {
                clock.setTime(Time.units(Math.max(T0 + i * STEP, clock.getTime())));
                if (i % 97 == 50) {
                    try { db.deleteIndex("by-s"); } catch (NoSuchIndexException e) { }
                    db.indexBuilder("by-s").dir("/e7/obj/").type("string").field("s").start();
                }
                WBuilder w = c.w();
                LinkedHashMap<String, Object> ops = gen(i, w);
                long logged = prevTime == -2 ? db.currentTime().units() : prevTime;
                w.put("/e7/log/" + ((i - 1 + 32) % 32) + ".bin", ByteBuffer.allocate(16).putLong(i - 1).putLong(logged).array());
                Transaction t = w.execute();
                prevTime = t.getTime().units();
                applyModel(ops, i);
                if (i % 11 == 0) { db.sync(); System.out.println("S " + i); System.out.flush(); }
                Random r = new Random(seed * 31 + i);
                int nm = i % 200 >= 120 && i % 200 < 126 ? 3 + r.nextInt(6) : r.nextInt(5) == 0 ? 1 : 0;
                for (int k = 0; k < nm; k++) {
                    clock.setTime(Time.units(clock.getTime() + 20_000));
                    System.out.println("M " + i); System.out.flush();
                    db.maintain(new int[] {100, 2000, 100_000}[r.nextInt(3)]);
                    System.out.println("m " + i); System.out.flush();
                }
            }
            if (maxTx == 0) check(db, c, n);
            db.close();
        } catch (Throwable t) {
            System.out.println("FAIL child exception: " + t);
            t.printStackTrace(System.out);
            System.out.flush();
            Runtime.getRuntime().halt(1);
        }
    }

    static void applyModel(Map<String, Object> ops, long i) {
        for (Map.Entry<String, Object> e : ops.entrySet()) {
            hist.computeIfAbsent(e.getKey(), x -> new TreeMap<>()).put(i, e.getValue());
            if (e.getValue() == null) live.remove(e.getKey()); else live.put(e.getKey(), e.getValue());
        }
    }

    static Object at(String k, long i) {
        TreeMap<Long, Object> h = hist.get(k);
        if (h == null) return null;
        Map.Entry<Long, Object> e = h.floorEntry(i);
        return e == null ? null : e.getValue();
    }

    /** Transaction i's KVs (and, with w, its calls): a function of the seed, i and the state before. */
    static LinkedHashMap<String, Object> gen(long i, WBuilder w) {
        Random r = new Random(seed * 1_000_003L + i);
        LinkedHashMap<String, Object> ops = new LinkedHashMap<>();
        int phase = (int) (i % 200);
        int n = phase < 40 ? 20 + r.nextInt(20) : phase >= 110 && phase < 120 ? 40 : 1 + r.nextInt(12);
        List<String> objs = new ArrayList<>();
        if (phase >= 110 && phase < 120) for (String k : live.keySet()) if (k.startsWith("/e7/obj/")) objs.add(k);
        for (int j = 0; j < n; j++) {
            if (phase >= 110 && phase < 120) {       // a mass delete of objects
                if (objs.isEmpty()) break;
                String k = objs.get(r.nextInt(objs.size()));
                ops.put(k, null);
                continue;
            }
            if (r.nextInt(3) == 0) {
                String k = "/e7/bin/b" + r.nextInt(400) + ".bin";
                if (r.nextInt(4) == 0) ops.put(k, null);
                else ops.put(k, EOracle.value(r, r.nextInt(30) == 0 ? 50_000 + r.nextInt(400_000) : r.nextInt(500)));
            } else {
                String k = "/e7/obj/o" + r.nextInt(500);
                if (r.nextInt(5) == 0) ops.put(k, null);
                else { Obj o = new Obj(); o.n = r.nextInt(1000) - 300; o.s = r.nextInt(8) == 0 ? null : "s" + r.nextInt(50); ops.put(k, o); }
            }
        }
        ops.put("/e7/marker.bin", ByteBuffer.allocate(8).putLong(i).array());
        if (w != null) for (Map.Entry<String, Object> e : ops.entrySet()) { if (e.getValue() == null) w.delete(e.getKey()); else w.put(e.getKey(), e.getValue()); }
        return ops;
    }

    static boolean same(Object want, Object got) {
        if (want == null || got == null) return want == got;
        if (want instanceof byte[]) return got instanceof byte[] && Arrays.equals((byte[]) want, (byte[]) got);
        Obj x = (Obj) want, y = (Obj) got;
        return x.n == y.n && Objects.equals(x.s, y.s);
    }

    static void check(Database db, Connection c, long n) {
        c.setLookupTime(Time.MAX);
        listing(c, "/e7/obj/", n, "recovered " + n);
        listing(c, "/e7/bin/", n, "recovered " + n);
        indexScan(c, "by-n", n, "recovered " + n);
        try { indexScan(c, "by-s", n, "recovered " + n); } catch (NoSuchIndexException e) { }
        long first = db.getFirstAvailableLookupTime().units();
        List<long[]> logged = new ArrayList<>();
        for (int s = 0; s < 32; s++) {
            byte[] lv = c.get("/e7/log/" + s + ".bin", byte[].class);
            if (lv == null) continue;
            ByteBuffer bb = ByteBuffer.wrap(lv);
            long j = bb.getLong(), tj = bb.getLong();
            if (j >= 0 && j < n && j >= n - 31 && tj >= first) logged.add(new long[] {j, tj});
        }
        Random vr = new Random(n);
        Connection oc = db.newConnection();
        for (int k = 0; k < 2 && !logged.isEmpty(); k++) {
            long[] jt = logged.get(vr.nextInt(logged.size()));
            oc.setLookupTime(Time.units(jt[1]));
            listing(oc, "/e7/obj/", jt[0], "recovered " + n + ", at the time " + jt[1] + " of transaction " + jt[0]);
            indexScan(oc, "by-n", jt[0], "recovered " + n + ", at the time of " + jt[0]);
        }
    }

    static void listing(Connection c, String d, long i, String what) {
        TreeMap<String, Object> want = new TreeMap<>(EOracle.ORDER);
        for (String k : hist.keySet()) if (k.startsWith(d) && at(k, i) != null) want.put(k, at(k, i));
        Iterator<Map.Entry<String, Object>> it = want.entrySet().iterator();
        Class<?> type = d.equals("/e7/obj/") ? Obj.class : byte[].class;
        for (Kv<?> kv : c.usePrimary(type).dir(d).kvs()) {
            EOracle.check(it.hasNext(), what + ": listing of " + d + " has an extra " + kv.key());
            Map.Entry<String, Object> e = it.next();
            EOracle.check(e.getKey().equals(kv.key()), what + ": listing of " + d + ": " + kv.key() + ", expected " + e.getKey());
            EOracle.check(same(e.getValue(), kv.value()), what + ": the value at " + kv.key() + " differs");
        }
        EOracle.check(!it.hasNext(), what + ": listing of " + d + " lacks " + (it.hasNext() ? it.next().getKey() : ""));
    }

    static void indexScan(Connection c, String name, long i, String what) {
        List<String> want = new ArrayList<>();
        for (String k : hist.keySet()) {
            if (!k.startsWith("/e7/obj/")) continue;
            Object v = at(k, i);
            if (v instanceof Obj && (name.equals("by-n") || ((Obj) v).s != null)) want.add(k);
        }
        Comparator<String> ord = name.equals("by-n")
                ? Comparator.comparingLong((String k) -> ((Obj) at(k, i)).n).thenComparing((x, y) -> EOracle.ORDER.compare(x, y))
                : Comparator.comparing((String k) -> ((Obj) at(k, i)).s).thenComparing((x, y) -> EOracle.ORDER.compare(x, y));
        want.sort(ord);
        for (int q = 0; q < 2; q++) {
            List<String> got = new ArrayList<>();
            UseIndexBuilder<Obj> b = c.useIndex(name, Obj.class);
            if (q == 1) b.backward();
            for (Kv<Obj> kv : b.kvs()) {
                got.add(kv.key());
                EOracle.check(same(at(kv.key(), i), kv.value()), what + ": index " + name + " gives a value at " + kv.key() + " that differs");
            }
            List<String> w = new ArrayList<>(want);
            if (q == 1) Collections.reverse(w);
            EOracle.check(got.equals(w), what + ": index " + name + (q == 1 ? " backward" : "") + ": " + got.size() + " entries, expected " + w.size()
                    + (got.isEmpty() || w.isEmpty() ? "" : ", first " + got.get(0) + " / " + w.get(0)));
        }
        if (name.equals("by-n")) {
            List<String> got = new ArrayList<>();
            for (Kv<Obj> kv : c.useIndex(name, Obj.class).from(100, false).kvs()) got.add(kv.key());
            List<String> w = new ArrayList<>();
            for (String k : want) if (((Obj) at(k, i)).n > 100) w.add(k);
            EOracle.check(got.equals(w), what + ": index by-n from 100 exclusive: " + got.size() + ", expected " + w.size());
        }
    }
}
