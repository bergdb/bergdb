import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.TestNodeSize;
import bergdb.core.Trans;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

import java.io.*;
import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

/**
 * App e4 of 031-08: SIGKILLs of a child JVM inside commits and inside maintain(budget) calls,
 * with reclaim under a clock that the child moves (Core API, node sizes 8 to 62 through
 * TestNodeSize, file streams).
 *
 * The child's actions are a function of the seed, the action number i and the state before
 * it: transaction i (loads, scattered and ranged deletes, mass deletes of half the keys,
 * churn of a hot range, values up to 6 kB and now and then 100 kB to 2 MB) writes the marker
 * 05 4d with i and, at 05 4c with (i mod 64), the time of transaction i - 1; between
 * transactions, maintain(budget) calls (budgets 100 to 100,000, long ones after the mass
 * deletes), each printed "M i" before and "m i" after. The clock is the child's: transaction
 * i runs at T0 + i x 20 ms and a maintain() call after it at that plus 1 ms a call, so the
 * retain duration (1 or 3 s, 50 or 150 transactions) and a small startup distance (100 kB to
 * 1 MB) make reclaim cut often. A child opens the database, reads the marker n, replays the
 * oracle to n (a versioned model, transaction j at the model time j), and checks: a full scan
 * and 300 gets at the latest state; for 3 of the last 63 transactions whose logged times are
 * at or after getFirstAvailableLookupTime(), the full state at that time against the
 * model's state after that transaction; then prints "R n" and goes on, syncing every 13th
 * transaction ("S i"). The parent kills it (SIGKILL) at a random time after its "R" line,
 * counts where the kill landed (in a maintain() call or not), and checks that each recovery
 * is at or after the last synced transaction and not before the last recovery. Every DBKILLS
 * kills a new database; each ends with a clean run that checks and closes.
 *
 * Usage: java E4KillMaintain parent SEED DIR KILLS [DBKILLS] [maxDelayMs]
 *        java E4KillMaintain child SEED DIR NODESIZE RETAINMS SD [maxTx]
 */
public class E4KillMaintain {
    static final byte[] MARKER = {0x05, 0x4d};
    static final long T0 = 17_700_000_000_000_000L;   // 2026-02 in clock units
    static final long STEP = 200_000L;                  // 20 ms a transaction

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
        long recoveries = 0;
        long t0 = System.currentTimeMillis();
        while (done < kills) {
            dbs++;
            long dbSeed = seed * 1000 + dbs;
            int nodeSize = new int[] {8, 14, 30, 62, 8, 62}[rnd.nextInt(6)];
            int retainMs = rnd.nextBoolean() ? 1000 : 3000;
            int sd = new int[] {100_000, 300_000, 1_000_000}[rnd.nextInt(3)];
            Common.rmrf(dir);
            long maxSynced = -1, lastRecovered = -1;
            for (int k = 0; k < dbKills && done < kills; k++) {
                boolean clean = rnd.nextInt(10) == 0;
                List<String> cmd = new ArrayList<>(List.of(java, "-ea", "-Xmx2g", "-XX:+ExitOnOutOfMemoryError", "-cp", cp,
                        "E4KillMaintain", "child", "" + dbSeed, dir.getPath(), "" + nodeSize, "" + retainMs, "" + sd));
                if (clean) cmd.add("" + (100 + rnd.nextInt(300)));
                Process p = new ProcessBuilder(cmd).redirectErrorStream(true).start();
                final AtomicLong synced = new AtomicLong(maxSynced);
                final AtomicLong recovered = new AtomicLong(-2);
                final AtomicLong inM = new AtomicLong(0);       // 1 while the child is in a maintain() call
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
                long delay = kind == 0 ? rnd.nextInt(500) : 200 + rnd.nextInt(maxDelay);
                boolean exited;
                if (clean) exited = p.waitFor(900, TimeUnit.SECONDS);   // a hang guard
                else if (kind == 0) exited = p.waitFor(delay, TimeUnit.MILLISECONDS);
                else {
                    long until = System.currentTimeMillis() + 120_000;
                    while (recovered.get() == -2 && p.isAlive() && System.currentTimeMillis() < until) Thread.sleep(2);
                    exited = p.waitFor(delay, TimeUnit.MILLISECONDS);
                }
                boolean wasInM = inM.get() == 1;
                boolean wasInStart = recovered.get() == -2;
                if (!exited) {
                    if (clean) { System.out.println("FAIL a clean child did not end in 900 s (seed " + dbSeed + ")"); dumpTail(tail); p.destroyForcibly(); System.exit(1); }
                    p.destroyForcibly();
                    p.waitFor();
                    if (wasInM) inMaintain++;
                    if (wasInStart) inStart++;
                }
                reader.join();
                int code = p.exitValue();
                if (fail.length() > 0 || (exited && code != 0)) {
                    System.out.println("FAIL child of db " + dbs + " (seed " + dbSeed + ", node " + nodeSize + ", retain " + retainMs
                            + ", sd " + sd + ") after kill " + done + ", exit " + code + ":");
                    dumpTail(tail);
                    System.exit(1);
                }
                long r = recovered.get();
                if (r != -2) {
                    if (r < maxSynced) {
                        System.out.println("FAIL db " + dbs + ": recovered transaction " + r + " but " + maxSynced + " was synced (seed "
                                + dbSeed + ", node " + nodeSize + ", sd " + sd + ")");
                        dumpTail(tail);
                        System.exit(1);
                    }
                    if (r < lastRecovered) {
                        System.out.println("FAIL db " + dbs + ": recovered " + r + " after an earlier start recovered " + lastRecovered
                                + " (seed " + dbSeed + ")");
                        System.exit(1);
                    }
                    lastRecovered = r;
                    recoveries++;
                }
                maxSynced = Math.max(maxSynced, synced.get());
                if (clean) cleanExits++; else done++;
                if ((done + cleanExits) % 25 == 0) Common.log("kills " + done + " (" + inMaintain + " in maintain, " + inStart
                        + " in a start), clean exits " + cleanExits + ", databases " + dbs + ", last recovered " + lastRecovered
                        + ", synced " + maxSynced + ", node " + nodeSize + ", sd " + sd + ", retain " + retainMs);
            }
            List<String> cmd = List.of(java, "-ea", "-Xmx2g", "-cp", cp, "E4KillMaintain", "child", "" + dbSeed, dir.getPath(),
                    "" + nodeSize, "" + retainMs, "" + sd, "0");
            Process p = new ProcessBuilder(cmd).redirectErrorStream(true).start();
            String out = new String(p.getInputStream().readAllBytes());
            p.waitFor();
            if (p.exitValue() != 0 || out.contains("FAIL")) {
                System.out.println("FAIL final check of db " + dbs + " (seed " + dbSeed + "):\n" + out);
                System.exit(1);
            }
        }
        Common.rmrf(dir);
        Common.log("OK E4KillMaintain seed " + seed + ": " + done + " kills (" + inMaintain + " in a maintain() call, " + inStart
                + " in a start), " + cleanExits + " clean exits, " + dbs + " databases, " + recoveries + " recoveries checked, "
                + (System.currentTimeMillis() - t0) / 1000 + " s");
    }

    static void dumpTail(List<String> tail) {
        synchronized (tail) { for (String s : tail) System.out.println("  | " + s); }
    }

    // ---------------- child ----------------

    static long seed;
    static final Common.Model model = new Common.Model();   // transaction j at the model time j
    static final Common.ManualClock clock = new Common.ManualClock(T0);
    static long olderChecked;

    static void child(String[] a) throws Exception {
        seed = Long.parseLong(a[1]);
        File dir = new File(a[2]);
        int nodeSize = Integer.parseInt(a[3]);
        int retainMs = Integer.parseInt(a[4]);
        int sd = Integer.parseInt(a[5]);
        long maxTx = a.length > 6 ? Long.parseLong(a[6]) : Long.MAX_VALUE;
        dir.mkdirs();
        Db db;
        try {
            db = builder(nodeSize, dir).start();
        } catch (bergdb.pub.util.DatabaseNotCreatedException e) {
            // a kill inside the creating start: no data; remove the files and create again (its Javadoc)
            for (File f : dir.listFiles()) if (f.getName().endsWith(".bergdb")) f.delete();
            db = builder(nodeSize, dir).start();
        }
        try {
            GetData gd = db.newGetData();
            byte[] mv = db.getOne(Long.MAX_VALUE, Keys.toSegments(MARKER), gd);
            long n = mv == null ? -1 : java.nio.ByteBuffer.wrap(mv).getLong();
            clock.t.set(T0 + (n + 1) * STEP);
            if (n < 0) {
                db.setStartupDistance(sd);
                db.setRetainDuration(retainMs * 10_000L);
            }
            for (long i = 0; i <= n; i++) {
                model.apply(gen(i), i);
                if (i % 64 == 0 && i > 64) model.prune(i - 64);   // the checks read the last 63 transactions' states only
            }
            if (n > 64) model.prune(n - 64);
            check(db, n);
            System.out.println("R " + n);
            System.out.println("older states checked " + olderChecked);
            System.out.flush();
            long end = maxTx == Long.MAX_VALUE ? Long.MAX_VALUE : n + 1 + maxTx;
            long prevTime = -1;
            if (n >= 0) {
                prevTime = -2;   // the time of n is not known after a restart: a currentTime() before n + 1
                // the settings: those of the last change at or before n, or of a change just before n + 1, whose
                // call came before transaction n + 1 and may be there without it (Database.setRetainDuration())
                long c = lastChange(n);
                long[] want = settings(c, retainMs, sd), next = (n + 1) % CHANGE == CHANGE / 2 ? settings(n + 1, retainMs, sd) : want;
                long gotR = db.getRetainDuration(), gotS = db.getStartupDistance();
                if (!((gotR == want[0] && gotS == want[1]) || (gotR == next[0] && gotS == next[1]) || (gotR == next[0] && gotS == want[1])))
                    fail("recovered " + n + ": the retain duration " + gotR + " and the startup distance " + gotS + ", expected " + want[0] + " and "
                            + want[1] + (next != want ? " (or " + next[0] + " and " + next[1] + ")" : ""));
            }
            for (long i = n + 1; i < end; i++) {
                clock.t.set(T0 + i * STEP);
                if (i % CHANGE == CHANGE / 2) {           // the settings change before transaction i
                    long[] st = settings(i, retainMs, sd);
                    db.setRetainDuration(st[0]);
                    db.setStartupDistance((int) st[1]);
                }
                LinkedHashMap<Common.K, byte[]> ops = gen(i);
                Trans.Builder tb = db.trans();
                for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) {
                    if (e.getValue() == Common.DELETED) tb.delete(e.getKey().b);
                    else tb.put(e.getKey().b, e.getValue());
                }
                long logged = prevTime == -2 ? db.currentTime() : prevTime;   // at most the time of i - 1, never after it
                tb.put(new byte[] {0x05, 0x4c, (byte) ((i - 1 + 64) % 64)}, java.nio.ByteBuffer.allocate(16).putLong(i - 1).putLong(logged).array());
                Trans t = tb.build();
                db.execute(t);
                prevTime = t.tt;
                model.apply(ops, i);
                if (i % 64 == 0 && i > 64) model.prune(i - 64);
                if (i % 13 == 0) {
                    db.sync(SyncLevel.ORDINARY);
                    System.out.println("S " + i);
                    System.out.flush();
                }
                Random r = new Random(seed * 7_000_003L + i);
                int nm = maintainCalls(i, r);
                for (int k = 0; k < nm; k++) {
                    clock.t.addAndGet(10_000L);
                    int budget = r.nextInt(5) == 0 ? 100_000 : r.nextInt(4) == 0 ? 100 : 100 + r.nextInt(20_000);
                    System.out.println("M " + i);
                    System.out.flush();
                    db.maintain(budget);
                    System.out.println("m " + i);
                    System.out.flush();
                }
            }
            if (maxTx == 0) check(db, n);
            db.close();
        } catch (Throwable t) {
            System.out.println("FAIL child exception: " + t);
            t.printStackTrace(System.out);
            System.out.flush();
            Runtime.getRuntime().halt(1);
        }
    }

    /** The settings change every CHANGE transactions, before transaction k with k % CHANGE == CHANGE / 2. */
    static final int CHANGE = 150;

    static long lastChange(long n) {
        if (n < CHANGE / 2) return -1;
        return (n - CHANGE / 2) / CHANGE * CHANGE + CHANGE / 2;
    }

    /** {retain duration, startup distance} from the change at k on (k = -1: the creation's). */
    static long[] settings(long k, int retainMs, int sd) {
        if (k < 0) return new long[] {retainMs * 10_000L, sd};
        Random r = new Random(seed * 13 + k);
        return new long[] {new long[] {10_000_000L, 30_000_000L, 5_000_000_000L}[r.nextInt(3)],
                new int[] {100_000, 300_000, 1_000_000, sd}[r.nextInt(4)]};
    }

    static DbBuilder builder(int nodeSize, File dir) throws IOException {
        DbBuilder b = TestNodeSize.builder(nodeSize).mainStream(new FileStream(dir, false)).clock(clock);
        b.cacheSizeIndicator(8_000_000);
        return b;
    }

    /** How many maintain() calls follow transaction i. */
    static int maintainCalls(long i, Random r) {
        int phase = (int) (i % 400);
        if (phase >= 140 && phase < 150) return 3 + r.nextInt(10);       // after the mass delete
        return r.nextInt(4) == 0 ? 1 + r.nextInt(3) : 0;
    }

    /** The checks after a recovery to the marker n. */
    static void check(Db db, long n) {
        GetData gd = db.newGetData();
        // the latest state
        List<Kvt> got = scan(db, Long.MAX_VALUE);
        compare(got, model.stateAt(n), "recovered " + n + ", latest");
        Random vr = new Random(n);
        List<Common.K> ks = new ArrayList<>(model.hist.keySet());
        for (int i = 0; i < 300 && !ks.isEmpty(); i++) {
            Common.K k = ks.get(vr.nextInt(ks.size()));
            byte[] got1 = db.getOne(Long.MAX_VALUE, Keys.toSegments(k.b), gd);
            if (!Arrays.equals(got1, model.valueAt(k, n))) fail("recovered " + n + ": get " + k + " gave " + Common.hex(got1)
                    + ", expected " + Common.hex(model.valueAt(k, n)));
        }
        // older states, by the logged times
        long first = db.getFirstAvailableLookupTime();
        List<long[]> logged = new ArrayList<>();
        for (int s = 0; s < 64; s++) {
            byte[] lv = db.getOne(Long.MAX_VALUE, Keys.toSegments(new byte[] {0x05, 0x4c, (byte) s}), gd);
            if (lv == null) continue;
            java.nio.ByteBuffer bb = java.nio.ByteBuffer.wrap(lv);
            long j = bb.getLong(), tj = bb.getLong();
            if (j >= 0 && j < n && j >= n - 63 && tj >= first) logged.add(new long[] {j, tj});
        }
        for (int c = 0; c < 3 && !logged.isEmpty(); c++) {
            long[] jt = logged.get(vr.nextInt(logged.size()));
            // the logged time is that of transaction j, or after a restart a currentTime() before j + 1: the state after j
            List<Kvt> old = scan(db, jt[1]);
            TreeMap<Common.K, byte[]> exp = model.stateAt(jt[0]);
            if (!same(old, exp)) compare(old, exp, "recovered " + n + ", at the time " + jt[1] + " of transaction " + jt[0]
                    + " (first available " + first + ")");
            olderChecked++;
        }
    }

    /** A full scan at t, BergDB's keys and the log keys 05 4c xx (not in the model) left out. */
    static List<Kvt> scan(Db db, long t) {
        List<Kvt> l = new ArrayList<>();
        for (Kvt kvt : Common.scanAll(db, t, null)) {
            byte[] k = Keys.toBytes(kvt.key);
            if (k.length == 3 && k[0] == 0x05 && k[1] == 0x4c) continue;
            l.add(kvt);
        }
        return l;
    }

    static boolean same(List<Kvt> got, TreeMap<Common.K, byte[]> exp) {
        if (got.size() != exp.size()) return false;
        Iterator<Map.Entry<Common.K, byte[]>> it = exp.entrySet().iterator();
        for (Kvt kvt : got) {
            Map.Entry<Common.K, byte[]> e = it.next();
            if (!e.getKey().equals(new Common.K(Keys.toBytes(kvt.key))) || !Arrays.equals(e.getValue(), kvt.value)) return false;
        }
        return true;
    }

    static void compare(List<Kvt> got, TreeMap<Common.K, byte[]> exp, String what) {
        int idx = 0;
        Iterator<Map.Entry<Common.K, byte[]>> it = exp.entrySet().iterator();
        for (Kvt kvt : got) {
            Common.K k = new Common.K(Keys.toBytes(kvt.key));
            if (!it.hasNext()) fail(what + ": extra KV " + k + " at " + idx);
            Map.Entry<Common.K, byte[]> e = it.next();
            if (!e.getKey().equals(k)) fail(what + ": index " + idx + " key " + k + ", expected " + e.getKey() + " (model " + exp.size()
                    + " KVs, the scan " + got.size() + ")");
            if (!Arrays.equals(e.getValue(), kvt.value)) fail(what + ": key " + k + " value " + Common.hex(kvt.value) + ", expected "
                    + Common.hex(e.getValue()));
            idx++;
        }
        if (it.hasNext()) fail(what + ": missing KV " + it.next().getKey() + " (model " + exp.size() + ", scan " + got.size() + ")");
    }

    static void fail(String s) {
        System.out.println("FAIL " + s);
        System.out.flush();
        Runtime.getRuntime().halt(1);
    }

    /** Transaction i: a function of the seed, i and the model's state before it. */
    static LinkedHashMap<Common.K, byte[]> gen(long i) {
        Random r = new Random(seed * 1_000_003L + i);
        LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
        TreeMap<Common.K, byte[]> live = model.latest;
        int phase = (int) (i % 400);
        if (phase < 60) {
            int n = 50 + r.nextInt(440);
            for (int j = 0; j < n; j++) ops.put(new Common.K(key(r, i, j)), val(r));
        } else if (phase < 140) {
            if (r.nextInt(3) == 0 && !live.isEmpty()) {
                int n = 20 + r.nextInt(300);
                for (int j = 0; j < n; j++) {
                    byte[] probe = new byte[1 + r.nextInt(6)];
                    r.nextBytes(probe);
                    Common.K k = live.ceilingKey(new Common.K(probe));
                    if (k == null) k = live.firstKey();
                    ops.put(k, r.nextInt(3) == 0 ? val(r) : Common.DELETED);
                }
            } else {
                int n = 1 + r.nextInt(40);
                for (int j = 0; j < n; j++) ops.put(new Common.K(key(r, i, j)), val(r));
            }
        } else if (phase < 150 && !live.isEmpty()) {
            // the mass delete: every second live key, from a random start, 480 a transaction
            int n = 480;
            byte[] probe = new byte[1 + r.nextInt(3)];
            r.nextBytes(probe);
            int s = 0;
            for (Common.K k : live.tailMap(new Common.K(probe), true).keySet()) {
                if (ops.size() >= n) break;
                if (s++ % 2 == 0) ops.put(k, Common.DELETED);
            }
            for (Common.K k : live.keySet()) {
                if (ops.size() >= n) break;
                if (s++ % 2 == 0) ops.put(k, Common.DELETED);
            }
        } else {
            int n = 1 + r.nextInt(30);
            byte[] probe = {0x10, (byte) ((i / 40) % 256)};
            List<Common.K> hot = new ArrayList<>();
            for (Common.K k : live.tailMap(new Common.K(probe), true).keySet()) { if (hot.size() >= 200) break; hot.add(k); }
            for (int j = 0; j < n; j++) {
                if (hot.isEmpty() || r.nextInt(4) == 0) ops.put(new Common.K(key(r, i, j)), val(r));
                else {
                    Common.K k = hot.get(r.nextInt(hot.size()));
                    ops.put(k, r.nextInt(3) == 0 ? Common.DELETED : val(r));
                }
            }
        }
        ops.remove(new Common.K(MARKER));
        for (int s = 0; s < 64; s++) ops.remove(new Common.K(new byte[] {0x05, 0x4c, (byte) s}));
        while (ops.size() > Db.MAX_OPERATIONS - 2) ops.remove(ops.keySet().iterator().next());
        long bytes = 0;
        for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) bytes += e.getValue().length;
        if (bytes > 30_000_000) for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) if (e.getValue().length > 100_000) e.setValue(new byte[1]);
        ops.put(new Common.K(MARKER), java.nio.ByteBuffer.allocate(8).putLong(i).array());
        return ops;
    }

    static byte[] key(Random r, long i, int j) {
        switch (r.nextInt(4)) {
            case 0: return new byte[] {0x10, (byte) r.nextInt(256), (byte) r.nextInt(256), (byte) r.nextInt(256)};
            case 1: {
                byte[] k = new byte[Db.MAX_KEY_BYTES];          // at the limit, a long shared start
                Arrays.fill(k, (byte) 0x44);
                k[0] = 0x20;
                k[108] = (byte) r.nextInt(256); k[109] = (byte) r.nextInt(256); k[110] = (byte) r.nextInt(256);
                return k;
            }
            case 2: {
                byte[] k = new byte[2 + r.nextInt(Db.MAX_KEY_BYTES - 1)];
                r.nextBytes(k);
                k[0] = 0x30;
                return k;
            }
            default:
                return new byte[] {0x40, (byte) (i >>> 24), (byte) (i >>> 16), (byte) (i >>> 8), (byte) i, (byte) j, (byte) (j >>> 8)};
        }
    }

    static byte[] val(Random r) {
        int x = r.nextInt(1000);
        // a value of 0.1 to 2 MB in one KV of 2,000 (one of 500 until kill round 3, whose final check ran out of a heap of 1 GB:
        // the oracle and the check's scan each hold every live value)
        byte[] v = new byte[x < 700 ? r.nextInt(30) : x < 985 ? r.nextInt(600) : x < 998 ? r.nextInt(6000)
                : r.nextInt(4) == 0 ? 100_000 + r.nextInt(1_900_000) : r.nextInt(6000)];
        r.nextBytes(v);
        return v;
    }
}
