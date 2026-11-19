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
 * App 4 of 024-26: kills of a child JVM (SIGKILL) at random points during a delete-heavy
 * workload with reclaim on, then a check of the database against the oracle.
 *
 * The workload is a deterministic function of the seed and the transaction number i, and of
 * the state before it: transaction i writes the marker key 05 4d with the value i. A child
 * opens the database, reads the marker n, replays the oracle up to n, checks that the
 * database equals it (full scan, gets), prints "R n", and goes on from n + 1; after each
 * sync it prints "S i". The parent kills it after a random delay, and checks that the next
 * child recovers at least the last synced transaction. A child that finds a difference
 * prints "FAIL ..." and exits 1. Every DBKILLS kills the parent starts a new database.
 *
 * Usage: java -cp bergdb-release.jar:out Kill parent SEED DIR KILLS [DBKILLS] [maxDelayMs]
 *        java -cp bergdb-release.jar:out Kill child SEED DIR NODESIZE RETAINMS [maxTx]
 */
public class Kill {
    static final byte[] MARKER = {0x05, 0x4d};

    public static void main(String[] a) throws Exception {
        if (a[0].equals("parent")) parent(a);
        else child(a);
    }

    // ---------------- parent ----------------

    static void parent(String[] a) throws Exception {
        long seed = Long.parseLong(a[1]);
        File dir = new File(a[2]);
        int kills = Integer.parseInt(a[3]);
        int dbKills = a.length > 4 ? Integer.parseInt(a[4]) : 25;
        int maxDelay = a.length > 5 ? Integer.parseInt(a[5]) : 3000;
        Random rnd = new Random(seed);
        String java = System.getProperty("java.home") + "/bin/java";
        String cp = System.getProperty("java.class.path");
        int done = 0, cleanExits = 0, dbs = 0, early = 0;
        long totalRecovered = 0;
        long t0 = System.currentTimeMillis();
        while (done < kills) {
            dbs++;
            long dbSeed = seed * 1000 + dbs;
            int nodeSize = new int[] {8, 14, 30, 62, 8, 30}[rnd.nextInt(6)];
            int retainMs = rnd.nextBoolean() ? 1000 : rnd.nextBoolean() ? 3000 : 0;
            Common.rmrf(dir);
            long maxSynced = -1, lastRecovered = -1;
            for (int k = 0; k < dbKills && done < kills; k++) {
                boolean clean = rnd.nextInt(12) == 0;
                List<String> cmd = new ArrayList<>(List.of(java, "-ea", "-Xmx1g", "-cp", cp, "Kill", "child", "" + dbSeed,
                        dir.getPath(), "" + nodeSize, "" + retainMs));
                if (clean) cmd.add("" + (200 + rnd.nextInt(300)));
                ProcessBuilder pb = new ProcessBuilder(cmd).redirectErrorStream(true);
                Process p = pb.start();
                final AtomicLong synced = new AtomicLong(maxSynced);
                final AtomicLong recovered = new AtomicLong(-2);
                final StringBuilder fail = new StringBuilder();
                final List<String> tail = Collections.synchronizedList(new ArrayList<>());
                Thread reader = new Thread(() -> {
                    try (BufferedReader br = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
                        String line;
                        while ((line = br.readLine()) != null) {
                            if (line.startsWith("S ")) synced.accumulateAndGet(Long.parseLong(line.substring(2)), Math::max);
                            else if (line.startsWith("R ")) recovered.set(Long.parseLong(line.substring(2)));
                            else {
                                tail.add(line);
                                if (tail.size() > 60) tail.remove(0);
                                if (line.startsWith("FAIL")) synchronized (fail) { fail.append(line).append('\n'); }
                            }
                        }
                    } catch (IOException e) { }
                });
                reader.start();
                long delay;
                int kind = rnd.nextInt(10);
                if (kind == 0) { delay = rnd.nextInt(400); early++; }       // during the start or the check
                else delay = 300 + rnd.nextInt(maxDelay);
                boolean exited;
                if (clean) exited = p.waitFor(600, TimeUnit.SECONDS);   // a hang, not a speed: 120 s until 028-23, generous for a loaded machine
                else if (kind == 0) exited = p.waitFor(delay, TimeUnit.MILLISECONDS);
                else {
                    // Most kills count their delay from the child's "R" line, so that they land in the work.
                    long until = System.currentTimeMillis() + 60_000;
                    while (recovered.get() == -2 && p.isAlive() && System.currentTimeMillis() < until) Thread.sleep(2);
                    exited = p.waitFor(delay - 250, TimeUnit.MILLISECONDS);
                }
                if (!exited) {
                    if (clean) { System.out.println("FAIL a clean child did not end in 600 s"); dumpTail(tail); p.destroyForcibly(); System.exit(1); }
                    p.destroyForcibly();
                    p.waitFor();
                }
                reader.join();
                int code = p.exitValue();
                if (fail.length() > 0 || (exited && code != 0)) {
                    System.out.println("FAIL child of db " + dbs + " (seed " + dbSeed + ", node " + nodeSize + ", retain "
                            + retainMs + ") after kill " + done + ", exit " + code + ":");
                    dumpTail(tail);
                    System.exit(1);
                }
                long r = recovered.get();
                if (r != -2) {
                    if (r < maxSynced) {
                        System.out.println("FAIL db " + dbs + ": recovered transaction " + r + " but " + maxSynced
                                + " was synced (seed " + dbSeed + ", node " + nodeSize + ")");
                        dumpTail(tail);
                        System.exit(1);
                    }
                    if (r < lastRecovered) {
                        System.out.println("FAIL db " + dbs + ": recovered " + r + " after an earlier start recovered "
                                + lastRecovered + " (seed " + dbSeed + ")");
                        System.exit(1);
                    }
                    lastRecovered = r;
                    totalRecovered++;
                }
                maxSynced = Math.max(maxSynced, synced.get());
                if (clean) cleanExits++; else done++;
                if ((done + cleanExits) % 25 == 0) Common.log("kills " + done + ", clean exits " + cleanExits + ", databases "
                        + dbs + ", last recovered " + lastRecovered + ", synced " + maxSynced + ", node " + nodeSize
                        + ", retain " + retainMs);
            }
            // A last start that checks the state, with no kill.
            List<String> cmd = List.of(java, "-ea", "-Xmx1g", "-cp", cp, "Kill", "child", "" + dbSeed, dir.getPath(),
                    "" + nodeSize, "" + retainMs, "0");
            Process p = new ProcessBuilder(cmd).redirectErrorStream(true).start();
            String out = new String(p.getInputStream().readAllBytes());
            p.waitFor();
            if (p.exitValue() != 0 || out.contains("FAIL")) {
                System.out.println("FAIL final check of db " + dbs + ":\n" + out);
                System.exit(1);
            }
        }
        Common.log("OK Kill seed " + seed + ": " + done + " kills (" + early + " aimed at the start), " + cleanExits
                + " clean exits, " + dbs + " databases, " + totalRecovered + " recoveries checked, "
                + (System.currentTimeMillis() - t0) / 1000 + " s");
    }

    static void dumpTail(List<String> tail) {
        synchronized (tail) { for (String s : tail) System.out.println("  | " + s); }
    }

    // ---------------- child ----------------

    static long seed;
    static TreeMap<Common.K, byte[]> model = new TreeMap<>();
    static int keyCounter;

    static void child(String[] a) throws Exception {
        seed = Long.parseLong(a[1]);
        File dir = new File(a[2]);
        int nodeSize = Integer.parseInt(a[3]);
        int retainMs = Integer.parseInt(a[4]);
        long maxTx = a.length > 5 ? Long.parseLong(a[5]) : Long.MAX_VALUE;
        dir.mkdirs();
        DbBuilder b = TestNodeSize.builder(nodeSize).mainStream(new FileStream(dir, false)).startupDistance(300_000);  // TestNodeSize: since 026-08 the size setters are package-private (028-23)
        b.cacheSizeIndicator(4_000_000);
        Db db = b.start();
        try {
            // Recover: the marker, the replay, the check.
            GetData gd = db.newGetData();
            byte[] mv = db.getOne(Long.MAX_VALUE, Keys.toSegments(MARKER), gd);
            long n = mv == null ? -1 : java.nio.ByteBuffer.wrap(mv).getLong();
            for (long i = 0; i <= n; i++) {
                LinkedHashMap<Common.K, byte[]> ops = gen(i);
                applyModel(ops);
            }
            List<Kvt> got = Common.scanAll(db, Long.MAX_VALUE, null);
            int idx = 0;
            Iterator<Map.Entry<Common.K, byte[]>> it = model.entrySet().iterator();
            for (Kvt kvt : got) {
                Common.K k = new Common.K(Keys.toBytes(kvt.key));
                if (!it.hasNext()) fail("recovered " + n + ": extra KV " + k + " at " + idx);
                Map.Entry<Common.K, byte[]> e = it.next();
                if (!e.getKey().equals(k)) fail("recovered " + n + ": index " + idx + " key " + k + ", expected " + e.getKey()
                        + " (model has " + model.size() + " KVs, the scan " + got.size() + ")");
                if (!Arrays.equals(e.getValue(), kvt.value)) fail("recovered " + n + ": key " + k + " value "
                        + Common.hex(kvt.value) + ", expected " + Common.hex(e.getValue()));
                idx++;
            }
            if (it.hasNext()) fail("recovered " + n + ": missing KV " + it.next().getKey() + " (model " + model.size()
                    + ", scan " + got.size() + ")");
            // Gets of keys deleted and present.
            Random vr = new Random(n);
            List<Common.K> ks = new ArrayList<>(model.keySet());
            for (int i = 0; i < 200 && !ks.isEmpty(); i++) {
                Common.K k = ks.get(vr.nextInt(ks.size()));
                if (!Arrays.equals(db.getOne(Long.MAX_VALUE, Keys.toSegments(k.b), gd), model.get(k))) fail("get " + k);
            }
            System.out.println("R " + n);
            System.out.flush();
            if (retainMs > 0 && db.getRetainDuration() != retainMs * 10_000L) db.setRetainDuration(retainMs * 10_000L);
            // Go on.
            long end = maxTx == Long.MAX_VALUE ? Long.MAX_VALUE : n + 1 + maxTx;
            for (long i = n + 1; i < end; i++) {
                LinkedHashMap<Common.K, byte[]> ops = gen(i);
                Trans.Builder tb = db.trans();
                for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) {
                    if (e.getValue() == Common.DELETED) tb.delete(e.getKey().b);
                    else tb.put(e.getKey().b, e.getValue());
                }
                db.execute(tb.build());
                applyModel(ops);
                if (i % 17 == 0) {
                    db.sync(SyncLevel.ORDINARY);
                    System.out.println("S " + i);
                    System.out.flush();
                }
            }
            db.close();
        } catch (Throwable t) {
            System.out.println("FAIL child exception: " + t);
            t.printStackTrace(System.out);
            System.out.flush();
            Runtime.getRuntime().halt(1);
        }
    }

    static void fail(String s) {
        System.out.println("FAIL " + s);
        System.out.flush();
        Runtime.getRuntime().halt(1);
    }

    static void applyModel(LinkedHashMap<Common.K, byte[]> ops) {
        for (Map.Entry<Common.K, byte[]> e : ops.entrySet()) {
            if (e.getValue() == Common.DELETED) model.remove(e.getKey());
            else model.put(e.getKey(), e.getValue());
        }
    }

    /** Transaction i: a function of the seed, i and the model's state before it. */
    static LinkedHashMap<Common.K, byte[]> gen(long i) {
        Random r = new Random(seed * 1_000_003L + i);
        LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
        int phase = (int) (i % 300);
        if (phase < 60) {
            int n = 100 + r.nextInt(400);
            for (int j = 0; j < n; j++) ops.put(new Common.K(key(r, i, j)), val(r));
        } else if (phase < 140 && !model.isEmpty()) {
            // scattered deletes: keys chosen from the model by random probes
            int n = 50 + r.nextInt(450);
            for (int j = 0; j < n; j++) {
                byte[] probe = new byte[1 + r.nextInt(8)];
                r.nextBytes(probe);
                Common.K k = model.ceilingKey(new Common.K(probe));
                if (k == null) k = model.firstKey();
                ops.put(k, Common.DELETED);
            }
        } else if (phase < 170 && !model.isEmpty()) {
            // a ranged delete in key order
            byte[] probe = new byte[1 + r.nextInt(4)];
            r.nextBytes(probe);
            int n = 100 + r.nextInt(400);
            for (Common.K k : model.tailMap(new Common.K(probe), true).keySet()) {
                if (ops.size() >= n) break;
                ops.put(k, Common.DELETED);
            }
        } else {
            // churn: overwrites, deletes and re-puts of a hot range
            int n = 1 + r.nextInt(60);
            byte[] probe = {0x10, (byte) ((i / 50) % 256)};
            List<Common.K> hot = new ArrayList<>();
            for (Common.K k : model.tailMap(new Common.K(probe), true).keySet()) { if (hot.size() >= 300) break; hot.add(k); }
            for (int j = 0; j < n; j++) {
                if (hot.isEmpty() || r.nextInt(4) == 0) ops.put(new Common.K(key(r, i, j)), val(r));
                else {
                    Common.K k = hot.get(r.nextInt(hot.size()));
                    ops.put(k, r.nextInt(3) == 0 ? Common.DELETED : val(r));
                }
            }
        }
        ops.remove(new Common.K(MARKER));
        while (ops.size() > Db.MAX_OPERATIONS - 1) ops.remove(ops.keySet().iterator().next());
        ops.put(new Common.K(MARKER), java.nio.ByteBuffer.allocate(8).putLong(i).array());
        return ops;
    }

    static byte[] key(Random r, long i, int j) {
        int shape = r.nextInt(4);
        switch (shape) {
            case 0: return new byte[] {0x10, (byte) r.nextInt(256), (byte) r.nextInt(256), (byte) r.nextInt(256)};
            case 1: {
                byte[] k = new byte[20];
                Arrays.fill(k, (byte) 0x44);
                k[0] = 0x20;
                k[17] = (byte) r.nextInt(256); k[18] = (byte) r.nextInt(256); k[19] = (byte) r.nextInt(256);
                return k;
            }
            case 2: {
                byte[] k = new byte[2 + r.nextInt(Db.MAX_KEY_BYTES - 1)];
                r.nextBytes(k);
                k[0] = 0x30;
                return k;
            }
            default: {
                // keys in time order, as a log
                return new byte[] {0x40, (byte) (i >>> 24), (byte) (i >>> 16), (byte) (i >>> 8), (byte) i, (byte) j, (byte) (j >>> 8)};
            }
        }
    }

    static byte[] val(Random r) {
        int x = r.nextInt(100);
        byte[] v = new byte[x < 70 ? r.nextInt(30) : x < 98 ? r.nextInt(300) : r.nextInt(6000)];
        r.nextBytes(v);
        return v;
    }
}
