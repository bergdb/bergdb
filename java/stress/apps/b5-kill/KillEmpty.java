import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.Trans;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

import java.io.*;
import java.util.*;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;

/**
 * B5 of 026-13, from app 4 of 024-26: kills of a child JVM (SIGKILL) at random points of a
 * workload that loads keys, deletes them all (back to empty, bergdb 026-05, P8), and then
 * drives the database with small transactions and maintain() calls while reclaim cuts; one
 * transaction in seven is preceded by one whose value transformation throws, which must be
 * refused and write nothing (bergdb 026-06). Then a check of the database against the oracle.
 *
 * The workload is a deterministic function of the seed and the transaction number i, and of
 * the state before it: transaction i writes the marker key 05 4d with the value i. A child
 * opens the database, reads the marker n, replays the oracle up to n, checks that the
 * database equals it (full scan, gets), prints "R n", and goes on from n + 1; after each
 * sync it prints "S i". The parent kills it after a random delay, and checks that the next
 * child recovers at least the last synced transaction. A child that finds a difference
 * prints "FAIL ..." and exits 1. Every DBKILLS kills the parent starts a new database.
 *
 * A kill that leaves a creation that did not complete makes the next start throw
 * DatabaseNotCreatedException (bergdb 028-18): a kill inside the creating start, or, as the
 * Core API's creating start does not sync (Db.startInner), one after it returned and before
 * the creation's two records were written. The child then checks that the refused start
 * changed no file, prints "NOTCREATED", removes the stream's files and starts again, which
 * creates the database, as the exception says (bergdb 028-35). The parent accepts the
 * refusal only while nothing durable of the database was seen: no child reported a sync
 * ("S i") or recovered a transaction ("R n", n >= 0). After that the stream holds the whole
 * creation, and a refusal is a failure.
 *
 * Usage: java -cp bergdb-release.jar:out KillEmpty parent SEED DIR KILLS [DBKILLS] [maxDelayMs]
 *        java -cp bergdb-release.jar:out KillEmpty child SEED DIR NODESIZE RETAINMS [maxTx]
 */
public class KillEmpty {
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
        int done = 0, cleanExits = 0, dbs = 0, early = 0, notCreated = 0;
        long totalRecovered = 0;
        long t0 = System.currentTimeMillis();
        while (done < kills) {
            dbs++;
            long dbSeed = seed * 1000 + dbs;
            int nodeSize = 30;  // 026-08: every database a user makes has the node size 30, and no public method sets another
            int retainMs = rnd.nextInt(4) == 0 ? 3000 : 1000;
            Common.rmrf(dir);
            long maxSynced = -1, lastRecovered = -1;
            for (int k = 0; k < dbKills && done < kills; k++) {
                boolean clean = rnd.nextInt(12) == 0;
                List<String> cmd = new ArrayList<>(List.of(java, "-ea", "-Xmx1g", "-cp", cp, "KillEmpty", "child", "" + dbSeed,
                        dir.getPath(), "" + nodeSize, "" + retainMs));
                if (clean) cmd.add("" + (200 + rnd.nextInt(300)));
                ProcessBuilder pb = new ProcessBuilder(cmd).redirectErrorStream(true);
                Process p = pb.start();
                final AtomicLong synced = new AtomicLong(maxSynced);
                final AtomicLong recovered = new AtomicLong(-2);
                final AtomicBoolean refused = new AtomicBoolean();     // the child printed "NOTCREATED"
                final StringBuilder fail = new StringBuilder();
                final List<String> tail = Collections.synchronizedList(new ArrayList<>());
                Thread reader = new Thread(() -> {
                    try (BufferedReader br = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
                        String line;
                        while ((line = br.readLine()) != null) {
                            if (line.startsWith("S ")) synced.accumulateAndGet(Long.parseLong(line.substring(2)), Math::max);
                            else if (line.startsWith("R ")) recovered.set(Long.parseLong(line.substring(2)));
                            else if (line.equals("NOTCREATED")) refused.set(true);
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
                if (refused.get()) {
                    if (maxSynced >= 0 || lastRecovered >= 0) {
                        System.out.println("FAIL db " + dbs + " (seed " + dbSeed + "): a start refused it as not created "
                                + "after a sync (" + maxSynced + ") or a recovery (" + lastRecovered + ")");
                        dumpTail(tail);
                        System.exit(1);
                    }
                    notCreated++;
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
            List<String> cmd = List.of(java, "-ea", "-Xmx1g", "-cp", cp, "KillEmpty", "child", "" + dbSeed, dir.getPath(),
                    "" + nodeSize, "" + retainMs, "0");
            Process p = new ProcessBuilder(cmd).redirectErrorStream(true).start();
            String out = new String(p.getInputStream().readAllBytes());
            p.waitFor();
            if (p.exitValue() != 0 || out.contains("FAIL")) {
                System.out.println("FAIL final check of db " + dbs + ":\n" + out);
                System.exit(1);
            }
            if (out.contains("NOTCREATED\n")) {
                if (maxSynced >= 0 || lastRecovered >= 0) {
                    System.out.println("FAIL final check of db " + dbs + " (seed " + dbSeed + "): a start refused it as "
                            + "not created after a sync (" + maxSynced + ") or a recovery (" + lastRecovered + ")");
                    System.exit(1);
                }
                notCreated++;
            }
        }
        Common.log("OK KillEmpty seed " + seed + ": " + done + " kills (" + early + " aimed at the start), " + cleanExits
                + " clean exits, " + dbs + " databases, " + totalRecovered + " recoveries checked, " + notCreated
                + " creations cut and made again, "
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
        DbBuilder b = Db.builder().mainStream(new FileStream(dir, false));
        b.cacheSizeIndicator(4_000_000);
        Map<String, Long> files = streamFiles(dir);
        Db db;
        try {
            db = b.start();
        } catch (DatabaseNotCreatedException e) {
            // A kill during the creation, or before it was durable (bergdb 028-18): no data,
            // and the start wrote nothing. The parent checks that nothing durable was seen.
            Map<String, Long> after = streamFiles(dir);
            if (!after.equals(files)) fail("the refused start changed the stream's files: " + files + ", then " + after);
            System.out.println("NOTCREATED");
            System.out.flush();
            for (String name : after.keySet()) {
                if (!new File(dir, name).delete()) fail("could not remove " + name);
            }
            b = Db.builder().mainStream(new FileStream(dir, false));
            b.cacheSizeIndicator(4_000_000);
            db = b.start();
        }
        db.setStartupDistance(300_000);     // after the start since bergdb 028-13; nothing written if in force
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
                if (i % 7 == 3) poison(db, i);
                if (phaseOf(i) == 2 && i % 5 == 0) for (int c = 0; c < 4 && db.maintain(); c++) { }
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

    /** The stream's files in dir (*.bergdb), each with its length. */
    static Map<String, Long> streamFiles(File dir) {
        TreeMap<String, Long> m = new TreeMap<>();
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) if (f.getName().endsWith(".bergdb")) m.put(f.getName(), f.length());
        return m;
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

    /** The phase of transaction i: 0 load, 1 delete everything, 2 drive. */
    static int phaseOf(long i) {
        int p = (int) (i % 1500);
        return p < 150 ? 0 : p < 260 ? 1 : 2;
    }

    /** A transaction whose value transformation throws, with puts over live keys: refused, nothing written. */
    static void poison(Db db, long i) {
        Random r = new Random(seed * 7 + i);
        Trans.Builder b = db.trans();
        int k = 0;
        for (Common.K key : model.keySet()) { if (k++ > 20) break; b.put(key.b, new byte[] {0x66, 0x66}); }
        b.put(new byte[] {0x07, (byte) i}, new byte[] {0x66});
        b.put(Keys.toSegments(new byte[] {0x07, 0x7f}), null, new byte[] {1}, (tt, in, prev) -> {
            if (r.nextInt(3) == 0) return new byte[Db.MAX_VALUE_BYTES + 1];
            throw new IllegalStateException("poison " + i);
        });
        try {
            db.execute(b.build());
            fail("the poison transaction before " + i + " committed");
        } catch (DbFailedException e) {
            fail("the poison transaction before " + i + " failed the database: " + e + " cause " + e.getCause());
        } catch (DbException e) {
            // refused, as it must be
        }
    }

    /** Transaction i: a function of the seed, i and the model's state before it. */
    static LinkedHashMap<Common.K, byte[]> gen(long i) {
        Random r = new Random(seed * 1_000_003L + i);
        LinkedHashMap<Common.K, byte[]> ops = new LinkedHashMap<>();
        int phase = phaseOf(i);
        if (phase == 0) {
            int n = 100 + r.nextInt(400);
            for (int j = 0; j < n; j++) ops.put(new Common.K(key(r, i, j)), val(r));
        } else if (phase == 1) {
            // everything, in key order, 499 a transaction, until empty
            for (Common.K k : model.keySet()) {
                if (ops.size() >= 499) break;
                if (!k.equals(new Common.K(MARKER))) ops.put(k, Common.DELETED);
            }
        } else {
            // the drive: an overwrite of one key, now and then a few more
            byte[] v = new byte[200 + r.nextInt(1300)];
            r.nextBytes(v);
            ops.put(new Common.K(new byte[] {0x06, 0x01}), v);
            if (r.nextInt(20) == 0) ops.put(new Common.K(key(r, i, 0)), val(r));
            if (r.nextInt(20) == 0 && model.size() > 2) {
                Common.K k = model.higherKey(new Common.K(new byte[] {0x06, 0x01}));
                if (k != null && !k.equals(new Common.K(MARKER))) ops.put(k, Common.DELETED);
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
