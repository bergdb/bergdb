import bergdb.pub.*;

import java.io.*;
import java.lang.management.ManagementFactory;
import java.nio.ByteBuffer;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

/**
 * B3 of 026-13: many small databases open at once, opened and closed again and again, and
 * bursty writers with idle gaps around 2 s, about the write buffer that grows with the write
 * rate and shrinks after 2 s with nothing to write (bergdb 026-07). Written from the Javadoc
 * of DatabaseBuilder (startupDistanceInMb), Database (stop, close, the write buffer and the
 * buffer time) and Connection only.
 *
 * Mode many: NDB file databases open at once; worker threads pick a database, write a burst
 * (small values, or values of up to 1 MB that fill the buffer), and leave it idle for 1.5 to
 * 2.5 s; others close a database and open it again (half by stop() then close()), or open
 * one of a spare pool, write a little and close it. Every read is checked against the
 * databases' models; every reopen checks all keys. At the end, on NDB new databases with a
 * cache of 1 MB: the heap of each just started (about 0.7 MB, DatabaseBuilder; FAIL over 1 MB),
 * 0.3 s after a fast write of small values (the buffers grown), 3.5 s and 10 s after, and after
 * a close and an open of each; 3.5 s after the writes and a sync of each the heap must be within 500 kB a
 * database of the reopened one (the buffers shrank back); on a loaded machine 10 s after will do, with a NOTE.
 *
 * Mode kill: a child JVM writes bursts with idle gaps around 2 s to NDB databases, each
 * transaction i of a database a function of the seed, the database and i, with a marker;
 * it syncs some and prints what it committed and synced. The parent SIGKILLs it at a random
 * time, a checker child opens every database and checks its contents against the function
 * at its marker; the marker must be at or after the last synced transaction, and should be
 * at or after the last transaction committed 2 s before the kill ("written ... once the
 * buffer time, 50 ms, has passed", Database.stop()).
 *
 * Each database has a cache budget of 2 MB (DatabaseBuilder.cacheSizeInMb), so that the heap is the buffers'.
 *
 * Usage: java -cp bergdb-release.jar:out Buffers many SEED NDB SECONDS DIR
 *        java -cp bergdb-release.jar:out Buffers kill SEED DIR KILLS NDB
 */
public class Buffers {
    public static void main(String[] a) throws Exception {
        try {
            main2(a);
        } catch (Common.Fail f) {
            System.out.println("FAIL Buffers " + String.join(" ", a) + ": " + f.getMessage());
            System.exit(1);
        }
    }

    static void main2(String[] a) throws Exception {
        switch (a[0]) {
            case "many": many(Long.parseLong(a[1]), Integer.parseInt(a[2]), Integer.parseInt(a[3]), new File(a[4])); break;
            case "kill": killParent(Long.parseLong(a[1]), new File(a[2]), Integer.parseInt(a[3]), Integer.parseInt(a[4])); break;
            case "child": child(Long.parseLong(a[1]), new File(a[2]), Integer.parseInt(a[3])); break;
            case "check": check(Long.parseLong(a[1]), new File(a[2]), Integer.parseInt(a[3])); break;
            default: throw new IllegalArgumentException(a[0]);
        }
    }

    // ================= many =================

    static final class Slot {
        final File dir;
        Database db;                                     // null while closed
        final TreeMap<String, Long> model = new TreeMap<>();   // key -> the seed of its value (gen)
        long lastWrite;                                  // ms
        int opens, bursts;
        Slot(File dir) { this.dir = dir; }
    }

    static volatile String failure;
    static final AtomicLong bursts = new AtomicLong(), txs = new AtomicLong(), bytes = new AtomicLong(), reopens = new AtomicLong(),
            spareCycles = new AtomicLong(), gaps = new AtomicLong();

    static void many(long seed, int ndb, int seconds, File root) throws Exception {
        Common.rmrf(root);
        long t0 = System.currentTimeMillis();
        List<Slot> slots = new ArrayList<>();
        for (int i = 0; i < ndb; i++) {
            Slot s = new Slot(new File(root, "db" + i));
            s.db = Factory.database().cacheSizeInMb(2).create(s.dir.getPath()).start();
            s.opens++;
            slots.add(s);
        }
        List<Slot> spare = new ArrayList<>();
        for (int i = 0; i < 40; i++) spare.add(new Slot(new File(root, "spare" + i)));
        System.gc();
        Common.log("opened " + ndb + " databases; heap used " + used() / 1_000_000 + " MB");
        long end = System.currentTimeMillis() + seconds * 1000L;
        List<Thread> ts = new ArrayList<>();
        for (int w = 0; w < 6; w++) {
            final Random r = new Random(seed * 101 + w);
            ts.add(new Thread(() -> run(() -> { while (System.currentTimeMillis() < end && failure == null) burst(slots, r); })));
        }
        for (int w = 0; w < 2; w++) {
            final Random r = new Random(seed * 103 + w);
            ts.add(new Thread(() -> run(() -> { while (System.currentTimeMillis() < end && failure == null) reopen(slots, r); })));
        }
        final Random sr = new Random(seed * 107);
        ts.add(new Thread(() -> run(() -> { while (System.currentTimeMillis() < end && failure == null) spareCycle(spare, sr); })));
        for (Thread t : ts) t.start();
        long nextLog = System.currentTimeMillis() + 15_000;
        while (System.currentTimeMillis() < end && failure == null) {
            Thread.sleep(200);
            if (System.currentTimeMillis() > nextLog) {
                Common.log("bursts " + bursts + ", transactions " + txs + ", " + bytes.get() / 1_000_000 + " MB, gaps near 2 s "
                        + gaps + ", reopens " + reopens + ", spare cycles " + spareCycles + ", heap used " + used() / 1_000_000 + " MB");
                nextLog += 15_000;
            }
        }
        for (Thread t : ts) t.join();
        if (failure != null) { System.out.println("FAIL Buffers many seed " + seed + ": " + failure); closeAll(slots); System.exit(1); }
        // Every database against its model.
        for (Slot s : slots) verify(s, "end");
        long heap = heapPhase(slots, new Random(seed * 109));
        for (Slot s : slots) {
            s.db = Factory.database().cacheSizeInMb(2).open(s.dir.getPath()).start();
            verify(s, "end after a restart");
            s.db.close();
        }
        for (Slot s : spare) {
            if (s.opens == 0) continue;
            s.db = Factory.database().cacheSizeInMb(2).open(s.dir.getPath()).start();
            verify(s, "spare at the end");
            s.db.close();
        }
        Common.log("OK Buffers many seed " + seed + ": " + ndb + " databases, " + bursts + " bursts, " + txs + " transactions, "
                + bytes.get() / 1_000_000 + " MB, " + gaps + " gaps of 1.5 to 2.5 s, " + reopens + " reopens, " + spareCycles
                + " open-write-close cycles, buffers' heap after 3.5 s idle " + heap / 1000 + " kB a database, " + (System.currentTimeMillis() - t0) / 1000 + " s");
        Common.rmrf(root);
    }

    /**
     * The heap of the buffers: all closed (the base), all open with a cache of 1 MB, then a fast
     * write of small values to each (the buffer grows with the write rate), then the heap 0.3 s
     * and 3.5 s after the last write. Returns the heap a database 3.5 s after, above the open's.
     */
    static long heapPhase(List<Slot> given, Random r) throws Exception {
        int n = given.size();
        closeAll(given);
        File root = given.get(0).dir.getParentFile();
        List<Slot> slots = new ArrayList<>();                       // new databases, small: the Javadoc's case
        for (int i = 0; i < n; i++) slots.add(new Slot(new File(root, "heap" + i)));
        long base = usedAfterGc();
        for (Slot s : slots) s.db = Factory.database().cacheSizeInMb(1).create(s.dir.getPath()).start();
        long open = usedAfterGc();
        List<Thread> ts = new ArrayList<>();
        for (int w = 0; w < 6; w++) {
            final int ww = w;
            ts.add(new Thread(() -> run(() -> {
                Random rr = new Random(ww);
                for (int i = ww; i < n; i += 6) {
                    Slot s = slots.get(i);
                    Connection c = s.db.newConnection();
                    for (int t = 0; t < 20; t++) {
                        WBuilder wb = c.w();
                        for (int k = 0; k < 500; k++) {
                            long vs = rr.nextLong() & ~1L;
                            String key = "/b/" + (k % 400) + ".bin";
                            wb.put(key, gen(vs));
                            s.model.put(key, vs);
                        }
                        wb.execute();
                    }
                }
            })));
        }
        for (Thread t : ts) t.start();
        for (Thread t : ts) t.join();
        if (failure != null) throw new Common.Fail(failure);
        // The 2 s count from "nothing to write" (DatabaseBuilder): with 150 databases the buffers still wrote
        // a backlog of about 1 GB after the last put, and shrank 3.4 to 4.1 s after it (soak 1, the curve);
        // so the clock starts when sync() has returned on each.
        for (Slot s : slots) s.db.sync();
        Thread.sleep(300);
        long soon = usedAfterGc();
        if (Boolean.getBoolean("curve")) {                     // -Dcurve=true: the heap after GC every 0.5 s for 12 s, then on
            long t0 = System.currentTimeMillis() - 600;
            StringBuilder sb = new StringBuilder("heap curve after the writes (s: MB):");
            while (System.currentTimeMillis() - t0 < 12_000) {
                Thread.sleep(200);
                sb.append(String.format(" %.1f: %d", (System.currentTimeMillis() - t0) / 1000.0, usedAfterGc() / 1_000_000));
            }
            Common.log(sb.toString());
        }
        Thread.sleep(3200);
        long idle = usedAfterGc();
        Thread.sleep(6500);
        long idle10 = usedAfterGc();
        for (Slot s : slots) { s.db.close(); s.db = Factory.database().cacheSizeInMb(1).open(s.dir.getPath()).start(); }
        long reopened = usedAfterGc();
        Common.log("heap: " + idle10 / 1_000_000 + " MB 10 s after the writes, " + reopened / 1_000_000
                + " MB after a close and an open of each (" + (reopened - base) / n / 1000 + " kB a database)");
        long perDb = (idle - open) / n;
        Common.log("heap: " + base / 1_000_000 + " MB all closed, " + open / 1_000_000 + " MB with " + n + " open ("
                + (open - base) / n / 1000 + " kB a database), " + soon / 1_000_000 + " MB 0.3 s after a fast write to each ("
                + (soon - open) / n / 1000 + " kB a database more), " + idle / 1_000_000 + " MB 3.5 s after (" + perDb / 1000
                + " kB a database more than when opened)");
        // The buffers have shrunk: the heap 3.5 s after the writes is about that of the same databases just
        // opened again (what remains is their data's, which a start loads; not the buffers').
        // On a loaded machine the 2 idle s can come later than 3.5 s after the syncs (028-23: the kind of
        // the test is functional, its result must not depend on speed): then 10 s after is the check, and
        // 3.5 s only a NOTE.
        if ((idle - reopened) / n > 500_000) {
            if ((idle10 - reopened) / n > 500_000) throw new Common.Fail("heap " + (idle - reopened) / n / 1000 + " kB 3.5 s and "
                    + (idle10 - reopened) / n / 1000 + " kB 10 s after the writes and syncs, a database more than after a close"
                    + " and an open: the buffers did not shrink");
            Common.log("NOTE heap " + (idle - reopened) / n / 1000 + " kB a database more 3.5 s after the writes and syncs than"
                    + " after a close and an open, " + (idle10 - reopened) / n / 1000 + " kB 10 s after: the buffers shrank late"
                    + " (a loaded machine?)");
        }
        if ((open - base) / n > 1_000_000) throw new Common.Fail("a new database holds " + (open - base) / n / 1000 + " kB, not about 0.7 MB");
        for (Slot s : slots) verify(s, "after the heap phase");
        closeAll(slots);
        return (idle - reopened) / n;
    }

    interface Body { void run() throws Exception; }

    static void run(Body b) {
        try { b.run(); }
        catch (Throwable t) {
            StringWriter sw = new StringWriter();
            t.printStackTrace(new PrintWriter(sw));
            if (failure == null) { failure = t.getMessage() + "\n" + sw; System.out.println("FAILURE in a thread: " + failure); System.out.flush(); }
        }
    }

    static long used() { return ManagementFactory.getMemoryMXBean().getHeapMemoryUsage().getUsed(); }

    static long usedAfterGc() throws InterruptedException {
        for (int i = 0; i < 3; i++) { System.gc(); Thread.sleep(100); }
        return used();
    }

    static void closeAll(List<Slot> slots) {
        for (Slot s : slots) synchronized (s) { if (s.db != null) { try { s.db.close(); } catch (Throwable t) { } s.db = null; } }
    }

    /** A value's seed: its size and its bytes follow from it (gen), so the model holds a long a key. */
    static long value(Random r, boolean big) {
        long s = r.nextLong() & ~1L;
        return big ? s | 1L : s;
    }

    static byte[] gen(Long s) {
        if (s == null) return null;
        Random r = new Random(s);
        byte[] v = new byte[(s & 1) == 1 ? 100_000 + r.nextInt(1_000_000) : r.nextInt(300)];
        r.nextBytes(v);
        return v;
    }

    /** A burst on one database that is idle: then 1.5 to 2.5 s with nothing to write. */
    static void burst(List<Slot> slots, Random r) throws Exception {
        Slot s = slots.get(r.nextInt(slots.size()));
        synchronized (s) {
            if (s.db == null) return;
            long now = System.currentTimeMillis();
            long idle = now - s.lastWrite;
            if (s.lastWrite != 0 && idle < 1500) return;          // let it be idle at least 1.5 s
            if (s.lastWrite != 0 && idle <= 2500) gaps.incrementAndGet();
            boolean big = r.nextInt(10) == 0;
            int n = big ? 5 + r.nextInt(30) : 20 + r.nextInt(300);
            Connection c = s.db.newConnection();
            for (int i = 0; i < n; i++) {
                int k = r.nextInt(400);
                String key = "/b/" + k + ".bin";
                if (r.nextInt(8) == 0) {
                    c.delete(key);
                    s.model.remove(key);
                } else if (r.nextInt(4) == 0) {
                    WBuilder w = c.w();
                    Map<String, Long> m = new HashMap<>();
                    for (int j = 0; j < 1 + r.nextInt(20); j++) {
                        long vs = value(r, big && j == 0);
                        byte[] v = gen(vs);
                        String kk = "/b/" + r.nextInt(400) + ".bin";
                        w.put(kk, v);
                        m.put(kk, vs);
                        bytes.addAndGet(v.length);
                    }
                    w.execute();
                    s.model.putAll(m);
                } else {
                    long vs = value(r, big);
                    byte[] v = gen(vs);
                    c.put(key, v);
                    s.model.put(key, vs);
                    bytes.addAndGet(v.length);
                }
                txs.incrementAndGet();
                if (r.nextInt(20) == 0) {
                    String kk = "/b/" + r.nextInt(400) + ".bin";
                    byte[] got = c.get(kk, byte[].class);
                    if (!Arrays.equals(got, gen(s.model.get(kk)))) throw new Common.Fail(s.dir.getName() + ": get " + kk + " in a burst: "
                            + Common.hex(got) + ", expected " + Common.hex(gen(s.model.get(kk))));
                }
            }
            if (r.nextInt(5) == 0) s.db.sync();
            s.lastWrite = System.currentTimeMillis();
            s.bursts++;
            bursts.incrementAndGet();
        }
        Thread.sleep(r.nextInt(30));
    }

    static void verify(Slot s, String what) {
        Connection c = s.db.newConnection();
        int n = 0;
        for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/b/").kvs()) {
            byte[] exp = gen(s.model.get(kv.key()));
            if (!Arrays.equals(exp, kv.value())) throw new Common.Fail(what + ": " + s.dir.getName() + " " + kv.key() + " = "
                    + Common.hex(kv.value()) + ", expected " + Common.hex(exp));
            n++;
        }
        if (n != s.model.size()) throw new Common.Fail(what + ": " + s.dir.getName() + " has " + n + " keys, expected " + s.model.size());
    }

    /** Closes a database and opens it again, at once or after an idle gap; then checks every key. */
    static void reopen(List<Slot> slots, Random r) throws Exception {
        Slot s = slots.get(r.nextInt(slots.size()));
        synchronized (s) {
            if (s.db == null) return;
            if (r.nextBoolean()) s.db.stop();
            s.db.close();
            s.db = Factory.database().cacheSizeInMb(2).open(s.dir.getPath()).start();
            s.opens++;
            verify(s, "reopen");
            reopens.incrementAndGet();
        }
        Thread.sleep(200 + r.nextInt(800));
    }

    /** Opens a spare database, writes a little or a lot, closes it (sometimes stop() alone first). */
    static void spareCycle(List<Slot> spare, Random r) throws Exception {
        Slot s = spare.get(r.nextInt(spare.size()));
        s.db = (s.opens == 0 ? Factory.database().cacheSizeInMb(2).create(s.dir.getPath()) : Factory.database().cacheSizeInMb(2).open(s.dir.getPath())).start();
        s.opens++;
        verify(s, "spare open");
        Connection c = s.db.newConnection();
        int n = r.nextInt(30);
        for (int i = 0; i < n; i++) {
            String key = "/b/" + r.nextInt(100) + ".bin";
            long vs = value(r, r.nextInt(10) == 0);
            c.put(key, gen(vs));
            s.model.put(key, vs);
        }
        if (r.nextBoolean()) s.db.stop();
        s.db.close();
        s.db = null;
        spareCycles.incrementAndGet();
    }

    // ================= kill =================

    static final int SLOTS = 40;

    /** The value of slot j as transaction i of database d wrote it. */
    static byte[] tval(long seed, int d, long i) {
        Random r = new Random(seed * 1_000_003L + d * 7_919L + i);
        int size = i % 97 < 6 ? 200_000 + r.nextInt(900_000) : r.nextInt(400);
        byte[] v = new byte[size + 8];
        r.nextBytes(v);
        ByteBuffer.wrap(v).putLong(i);
        return v;
    }

    static void child(long seed, File root, int ndb) throws Exception {
        Database[] dbs = new Database[ndb];
        long[] next = new long[ndb];
        for (int d = 0; d < ndb; d++) {
            File f = new File(root, "db" + d);
            boolean exists = f.exists() && Objects.requireNonNull(f.list()).length > 1;
            dbs[d] = (exists ? Factory.database().open(f.getPath()) : Factory.database().create(f.getPath())).start();
            String mk = dbs[d].connection().get("/m/i.txt", String.class);
            next[d] = mk == null ? 0 : Long.parseLong(mk) + 1;
        }
        System.out.println("READY");
        System.out.flush();
        Random r = new Random(seed ^ System.nanoTime());
        long[] lastWrite = new long[ndb];
        while (true) {
            int d = r.nextInt(ndb);
            long now = System.currentTimeMillis();
            if (lastWrite[d] != 0 && now - lastWrite[d] < 1500 + r.nextInt(1000)) { Thread.sleep(5); continue; }
            Connection c = dbs[d].connection();
            int n = 1 + r.nextInt(r.nextBoolean() ? 10 : 150);
            for (int k = 0; k < n; k++) {
                long i = next[d]++;
                Transaction t = c.w().put("/s/" + (i % SLOTS) + ".bin", tval(seed, d, i)).put("/m/i.txt", "" + i).execute();
                System.out.println("C " + d + " " + i + " " + System.currentTimeMillis());
                if (r.nextInt(40) == 0) { t.sync(); System.out.println("S " + d + " " + i); }
            }
            lastWrite[d] = System.currentTimeMillis();
        }
    }

    static void check(long seed, File root, int ndb) throws Exception {
        for (int d = 0; d < ndb; d++) {
            File f = new File(root, "db" + d);
            if (!f.exists()) { System.out.println("M " + d + " -1"); continue; }
            try (Database db = Factory.database().open(f.getPath()).start()) {
                Connection c = db.connection();
                String mk = c.get("/m/i.txt", String.class);
                long n = mk == null ? -1 : Long.parseLong(mk);
                for (int j = 0; j < SLOTS; j++) {
                    long last = n - Math.floorMod(n - j, SLOTS);          // the last i <= n with i % SLOTS == j
                    byte[] exp = last >= 0 ? tval(seed, d, last) : null;
                    byte[] got = c.get("/s/" + j + ".bin", byte[].class);
                    if (!Arrays.equals(exp, got)) {
                        System.out.println("FAIL db" + d + " marker " + n + ": slot " + j + " = " + Common.hex(got) + ", expected "
                                + Common.hex(exp) + " (transaction " + last + ")");
                        System.exit(1);
                    }
                }
                System.out.println("M " + d + " " + n);
            } catch (bergdb.pub.util.DatabaseNotCreatedException e) {
                System.out.println("M " + d + " -1");
            }
        }
        System.out.println("CHECKED");
    }

    static void killParent(long seed, File root, int kills, int ndb) throws Exception {
        Common.rmrf(root);
        root.mkdirs();
        Random rnd = new Random(seed);
        String java = System.getProperty("java.home") + "/bin/java";
        String cp = System.getProperty("java.class.path");
        long[] synced = new long[ndb], committedBefore = new long[ndb], lastRecovered = new long[ndb];
        Arrays.fill(synced, -1);
        Arrays.fill(lastRecovered, -1);
        long late = 0, checkedTx = 0, t0 = System.currentTimeMillis();
        for (int k = 0; k < kills; k++) {
            Process p = new ProcessBuilder(java, "-Xmx1g", "-cp", cp, "Buffers", "child", "" + seed, root.getPath(), "" + ndb)
                    .redirectErrorStream(true).start();
            final ConcurrentHashMap<Integer, TreeMap<Long, Long>> commits = new ConcurrentHashMap<>();   // d -> i -> ms
            final long[] syncedNow = synced.clone();
            final List<String> other = Collections.synchronizedList(new ArrayList<>());
            final AtomicLong ready = new AtomicLong();
            Thread reader = new Thread(() -> {
                try (BufferedReader br = new BufferedReader(new InputStreamReader(p.getInputStream()))) {
                    String line;
                    while ((line = br.readLine()) != null) {
                        String[] f = line.split(" ");
                        if (line.startsWith("C ")) {
                            TreeMap<Long, Long> m = commits.computeIfAbsent(Integer.parseInt(f[1]), x -> new TreeMap<>());
                            synchronized (m) { m.put(Long.parseLong(f[2]), Long.parseLong(f[3])); }
                        } else if (line.startsWith("S ")) {
                            int d = Integer.parseInt(f[1]);
                            synchronized (syncedNow) { syncedNow[d] = Math.max(syncedNow[d], Long.parseLong(f[2])); }
                        } else if (line.equals("READY")) ready.set(System.currentTimeMillis());
                        else { other.add(line); if (other.size() > 40) other.remove(0); }
                    }
                } catch (IOException e) { }
            });
            reader.start();
            long until = System.currentTimeMillis() + 300_000;    // a hang, not a speed: 60 s until 028-23
            while (ready.get() == 0 && p.isAlive() && System.currentTimeMillis() < until) Thread.sleep(5);
            if (ready.get() == 0) { System.out.println("FAIL the child did not start in 300 s: " + other); p.destroyForcibly(); System.exit(1); }
            Thread.sleep(500 + rnd.nextInt(6000));
            long killMs = System.currentTimeMillis();
            p.destroyForcibly();
            p.waitFor();
            reader.join();
            if (!other.isEmpty()) { System.out.println("FAIL the child printed: " + other); System.exit(1); }
            Process c = new ProcessBuilder(java, "-Xmx1g", "-cp", cp, "Buffers", "check", "" + seed, root.getPath(), "" + ndb)
                    .redirectErrorStream(true).start();
            String out = new String(c.getInputStream().readAllBytes());
            c.waitFor();
            if (c.exitValue() != 0 || !out.contains("CHECKED")) { System.out.println("FAIL check after kill " + k + ":\n" + out); System.exit(1); }
            for (String line : out.split("\n")) {
                if (!line.startsWith("M ")) continue;
                String[] f = line.split(" ");
                int d = Integer.parseInt(f[1]);
                long n = Long.parseLong(f[2]);
                if (n < syncedNow[d]) {
                    System.out.println("FAIL db" + d + " after kill " + k + ": recovered " + n + " but " + syncedNow[d] + " was synced");
                    System.exit(1);
                }
                if (n < lastRecovered[d]) {
                    System.out.println("FAIL db" + d + " after kill " + k + ": recovered " + n + " after " + lastRecovered[d] + " before");
                    System.exit(1);
                }
                TreeMap<Long, Long> cm = commits.get(d);
                if (cm != null) {
                    long old = -1;
                    for (Map.Entry<Long, Long> e : cm.entrySet()) if (e.getValue() <= killMs - 2000) old = e.getKey();
                    checkedTx += cm.size();
                    if (old > n) {
                        late++;
                        System.out.println("LATE db" + d + " after kill " + k + ": recovered " + n + ", but " + old + " was committed at "
                                + (killMs - cm.get(old)) + " ms before the kill (the first lost one " + (killMs - cm.get(n + 1)) + " ms before)");
                    }
                }
                lastRecovered[d] = n;
            }
            synced = syncedNow;
            if (k % 10 == 9) Common.log("kills " + (k + 1) + ", committed transactions seen " + checkedTx + ", lost after 2 s: " + late);
        }
        Common.log((late == 0 ? "OK" : "NOTE") + " Buffers kill seed " + seed + ": " + kills + " kills, " + ndb + " databases, "
                + checkedTx + " committed transactions seen, " + late + " databases lost a transaction committed 2 s or more before the kill, "
                + (System.currentTimeMillis() - t0) / 1000 + " s");
        Common.rmrf(root);
    }
}
