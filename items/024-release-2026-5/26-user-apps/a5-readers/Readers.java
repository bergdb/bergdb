import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.dag.GetMany;
import bergdb.dag.Kvt;
import bergdb.stream.FileStream;

import java.io.File;
import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

/**
 * App 5 of 024-26: readers at older times while a writer deletes. One writer runs bulk
 * loads, scattered and ranged deletes, deletes of most keys and churn; R reader threads
 * read at times the writer has published (full scans, gets, range scans) and at the latest
 * state, and compare each result with the oracle's state at the read's actual lookup time.
 * With a retain duration, a read may be cut: then the first available lookup time must be
 * after the read's time.
 *
 * Usage: java -cp bergdb-release.jar:out Readers SEED NODESIZE KEYS SECONDS READERS DIR [retainMs]
 */
public class Readers {
    static final Common.Model m = new Common.Model();
    static final AtomicBoolean stop = new AtomicBoolean();
    static final AtomicReference<String> failure = new AtomicReference<>();
    static final AtomicLong reads = new AtomicLong(), cut = new AtomicLong(), scans = new AtomicLong();
    static final List<Long> published = Collections.synchronizedList(new ArrayList<>());
    static Db db;
    static long retain;

    public static void main(String[] a) throws Exception {
        long seed = Long.parseLong(a[0]);
        int nodeSize = Integer.parseInt(a[1]);
        int keys = Integer.parseInt(a[2]);
        int seconds = Integer.parseInt(a[3]);
        int readers = Integer.parseInt(a[4]);
        File dir = new File(a[5]);
        long retainMs = a.length > 6 ? Long.parseLong(a[6]) : 0;
        retain = retainMs * 10_000L;
        Common.rmrf(dir);
        DbBuilder b = Db.builder().mainStream(new FileStream(dir, false)).startupDistance(400_000);
        if (nodeSize == 8) b.maxNodeSize8();
        else if (nodeSize == 14) b.maxNodeSize14();
        else if (nodeSize == 62) b.maxNodeSize62();
        else b.maxNodeSize30();
        if (seed % 2 == 0) b.cacheSizeIndicator(3_000_000);
        db = b.start();
        if (retain > 0) db.setRetainDuration(retain);
        long t0 = System.currentTimeMillis();
        Thread w = new Thread(() -> writer(seed, keys), "writer");
        List<Thread> rs = new ArrayList<>();
        for (int i = 0; i < readers; i++) {
            final long rseed = seed * 100 + i;
            rs.add(new Thread(() -> reader(rseed), "reader-" + i));
        }
        w.start();
        for (Thread t : rs) t.start();
        while (System.currentTimeMillis() - t0 < seconds * 1000L && failure.get() == null) Thread.sleep(200);
        stop.set(true);
        w.join();
        for (Thread t : rs) t.join();
        long txs = m.times.size();
        db.close();
        if (failure.get() != null) {
            System.out.println("FAIL Readers seed " + seed + " node " + nodeSize + ": " + failure.get());
            System.exit(1);
        }
        Common.log("OK Readers seed " + seed + " node " + nodeSize + " readers " + readers + " retain " + retainMs + ": "
                + txs + " transactions, " + reads.get() + " checked reads (" + scans.get() + " full scans), " + cut.get()
                + " cut reads, " + (System.currentTimeMillis() - t0) + " ms");
    }

    static void fail(String s) { failure.compareAndSet(null, s); stop.set(true); }

    static void writer(long seed, int nKeys) {
        Random r = new Random(seed);
        int counter = 0;
        try {
            while (!stop.get()) {
                // load
                List<Common.K> ks = new ArrayList<>();
                while (m.latest.size() + ks.size() < nKeys) {
                    int c = counter++;
                    byte[] k = r.nextBoolean() ? new byte[] {0x10, (byte) (c >>> 16), (byte) (c >>> 8), (byte) c}
                            : new byte[] {0x20, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, 0x41, (byte) (c >>> 16), (byte) (c >>> 8), (byte) c};
                    ks.add(new Common.K(k));
                }
                Collections.shuffle(ks, r);
                batches(r, ks, false);
                // scattered deletes of half
                ks = new ArrayList<>();
                for (Common.K k : m.latest.keySet()) if (r.nextBoolean()) ks.add(k);
                Collections.shuffle(ks, r);
                batches(r, ks, true);
                // ranged deletes
                List<Common.K> live = new ArrayList<>(m.latest.keySet());
                if (live.size() > 10) {
                    int from = r.nextInt(live.size());
                    batches(r, new ArrayList<>(live.subList(from, Math.min(live.size(), from + live.size() / 3))), true);
                }
                // churn
                for (int i = 0; i < 100 && !stop.get(); i++) {
                    live = new ArrayList<>(m.latest.keySet());
                    if (live.isEmpty()) break;
                    Map<Common.K, byte[]> ops = new LinkedHashMap<>();
                    int from = r.nextInt(live.size());
                    for (int j = 0; j < 1 + r.nextInt(40); j++) {
                        Common.K k = live.get((from + r.nextInt(100)) % live.size());
                        ops.put(k, r.nextInt(3) == 0 ? Common.DELETED : Common.value(r, 50));
                    }
                    run(ops);
                }
                // delete most
                ks = new ArrayList<>();
                int i = 0;
                for (Common.K k : m.latest.keySet()) if (i++ % 25 != 0) ks.add(k);
                batches(r, ks, true);
            }
        } catch (Throwable t) {
            fail("writer: " + t);
            t.printStackTrace(System.out);
        }
    }

    static void batches(Random r, List<Common.K> ks, boolean delete) {
        int i = 0;
        while (i < ks.size() && !stop.get()) {
            int n = 1 + r.nextInt(Db.MAX_OPERATIONS);
            Map<Common.K, byte[]> ops = new LinkedHashMap<>();
            for (int j = i; j < Math.min(ks.size(), i + n); j++) ops.put(ks.get(j), delete ? Common.DELETED : Common.value(r, 60));
            run(ops);
            i += n;
        }
    }

    static void run(Map<Common.K, byte[]> ops) {
        long tt = Common.exec(db, m, ops);
        published.add(tt);
    }

    static void reader(long seed) {
        Random r = new Random(seed);
        try {
            while (!stop.get()) {
                long t;
                int n = published.size();
                if (n == 0) { Thread.sleep(5); continue; }
                int kind = r.nextInt(10);
                if (kind < 3) t = published.get(n - 1);
                else if (kind < 8) t = published.get(r.nextInt(n));
                else t = published.get(r.nextInt(n)) - 1;
                if (t <= 0) continue;
                try {
                    int what = r.nextInt(4);
                    if (what == 0) { Common.verifyFull(db, m, t, Thread.currentThread().getName() + " scan at " + t); scans.incrementAndGet(); }
                    else if (what == 1) Common.verifyGets(db, m, t, r, 50, Thread.currentThread().getName() + " gets at " + t);
                    else if (what == 2) Common.verifyRange(db, m, t, r, Thread.currentThread().getName() + " range at " + t);
                    else latest(r);
                    reads.incrementAndGet();
                } catch (Common.Fail f) {
                    fail(f.getMessage());
                } catch (RuntimeException e) {
                    if (!Common.isNotAvailable(e)) throw e;
                    long fa = db.getFirstAvailableLookupTime();
                    if (fa <= t) fail("read at " + t + " cut, but first available is " + fa + ": " + e);
                    if (retain == 0) fail("read at " + t + " cut with no retain duration: " + e);
                    cut.incrementAndGet();
                }
            }
        } catch (Throwable t) {
            fail(Thread.currentThread().getName() + ": " + t);
            t.printStackTrace(System.out);
        }
    }

    /** A scan of the latest state: compared once the model has the transactions up to its time. */
    static void latest(Random r) throws InterruptedException {
        GetMany g = db.newGetMany();
        db.getMany(g);
        long actual = g.actualLookupTime;
        long until = System.currentTimeMillis() + 2000;
        while (m.lastTime < actual && System.currentTimeMillis() < until) Thread.sleep(1);
        if (m.lastTime < actual) return;      // a transaction of BergDB's own is the last
        List<Kvt> got = new ArrayList<>();
        for (Kvt kvt : g.result) if (!Common.isBergKey(bergdb.dag.Keys.toBytes(kvt.key))) got.add(kvt);
        Common.compareScan(Thread.currentThread().getName() + " latest at " + actual, got, m, actual, true);
        scans.incrementAndGet();
    }
}
