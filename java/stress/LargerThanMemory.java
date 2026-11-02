package bergdb.core;

import java.io.File;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Random;

import bergdb.dag.GetMany;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.PointerFollower;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * A database larger than memory (bergdb item 001, WP J8; bergdb 001-10): on disk
 * (FileStream), in a capped JVM, with the capacity controller's budget much smaller than the
 * data and the index. Phases: load (keys in random order), uniform updates, hot updates (90
 * percent of the puts on 1 percent of the keys), with reclaim on; gets (cold after each
 * restart, then warm) and scans, every value checked; cold restarts, after each every key
 * checked; and at the end every key checked. A thread samples the memory every second: the
 * heap in use after the last garbage collection (the heap pools' collection usage), the heap
 * in use (with garbage not yet collected), the resident bytes the controller
 * counts (Residents), the bytes on disk; and at the end of every phase, the heap in use after
 * a full collection (System.gc()), what is live then: the run fails if that is ever above three
 * quarters of the cap (the collection usage overstates what is live, since a young collection
 * does not collect the old generation). The index's size is measured by a scan that caches
 * nothing, which visits every index node of the latest tree once.
 *
 * The expected values are computed from the key and its version, an int per key, so that no
 * copy of the database is in the heap.
 *
 * Usage: java -Xmx2g [-Dprop=value ...] -cp bergdb.jar:stress bergdb.core.LargerThanMemory
 * Properties: keys=N (default 20000000), valsize=N (bytes, default 100), budget=MB (default
 * 500), dir=D (default build/ltm, emptied first), updates=N (transactions of each update
 * phase, default 200000), tsize=N (puts per update transaction, default 10), restarts=N
 * (cycles of updates and a restart, default 2), gets=N (per read phase, default 1000000),
 * scans=N (scans of 10,000 KVs per read phase, default 20), retain=S (reclaim's retain
 * duration in seconds, default 2; 0: off), maxnode=N (8, 14, 30 or 62; default 30), sd=N
 * (the startup distance in bytes; default the Db's).
 * Prints a line per phase and LARGER THAN MEMORY OK, or an error and exits 1.
 */
public class LargerThanMemory {
    final int keys = Integer.getInteger("keys", 20 * 1000 * 1000);
    final int valsize = Math.max(8, Integer.getInteger("valsize", 100));
    final long budget = Long.getLong("budget", 500) * 1000 * 1000;
    final File dir = new File(System.getProperty("dir", "build/ltm"));
    final int updates = Integer.getInteger("updates", 200 * 1000);
    final int tsize = Integer.getInteger("tsize", 10);
    final int restarts = Integer.getInteger("restarts", 2);
    final int gets = Integer.getInteger("gets", 1000 * 1000);
    final int scans = Integer.getInteger("scans", 20);
    final int retain = Integer.getInteger("retain", 2);
    final int maxNode = Integer.getInteger("maxnode", 30);
    final int sd = Integer.getInteger("sd", 0);

    final int[] version;
    final Random rnd = new Random(1);
    final CoreTestClock clock = new CoreTestClock();
    long time = bergdb.pub.util.Clock.UNITS_PER_SEC;
    final long tstep = bergdb.pub.util.Clock.UNITS_PER_SEC / 10000;   // 100 us
    Db db;
    volatile String phase = "start";
    volatile long maxHeap = 0, maxLive = 0, maxResident = 0, maxDisk = 0;
    long maxFull = 0;           // the heap in use after a full collection, at the phases' ends
    long iterations = 0;        // reclaim's iterations, of the processes before the last
    volatile boolean done = false;
    final long t0 = System.nanoTime();

    LargerThanMemory() {
        version = new int[keys];
    }

    long seconds() {
        return (System.nanoTime() - t0) / 1000000000L;
    }

    Db start(boolean create) throws Exception {
        if (create) {
            dir.mkdirs();
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) f.delete();
        }
        DbBuilder b = Db.builder().stream("main", new FileStream(dir)).clock(clock).testId()
                .cacheSizeIndicator(budget).evictionSchedule(Eviction.Schedule.BUDGET, 1);
        if (maxNode == 8) b.maxNodeSize8();
        if (maxNode == 14) b.maxNodeSize14();
        if (maxNode == 30) b.maxNodeSize30();
        if (maxNode == 62) b.maxNodeSize62();
        if (sd > 0) b.startupDistance(sd);
        if (retain > 0) b.retainDuration(retain * bergdb.pub.util.Clock.UNITS_PER_SEC);
        Db d = b.build();
        d.start();
        return d;
    }

    byte[] key(int k) {
        return KeyFactory.binaryIntKey(k);
    }

    byte[] value(int k, int v) {
        byte[] b = new byte[valsize];
        b[0] = (byte) (k >>> 24); b[1] = (byte) (k >>> 16); b[2] = (byte) (k >>> 8); b[3] = (byte) k;
        b[4] = (byte) (v >>> 24); b[5] = (byte) (v >>> 16); b[6] = (byte) (v >>> 8); b[7] = (byte) v;
        for (int i = 8; i < valsize; i++) b[i] = (byte) (k * 31 + v + i);
        return b;
    }

    void check(int k, byte[] got, String what) {
        if (!Arrays.equals(value(k, version[k]), got)) {
            throw new AssertionError(what + ": wrong value for key " + k + ", version "
                    + version[k] + (got == null ? ", got null" : ""));
        }
    }

    void execute(Trans.Builder b) {
        time += tstep;
        clock.setTime(time);
        db.execute(b.build());
    }

    /** Samples the memory every second; prints a line every 10 s. */
    Thread sampler() {
        Thread t = new Thread(new Runnable() {
            public void run() {
                Runtime rt = Runtime.getRuntime();
                long last = 0;
                while (!done) {
                    try {
                        Thread.sleep(1000);
                    } catch (InterruptedException e) {
                        return;
                    }
                    long heap = rt.totalMemory() - rt.freeMemory();
                    long live = 0;
                    for (java.lang.management.MemoryPoolMXBean pool
                            : java.lang.management.ManagementFactory.getMemoryPoolMXBeans()) {
                        if (pool.getType() != java.lang.management.MemoryType.HEAP) continue;
                        java.lang.management.MemoryUsage u = pool.getCollectionUsage();
                        if (u != null) live += u.getUsed();
                    }
                    Db d = db;
                    long res = d == null ? 0 : d.internal().cache().residents().bytes();
                    long disk = disk();
                    if (heap > maxHeap) maxHeap = heap;
                    if (live > maxLive) maxLive = live;
                    if (res > maxResident) maxResident = res;
                    if (disk > maxDisk) maxDisk = disk;
                    if (seconds() - last >= 10) {
                        last = seconds();
                        System.out.println("   memory at " + last + " s (" + phase + "): live after GC "
                                + live / 1000000 + " MB, heap used " + heap / 1000000 + " MB, resident "
                                + res / 1000000 + " MB, on disk " + disk / 1000000 + " MB");
                    }
                }
            }
        });
        t.setDaemon(true);
        t.start();
        return t;
    }

    /** The bytes of the stream's files on disk. */
    long disk() {
        long sum = 0;
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) sum += f.length();
        return sum;
    }

    void load() {
        phase = "load";
        long s = System.nanoTime();
        int[] order = new int[keys];
        for (int i = 0; i < keys; i++) order[i] = i;
        for (int i = keys - 1; i > 0; i--) {
            int j = rnd.nextInt(i + 1);
            int x = order[i]; order[i] = order[j]; order[j] = x;
        }
        for (int i = 0; i < keys; i += 1000) {
            Trans.Builder b = db.trans();
            for (int j = i; j < Math.min(keys, i + 1000); j++) b.put(key(order[j]), value(order[j], 0));
            execute(b);
        }
        report("load", keys, s);
    }

    void update(boolean hot) {
        phase = hot ? "hot updates" : "uniform updates";
        long s = System.nanoTime();
        int hotKeys = Math.max(1, keys / 100);
        for (int i = 0; i < updates; i++) {
            Trans.Builder b = db.trans();
            HashSet<Integer> ks = new HashSet<Integer>();
            for (int j = 0; j < tsize; j++) {
                int k = hot && rnd.nextInt(10) < 9 ? rnd.nextInt(hotKeys) : rnd.nextInt(keys);
                if (!ks.add(k)) continue;
                version[k]++;
                b.put(key(k), value(k, version[k]));
            }
            execute(b);
        }
        report(phase, (long) updates * tsize, s);
    }

    void reads(String what) {
        phase = what + " gets";
        long s = System.nanoTime();
        long loads0 = db.internal().nodeCollection().loads();
        for (int i = 0; i < gets; i++) {
            int k = rnd.nextInt(keys);
            check(k, DbUtil.get(db, key(k)), what + " get");
        }
        report(what + " gets (" + (db.internal().nodeCollection().loads() - loads0) + " loads)",
                gets, s);
        phase = what + " scans";
        s = System.nanoTime();
        long n = 0;
        for (int i = 0; i < scans; i++) {
            GetMany g = db.newGetMany();
            g.startKey = bergdb.dag.Keys.toSegments(key(rnd.nextInt(keys)));
            final int[] count = new int[1];
            g.stopCondition = new GetMany.StopCondition() {
                public int handleKvt(Kvt kvt) {
                    return ++count[0] >= 10000 ? ADD_AND_STOP : ADD;
                }
                public void eod() {}
            };
            db.getMany(g);
            for (Kvt kvt : g.result) {
                byte[] kb = bergdb.dag.Keys.toBytes(kvt.key);
                if (kb.length != 4) continue;
                int k = ((kb[0] & 0xff) << 24) | ((kb[1] & 0xff) << 16) | ((kb[2] & 0xff) << 8) | (kb[3] & 0xff);
                if (k < 0 || k >= keys) continue;
                check(k, kvt.value, what + " scan");
                n++;
            }
        }
        report(what + " scans", n, s);
    }

    void checkAll(String what) {
        phase = "check every key (" + what + ")";
        long s = System.nanoTime();
        for (int k = 0; k < keys; k++) check(k, DbUtil.get(db, key(k)), "check " + what);
        report("every key checked (" + what + ")", keys, s);
    }

    void restart(int r) throws Exception {
        phase = "restart " + r;
        iterations += db.internal().reclaim().getIterationCount();
        db.sync(SyncLevel.STRONG);
        db.close();     // Closed before the directory opens again (bergdb 005-63).
        db = null;
        System.gc();
        long s = System.nanoTime();
        db = start(false);
        System.out.println("   restart " + r + ": startup " + (System.nanoTime() - s) / 1000000
                + " ms, on disk " + disk() / 1000000 + " MB, resident "
                + db.internal().cache().residents().bytes() / 1000000 + " MB");
    }

    /** The memory size of every index node of the latest tree, by a scan. */
    void indexSize() {
        phase = "index size";
        long s = System.nanoTime();
        final HashSet<Long> ids = new HashSet<Long>();
        final long[] bytes = new long[1];
        GetMany g = db.newGetMany();
        final PointerFollower real = g.gd.pointerFollower;
        g.gd.pointerFollower = new PointerFollower() {
            public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
                Node n = real.followPointer(predecessor, pointerIndex, op);
                if (n.isIndexNode() && ids.add(n.getId())) bytes[0] += n.getMemSize();
                return n;
            }
        };
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                return CONTINUE;
            }
            public void eod() {}
        };
        db.getMany(g);
        System.out.println("   the index: " + ids.size() + " index nodes, " + bytes[0] / 1000000
                + " MB in memory (" + (System.nanoTime() - s) / 1000000 + " ms); the budget "
                + budget / 1000000 + " MB; on disk " + disk() / 1000000 + " MB");
    }

    void report(String what, long count, long startNanos) {
        double sec = (System.nanoTime() - startNanos) / 1e9;
        System.gc();
        Runtime rt = Runtime.getRuntime();
        long full = rt.totalMemory() - rt.freeMemory();
        if (full > maxFull) maxFull = full;
        System.out.printf("   %s: %d in %.1f s, %.0f per s; live after a full GC %d MB; so far at most: %d MB so, collection usage %d MB, heap used %d MB, resident %d MB%n",
                what, count, sec, count / sec, full / 1000000, maxFull / 1000000, maxLive / 1000000,
                maxHeap / 1000000, maxResident / 1000000);
    }

    void run() throws Exception {
        System.out.println("LargerThanMemory: keys " + keys + ", values " + valsize + " bytes, budget "
                + budget / 1000000 + " MB, max heap " + Runtime.getRuntime().maxMemory() / 1000000
                + " MB, maxnode " + maxNode + ", reclaim " + (retain > 0 ? retain + " s" : "off")
                + ", dir " + dir);
        Thread sampler = sampler();
        db = start(true);
        load();
        indexSize();
        for (int r = 1; r <= restarts; r++) {
            update(false);
            update(true);
            reads("warm");
            restart(r);
            reads("cold");
            checkAll("after restart " + r);
        }
        checkAll("at the end");
        indexSize();
        System.out.println("   " + db.internal().eviction().summary());
        Reclaim reclaim = db.internal().reclaim();
        System.out.println("   reclaim: " + (iterations + reclaim.getIterationCount())
                + " iterations; the first available time " + db.getFirstAvailableLookupTime()
                + ", the last " + time + "; on disk " + disk() / 1000000 + " MB, at most "
                + maxDisk / 1000000 + " MB");
        done = true;
        sampler.join(2000);
        long max = Runtime.getRuntime().maxMemory();
        System.out.println("   at most: live after a full GC " + maxFull / 1000000
                + " MB (at the phases' ends), collection usage " + maxLive / 1000000
                + " MB, heap used " + maxHeap / 1000000 + " MB, of " + max / 1000000 + " MB; resident "
                + maxResident / 1000000 + " MB; " + seconds() + " s");
        db.stop();
        if (maxFull > max * 3 / 4) {
            System.out.println("LARGER THAN MEMORY FAILED: the live heap came above three quarters of the cap");
            System.exit(1);
        }
        System.out.println("LARGER THAN MEMORY OK");
    }

    public static void main(String[] args) throws Exception {
        try {
            new LargerThanMemory().run();
        } catch (Throwable e) {
            e.printStackTrace(System.out);
            System.out.println("LARGER THAN MEMORY FAILED: " + e);
            System.exit(1);
        }
    }
}
