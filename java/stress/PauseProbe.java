package bergdb.core;

import java.io.File;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Random;

import bergdb.stream.FileStream;

/**
 * The pause probe (bergdb item 009, step 1a; items/009-handles/02-implementation-plan.md):
 * how long a get or a commit can be stopped, with the capacity controller's budget well below
 * the data, on disk (FileStream). It times every operation and prints, per phase, the median,
 * the 99th, 99.9th and 99.99th percentiles and the longest wait of a get and of a commit, with
 * the JVM uptime of the five longest, so that a GC log (-Xlog:gc*,safepoint) tells the
 * collector's stops from BergDB's; and the eviction's own figures.
 *
 * Phases: the load (keys in random order, 1,000 puts a transaction), then for each writer
 * size in tsize a phase of 'seconds' seconds: one writer doing transactions of that many puts
 * on random keys, as fast as it can, and 'readers' threads doing gets of random keys. Every
 * value read is checked: it names its key (the first four bytes).
 *
 * It uses only what 2026.1 and later versions have, so that one compiled copy runs on both
 * jars (009-02, phase 5); the eviction's figures are read by reflection: CacheStats if the jar
 * has it (Db.Internal.cacheStats(), since 009), else Eviction.summary().
 *
 * Usage: java -Xmx2g [-XX:+UseZGC] [-Xlog:gc*,safepoint:file=gc.log:uptime,level,tags]
 *            [-Dprop=value ...] -cp bergdb.jar:stress bergdb.core.PauseProbe
 * Properties: keys=N (default 1000000), valsize=N (bytes, default 100), budget=MB (default
 * 20), dir=D (default build/pauseprobe, emptied first), readers=N (default 4), seconds=S (per
 * phase, default 60), tsize=N,N,... (the writer's puts a transaction, a phase each; default
 * 1,500; 1,1000 until bergdb 024-24); lower=MB (default 0: none) and lowerAt=S (default
 * 10), the lowered budget (bergdb
 * 005-52): each phase starts with the budget 'budget', and lowerAt seconds into it, between
 * two of the writer's commits, the budget becomes 'lower'; a sampler reads the resident bytes
 * every 10 ms until they are at most 'lower' or the phase ends, and the phase's block has a
 * line "lowered:" with the time they took. Db.setCacheSizeIndicator (since fd8f513) and the
 * resident bytes are reached by reflection, found once at the start and only with lower, so
 * that without it the probe runs and prints as before.
 * Prints a block per phase and PAUSE PROBE OK, or an error and exits 1.
 */
public class PauseProbe {
    final int keys = Integer.getInteger("keys", 1000 * 1000);
    final int valsize = Math.max(8, Integer.getInteger("valsize", 100));
    final long budget = Long.getLong("budget", 20) * 1000 * 1000;
    final File dir = new File(System.getProperty("dir", "build/pauseprobe"));
    final int readers = Integer.getInteger("readers", 4);
    final int seconds = Integer.getInteger("seconds", 60);
    final int[] tsizes = parse(System.getProperty("tsize", "1,500"));      // L1: 1,1000 until 024-24
    /** The lowered budget, in bytes, 0 for none, and the seconds into a phase (bergdb 005-52). */
    final long lower = Long.getLong("lower", 0) * 1000 * 1000;
    final int lowerAt = Integer.getInteger("lowerAt", 10);
    /** Db.setCacheSizeIndicator, and the resident bytes' path; found by findLowering(). */
    Method setBudget, internal, cache, residents, bytes;
    Db db;
    /** The disk's waits for the report (bergdb 005-46). */
    final TimedIo io = new TimedIo();
    volatile boolean stop = false;
    volatile Throwable failure = null;

    static int[] parse(String s) {
        String[] parts = s.split(",");
        int[] r = new int[parts.length];
        for (int i = 0; i < parts.length; i++) r[i] = Integer.parseInt(parts[i].trim());
        return r;
    }

    /**
     * Latencies in buckets of a quarter of a power of two of nanoseconds (so a bucket is at
     * most 19 percent wide), the longest exactly, and the five longest with their uptimes.
     */
    static final class Lat {
        final long[] buckets = new long[4 * 64];
        long count = 0, max = 0;
        final long[] topNs = new long[5];
        final long[] topAt = new long[5];

        static int bucket(long ns) {
            if (ns < 1) return 0;
            int e = 63 - Long.numberOfLeadingZeros(ns);
            int q = e < 2 ? 0 : (int) ((ns >>> (e - 2)) & 3);
            return 4 * e + q;
        }

        static long lowerBound(int b) {
            int e = b / 4, q = b % 4;
            return e < 2 ? (1L << e) : (1L << e) + ((long) q << (e - 2));
        }

        void add(long ns, long uptimeMs) {
            buckets[bucket(ns)]++;
            count++;
            if (ns > max) max = ns;
            if (ns > topNs[4]) {
                int i = 4;
                while (i > 0 && topNs[i - 1] < ns) {
                    topNs[i] = topNs[i - 1];
                    topAt[i] = topAt[i - 1];
                    i--;
                }
                topNs[i] = ns;
                topAt[i] = uptimeMs;
            }
        }

        void addAll(Lat o) {
            for (int i = 0; i < buckets.length; i++) buckets[i] += o.buckets[i];
            count += o.count;
            if (o.max > max) max = o.max;
            for (int j = 0; j < 5; j++) if (o.topNs[j] > 0) addTop(o.topNs[j], o.topAt[j]);
        }

        private void addTop(long ns, long at) {
            if (ns <= topNs[4]) return;
            int i = 4;
            while (i > 0 && topNs[i - 1] < ns) {
                topNs[i] = topNs[i - 1];
                topAt[i] = topAt[i - 1];
                i--;
            }
            topNs[i] = ns;
            topAt[i] = at;
        }

        /** The lower bound of the bucket of the p-th quantile, in ms. */
        double quantileMs(double p) {
            long rank = (long) Math.ceil(p * count);
            long seen = 0;
            for (int b = 0; b < buckets.length; b++) {
                seen += buckets[b];
                if (seen >= rank && buckets[b] > 0) return lowerBound(b) / 1e6;
            }
            return max / 1e6;
        }

        String line(String what) {
            StringBuilder sb = new StringBuilder();
            sb.append(String.format("%-8s %d, median %.3f ms, p99 %.3f, p99.9 %.3f, p99.99 %.3f,"
                    + " max %.3f ms", what, count, quantileMs(0.5), quantileMs(0.99),
                    quantileMs(0.999), quantileMs(0.9999), max / 1e6));
            sb.append("; longest at uptime");
            for (int j = 0; j < 5 && topNs[j] > 0; j++) {
                sb.append(String.format(" %.3fs (%.1f ms)", topAt[j] / 1e3, topNs[j] / 1e6));
            }
            return sb.toString();
        }
    }

    static long uptimeMs() {
        return java.lang.management.ManagementFactory.getRuntimeMXBean().getUptime();
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

    static int keyOf(byte[] v) {
        return ((v[0] & 0xff) << 24) | ((v[1] & 0xff) << 16) | ((v[2] & 0xff) << 8) | (v[3] & 0xff);
    }

    Db start() throws java.io.IOException {
        dir.mkdirs();
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) f.delete();
        Db d = Db.builder().stream("main", new FileStream(dir, io)).testId()
                .cacheSizeIndicator(budget).evictionSchedule(Eviction.Schedule.BUDGET, 1).build();
        d.start();
        return d;
    }

    /** The eviction's figures, by reflection: CacheStats (009 on) or Eviction.summary(). */
    String evictionFigures() {
        try {
            Object in = db.getClass().getMethod("internal").invoke(db);
            try {
                Method m = in.getClass().getMethod("cacheStats");
                return String.valueOf(m.invoke(in));
            } catch (NoSuchMethodException e) {
                Object ev = in.getClass().getMethod("eviction").invoke(in);
                return String.valueOf(ev.getClass().getMethod("summary").invoke(ev));
            }
        } catch (Exception e) {
            return "(no eviction figures: " + e + ")";
        }
    }

    /**
     * Finds, for lower (bergdb 005-52), Db.setCacheSizeIndicator(long) and the resident bytes,
     * db.internal().cache().residents().bytes(); a jar without them fails the probe here, at
     * once.
     */
    void findLowering() {
        try {
            setBudget = Db.class.getMethod("setCacheSizeIndicator", long.class);
            internal = Db.class.getMethod("internal");
            cache = internal.getReturnType().getMethod("cache");
            residents = cache.getReturnType().getMethod("residents");
            bytes = residents.getReturnType().getMethod("bytes");
        } catch (NoSuchMethodException e) {
            throw new IllegalStateException("lower is set, but this jar has no " + e.getMessage()
                    + ": it needs Db.setCacheSizeIndicator (since fd8f513, bergdb 005-52) and "
                    + "the resident bytes (Residents, item 009)", e);
        }
    }

    long residentBytes() throws Exception {
        return (Long) bytes.invoke(residents.invoke(cache.invoke(internal.invoke(db))));
    }

    /**
     * The lowering of a phase (bergdb 005-52): sets the budget to 'lower', and starts a sampler
     * that reads the resident bytes every 10 ms until they are at most 'lower' (reachedNs) or
     * the phase ends (stop). Called by the writer between two commits, outside their times.
     */
    final class Lowering {
        final long atNs = System.nanoTime();
        final long atUptimeMs = uptimeMs();
        final long before;
        volatile long reachedNs = -1;
        volatile long lastBytes;
        final Thread sampler;

        Lowering() throws Exception {
            before = residentBytes();
            lastBytes = before;
            setBudget.invoke(db, lower);
            sampler = new Thread(new Runnable() {
                public void run() {
                    try {
                        while (!stop) {
                            long b = residentBytes();
                            lastBytes = b;
                            if (b <= lower) {
                                reachedNs = System.nanoTime();
                                return;
                            }
                            Thread.sleep(10);
                        }
                    } catch (Throwable e) {
                        failure = e;
                        stop = true;
                    }
                }
            });
            sampler.setDaemon(true);
            sampler.start();
        }

        /** The phase's line, after the sampler has ended. */
        String line() {
            String s = String.format("lowered: budget %d to %d MB at uptime %.3f s, resident %d MB",
                    budget / 1000000, lower / 1000000, atUptimeMs / 1e3, before / 1000000);
            if (reachedNs >= 0) {
                return s + String.format("; reached in %.3f s", (reachedNs - atNs) / 1e9);
            }
            return s + "; not reached, resident " + lastBytes / 1000000 + " MB at the phase's end";
        }
    }

    void load() {
        int[] order = new int[keys];
        for (int i = 0; i < keys; i++) order[i] = i;
        Random rnd = new Random(1);
        for (int i = keys - 1; i > 0; i--) {
            int j = rnd.nextInt(i + 1);
            int x = order[i]; order[i] = order[j]; order[j] = x;
        }
        Lat commits = new Lat();
        long s = System.nanoTime();
        long from = uptimeMs();
        // Batches of 500, L1 (bergdb 024-24; 1,000 until then).
        for (int i = 0; i < keys; i += Db.MAX_OPERATIONS) {
            Trans.Builder b = db.trans();
            for (int j = i; j < Math.min(keys, i + Db.MAX_OPERATIONS); j++) b.put(key(order[j]), value(order[j], 0));
            Trans t = b.build();
            long t0 = System.nanoTime();
            db.execute(t);
            commits.add(System.nanoTime() - t0, uptimeMs());
        }
        long to = uptimeMs();
        System.out.println(String.format("load: %d keys in %.1f s; uptime %.3f to %.3f s",
                keys, (System.nanoTime() - s) / 1e9, from / 1e3, to / 1e3));
        System.out.println("  " + commits.line("commits"));
        System.out.println("  " + evictionFigures());
        diskWaits();
    }

    /**
     * The disk's waits since the last call (bergdb 005-46): the writer's for room in the write
     * buffer, the file and directory forces, the deletes. Not BergDB's, but a long get or
     * commit at the same uptime is the disk's.
     */
    void diskWaits() {
        System.out.println("  " + TimedIo.writeBufferWaits(db));
        for (String line : io.take().split("\n")) System.out.println("  " + line);
    }

    void phase(final int tsize) throws Exception {
        stop = false;
        final Lat[] getLats = new Lat[readers];
        Thread[] ts = new Thread[readers];
        for (int r = 0; r < readers; r++) {
            final int rr = r;
            getLats[r] = new Lat();
            ts[r] = new Thread(new Runnable() {
                public void run() {
                    Random rnd = new Random(100 + rr);
                    try {
                        while (!stop) {
                            int k = rnd.nextInt(keys);
                            byte[] kb = key(k);
                            long t0 = System.nanoTime();
                            byte[] v = DbUtil.get(db, kb);
                            long ns = System.nanoTime() - t0;
                            getLats[rr].add(ns, uptimeMs());
                            if (v == null || keyOf(v) != k) {
                                throw new AssertionError("get of key " + k + " gave "
                                        + (v == null ? "null" : "the value of key " + keyOf(v)));
                            }
                        }
                    } catch (Throwable e) {
                        failure = e;
                        stop = true;
                    }
                }
            });
        }
        Lat commits = new Lat();
        Random rnd = new Random(tsize);
        int version = 1;
        if (lower > 0) setBudget.invoke(db, budget);     // each phase from the same budget
        Lowering lowering = null;
        long from = uptimeMs();
        for (Thread t : ts) t.start();
        final long begin = System.nanoTime();
        long end = begin + seconds * 1000000000L;
        while (System.nanoTime() < end && failure == null) {
            if (lower > 0 && lowering == null
                    && System.nanoTime() - begin >= lowerAt * 1000000000L) {
                lowering = new Lowering();
            }
            Trans.Builder b = db.trans();
            for (int j = 0; j < tsize; j++) {
                int k = rnd.nextInt(keys);
                b.put(key(k), value(k, version));
            }
            version++;
            Trans t = b.build();
            long t0 = System.nanoTime();
            db.execute(t);
            commits.add(System.nanoTime() - t0, uptimeMs());
        }
        stop = true;
        for (Thread t : ts) t.join();
        if (lowering != null) lowering.sampler.join();
        long to = uptimeMs();
        if (failure != null) throw new RuntimeException("a reader or the sampler failed", failure);
        Lat gets = new Lat();
        for (Lat l : getLats) gets.addAll(l);
        System.out.println(String.format("phase tsize=%d, %d readers, %d s; uptime %.3f to %.3f s",
                tsize, readers, seconds, from / 1e3, to / 1e3));
        if (lowering != null) System.out.println("  " + lowering.line());
        System.out.println("  " + gets.line("gets"));
        System.out.println("  " + commits.line("commits"));
        System.out.println("  " + evictionFigures());
        diskWaits();
    }

    void run() throws Exception {
        System.out.println("PauseProbe: keys=" + keys + " valsize=" + valsize + " budget="
                + budget / 1000000 + " MB readers=" + readers + " seconds=" + seconds
                + " tsize=" + Arrays.toString(tsizes) + " java=" + System.getProperty("java.version")
                + " gc=" + gcNames() + " xmx=" + Runtime.getRuntime().maxMemory() / 1000000 + " MB"
                + (lower > 0 ? " lower=" + lower / 1000000 + " MB lowerAt=" + lowerAt + " s" : ""));
        if (lower > 0) {
            if (lowerAt < 0 || lowerAt >= seconds) {
                throw new IllegalArgumentException("lowerAt=" + lowerAt + " must be from 0 to "
                        + "less than seconds=" + seconds);
            }
            findLowering();
        }
        db = start();
        load();
        for (int tsize : tsizes) phase(tsize);
        db.stop();
        System.out.println("PAUSE PROBE OK");
    }

    static String gcNames() {
        StringBuilder sb = new StringBuilder();
        for (java.lang.management.GarbageCollectorMXBean b
                : java.lang.management.ManagementFactory.getGarbageCollectorMXBeans()) {
            if (sb.length() > 0) sb.append('+');
            sb.append(b.getName().replace(' ', '_'));
        }
        return sb.toString();
    }

    public static void main(String[] args) {
        try {
            new PauseProbe().run();
        } catch (Throwable e) {
            e.printStackTrace();
            System.out.println("PAUSE PROBE FAILED: " + e);
            System.exit(1);
        }
        System.exit(0);
    }
}
