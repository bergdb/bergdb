package bergdb.core;

import java.io.File;
import java.util.Random;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * bergdb 005-65's fix: an untimed count of the entries into Eviction.evictorLock with reader
 * threads doing random gets on a database on disk (from the OS's cache) under a budget smaller
 * than it, after 3 s of warming. Needs an Eviction with mkcount.py's counters (run.sh). Not
 * timed: the gets a second it prints are not a measurement. Written 2026-10-29 by Claude
 * (Opus 5.5, Claude Code).
 * Usage: java -cp PROBE:CLASSES -Ddir=DIR [-Dkeys=N -Dvalsize=B -Dbudget=MB -Dthreads=T -Dsec=S]
 *        bergdb.core.EntriesProbe load|gets
 */
public class EntriesProbe {
    static final int KEYS = Integer.getInteger("keys", 1000000);
    static final int VALSIZE = Integer.getInteger("valsize", 100);

    static byte[] value(int k) {
        byte[] b = new byte[VALSIZE];
        for (int i = 0; i < VALSIZE; i++) b[i] = (byte) (k * 31 + i);
        return b;
    }

    public static void main(String[] args) throws Exception {
        File dir = new File(System.getProperty("dir"));
        long budget = Long.getLong("budget", 20) * 1000 * 1000;
        final int threads = Integer.getInteger("threads", 8);
        int sec = Integer.getInteger("sec", 10);
        CoreTestClock clock = new CoreTestClock();
        if (args[0].equals("load")) {
            dir.mkdirs();
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) f.delete();
            Db db = Db.builder().stream("main", new FileStream(dir)).clock(clock).testId()
                    .startupDistance(10 * 1000 * 1000).noEvict().build();
            db.start();
            long time = bergdb.pub.util.Clock.UNITS_PER_SEC;
            for (int i = 0; i < KEYS; i += 1000) {
                time += 1000;
                clock.setTime(time);
                Trans.Builder b = db.trans();
                for (int k = i; k < Math.min(KEYS, i + 1000); k++) b.put(KeyFactory.binaryIntKey(k), value(k));
                db.execute(b.build());
            }
            db.sync(SyncLevel.STRONG);
            db.close();
            System.out.println("LOADED " + KEYS + " keys");
            return;
        }
        final Db db = Db.builder().stream("main", new FileStream(dir)).clock(clock).testId()
                .startupDistance(10 * 1000 * 1000).cacheSizeIndicator(budget)
                .evictionSchedule(Eviction.Schedule.BUDGET, 1).build();
        db.start();
        final Eviction e = db.internal().eviction();
        final java.util.concurrent.atomic.LongAdder gets = new java.util.concurrent.atomic.LongAdder();
        final long[] stop = {System.nanoTime() + (3L + sec) * 1000000000L};
        Thread[] ts = new Thread[threads];
        for (int t = 0; t < threads; t++) {
            final Random r = new Random(t);
            ts[t] = new Thread(new Runnable() {
                public void run() {
                    while (System.nanoTime() < stop[0]) {
                        for (int j = 0; j < 64; j++) {
                            int k = r.nextInt(KEYS);
                            byte[] v = DbUtil.get(db, KeyFactory.binaryIntKey(k));
                            if (v == null || v.length != VALSIZE || v[0] != (byte) (k * 31)) throw new AssertionError("k" + k);
                        }
                        gets.add(64);
                    }
                }
            });
            ts[t].start();
        }
        Thread.sleep(3000);         // warm
        long[] a = snap(db, e, gets);
        long t0 = System.nanoTime();
        Thread.sleep(sec * 1000L);
        long[] b = snap(db, e, gets);
        double s = (System.nanoTime() - t0) / 1e9;
        for (Thread t : ts) t.join();
        String[] names = {"gets", "loads", "afterLoad calls over the trigger", "wake: evictorLock entries",
                "wake: skipped (a request pending)", "the thread's evictorLock entries", "series (requests taken)", "batches"};
        StringBuilder out = new StringBuilder(String.format(java.util.Locale.ROOT, "ENTRIES %d threads, %d keys, budget %d MB, %.1f s:",
                threads, KEYS, budget / 1000000, s));
        for (int i = 0; i < names.length; i++) {
            out.append(String.format(java.util.Locale.ROOT, "%n  %-36s %,12.0f a second", names[i], (b[i] - a[i]) / s));
        }
        out.append(String.format(java.util.Locale.ROOT, "%n  evictorLock entries in all %,.0f a second (%.2f %% of the loads); resident %d bytes; %s",
                (b[3] - a[3] + b[5] - a[5]) / s, 100.0 * (b[3] - a[3]) / Math.max(1, b[1] - a[1]),
                db.internal().cache().residents().bytes(), e.stats()));
        System.out.println(out);
        db.close();
    }

    static long[] snap(Db db, Eviction e, java.util.concurrent.atomic.LongAdder gets) {
        return new long[] {gets.sum(), db.internal().nodeCollection().loads(), Eviction.OVER.sum(),
                Eviction.WAKE_ENTRIES.sum(), Eviction.WAKE_SKIPS.sum(), Eviction.THREAD_ENTRIES.sum(),
                Eviction.SERIES.sum(), e.batchesSoFar()};
    }
}
