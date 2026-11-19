package bergdb.core;

import java.util.Random;

import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * The hit rate of a hot set before and after a reclaim iteration, with the capacity
 * controller (bergdb item 001, WPs J6 and J7; bergdb 001-08, 7.5 and 7.6). Two
 * databases get the same workload: keys with values, a hot set read again and again, and
 * updates of random keys; database B has reclaim on, A has not. Both have a budget smaller
 * than the data and larger than the hot set. The loads per hot read (NodeCollection.loads)
 * are measured before the updates, and after them, when B has done an iteration (its scan
 * reads every KV through the maintenance follower, which caches nothing). The difference
 * between B and A after is reclaim's effect on the cache.
 *
 * Usage: java [-Dprop=value ...] -cp bergdb.jar:stress bergdb.core.ReclaimHitRate
 * Properties: keys=N (default 20000), valsize=N (200), hot=N (500), budget=B (bytes,
 * default 3000000), reads=N (hot reads per measurement, 20000).
 */
public class ReclaimHitRate {
    static final int KEYS = Integer.getInteger("keys", 20000);
    static final int VALSIZE = Integer.getInteger("valsize", 200);
    static final int HOT = Integer.getInteger("hot", 500);
    static final long BUDGET = Long.getLong("budget", 3 * 1000 * 1000);
    static final int READS = Integer.getInteger("reads", 20000);

    static Db start(MemoryStream s, CoreTestClock clock) {
        Db db = Db.builder().testSetup(s).clock(clock)
                .cacheSizeIndicator(BUDGET).evictionSchedule(Eviction.Schedule.BUDGET, 1).start();
        db.setStartupDistance(200 * 1000);      // nothing written if in force (bergdb 028-13)
        return db;
    }

    /** Loads per hot read, over READS reads of the hot set. */
    static double hotLoads(Db db, Random r) {
        long before = db.internal().nodeCollection().loads();
        for (int i = 0; i < READS; i++) {
            DbUtil.get(db, "k" + r.nextInt(HOT));
        }
        return (double) (db.internal().nodeCollection().loads() - before) / READS;
    }

    public static void main(String[] args) {
        MemoryStream sa = new MemoryStream(), sb = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long time = Clock.UNITS_PER_SEC;
        clock.setTime(time);
        Db a = start(sa, clock), b = start(sb, clock);
        byte[] v = new byte[VALSIZE];
        for (int i = 0; i < KEYS; i += 100) {
            time += Clock.UNITS_PER_SEC / 100;
            clock.setTime(time);
            for (Db d : new Db[] {a, b}) {
                Trans.Builder t = d.trans();
                for (int k = i; k < Math.min(KEYS, i + 100); k++) t.put("k" + k, v);
                d.execute(t.build());
            }
        }
        // Warm the hot set, then measure.
        hotLoads(a, new Random(1));
        hotLoads(b, new Random(1));
        double a0 = hotLoads(a, new Random(2)), b0 = hotLoads(b, new Random(2));

        b.setRetainDuration(1 * Clock.UNITS_PER_SEC);
        Reclaim reclaim = b.internal().reclaim();
        Random r = new Random(3);
        int updates = 0;
        long iterations0 = reclaim.getIterationCount();
        while (reclaim.getIterationCount() < iterations0 + 1 && updates < 2000000) {
            time += Clock.UNITS_PER_SEC / 1000;
            clock.setTime(time);
            int k = HOT + r.nextInt(KEYS - HOT);
            for (Db d : new Db[] {a, b}) {
                d.execute(d.trans().put("k" + k, v).build());
            }
            updates++;
            if (updates % 50 == 0) {
                // The hot set stays in use during the updates.
                for (Db d : new Db[] {a, b}) {
                    for (int j = 0; j < 20; j++) DbUtil.get(d, "k" + r.nextInt(HOT));
                }
            }
        }
        double a1 = hotLoads(a, new Random(4)), b1 = hotLoads(b, new Random(4));
        System.out.println("keys " + KEYS + ", values " + VALSIZE + " bytes, hot set " + HOT
                + " keys, budget " + BUDGET + " bytes; " + updates + " updates, B's reclaim "
                + (reclaim.getIterationCount() - iterations0) + " iteration(s)");
        System.out.printf("loads per hot read: before, A %.4f, B %.4f; after, A %.4f (no reclaim), B %.4f (reclaim)%n",
                a0, b0, a1, b1);
        System.out.println("A: " + a.internal().eviction().summary());
        System.out.println("B: " + b.internal().eviction().summary());
        a.stop();
        b.stop();
    }
}
