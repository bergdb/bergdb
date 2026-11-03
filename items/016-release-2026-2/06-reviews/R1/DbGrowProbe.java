package bergdb.core;

import java.util.Arrays;

import bergdb.stream.MemoryStream;

/**
 * Probe for review R1 (016-06), R1-F1 on a database: a writer commits one put a transaction
 * (key kN, value vN) on a database with eight klongs a node (maxNodeSize8: arrays of 2, 6
 * and 14, so the leaves the writer appends to grow often), without eviction; two readers get
 * the last committed key and the one before it, again and again, and count answers other
 * than the committed value. Stops after SECONDS or 4,000,000 transactions.
 * Usage (before the jar): java -cp probes:build/bergdb.jar bergdb.core.DbGrowProbe SECONDS
 */
public class DbGrowProbe {
    static volatile int latest = -1;
    static volatile boolean stop;

    public static void main(String[] args) throws Exception {
        final long seconds = Long.parseLong(args.length > 0 ? args[0] : "30");
        final CoreTestClock clock = new CoreTestClock();
        final Db db = Db.builder().testSetup(new MemoryStream()).clock(clock).testId()
                .maxNodeSize8().noEvict().start();
        final long[] counts = new long[6];
        final String[] first = new String[1];
        try {
            Thread writer = new Thread(new Runnable() {
                public void run() {
                    long time = 1000 * 1000;
                    for (int n = 0; n < 4000000 && !stop; n++) {
                        clock.setTime(time += 1000);
                        db.execute(db.trans().put("k" + n, "v" + n).build());
                        latest = n;
                    }
                    counts[5] = latest + 1;
                }
            });
            Runnable read = new Runnable() {
                public void run() {
                    long gets = 0, missing = 0, wrong = 0, thrown = 0;
                    while (!stop) {
                        int m = latest;
                        if (m < 1) continue;
                        for (int j = m; j >= m - 1; j--) {
                            try {
                                byte[] v = DbUtil.get(db, "k" + j);
                                gets++;
                                if (v == null) {
                                    missing++;
                                    synchronized (first) {
                                        if (first[0] == null) first[0] = "k" + j + " missing";
                                    }
                                } else if (!Arrays.equals(v, ("v" + j).getBytes("UTF-8"))) {
                                    wrong++;
                                }
                            } catch (Throwable e) {
                                thrown++;
                                synchronized (first) {
                                    if (first[0] == null) first[0] = e.toString();
                                }
                            }
                        }
                    }
                    synchronized (counts) {
                        counts[0] += gets; counts[1] += missing; counts[2] += wrong;
                        counts[3] += thrown;
                    }
                }
            };
            Thread r1 = new Thread(read), r2 = new Thread(read);
            writer.start();
            r1.start();
            r2.start();
            long end = System.currentTimeMillis() + seconds * 1000;
            while (System.currentTimeMillis() < end && writer.isAlive()) Thread.sleep(100);
            stop = true;
            writer.join();
            r1.join();
            r2.join();
        } finally {
            db.close();
        }
        System.out.println("transactions " + counts[5] + ", gets " + counts[0] + ", missing "
                + counts[1] + ", wrong value " + counts[2] + ", thrown " + counts[3]
                + (first[0] == null ? "" : "; the first: " + first[0]));
    }
}
