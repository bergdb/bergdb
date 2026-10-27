package bergdb.core;

import java.util.Random;
import bergdb.dag.Spos;

/** DbTester.testDecreaseOfStartupDistance as a main, to run on either build. */
public class DecreaseProbe {
    static boolean dueLeft(Db db, long length, int sd) {
        return db.internal().transSeq().posOfTransBefore(length - 2L * sd + 1) != Spos.NULL;
    }
    static long section(Db db) { return db.getStreamLength() - db.internal().getStartupPosForEvict(); }
    static long putRandom(Db db, Random random, int keys, int size) {
        byte[] value = new byte[size];
        random.nextBytes(value);
        long length = db.getStreamLength();
        db.execute(db.trans().put("/k/" + random.nextInt(keys), value).build());
        return db.getStreamLength() - length;
    }
    public static void main(String[] args) {
        final int sd = 400 * 1000;
        int keys = Integer.getInteger("keys", 1000), vsize = Integer.getInteger("vsize", 1000);
        int n = Integer.getInteger("n", 3000), sd0 = Integer.getInteger("sd0", 1000000);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).startupDistance(sd0).start();
        Random random = new Random(1);
        long time = 10, before = 0;
        for (int i = 0; i < n; i++) {
            clock.setTime(time++);
            long record = putRandom(db, random, keys, vsize);
            if (i >= n - 300) before += record;
        }
        long length = db.getStreamLength();
        boolean due = dueLeft(db, length, sd);
        db.setStartupDistance(sd);
        boolean left = dueLeft(db, length, sd);
        double after = (double) section(db) / sd;
        long during = 0, largest = 0; double most = 0; int viol = 0, firstBelow = -1;
        for (int i = 0; i < 1200; i++) {
            clock.setTime(time++);
            length = db.getStreamLength();
            long record = putRandom(db, random, keys, vsize);
            if (dueLeft(db, length, sd)) viol++;
            largest = Math.max(largest, record);
            if (i < 300) during += record; else most = Math.max(most, (double) section(db) / sd);
            if (firstBelow < 0 && section(db) < 1.25 * sd) firstBelow = i;
        }
        System.out.printf("due=%b left=%b after=%.3f viol=%d during/before=%.3f most=%.3f firstBelow1.25=%d largest=%d mean=%d%n",
                due, left, after, viol, (double) during / before, most, firstBelow, largest, before / 300);
        db.close();
    }
}
