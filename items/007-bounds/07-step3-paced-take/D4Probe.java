package bergdb.core;

import java.util.Random;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * bergdb 007-07: a change of the startup distance on an in-memory database, with restarts
 * after it if asked; prints the records and the sections (the stream's length minus the
 * startup pos) around it, and with restarts whether the stream is the same as without. Runs
 * on any build: compile against its bergdb.jar and put the class first on the class path.
 * -Dsd0 (the setting before) -Dsd (after) -Dkeys -Dvsize -Dper (puts a transaction)
 * -Dn (transactions before) -Dn2 (after) -Drestart=K (a restart every K transactions after the
 * change, 0 none) -Dverbose=N (print the first N records after the change).
 */
public class D4Probe {
    static int sd0 = Integer.getInteger("sd0", 4000000), sd = Integer.getInteger("sd", 400000);
    static int keys = Integer.getInteger("keys", 2000), vsize = Integer.getInteger("vsize", 100);
    static int per = Integer.getInteger("per", 1);
    static int n = Integer.getInteger("n", 40000), n2 = Integer.getInteger("n2", 20000);
    static int restart = Integer.getInteger("restart", 0), verbose = Integer.getInteger("verbose", 0);

    MemoryStream stream = new MemoryStream();
    CoreTestClock clock = new CoreTestClock();
    Db db;

    Db start() { return Db.builder().testSetup(stream).clock(clock).startupDistance(sd0).start(); }

    long run(boolean print, int restartEvery) {
        db = start();
        Random r = new Random(1);
        long time = 10;
        long sumBefore = 0, cntBefore = 0, maxBefore = 0;
        for (int i = 0; i < n; i++) {
            clock.setTime(time++);
            long len = db.getStreamLength();
            db.execute(tx(r));
            long rec = db.getStreamLength() - len;
            if (i >= n / 2) { sumBefore += rec; cntBefore++; maxBefore = Math.max(maxBefore, rec); }
        }
        long len0 = db.getStreamLength();
        long sp0 = db.internal().getStartupPosForEvict();
        db.setStartupDistance(sd);
        long len1 = db.getStreamLength();
        long sp1 = db.internal().getStartupPosForEvict();
        if (print) System.out.printf("before: mean record %d, max %d, section %.3f sd0 = %.3f sd%n"
                + "dummy: record %d (%.1f x mean), section after %.3f sd%n",
                sumBefore / cntBefore, maxBefore, (double) (len0 - sp0) / sd0, (double) (len0 - sp0) / sd,
                len1 - len0, (double) (len1 - len0) / (sumBefore / cntBefore), (double) (len1 - sp1) / sd);
        long maxRec = 0; int maxAt = -1; int below2 = -1, below125 = -1, grow = 0; double most = 0;
        long prevSection = len1 - sp1; long sum = 0; int viol = 0;
        for (int i = 0; i < n2; i++) {
            clock.setTime(time++);
            long len = db.getStreamLength();
            db.execute(tx(r));
            long after = db.getStreamLength();
            long rec = after - len;
            long section = len - db.internal().getStartupPosForEvict();   // without the last record
            if (rec > maxRec) { maxRec = rec; maxAt = i; }
            sum += rec;
            if (below2 < 0 && section < 2L * sd) below2 = i;
            if (below125 < 0 && section < 1.25 * sd) below125 = i;
            if (below2 >= 0 && section >= 2L * sd) viol++;
            if (below2 < 0 && section > prevSection) grow++;
            if (below125 >= 0) most = Math.max(most, (double) section / sd);
            prevSection = section;
            if (print && i < verbose) System.out.printf("  %d: record %d, section %.3f sd%n", i, rec, (double) section / sd);
            if (restartEvery > 0 && i % restartEvery == restartEvery - 1) {
                db.sync(SyncLevel.STRONG);
                db.close();
                stream = stream.copy();     // close() closed it
                db = start();
            }
        }
        if (print) System.out.printf("after: below 2 sd at %d, below 1.25 sd at %d, then at most %.3f sd, %d over 2 sd; "
                + "largest record %d (%.1f x mean before) at %d, mean %d; section grew %d times before 2 sd%n",
                below2, below125, most, viol, maxRec, (double) maxRec / (sumBefore / cntBefore), maxAt, sum / n2, grow);
        db.sync(SyncLevel.STRONG);
        long length = db.getStreamLength();
        db.close();
        return length;
    }

    Trans tx(Random r) {
        Trans.Builder tb = db.trans();
        for (int k = 0; k < per; k++) {
            byte[] v = new byte[vsize];
            r.nextBytes(v);
            tb.put("/k/" + r.nextInt(keys), v);
        }
        return tb.build();
    }

    public static void main(String[] args) throws Exception {
        long t0 = System.nanoTime();
        D4Probe a = new D4Probe();
        a.run(true, 0);
        if (restart > 0) {
            D4Probe b = new D4Probe();
            b.run(false, restart);
            long la = a.stream.getLength(), lb = b.stream.getLength();
            boolean same = la == lb;
            if (same) {
                byte[] x = new byte[(int) la], y = new byte[(int) lb];
                a.stream.read(0, x, 0, (int) la);
                b.stream.read(0, y, 0, (int) lb);
                same = java.util.Arrays.equals(x, y);
            }
            System.out.printf("restarts every %d: stream %s (%d, %d bytes)%n", restart, same ? "identical" : "DIFFERS", la, lb);
        }
        System.out.printf("ms=%d%n", (System.nanoTime() - t0) / 1000000);
    }
}
