package bergdb.core;

import java.util.Random;
import bergdb.dag.Spos;

/** Calibrates the Db-level tests of the paced take (007-03 step 3). */
public class TakeProbe {
    public static void main(String[] args) {
        int sd = Integer.getInteger("sd", 20000);
        int sd2 = Integer.getInteger("sd2", 0);
        int keys = Integer.getInteger("keys", 2000);
        int n = Integer.getInteger("n", 20000);
        int n2 = Integer.getInteger("n2", 0);
        int vsize = Integer.getInteger("vsize", 16);
        boolean small = Boolean.getBoolean("small");
        int per = Integer.getInteger("per", 1);
        CoreTestClock clock = new CoreTestClock();
        DbBuilder b = Db.builder().testSetup().clock(clock).startupDistance(sd);
        if (small) b = b.maxNodeSize8();
        Db db = b.start();
        Random r = new Random(1);
        long time = 10;
        double sumS = 0, maxS = 0; long cnt = 0; long maxRec = 0; long sumRec = 0; int viol = 0;
        long t0 = System.nanoTime();
        for (int i = 0; i < n + n2; i++) {
            if (i == n && sd2 > 0) {
                long len0 = db.getStreamLength();
                long sp0 = db.internal().getStartupPosForEvict();
                boolean due = db.internal().transSeq().posOfTransBefore(len0 - 2L * sd2 + 1) != Spos.NULL;
                db.setStartupDistance(sd2);
                long len1 = db.getStreamLength();
                long sp1 = db.internal().getStartupPosForEvict();
                boolean left = db.internal().transSeq().posOfTransBefore(len0 - 2L * sd2 + 1) != Spos.NULL;
                System.out.printf("decrease: len0=%d S0=%d due=%b; after: rec=%d S=%d left=%b%n",
                        len0, len0 - sp0, due, len1 - len0, len1 - sp1, left);
                sd = db.getStartupDistance();
                sumS = 0; maxS = 0; cnt = 0; maxRec = 0; sumRec = 0;
            }
            clock.setTime(time++);
            Trans.Builder tb = db.trans();
            for (int k = 0; k < per; k++) {
                byte[] v = new byte[vsize];
                r.nextBytes(v);
                tb.put("/k/" + r.nextInt(keys), v);
            }
            long lenBefore = db.getStreamLength();
            db.execute(tb.build());
            long lenAfter = db.getStreamLength();
            long sp = db.internal().getStartupPosForEvict();
            if (db.internal().transSeq().posOfTransBefore(lenBefore - 2L * sd + 1) != Spos.NULL) viol++;
            long rec = lenAfter - lenBefore;
            if (rec > Integer.getInteger("big", 1 << 30)) System.out.printf("  big i=%d phase2=%b rec=%d S/sd=%.3f D=%d%n", i - n, i >= n, rec, (double) (lenAfter - sp) / sd, db.internal().transSeq().getSize());
            boolean measure = i >= n ? true : lenAfter > 4L * sd;
            if (measure) {
                double S = (double) (lenAfter - sp) / sd;
                sumS += S; maxS = Math.max(maxS, S); cnt++;
                sumRec += rec; maxRec = Math.max(maxRec, rec);
            }
            if (i >= n && ((i - n) < Integer.getInteger("first", 0) || (i - n) % Math.max(1, n2 / 20) == 0)) {
                System.out.printf("  i=%d len=%d S/sd=%.3f rec=%d%n", i - n, lenAfter, (double) (lenAfter - sp) / sd, rec);
            }
            if (i == n - 1 || i == n + n2 - 1) {
                System.out.printf("%s: len=%d cnt=%d S/sd mean=%.3f max=%.3f rec mean=%.0f max=%d max/mean=%.2f viol=%d D=%d%n",
                        i == n - 1 ? "phase1" : "phase2", lenAfter, cnt, sumS / cnt, maxS,
                        (double) sumRec / cnt, maxRec, maxRec / ((double) sumRec / cnt), viol,
                        db.internal().transSeq().getSize());
            }
        }
        System.out.printf("ms=%d%n", (System.nanoTime() - t0) / 1000000);
        db.close();
    }
}
