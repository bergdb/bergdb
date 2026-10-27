package bergdb.core;

import java.util.Random;
import bergdb.dag.Spos;

/** Mixed transaction sizes: a batch of 'batch' puts every 'every' transactions, else one put. */
public class MixedProbe {
    public static void main(String[] args) {
        int sd = Integer.getInteger("sd", 1000000);
        int keys = Integer.getInteger("keys", 20000), vsize = Integer.getInteger("vsize", 100);
        int n = Integer.getInteger("n", 40000), batch = Integer.getInteger("batch", 500);
        int every = Integer.getInteger("every", 1000);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).startupDistance(sd).start();
        Random r = new Random(1);
        long sumBatchDirty = 0; long sumSingle = 0, cntSingle = 0, maxSingle = 0, maxBatch = 0, sumBatch = 0, cntBatch = 0;
        double maxS = 0, sumS = 0; long cntS = 0; int viol = 0;
        long[] hist = new long[8];   // single records over 2^k * mean... computed after
        java.util.ArrayList<Long> singles = new java.util.ArrayList<Long>();
        for (int i = 0; i < n; i++) {
            clock.setTime(10 + i);
            int puts = i % every == every - 1 ? batch : 1;
            Trans.Builder tb = db.trans();
            for (int k = 0; k < puts; k++) {
                byte[] v = new byte[vsize];
                r.nextBytes(v);
                tb.put("/k/" + r.nextInt(keys), v);
            }
            long len0 = db.getStreamLength();
            db.execute(tb.build());
            long len1 = db.getStreamLength();
            long rec = len1 - len0;
            if (db.internal().transSeq().posOfTransBefore(len0 - 2L * sd + 1) != Spos.NULL) viol++;
            if (len1 < 4L * sd) continue;
            double S = (double) (len1 - db.internal().getStartupPosForEvict()) / sd;
            maxS = Math.max(maxS, S); sumS += S; cntS++;
            if (puts == 1) { sumSingle += rec; cntSingle++; maxSingle = Math.max(maxSingle, rec); singles.add(rec); }
            else { sumBatch += rec; cntBatch++; maxBatch = Math.max(maxBatch, rec); sumBatchDirty += db.internal().transSeq().last().gotDirtyNodes.size(); }
        }
        double mean = (double) sumSingle / cntSingle;
        int over10 = 0, over100 = 0;
        for (long x : singles) { if (x > 10 * mean) over10++; if (x > 100 * mean) over100++; }
        System.out.printf("len=%d S/sd mean=%.3f max=%.3f viol=%d single: mean=%.0f max=%d (x%.0f) >10x=%d >100x=%d of %d; batch: mean=%.0f max=%d gotDirty=%.0f%n",
                db.getStreamLength(), sumS / cntS, maxS, viol, mean, maxSingle, maxSingle / mean, over10, over100, cntSingle,
                (double) sumBatch / cntBatch, maxBatch, (double) sumBatchDirty / cntBatch);
        db.close();
    }
}
