package bergdb.core;

import java.lang.reflect.Field;
import java.util.Random;

/** Where the paced take's section settles, and why (007-03 step 3). */
public class ShareProbe {
    public static void main(String[] args) throws Exception {
        int sd = Integer.getInteger("sd", 800000);
        int keys = Integer.getInteger("keys", 2000);
        int n = Integer.getInteger("n", 12000);
        int vsize = Integer.getInteger("vsize", 1000);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().clock(clock).startupDistance(sd).start();
        Field fD = TransSeq.class.getDeclaredField("dirtyCount"); fD.setAccessible(true);
        Field fO = TransSeq.class.getDeclaredField("ownBytes"); fO.setAccessible(true);
        Random r = new Random(1);
        double sw = 0, sshare = 0, sdd = 0, sS = 0, sDN = 0, sdo = 0, sDO = 0; long cnt = 0;
        long smoved = 0;
        for (int i = 0; i < n; i++) {
            clock.setTime(10 + i);
            byte[] v = new byte[vsize];
            r.nextBytes(v);
            TransSeq ts = db.internal().transSeq();
            long D0 = fD.getLong(ts), O0 = fO.getLong(ts);
            int N0 = ts.getSize();
            long len0 = db.getStreamLength(), sp0 = db.internal().getStartupPosForEvict();
            db.execute(db.trans().put("/k/" + r.nextInt(keys), v).build());
            ts = db.internal().transSeq();
            long D1 = fD.getLong(ts);
            TransSeq.TransInfo last = ts.last();
            int d = last.gotDirtyNodes.size();
            long w = D0 - (D1 - d);
            long o = last.ownBytes;
            if (len0 > 4L * sd && O0 > 0) {
                double S = (double) (len0 - sp0) / sd;
                sw += w; sshare += (double) D0 * o / O0 * S; sdd += d; sS += S;
                sDN += (double) D0 / N0; sdo += (double) d / o; sDO += (double) D0 / O0; cnt++;
            }
        }
        System.out.printf("sd=%d cnt=%d E[w]=%.2f E[share]=%.2f E[d]=%.2f E[S/sd]=%.3f E[D/N]=%.2f E[d/o]=%.5f E[D/O]=%.5f%n",
                sd, cnt, sw / cnt, sshare / cnt, sdd / cnt, sS / cnt, sDN / cnt, sdo / cnt, sDO / cnt);
        db.close();
    }
}
