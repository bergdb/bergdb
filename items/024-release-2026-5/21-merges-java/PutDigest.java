package bergdb.core;

import java.security.MessageDigest;
import java.util.Random;

import bergdb.stream.MemoryStream;

/**
 * 024-21: the SHA-256 of streams of databases without deletes (puts and overwrites only), to
 * compare a build with merges (its record format set back to 6) with main's: the put path
 * must write the same bytes. Configurations: node sizes 8, 14, 30, 62; keys in order and at
 * random; overwrites; reclaim on (retain 1 s) and off.
 */
public class PutDigest {
    public static void main(String[] a) throws Exception {
        for (int b : new int[] {8, 14, 30, 62}) {
            for (int shape = 0; shape < 3; shape++) {
                for (int reclaim = 0; reclaim < 2; reclaim++) {
                    MemoryStream ms = new MemoryStream();
                    CoreTestClock clock = new CoreTestClock();
                    long t = 1000 * bergdb.pub.util.Clock.UNITS_PER_SEC;
                    clock.setTime(t);
                    DbBuilder bl = Db.builder().testSetup(ms).clock(clock).startupDistance(20000);
                    if (b == 8) bl.maxNodeSize8();
                    if (b == 14) bl.maxNodeSize14();
                    if (b == 62) bl.maxNodeSize62();
                    Db db = bl.start();
                    if (reclaim == 1) db.setRetainDuration(bergdb.pub.util.Clock.UNITS_PER_SEC);
                    Random r = new Random(b * 10 + shape);
                    int n = 20000;
                    for (int i = 0; i < 400; i++) {
                        t += bergdb.pub.util.Clock.UNITS_PER_SEC / 10;
                        clock.setTime(t);
                        Trans.Builder tb = db.trans();
                        for (int j = 0; j < 50; j++) {
                            int k = shape == 0 ? i * 50 + j : r.nextInt(shape == 1 ? n : 2000);
                            tb.put("/k/" + String.format("%07d", k), "v" + i + "-" + j);
                        }
                        db.execute(tb.build());
                    }
                    db.sync(bergdb.pub.util.SyncLevel.ORDINARY);
                    long len = db.getStreamLength();
                    MessageDigest md = MessageDigest.getInstance("SHA-256");
                    byte[] buf = new byte[65536];
                    long p = ms.getFirstPos();
                    while (p < len) {
                        int c = (int) Math.min(buf.length, len - p);
                        ms.read(p, buf, 0, c);
                        md.update(buf, 0, c);
                        p += c;
                    }
                    db.close();
                    StringBuilder sb = new StringBuilder();
                    for (byte x : md.digest()) sb.append(String.format("%02x", x & 0xff));
                    System.out.println("PUTDIGEST b=" + b + " shape=" + (shape == 0 ? "order" : shape == 1 ? "random" : "over")
                            + " reclaim=" + reclaim + " len=" + len + " sha256=" + sb);
                }
            }
        }
    }
}
