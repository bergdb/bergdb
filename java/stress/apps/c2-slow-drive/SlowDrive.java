import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;

/**
 * C2 of 026-13 (U13-4): after a mass delete, a slow drive of commits gets the dead stream back
 * only after twice the startup distance of stream per reclaim iteration, while maintain()
 * calls get it back by the clock. A database (MemoryStream, a clock the program moves, a
 * retain duration of 1 s, startup distance SD) gets 30,000 keys and loses them all, then a
 * drive of overwrites of one key of 900 bytes, one every DT ms, so R = 1000 / DT drive
 * transactions; a fresh twin gets the same drive. Printed every R: the stream kept,
 * getStreamLength() - getFirstAvailablePos(), of both. With "maintain", each drive
 * transaction is followed by maintain() calls until it returns false, on both.
 *
 * Usage: java -cp bergdb-release.jar:out SlowDrive SD DT RS [maintain]   (RS: the drive in R)
 */
public class SlowDrive {
    public static void main(String[] a) {
        int sd = Integer.parseInt(a[0]);
        int dt = Integer.parseInt(a[1]);
        int rs = Integer.parseInt(a[2]);
        boolean maintain = a.length > 3;
        AtomicLong clock = new AtomicLong(1_778_000_000_000L * 10_000L);
        Clock c = clock::get;
        Db db = open(c, sd), twin = open(c, sd);
        for (int i = 0; i < 30_000; i += 300) {                 // 30,000 keys, 300 a transaction
            Trans.Builder b = db.trans();
            for (int k = i; k < i + 300; k++) b.put(new byte[] {0x10, (byte) (k >> 16), (byte) (k >> 8), (byte) k}, new byte[60]);
            clock.addAndGet(50_000);
            db.execute(b.build());
        }
        for (int i = 0; i < 30_000; i += 300) {                 // all deleted, 300 a transaction
            Trans.Builder b = db.trans();
            for (int k = i; k < i + 300; k++) b.delete(new byte[] {0x10, (byte) (k >> 16), (byte) (k >> 8), (byte) k});
            clock.addAndGet(50_000);
            db.execute(b.build());
        }
        int r = 1000 / dt;
        Random rnd = new Random(1);
        long s0 = db.getStreamLength();
        System.out.println("SD " + sd + ", DT " + dt + " ms, R " + r + " transactions" + (maintain ? ", maintain() after each" : "")
                + "; after the delete: kept " + (db.getStreamLength() - db.getFirstAvailablePos()) / 1000 + " kB");
        for (int i = 1; i <= rs * r; i++) {
            byte[] v = new byte[900];
            rnd.nextBytes(v);
            clock.addAndGet(dt * 10_000L);
            for (Db d : new Db[] {db, twin}) {
                d.execute(d.trans().put(new byte[] {0x06, 0x01}, v).build());
                if (maintain) for (int n = 0; n < 50 && d.maintain(); n++) { }
            }
            if (i % r == 0) System.out.println("  " + i / r + " R: kept " + (db.getStreamLength() - db.getFirstAvailablePos()) / 1000
                    + " kB, twin " + (twin.getStreamLength() - twin.getFirstAvailablePos()) / 1000 + " kB; the drive wrote "
                    + (db.getStreamLength() - s0) / 1000 + " kB");
        }
        db.close();
        twin.close();
    }

    static Db open(Clock c, int sd) {
        Db db = Db.builder().mainStream(new MemoryStream()).clock(c).startupDistance(sd).start();
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        db.setStartupDistance(sd);
        return db;
    }
}
