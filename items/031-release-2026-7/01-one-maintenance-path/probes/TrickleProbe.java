package bergdb.core;

import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * bergdb 031-01's probe of maintain() in a database written slowly, from 028-51's
 * IdleLiveProbe: LIVE keys of 100 bytes put, 100 a transaction, each overwritten ROUNDS
 * times, then 20 R of maintain() calls, one a millisecond of a test clock (R = 1 s;
 * MemoryStream), with one value of 100 bytes overwritten every EVERY calls (0: none).
 * Prints the values the trickle wrote, the stream written during the calls and in their last
 * half, the last call that returned true, the stream kept and the first available position.
 *
 * In package bergdb.core; on the class path before the jar (from java/, after build.sh):
 *   javac -cp build/bergdb.jar -d OUT TrickleProbe.java
 *   java -cp OUT:build/bergdb.jar bergdb.core.TrickleProbe LIVE SD RS ROUNDS EVERY
 * RS: the calls in R. 031-01 ran LIVE 30000, SD 1000000, RS 20, ROUNDS 10 and EVERY 0, 1000
 * and 100, on main and on its prototype.
 */
public class TrickleProbe {
    public static void main(String[] a) throws Exception {
        int live = Integer.parseInt(a[0]);
        int sd = Integer.parseInt(a[1]);
        int rs = Integer.parseInt(a[2]);
        AtomicLong clock = new AtomicLong(1_778_000_000_000L * 10_000L);
        Clock c = clock::get;
        Db db = Db.builder().mainStream(new MemoryStream()).clock(c).start();
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        db.setStartupDistance(sd);
        for (int i = 0; i < live; i += 100) {
            Trans.Builder b = db.trans();
            for (int k = i; k < i + 100 && k < live; k++) b.put(new byte[] {0x10, (byte) (k >> 16), (byte) (k >> 8), (byte) k}, new byte[100]);
            clock.addAndGet(10_000);
            db.execute(b.build());
        }
        int rounds = a.length > 3 ? Integer.parseInt(a[3]) : 0;
        for (int r = 0; r < rounds; r++) {
            for (int i = 0; i < live; i += 100) {
                Trans.Builder b = db.trans();
                for (int k = i; k < i + 100 && k < live; k++) b.put(new byte[] {0x10, (byte) (k >> 16), (byte) (k >> 8), (byte) k}, new byte[100]);
                clock.addAndGet(100_000);
                db.execute(b.build());
            }
        }
        long len0 = db.getStreamLength();
        long lenHalf = 0, trueCalls = 0, lastTrue = -1, trickle = 0;
        int every = Integer.parseInt(a[4]);     // a put every 'every' calls (ms), 0: none
        for (int i = 0; i < rs * 1000; i++) {
            clock.addAndGet(10_000);
            if (every > 0 && i % every == 0) {      // the trickle: one value overwritten
                int k = (i / every) % Math.max(1, live);
                db.execute(db.trans().put(new byte[] {0x10, (byte) (k >> 16), (byte) (k >> 8), (byte) k}, new byte[100]).build());
                trickle += 100;
            }
            if (db.maintain()) { trueCalls++; lastTrue = i; }
            if (i == rs * 500) lenHalf = db.getStreamLength();
        }
        long len = db.getStreamLength();
        System.out.println("trickle " + trickle / 1000 + " kB of values; " + String.format("live %d (%d kB stream) sd %d: wrote %d kB in %d R, %d kB in the last %d R; last true call %d; kept %d kB; fp %d kB",
                live, len0 / 1000, sd, (len - len0) / 1000, rs, (len - lenHalf) / 1000, rs / 2, lastTrue, (len - db.getFirstAvailablePos()) / 1000, db.getFirstAvailablePos() / 1000));
        db.close();
    }
}
