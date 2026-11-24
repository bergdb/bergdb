package bergdb.core;

import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * bergdb 028-51's probe of maintain() in a database that is not written to: LIVE keys of 100
 * bytes put, 100 a transaction (and with ROUNDS, each overwritten ROUNDS times, 10 ms a
 * transaction, so that commits begin iterations too), then 20 R of maintain() calls, one a
 * millisecond of a test clock (R = 1 s; MemoryStream). Prints the stream written during the
 * calls, in the last half of them, the last call that returned true, the stream kept and the
 * first available position: a quiet database writes nothing in the last half.
 *
 * In package bergdb.core, as 028-47's probes; on the class path before the jar (from java/,
 * after build.sh):
 *   javac -cp build/bergdb.jar -d OUT IdleLiveProbe.java
 *   java -cp OUT:build/bergdb.jar bergdb.core.IdleLiveProbe LIVE SD RS [ROUNDS]
 * RS: the calls in R. 028-51 ran LIVE 3000 to 300000 with SD 5000000 or 50000000 and RS 20,
 * and LIVE 3000 to 30000 with SD 1000000, RS 20 and ROUNDS 10.
 */
public class IdleLiveProbe {
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
        long lenHalf = 0, trueCalls = 0, lastTrue = -1;
        for (int i = 0; i < rs * 1000; i++) {
            clock.addAndGet(10_000);
            if (db.maintain()) { trueCalls++; lastTrue = i; }
            if (i == rs * 500) lenHalf = db.getStreamLength();
        }
        long len = db.getStreamLength();
        System.out.println(String.format("live %d (%d kB stream) sd %d: wrote %d kB in %d R, %d kB in the last %d R; last true call %d; kept %d kB; fp %d kB",
                live, len0 / 1000, sd, (len - len0) / 1000, rs, (len - lenHalf) / 1000, rs / 2, lastTrue, (len - db.getFirstAvailablePos()) / 1000, db.getFirstAvailablePos() / 1000));
        db.close();
    }
}
