package bergdb.core;

import java.util.Random;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * bergdb 031-05's probe of the clock's hold (DbClock.hold): with the system clock, a writer
 * commits puts of 0 to 3,000 bytes at 200 keys and calls maintain(100) every 20th action,
 * while READERS threads call currentTime() and read at the time it returns, for SECONDS.
 * Reclaim is on (R = 1 s, startup distance 2,000 bytes). Prints DbClock.holdFailures (the
 * records of maintenance whose time had to follow a time handed out to a reader: 0 if the
 * hold covers them all), the calls of currentTime() and how many returned the last
 * transaction's time (held, as the system clock is ahead of it otherwise), and the writer's
 * actions and the stream's length.
 *
 *   javac -cp build/bergdb.jar -d OUT HoldProbe.java
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.HoldProbe SECONDS READERS
 *   (-Dproto315.eager=true for the commit's maintenance in its own call; -Dpause=MS)
 */
public class HoldProbe {
    /** -Dpause=MS: a sleep after each action, so that the writer is idle between actions. */
    static final long PAUSE = Long.getLong("pause", 0);

    public static void main(String[] args) throws Exception {
        final int seconds = Integer.parseInt(args[0]);
        final int readers = Integer.parseInt(args[1]);
        final Db db = Db.builder().mainStream(new MemoryStream()).start();
        db.setStartupDistance(2000);
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        final AtomicBoolean stop = new AtomicBoolean();
        final AtomicLong calls = new AtomicLong(), atLast = new AtomicLong();
        Thread[] rs = new Thread[readers];
        for (int i = 0; i < readers; i++) {
            final int seed = i;
            rs[i] = new Thread(() -> {
                Random r = new Random(seed);
                GetData gd = db.newGetData();
                while (!stop.get()) {
                    long t = db.currentTime();
                    calls.incrementAndGet();
                    if (t == db.lookupTime(Long.MAX_VALUE)) atLast.incrementAndGet();
                    db.getOne(t, Keys.toSegments("/k" + r.nextInt(200)), gd);
                }
            });
            rs[i].start();
        }
        Random r = new Random(1);
        long end = System.nanoTime() + seconds * 1_000_000_000L, actions = 0;
        while (System.nanoTime() < end) {
            if (actions % 20 == 19) {
                db.maintain(100);
            } else {
                db.execute(db.trans().put("/k" + r.nextInt(200), new byte[r.nextInt(3000)])
                        .build());
            }
            actions++;
            if (PAUSE > 0) Thread.sleep(PAUSE);
        }
        stop.set(true);
        for (Thread t : rs) t.join();
        System.out.println((Reclaim.eager ? "eager (D2)" : "deferred (D1)") + ": actions "
                + actions + ", stream " + db.getStreamLength() + ", iterations "
                + db.getReclaimIterationCount() + "; currentTime() " + calls.get()
                + ", of which at the last transaction's time " + atLast.get()
                + "; hold failures " + DbClock.holdFailures);
        db.close();
    }
}
