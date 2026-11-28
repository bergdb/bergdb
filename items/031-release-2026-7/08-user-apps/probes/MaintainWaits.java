import bergdb.pub.*;
import java.util.concurrent.atomic.*;

/**
 * 031-08, UA-7: maintain(budget) while other threads commit without a pause: the calls that
 * end in 10 s, and the longest call, with 0, 1 and 8 writer threads (a memory database, a
 * retain duration of 1 s on the system clock, so that reclaim has work).
 *
 * Usage: java -cp bergdb-release.jar:. MaintainWaits
 */
public class MaintainWaits {
    public static void main(String[] a) throws Exception {
        for (int writers : new int[] {0, 1, 8}) {
            try (Database db = Factory.database().memory().start()) {
                db.setStartupDistanceInMb(5);
                db.setRetainDuration(Duration.seconds(1));
                Connection c0 = db.connection();
                for (int i = 0; i < 20; i++) { WBuilder w = c0.w(); for (int j = 0; j < 400; j++) w.put("/d/k" + j + ".bin", new byte[300]); w.execute(); }
                AtomicBoolean stop = new AtomicBoolean();
                AtomicLong commits = new AtomicLong();
                Thread[] ts = new Thread[writers];
                for (int i = 0; i < writers; i++) {
                    final int id = i;
                    ts[i] = new Thread(() -> {
                        Connection c = db.connection();
                        int k = 0;
                        while (!stop.get()) { c.put("/w" + id + "/k" + (k++ % 500) + ".bin", new byte[200]); commits.incrementAndGet(); }
                    });
                    ts[i].start();
                }
                // the calls in a thread of their own, so that one that does not return does not hold the probe
                AtomicLong calls = new AtomicLong(), longest = new AtomicLong();
                AtomicBoolean done = new AtomicBoolean();
                Thread m = new Thread(() -> {
                    while (!done.get()) {
                        long t0 = System.nanoTime();
                        db.maintain(100);
                        longest.accumulateAndGet((System.nanoTime() - t0) / 1_000_000, Math::max);
                        calls.incrementAndGet();
                    }
                });
                m.start();
                Thread.sleep(10_000);
                done.set(true);
                long ended = calls.get();
                long c10 = commits.get();
                m.join(2_000);
                boolean stuck = m.isAlive();
                stop.set(true);
                for (Thread t : ts) t.join();
                m.join();
                System.out.println(writers + " writers: " + ended + " maintain(100) calls ended in 10 s" + (stuck ? ", and the call then running"
                        + " had not returned 2 s later; it returned when the writers stopped" : ", the longest " + longest.get() + " ms")
                        + "; " + c10 + " commits in the 10 s");
            }
        }
    }
}
