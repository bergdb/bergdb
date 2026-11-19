import bergdb.core.*;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.pub.util.DbException;
import bergdb.stream.FileStream;

import java.io.File;
import java.util.*;

/**
 * B2b of 026-13: a refused transaction gives its time back (releases/next.md, 026-06: "its
 * time given back"). Db's "Threads": a read at a time that currentTime() or a read's actual
 * lookup time gave reads the same state whenever it runs, and no transaction that runs or
 * comes later has a time at or before it. So while a transaction's value transformation runs
 * (and will throw), a reader takes currentTime() and reads; after the refusal the next
 * transaction commits; the reader reads at the same time again and must see the same state.
 * A clock that does not move makes the times next to each other.
 *
 * Usage: java -cp bergdb-release.jar:out GivenBack DIR ROUNDS [moving]
 */
public class GivenBack {
    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        int rounds = Integer.parseInt(a[1]);
        boolean moving = a.length > 2;
        Common.rmrf(dir);
        Common.ManualClock clock = new Common.ManualClock(1_778_000_000_000L * 10_000L);
        Db db = Db.builder().mainStream(new FileStream(dir, false)).clock(clock).start();
        int bad = 0, waited = 0;
        try {
            for (int i = 0; i < rounds; i++) {
                byte[] x = {0x10, (byte) (i >>> 8), (byte) i};
                final long[] seen = new long[3];
                final Object lock = new Object();
                final boolean[] inVt = {false};
                Thread reader = new Thread(() -> {
                    synchronized (lock) { while (!inVt[0]) { try { lock.wait(); } catch (InterruptedException e) { return; } } }
                    long t0 = System.nanoTime();
                    long t = db.currentTime();
                    seen[2] = (System.nanoTime() - t0) / 1_000_000;
                    GetData gd = db.newGetData();
                    byte[] v = db.getOne(t, Keys.toSegments(x), gd);
                    seen[0] = t;
                    seen[1] = gd.actualLookupTime;
                    if (v != null) throw new IllegalStateException("x present before");
                });
                reader.start();
                Trans bad1 = db.trans().put(Keys.toSegments(new byte[] {0x20}), null, new byte[1], (tt, in, prev) -> {
                    synchronized (lock) { inVt[0] = true; lock.notifyAll(); }
                    try { Thread.sleep(30); } catch (InterruptedException e) { }
                    throw new IllegalStateException("refuse");
                }).build();
                try { db.execute(bad1); throw new Common.Fail("committed"); } catch (DbException e) { }
                reader.join();
                if (moving) clock.advanceMillis(1);
                Trans good = db.trans().put(x, new byte[] {1}).build();
                db.execute(good);
                GetData gd = db.newGetData();
                byte[] v1 = db.getOne(seen[0], Keys.toSegments(x), gd);
                byte[] v2 = db.getOne(seen[1], Keys.toSegments(x), gd);
                if (seen[2] > 20) waited++;
                if (v1 != null || v2 != null || good.tt <= seen[0] || good.tt <= seen[1]) {
                    bad++;
                    if (bad <= 5) System.out.println("FINDING round " + i + ": currentTime() during the refused transaction gave "
                            + seen[0] + " (actual lookup " + seen[1] + "), the next transaction's time is " + good.tt
                            + "; a read at the first time now sees its write: " + (v1 != null) + ", at the second: " + (v2 != null)
                            + "; the refused one had tt " + bad1.tt);
                }
            }
        } finally {
            db.close();
        }
        Common.log((bad == 0 ? "OK" : "FAIL") + " GivenBack: " + rounds + " rounds, " + bad + " reads whose state changed, "
                + waited + " currentTime() calls that waited over 20 ms for the transaction");
        if (bad > 0) System.exit(1);
    }
}
