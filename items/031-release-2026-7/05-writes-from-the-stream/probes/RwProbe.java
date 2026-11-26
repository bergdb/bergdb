package bergdb.core;

import java.util.Random;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * bergdb 031-05's probe of a cost of the deferred design (D1): reclaim's copies, written at
 * the start of the next call, come after a read time that the application took while they
 * were due, so a read-modify-write that read a copied key is refused (RerunException). A
 * single thread does N read-modify-writes: currentTime(), a read of one of KEYS keys at it,
 * and a put of a new value of VALUE bytes at that key with the key as read and the read time
 * as the transaction's lookup time; a refused one is counted and done again. A test clock
 * moves 10 ms before each transaction; R = 1 s, startup distance SD.
 *
 *   javac -cp build/bergdb.jar -d OUT RwProbe.java
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.RwProbe N KEYS VALUE SD
 *   (-Dproto315.eager=true for the commit's maintenance in its own call; on a jar without
 *   the switch, such as 031-04's, the label says D1 and means that jar)
 */
public class RwProbe {
    public static void main(String[] args) {
        final int n = Integer.parseInt(args[0]), keys = Integer.parseInt(args[1]);
        final int value = Integer.parseInt(args[2]), sd = Integer.parseInt(args[3]);
        final AtomicLong time = new AtomicLong(Clock.UNITS_PER_SEC);
        Db db = Db.builder().mainStream(new MemoryStream()).clock(time::get).start();
        db.setStartupDistance(sd);
        db.setRetainDuration(Clock.UNITS_PER_SEC);
        Random r = new Random(1);
        for (int k = 0; k < keys; k++) {
            time.addAndGet(Clock.UNITS_PER_SEC / 1000);
            db.execute(db.trans().put("/k" + k, new byte[value]).build());
        }
        long refused = 0;
        for (int i = 0; i < n; i++) {
            String key = "/k" + r.nextInt(keys);
            while (true) {
                time.addAndGet(Clock.UNITS_PER_SEC / 100);
                long t = db.currentTime();
                db.getOne(t, bergdb.dag.Keys.toSegments(key), db.newGetData());
                try {
                    db.execute(db.trans().lookupTime(t).keyRead(key).put(key, new byte[value])
                            .build());
                    break;
                } catch (RerunException e) {
                    refused++;
                }
            }
        }
        final boolean eager = Boolean.getBoolean("proto315.eager");
        System.out.println((eager ? "eager (D2)" : "deferred (D1)") + ": " + n
                + " read-modify-writes at " + keys + " keys of " + value + " bytes, sd " + sd
                + ": refused " + refused + "; iterations " + db.getReclaimIterationCount()
                + ", stream " + db.getStreamLength());
        db.close();
    }
}
