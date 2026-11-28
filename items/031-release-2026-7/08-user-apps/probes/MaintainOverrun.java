import bergdb.pub.*;
import java.util.Random;

/**
 * 031-08, UA-5: what one maintain(budget) call writes beyond its budget, with a live value of
 * 8 MiB (Limits.MAX_VALUE_BYTES) among small ones, a retain duration of 1 s and a test clock.
 *
 * Usage: java -cp bergdb-release.jar:. MaintainOverrun [BUDGET]
 */
public class MaintainOverrun {
    public static void main(String[] a) throws Exception {
        int budget = a.length > 0 ? Integer.parseInt(a[0]) : 100;
        TestClock clock = new TestClock();
        clock.setTime(Time.utc("2026-01-01"));
        Random r = new Random(1);
        try (Database db = Factory.database().memory().clock(clock).start()) {
            db.setStartupDistanceInMb(5);
            Connection c = db.connection();
            for (int i = 0; i < 4; i++) {
                WBuilder w = c.w();
                for (int j = 0; j < 400; j++) { byte[] v = new byte[200]; r.nextBytes(v); w.put("/s/k" + i + "-" + j + ".bin", v); }
                w.execute();
                if (i == 1) { byte[] big = new byte[Limits.MAX_VALUE_BYTES]; r.nextBytes(big); c.put("/big.bin", big); }
            }
            db.setRetainDuration(Duration.seconds(1));
            long most = 0;
            int mostAt = -1, calls = 0;
            for (int i = 0; i < 400; i++) {
                clock.setTime(Time.units(clock.getTime() + 3_000_000));   // 0.3 s
                long before = db.getStreamSize(), first = db.getFirstAvailableLookupTime().units();
                db.maintain(budget);
                calls++;
                long wrote = db.getStreamSize() - before;
                if (db.getFirstAvailableLookupTime().units() == first && wrote > most) { most = wrote; mostAt = i; }
            }
            System.out.println("maintain(" + budget + "): the most that one call wrote, with no cut in it: " + most + " bytes (call "
                    + mostAt + " of " + calls + "); the budget's bytes " + 1000L * Math.max(100, Math.min(100_000, budget)));
        }
    }
}
