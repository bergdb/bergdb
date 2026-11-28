import bergdb.pub.*;

/**
 * 031-08, UA-8: maintain() on a new database with a finite retain duration and a few small
 * values: what each call writes, until the calls write nothing.
 *
 * Usage: java -cp bergdb-release.jar:. FreshMaintain [PUTS]
 */
public class FreshMaintain {
    public static void main(String[] a) throws Exception {
        int puts = a.length > 0 ? Integer.parseInt(a[0]) : 0;
        TestClock clock = new TestClock();
        clock.setTime(Time.utc("2026-01-01"));
        try (Database db = Factory.database().memory().clock(clock).start()) {
            System.out.println("new: " + db.getStreamSize());
            db.setStartupDistanceInMb(5);
            db.setRetainDuration(Duration.seconds(1));
            Connection c = db.connection();
            for (int i = 0; i < puts; i++) c.put("/k" + i + ".txt", "v" + i);
            System.out.println("after the settings and " + puts + " puts: " + db.getStreamSize());
            long last = -1;
            for (int i = 0; i < 40; i++) {
                clock.setTime(Time.units(clock.getTime() + 5_000_000));   // 0.5 s
                long before = db.getStreamSize();
                db.maintain(100_000);
                long after = db.getStreamSize();
                if (after != before) System.out.println("call " + i + ": " + before + " -> " + after);
                last = after;
            }
            System.out.println("after 40 calls: " + last);
        }
    }
}
