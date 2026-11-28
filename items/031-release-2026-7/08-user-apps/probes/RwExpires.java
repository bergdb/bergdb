import bergdb.pub.*;
import bergdb.pub.util.LookupTimeNotAvailableException;

/**
 * 031-08, UA-3: an rw() whose action runs longer than the retain duration, while reclaim cuts
 * past the action's read time, throws LookupTimeNotAvailableException from rw(), which
 * Connection.rw()'s Javadoc does not name; nothing of it is written.
 *
 * Usage: java -cp bergdb-release.jar:. RwExpires [index|plain]
 */
public class RwExpires {
    public static class Acc { public long balance; public Acc() {} }

    public static void main(String[] a) throws Exception {
        boolean index = a.length == 0 || a[0].equals("index");
        TestClock clock = new TestClock();
        clock.setTime(Time.utc("2026-01-01"));
        try (Database db = Factory.database().memory().clock(clock).start()) {
            db.setStartupDistanceInMb(5);
            db.setRetainDuration(Duration.seconds(1));
            Connection c = db.connection();
            if (index) db.indexBuilder("by-balance").dir("/acc/").type("long").field("balance").start().join();
            Acc x = new Acc();
            x.balance = 100;
            c.put("/acc/1", x);
            Connection other = db.newConnection();
            int[] runs = {0};
            try {
                c.rw(env -> {
                    runs[0]++;
                    Acc acc = env.get("/acc/1", Acc.class);           // fixes the run's read time
                    long readAt = db.currentTime().units();
                    for (int i = 0; i < 2000 && db.getFirstAvailableLookupTime().units() <= readAt; i++) {
                        clock.setTime(Time.units(clock.getTime() + 5_000_000));   // 0.5 s
                        other.put("/other/k" + (i % 50) + ".bin", new byte[2000]);  // not read by the action
                        db.maintain(100_000);
                    }
                    System.out.println("run " + runs[0] + ": read at " + readAt + ", first available now "
                            + db.getFirstAvailableLookupTime().units());
                    acc.balance -= 30;
                    env.put("/acc/1", acc);
                });
                System.out.println("rw() returned after " + runs[0] + " runs");
            } catch (LookupTimeNotAvailableException e) {
                System.out.println("rw() threw after " + runs[0] + " run(s): " + e);
            }
            System.out.println("balance now " + c.get("/acc/1", Acc.class).balance);
        }
    }
}
