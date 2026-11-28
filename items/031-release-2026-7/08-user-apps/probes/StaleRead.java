import bergdb.core.Db;
import bergdb.core.RerunException;
import bergdb.core.Trans;
import bergdb.dag.Keys;
import bergdb.pub.*;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.MemoryStream;

import java.nio.ByteBuffer;

/**
 * 031-08: a read-modify-write whose read time a cut passes while another transaction writes
 * what it read: the write after the read must make it run again (Core: RerunException; Pub:
 * rw() runs the action again), never commit over the other write.
 *
 * Usage: java -cp bergdb-release.jar:. StaleRead core|pub
 */
public class StaleRead {
    public static void main(String[] a) throws Exception {
        if (a[0].equals("core")) core(); else pub();
    }

    static void core() {
        long[] now = {17_700_000_000_000_000L};
        try (Db db = Db.builder().mainStream(new MemoryStream()).clock(() -> now[0]).start()) {
            db.setStartupDistance(100_000);
            db.setRetainDuration(10_000_000L);
            byte[] key = {0x10, 1};
            db.execute(db.trans().put(key, ByteBuffer.allocate(8).putLong(100).array()).build());
            long t0 = db.currentTime();                          // the read time
            byte[] old = db.getOne(t0, Keys.toSegments(key), db.newGetData());
            now[0] += 1_000;
            Trans w = db.trans().put(key, ByteBuffer.allocate(8).putLong(500).array()).build();
            db.execute(w);                                       // another write of the key, after t0
            for (int i = 0; i < 3000 && db.getFirstAvailableLookupTime() <= w.tt; i++) {
                now[0] += 5_000_000;
                db.execute(db.trans().put(new byte[] {0x20, (byte) (i % 50)}, new byte[2000]).build());
                db.maintain(100_000);
            }
            System.out.println("core: read at " + t0 + ", the other write at " + w.tt + ", first available now " + db.getFirstAvailableLookupTime());
            long v = ByteBuffer.wrap(old).getLong();
            Trans.Builder b = db.trans().lookupTime(t0).keyRead(Keys.toSegments(key));
            b.put(key, ByteBuffer.allocate(8).putLong(v - 30).array());
            try {
                db.execute(b.build());
                long got = ByteBuffer.wrap(db.getOne(Long.MAX_VALUE, Keys.toSegments(key), db.newGetData())).getLong();
                System.out.println("core: COMMITTED over the other write: the key holds " + got + " (the other write's 500 lost)");
            } catch (RerunException e) {
                System.out.println("core: RerunException, as it should: " + e.getMessage());
            }
        }
    }

    public static class Acc { public long balance; public Acc() {} }

    static void pub() {
        TestClock clock = new TestClock();
        clock.setTime(Time.utc("2026-01-01"));
        try (Database db = Factory.database().memory().clock(clock).start()) {
            db.setStartupDistanceInMb(5);
            db.setRetainDuration(Duration.seconds(1));
            Connection c = db.connection();
            Acc x = new Acc();
            x.balance = 100;
            c.put("/acc/1", x);
            Connection other = db.newConnection();
            int[] runs = {0};
            try {
                c.rw(env -> {
                    runs[0]++;
                    Acc acc = env.get("/acc/1", Acc.class);
                    if (runs[0] == 1) {
                        Acc y = new Acc();
                        y.balance = 500;
                        long wt = other.put("/acc/1", y).getTime().units();   // another write of what the action read
                        for (int i = 0; i < 3000 && db.getFirstAvailableLookupTime().units() <= wt; i++) {
                            clock.setTime(Time.units(clock.getTime() + 5_000_000));
                            other.put("/other/k" + (i % 50) + ".bin", new byte[2000]);
                            db.maintain(100_000);
                        }
                        System.out.println("pub: the other write at " + wt + ", first available now " + db.getFirstAvailableLookupTime().units());
                    }
                    acc.balance -= 30;
                    env.put("/acc/1", acc);
                });
                System.out.println("pub: rw() returned after " + runs[0] + " run(s); the account holds " + c.get("/acc/1", Acc.class).balance
                        + (runs[0] == 1 ? " (COMMITTED over the other write)" : " (470: ran again, as it should)"));
            } catch (LookupTimeNotAvailableException e) {
                System.out.println("pub: rw() threw after " + runs[0] + " run(s): " + e + "; the account holds " + c.get("/acc/1", Acc.class).balance);
            }
        }
    }
}
