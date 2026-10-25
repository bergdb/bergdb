import java.util.List;

import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.TransactionInfo;

/**
 * Probe of bergdb 005-42: what Connection.transactionInfo() gives, through the Pub API, for
 * a transaction that writes an index entry (A) and for a value that reclaim has rewritten
 * (B). Prints each KV's key(), or what key() and ikey() throw.
 *
 * A: an index on the long field 'salary' of /e/, a put of /e/x, a get of /e/x.
 * B: a put of /a at 1 s, then 20,000 puts of 2,000 bytes to /b/0 to /b/99, a second apart,
 * with a retention of 100 s and a startup distance of 1 MB, so that reclaim runs; then a
 * get of /a.
 *
 * Usage: java -ea -cp DIR:bergdb.jar TransactionInfoProbe
 */
public class TransactionInfoProbe {
    public static class Emp {
        public long salary;
        public Emp() {}
        public Emp(long salary) { this.salary = salary; }
    }

    public static void main(String[] args) throws Exception {
        partA();
        partB();
    }

    static void partA() {
        Database db = Factory.database().memory().start();
        db.indexBuilder("emp-salary").dir("/e/").type("long").field("salary").start().join();
        Connection c = db.connection();
        c.put("/e/x", new Emp(42));
        c.get("/e/x", Emp.class);
        System.out.println("A: a put of /e/x, in a directory with an index; a get of /e/x");
        print(c.transactionInfo());
        db.stop();
    }

    static void partB() {
        TestClock clock = new TestClock();
        long sec = Duration.seconds(1).units();
        clock.setTime(Time.units(sec));
        Database db = Factory.database().memory().clock(clock)
                .retainDuration(Duration.seconds(100)).startupDistanceInMb(1).start();
        Connection c = db.connection();
        Transaction t0 = c.w().put("/a", "a0").execute();
        byte[] v = new byte[2000];
        for (int i = 0; i < 20000; i++) {
            clock.setTime(Time.units((i + 2) * sec));
            c.put("/b/" + (i % 100), v);
        }
        c.get("/a", String.class);
        TransactionInfo info = c.transactionInfo();
        System.out.println("B: a put of /a at " + t0.getTime().units() / sec + " s, then 20,000 "
                + "puts of other keys; a get of /a at " + (20001) + " s");
        System.out.println("  time(): " + info.time().units() / sec + " s");
        print(info);
        db.stop();
    }

    static void print(TransactionInfo info) {
        List<Kv<byte[]>> kvs = info.kvs();
        System.out.println("  kvs(): " + kvs.size());
        for (int i = 0; i < kvs.size(); i++) {
            Kv<byte[]> kv = kvs.get(i);
            System.out.println("    " + i + ": key() " + call(kv, true) + "; ikey() "
                    + call(kv, false) + "; value " + (kv.value() == null ? "null"
                    : kv.value().length + " bytes"));
        }
    }

    static String call(Kv<byte[]> kv, boolean key) {
        try {
            return "= " + (key ? kv.key() : kv.ikey());
        } catch (RuntimeException e) {
            return "throws " + e.getClass().getSimpleName() + ": " + printable(e.getMessage());
        }
    }

    /** The string, with each character outside printable ASCII as a Java escape. */
    static String printable(String s) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c >= 32 && c < 127) {
                b.append(c);
            } else {
                b.append(String.format("\\u%04x", (int) c));
            }
        }
        return b.toString();
    }
}
