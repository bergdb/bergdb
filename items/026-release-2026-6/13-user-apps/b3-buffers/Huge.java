import bergdb.pub.*;

import java.io.File;
import java.util.*;

/**
 * B3b of 026-13: transactions larger than the write buffer's most (10 MB) and than its start
 * (64 KiB), right after a start and after 2.2 s idle (the buffer shrunk; DatabaseBuilder,
 * "write buffer"), alone and beside a writer of small values; each read back at once, after
 * a sync, and after a restart.
 *
 * Usage: java -Xmx3g -cp bergdb-release.jar:out Huge DIR ROUNDS
 */
public class Huge {
    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        int rounds = Integer.parseInt(a[1]);
        Common.rmrf(dir);
        Map<String, Long> model = Collections.synchronizedMap(new HashMap<>());
        Random r = new Random(1);
        Database db = Factory.database().cacheSizeInMb(20).create(dir.getPath()).start();
        try {
            for (int round = 0; round < rounds; round++) {
                if (round % 2 == 1) Thread.sleep(2200);
                final Database d = db;
                final boolean beside = round % 3 == 2;
                Thread small = null;
                final boolean[] stop = {false};
                if (beside) {
                    small = new Thread(() -> {
                        Connection c = d.newConnection();
                        Random rr = new Random(7);
                        while (!stop[0]) {
                            long s = rr.nextLong() & ~1L;
                            String k = "/s/" + rr.nextInt(100) + ".bin";
                            c.put(k, Buffers.gen(s));
                            model.put(k, s);
                        }
                    });
                    small.start();
                }
                Connection c = db.newConnection();
                WBuilder w = c.w();
                Map<String, Long> m = new HashMap<>();
                int n = 1 + r.nextInt(4);
                for (int i = 0; i < n; i++) {
                    long s = r.nextLong() | 1L;
                    String k = "/h/" + r.nextInt(10) + ".bin";
                    byte[] v = big(s);
                    w.put(k, v);
                    m.put(k, s);
                }
                w.execute();
                model.putAll(m);
                stop[0] = true;
                if (small != null) small.join();
                check(db, model, "round " + round + " at once");
                if (r.nextBoolean()) db.sync();
                if (round % 4 == 3) {
                    db.close();
                    db = Factory.database().cacheSizeInMb(20).open(dir.getPath()).start();
                    check(db, model, "round " + round + " after a restart");
                }
            }
            db.close();
            db = Factory.database().open(dir.getPath()).start();
            check(db, model, "final");
        } finally {
            db.close();
        }
        Common.log("OK Huge: " + rounds + " rounds of transactions of 7 to 31 MB");
    }

    static byte[] big(long s) {
        Random r = new Random(s);
        byte[] v = new byte[7_000_000 + r.nextInt(1_300_000)];
        r.nextBytes(v);
        return v;
    }

    static void check(Database db, Map<String, Long> model, String what) {
        Connection c = db.newConnection();
        synchronized (model) {
            for (Map.Entry<String, Long> e : model.entrySet()) {
                byte[] exp = (e.getValue() & 1) == 1 && e.getKey().startsWith("/h/") ? big(e.getValue()) : Buffers.gen(e.getValue());
                byte[] got = c.get(e.getKey(), byte[].class);
                if (!Arrays.equals(exp, got)) {
                    System.out.println("FAIL Huge " + what + ": " + e.getKey() + " = " + Common.hex(got) + " (" + (got == null ? 0 : got.length)
                            + " bytes), expected " + exp.length + " bytes");
                    System.exit(1);
                }
            }
        }
    }
}
