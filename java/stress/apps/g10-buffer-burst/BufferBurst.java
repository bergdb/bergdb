import bergdb.pub.*;
import bergdb.pub.util.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

/**
 * BufferBurst (031-02, e10). The write buffer that grows with the write rate and shrinks
 * after 2 seconds with nothing to write (Database.stop(), "The write buffer"): bursts of 2 to
 * 40 MB from one to three writer threads, values of 0 to 200 kB, some syncs, then pauses of
 * 2.2 to 3.5 s with nothing written, again and again; a stop or a close now and then right
 * after a burst or in a pause. Each value is made from its key and its version, so the
 * oracle keeps only the version of each key. After each burst a sample is read, and after
 * each restart every key, by a listing and by gets.
 *
 * Usage: java BufferBurst DIR SEED ROUNDS
 */
public class BufferBurst {
    static void fail(String m) {
        System.out.println("BUFFERBURST FAILED: " + m);
        System.out.flush();
        System.exit(1);
    }

    static final int KEYS = 2000;
    static final ConcurrentHashMap<Integer, Long> version = new ConcurrentHashMap<>();

    static String key(int i) { return String.format("/b/k%05d.bin", i); }

    static byte[] value(int i, long v) {
        Random r = new Random(i * 1_000_003L + v * 7919L);
        int n = r.nextInt(10) == 0 ? 20_000 + r.nextInt(180_000) : r.nextInt(2000);
        byte[] b = new byte[n];
        r.nextBytes(b);
        return b;
    }

    public static void main(String[] args) throws Exception {
        String dir = args[0];
        long seed = Long.parseLong(args[1]);
        int rounds = Integer.parseInt(args[2]);
        Random r = new Random(seed);
        System.out.println("BufferBurst seed " + seed + " rounds " + rounds);
        Database db = Factory.database().create(dir).start();
        long bytes = 0, restarts = 0, stops = 0;
        for (int round = 0; round < rounds; round++) {
            long target = 2_000_000L + r.nextInt(38_000_000);
            int threads = 1 + r.nextInt(3);
            AtomicLong written = new AtomicLong();
            final Database d = db;
            final long rs = r.nextLong();
            List<Thread> ts = new ArrayList<>();
            for (int t = 0; t < threads; t++) {
                final int tid = t;
                Thread th = new Thread(() -> {
                    Random wr = new Random(rs + tid);
                    Connection c = d.connection();
                    while (written.get() < target) {
                        // Each thread owns the keys i with i % threads == tid.
                        int n = 1 + wr.nextInt(wr.nextBoolean() ? 5 : 200);
                        WBuilder w = c.w();
                        Map<Integer, Long> put = new HashMap<>();
                        for (int j = 0; j < n; j++) {
                            int i = wr.nextInt(KEYS / threads) * threads + tid;
                            if (i >= KEYS) continue;
                            long v = put.containsKey(i) ? put.get(i) + 1 : version.getOrDefault(i, 0L) + 1;
                            put.put(i, v);
                        }
                        long sz = 0;
                        for (Map.Entry<Integer, Long> e : put.entrySet()) {
                            byte[] val = value(e.getKey(), e.getValue());
                            sz += val.length;
                            w.put(key(e.getKey()), val);
                        }
                        w.execute();
                        version.putAll(put);
                        written.addAndGet(sz);
                        if (wr.nextInt(50) == 0) c.sync();
                    }
                });
                th.start();
                ts.add(th);
            }
            for (Thread th : ts) th.join();
            bytes += written.get();
            // A sample.
            Connection c = db.connection();
            for (int q = 0; q < 200; q++) check(c, r.nextInt(KEYS), "round " + round + " sample");
            int what = r.nextInt(10);
            if (what < 2) {
                // Close at once after the burst.
                db.close();
                db = Factory.database().open(dir).start();
                checkAll(db, "round " + round + " closed after a burst");
                restarts++;
            } else if (what < 3) {
                // stop() and a start that waits for the close.
                db.stop();
                stops++;
                long until = System.currentTimeMillis() + 60_000;
                while (true) {
                    try {
                        db = Factory.database().open(dir).start();
                        break;
                    } catch (DbException e) {
                        if (System.currentTimeMillis() > until) fail("no start a minute after stop(): " + e);
                        Thread.sleep(50);
                    }
                }
                checkAll(db, "round " + round + " stopped after a burst");
                restarts++;
            } else {
                // A pause: the buffer shrinks.
                Thread.sleep(2200 + r.nextInt(1300));
                for (int q = 0; q < 50; q++) check(db.connection(), r.nextInt(KEYS), "round " + round + " after a pause");
                if (what == 9) {
                    db.close();
                    db = Factory.database().open(dir).start();
                    checkAll(db, "round " + round + " closed after a pause");
                    restarts++;
                }
            }
            System.out.println("  round " + round + ": " + bytes / 1_000_000 + " MB written, restarts " + restarts
                    + " (" + stops + " by stop())");
        }
        db.close();
        db = Factory.database().open(dir).start();
        checkAll(db, "end");
        db.close();
        System.out.println("BUFFERBURST OK");
    }

    static void check(Connection c, int i, String what) {
        byte[] got = c.get(key(i), byte[].class);
        Long v = version.get(i);
        byte[] exp = v == null ? null : value(i, v);
        if (!Arrays.equals(got, exp)) fail(what + ": " + key(i) + " has " + (got == null ? "no value" : got.length + " bytes")
                + ", expected version " + v + (exp == null ? "" : " of " + exp.length + " bytes"));
    }

    static void checkAll(Database db, String what) {
        Connection c = db.connection();
        int n = 0;
        for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/b/").kvs()) {
            int i = Integer.parseInt(kv.key().substring(4, 9));
            Long v = version.get(i);
            if (v == null || !Arrays.equals(kv.value(), value(i, v))) fail(what + ": " + kv.key() + " differs (version " + v + ")");
            n++;
        }
        if (n != version.size()) fail(what + ": " + n + " keys listed, expected " + version.size());
    }
}
