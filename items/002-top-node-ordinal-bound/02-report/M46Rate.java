package bergdb.core;

import java.util.Random;

import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * Bergdb item 002 (M46): transactions per second and per new top node, and stream bytes per
 * transaction, for small hot workloads on an in-memory database (Db.builder().testSetup).
 * The clock advances 'tick' units (100 ns each) per transaction.
 *
 * Usage: java -cp bergdb.jar:. bergdb.core.M46Rate NODESIZE KEYS N RETAIN_S TICK [SD [PUTS]]
 *   KEYS keys, one random put of 16 bytes per transaction, or PUTS puts of distinct random
 *   keys (all KEYS keys when PUTS = KEYS); RETAIN_S 0: no reclaim; SD the startup distance.
 */
public final class M46Rate {
    public static void main(String[] args) {
        int maxNode = Integer.parseInt(args[0]);
        int keys = Integer.parseInt(args[1]);
        int n = Integer.parseInt(args[2]);
        int retain = Integer.parseInt(args[3]);
        long tick = Long.parseLong(args[4]);
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        DbBuilder b = Db.builder().testSetup(stream).clock(clock);
        if (maxNode == 8) b.maxNodeSize8(); else if (maxNode == 14) b.maxNodeSize14();
        else if (maxNode == 62) b.maxNodeSize62(); else b.maxNodeSize30();
        if (args.length > 5 && Integer.parseInt(args[5]) > 0) b.startupDistance(Integer.parseInt(args[5]));
        final int puts = args.length > 6 ? Integer.parseInt(args[6]) : 1;
        Db db = b.start();
        if (retain > 0) db.setRetainDuration(retain * Clock.UNITS_PER_SEC);
        Random rnd = new Random(1);
        byte[] v = new byte[16];
        long t = 0;
        int warm = Math.min(n / 5, 50000);
        long top0 = 0, len0 = 0, t0 = 0;
        for (int i = 0; i < warm + n; i++) {
            if (i == warm) {
                top0 = db.internal().superRoot().topNodeId;
                len0 = stream.getLength();
                t0 = System.nanoTime();
            }
            t += tick;
            clock.setTime(t);
            if (puts == 1) {
                String k = keys == 1 ? "/hot" : "/k/" + rnd.nextInt(keys);
                db.execute(db.trans().put(k, v).build());
            } else {
                // Distinct keys, in key order (Db.execute assumes sorted kvs).
                java.util.TreeSet<String> ks = new java.util.TreeSet<String>();
                if (puts == keys) for (int j = 0; j < keys; j++) ks.add(String.format("/k/%06d", j));
                else while (ks.size() < puts) ks.add(String.format("/k/%06d", rnd.nextInt(keys)));
                Trans.Builder tb = db.trans();
                for (String k : ks) tb.put(k, v);
                db.execute(tb.build());
            }
        }
        double s = (System.nanoTime() - t0) / 1e9;
        long tops = db.internal().superRoot().topNodeId - top0;
        long bytes = stream.getLength() - len0;
        System.out.printf("node=%-2d keys=%-5d retain=%-2ds tx=%-8d tx/s=%-8.0f tx/top=%-7.2f bytes/tx=%-6.1f (stream "
                + "first pos %d, length %d; all transactions %d; first available time %d of %d)%n", maxNode, keys,
                retain, n, n / s, n / (double) tops, bytes / (double) n, stream.getFirstPos(), stream.getLength(),
                db.getTransactionCount(), db.getFirstAvailableLookupTime(), t);
        db.stop();
    }
}
