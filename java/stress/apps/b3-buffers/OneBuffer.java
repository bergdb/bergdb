import bergdb.pub.*;

import java.io.File;
import java.lang.management.ManagementFactory;
import java.util.Random;

/**
 * B3c of 026-13: when does one database's write buffer shrink after a fast write? (bergdb
 * 026-07; DatabaseBuilder.startupDistanceInMb: "shrinks back to 64 KiB after 2 seconds with
 * nothing to write"). One file database (budget 4 MB); a fast write of 20 transactions of 500
 * small puts (as B3's heap phase), then the heap after a GC every 100 ms for 6 s. Printed:
 * the heap just after the writes, after sync() returned, and the first time it is back within
 * 1 MB of the heap before the writes, counted from the last write's return and from sync().
 *
 * Usage: java -cp bergdb-release.jar:out OneBuffer DIR ROUNDS
 */
public class OneBuffer {
    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        int rounds = Integer.parseInt(a[1]);
        Common.rmrf(dir);
        Database db = Factory.database().cacheSizeInMb(4).create(dir.getPath()).start();
        Connection c = db.newConnection();
        Random r = new Random(1);
        for (int round = 0; round < rounds; round++) {
            Thread.sleep(3000);
            long before = gcUsed();
            for (int t = 0; t < 20; t++) {
                WBuilder w = c.w();
                for (int k = 0; k < 500; k++) {
                    byte[] v = new byte[r.nextInt(300)];
                    r.nextBytes(v);
                    w.put("/b/" + (k % 400) + ".bin", v);
                }
                w.execute();
            }
            long end = System.nanoTime();
            long after = gcUsed();
            db.sync();
            long synced = System.nanoTime();
            long back = -1;
            while (System.nanoTime() - end < 6_000_000_000L) {
                Thread.sleep(100);
                if (gcUsed() < before + 1_000_000) { back = System.nanoTime(); break; }
            }
            Common.log("round " + round + ": heap " + before / 1000 + " kB before, " + (after - before) / 1000 + " kB more after the writes; sync() took "
                    + (synced - end) / 1_000_000 + " ms; back within 1 MB " + (back < 0 ? "not in 6 s" : (back - end) / 1_000_000
                    + " ms after the last write, " + (back - synced) / 1_000_000 + " ms after sync() returned"));
        }
        db.close();
    }

    static long gcUsed() {
        System.gc();
        return ManagementFactory.getMemoryMXBean().getHeapMemoryUsage().getUsed();
    }
}
