import java.io.File;
import java.lang.management.ManagementFactory;
import java.util.ArrayList;
import java.util.List;

import bergdb.pub.*;

/**
 * bergdb 026-07: the heap of started small databases. Starts N file databases (and N
 * memory databases), each with one small put and a sync, and prints the heap after GC per
 * database; then one burst of 1 kB puts in one database, the heap at once and after 2 s
 * of no writes. Usage: java -cp build/classes:. HeapProbe DIR N
 */
public class HeapProbe {
    static long used() throws InterruptedException {
        long best = Long.MAX_VALUE;
        for (int i = 0; i < 5; i++) {
            System.gc();
            Thread.sleep(100);
            long u = ManagementFactory.getMemoryMXBean().getHeapMemoryUsage().getUsed();
            best = Math.min(best, u);
        }
        return best;
    }

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        int n = Integer.parseInt(args[1]);
        long base = used();
        List<Database> dbs = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            Database db = Factory.database().create(new File(dir, "f" + i).getPath()).start();
            db.connection().w().put("/k", "v" + i).execute();
            db.connection().sync();
            dbs.add(db);
        }
        Thread.sleep(500);
        long files = used();
        System.out.printf("file databases %d: %.2f MB of heap each (base %.1f MB)%n", n,
                (files - base) / 1e6 / n, base / 1e6);
        for (int i = 0; i < n; i++) {
            Database db = Factory.database().memory().start();
            db.connection().w().put("/k", "v" + i).execute();
            db.connection().sync();
            dbs.add(db);
        }
        Thread.sleep(500);
        long mems = used();
        System.out.printf("memory databases %d: %.2f MB of heap each%n", n, (mems - files) / 1e6 / n);

        // A burst in the first database: 20,000 transactions of one 1 kB value, no sync.
        Database db = dbs.get(0);
        Connection c = db.connection();
        String v = "x".repeat(1000);
        long t0 = System.nanoTime();
        for (int i = 0; i < 20000; i++) {
            c.w().put("/b/" + i, v).execute();
        }
        long t1 = System.nanoTime();
        long burst = used();
        System.out.printf("after a burst of 20,000 1 kB puts (%.0f ms): +%.2f MB%n",
                (t1 - t0) / 1e6, (burst - mems) / 1e6);
        Thread.sleep(2000);
        long idle = used();
        System.out.printf("2 s later, no writes: +%.2f MB%n", (idle - mems) / 1e6);
        for (Database d : dbs) {
            d.close();
        }
    }
}
