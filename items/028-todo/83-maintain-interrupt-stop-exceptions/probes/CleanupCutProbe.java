package bergdb.pubimp;

import java.io.File;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import bergdb.pub.*;

/**
 * 028-83, e3 seed 101 of 031-08 (its FAIL "the restart changed the first available time"),
 * in a set order: a deleted index's cleanup, a background commit of the database's own,
 * moves the first available time between an application's read of it and close(), with no
 * commit of the application's; the start then gives the time that close() left. The test
 * hook of IndexManager holds the cleanup's first step until the read is made and the clock
 * has passed the retain duration; DatabaseImp.testHookAfterStart reads the time right
 * after the Core's start, before the index manager resumes the cleanup.
 *
 * Usage (from java/, after java/build.sh):
 *   javac -cp build/bergdb.jar -d OUT CleanupCutProbe.java
 *   java -cp OUT:build/bergdb.jar bergdb.pubimp.CleanupCutProbe DIR
 * Prints the times and "PROBE OK" when the order is as described.
 */
public class CleanupCutProbe {
    public static class Item {
        public long n;
        public Item() {}
    }

    static final long SEC = 10_000_000L;

    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        rmrf(dir);
        TestClock clock = new TestClock();
        long t = Time.utc("2026-03-01").units();
        clock.setTime(Time.units(t));
        Database db = Factory.database().create(dir.getPath()).clock(clock).start();
        ((DatabaseImp) db).getDb().setStartupDistance(100_000);
        db.setRetainDuration(Duration.units(SEC));
        Connection c = db.connection();
        WBuilder w = c.w();
        for (int i = 0; i < 400; i++) { Item it = new Item(); it.n = i; w.put("/d/k" + i, it); }
        w.execute();
        db.indexBuilder("ix").dir("/d/").type("long").field("n").start().join();
        // Churn with the clock moving: iterations run, and cuts are decided at commits.
        byte[] v = new byte[2000];
        for (int i = 0; i < 4000; i++) {
            clock.setTime(Time.units(t += SEC / 100));
            c.put("/x/k" + (i % 300) + ".bin", v);
        }
        // The clock stands: maintain() calls until they write nothing, so that an iteration
        // that is done waits for the retain duration only.
        for (int i = 0, quiet = 0; i < 10_000 && quiet < 5; i++) {
            long s0 = db.getStreamSize();
            db.maintain(100_000);
            quiet = db.getStreamSize() == s0 ? quiet + 1 : 0;
        }
        CountDownLatch inStep = new CountDownLatch(1), go = new CountDownLatch(1);
        IndexManager m = ((DatabaseImp) db).getIndexManager();
        m.testHook = point -> {
            if (point.equals(IndexManager.CLEANUP_STEP) && inStep.getCount() > 0) {
                inStep.countDown();
                try { go.await(60, TimeUnit.SECONDS); } catch (InterruptedException e) { }
            }
        };
        db.deleteIndex("ix");
        check(inStep.await(60, TimeUnit.SECONDS), "the cleanup reached its first step");
        clock.setTime(Time.units(t += 3 * SEC));        // past the retain duration
        long before = db.getFirstAvailableLookupTime().units();     // the app's read before close()
        long size0 = db.getStreamSize();
        go.countDown();                                  // the cleanup commits its steps
        long end = System.nanoTime() + 60_000_000_000L;
        while (cleanupRuns() && System.nanoTime() < end) Thread.sleep(1);
        check(!cleanupRuns(), "the cleanup ended");
        long moved = db.getFirstAvailableLookupTime().units();
        db.close();
        long closed = db.getFirstAvailableLookupTime().units();
        long[] atStart = new long[1];
        DatabaseImp.testHookAfterStart = d -> atStart[0] = d.getFirstAvailableLookupTime();
        Database db2;
        try {
            db2 = Factory.database().open(dir.getPath()).clock(clock).start();
        } finally {
            DatabaseImp.testHookAfterStart = null;
        }
        long after = db2.getFirstAvailableLookupTime().units();
        db2.close();
        System.out.println("read before close() " + before + ", after the cleanup's commits " + moved + " (stream "
                + size0 + " -> " + db.getStreamSize() + "), after close() " + closed + ", right after the Core's start "
                + atStart[0] + ", after the start " + after);
        check(moved > before, "the cleanup's commits moved the time, with no commit of the application's");
        check(closed == moved, "close() moved nothing");
        check(atStart[0] == closed, "the start gives the time that close() left");
        check(after == closed, "nothing resumed (the cleanup had ended)");
        System.out.println("PROBE OK: the restart changed nothing; the time moved at the cleanup's commit, before close()");
        rmrf(dir);
    }

    static boolean cleanupRuns() {
        for (Thread th : Thread.getAllStackTraces().keySet()) {
            if (th.getName().startsWith("IndexCleanup-") && th.isAlive()) return true;
        }
        return false;
    }

    static void check(boolean ok, String what) {
        if (!ok) {
            System.out.println("PROBE FAIL: " + what);
            System.exit(1);
        }
    }

    static void rmrf(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File x : fs) rmrf(x);
        f.delete();
    }
}
