package bergdb.core;

import java.io.File;
import java.nio.file.Files;
import java.util.Random;

import bergdb.pub.util.Clock;
import bergdb.stream.FileStream;

/**
 * Probe for bergdb 005-46: what a commit by a thread whose interrupt flag is set does to the
 * database. A database on a FileStream with reclaim on (the configuration of
 * FileStreamPowerLossTester: a startup distance of 20 KB, a retention of 2 s on a test clock),
 * puts of 1 to 2 KB values on 12 keys, 0.1 s apart on the clock. Before each commit the thread
 * sets its own interrupt flag, as a cancelled task's thread may have it, and clears it after;
 * every fifth commit is followed by a sync, with the flag cleared, as FileStreamPowerLossTester
 * does (a physical cut waits until the reclaim table that decides it is durable; on the test
 * clock, without syncs, the decisions come faster than the flushes, and no cut is made). Prints
 * what the first commit that fails threw, or the first physical cut (a move of the stream's
 * first position), and whether the database works after it.
 *
 * Usage: java -ea [-Dnointerrupt=true] [-Dnosync=true] -cp bergdb.jar:.
 *            bergdb.core.InterruptCutProbe BUFFER_BYTES
 *   BUFFER_BYTES: the write buffer, 100000 as DbBuilder.testSetup has it, or 10000000, the
 *   default. -Dnointerrupt=true: no interrupts. -Dnosync=true: no syncs, so that the writer
 *   fills a small buffer and waits for room.
 */
public class InterruptCutProbe {
    public static void main(String[] args) throws Exception {
        long sec = Clock.UNITS_PER_SEC;
        File dir = Files.createTempDirectory("bergdb-46-interrupt-").toFile();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(sec);
        FileStream fs = new FileStream(dir);
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        Db db = b.stream("main", fs, Integer.parseInt(args[0]), 10).clock(clock)
                .startupDistance(20000).retainDuration(2 * sec).start();
        Random r = new Random(1);
        long time = sec;
        long firstPos = fs.getFirstPos();
        int commits = 0;
        try {
            for (int i = 0; i < 20000; i++) {
                time += sec / 10;
                clock.setTime(time);
                byte[] value = new byte[1000 + r.nextInt(1000)];
                r.nextBytes(value);
                Trans t = db.trans().put("/k" + r.nextInt(12), value).build();
                if (!Boolean.getBoolean("nointerrupt")) Thread.currentThread().interrupt();
                try {
                    db.execute(t);
                    commits++;
                } catch (Throwable e) {
                    System.out.println("commit " + i + " threw " + e);
                    for (Throwable c = e.getCause(); c != null; c = c.getCause()) {
                        System.out.println("  caused by " + c);
                    }
                    Throwable root = e;
                    while (root.getCause() != null) root = root.getCause();
                    for (StackTraceElement el : root.getStackTrace()) {
                        if (el.getClassName().startsWith("bergdb.")) {
                            System.out.println("    at " + el);
                        }
                    }
                    System.out.println("  the stream's first position " + fs.getFirstPos()
                            + " (before: " + firstPos + ")");
                    break;
                } finally {
                    Thread.interrupted();
                }
                if (i % 5 == 0 && !Boolean.getBoolean("nosync")) db.sync(SyncLevel.ORDINARY);
                if (fs.getFirstPos() != firstPos) {
                    System.out.println("commit " + i + " made a physical cut: the first position"
                            + " from " + firstPos + " to " + fs.getFirstPos());
                    break;
                }
            }
            System.out.println(commits + " commits returned; reclaim's"
                    + " iterations " + db.getReclaimIterationCount() + ", the first available"
                    + " lookup time " + db.getFirstAvailableLookupTime() + ", the stream "
                    + db.getStreamLength() + " bytes, durable " + db.getDurableLength());
            try {
                db.execute(db.trans().put("/after", new byte[10]).build());
                System.out.println("then a commit by a thread not interrupted: OK");
            } catch (Throwable e) {
                System.out.println("then a commit by a thread not interrupted threw " + e);
            }
            try {
                DbUtil.get(db, "/k1".getBytes("UTF-8"));
                System.out.println("then a get: OK");
            } catch (Throwable e) {
                System.out.println("then a get threw " + e);
            }
        } finally {
            try {
                db.stop();
            } catch (Throwable e) {
                System.out.println("stop threw " + e);
            }
            File[] fs2 = dir.listFiles();
            if (fs2 != null) for (File f : fs2) f.delete();
            dir.delete();
        }
    }
}
