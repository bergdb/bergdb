package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;

import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;

/**
 * Probe for bergdb 005-46: the pause probe of item 009 (java/stress/PauseProbe.java) on a disk
 * whose force is now and then slow, as s1's. Every EVERY-th force of the stream's appends
 * takes DELAY ms more (FileStreamIo); everything else is the pause probe's. Prints the pause
 * probe's lines, and each slow force with its JVM uptime, so that the waits of gets and
 * commits can be set beside them.
 *
 * Usage: java -Dforcedelay=MS -Devery=N [the pause probe's properties] -cp bergdb.jar:stress:.
 *            bergdb.core.SlowForceProbe
 */
public class SlowForceProbe extends PauseProbe {
    final long delay = Long.getLong("forcedelay", 1000);
    final int every = Integer.getInteger("every", 100);

    Db start() throws IOException {
        dir.mkdirs();
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) f.delete();
        FileStreamIo io = new FileStreamIo() {
            int forces = 0;

            protected void forceFile(File file, RandomAccessFile h) throws IOException {
                if (delay > 0 && ++forces % every == 0) {
                    long from = uptimeMs();
                    try {
                        Thread.sleep(delay);
                    } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                    System.out.println(String.format("  slow force, uptime %.3f to %.3f s",
                            from / 1e3, uptimeMs() / 1e3));
                }
                super.forceFile(file, h);
            }
        };
        System.out.println("SlowForceProbe: every " + every + "th force takes " + delay + " ms more");
        Db d = Db.builder().stream("main", new FileStream(dir, io)).testId()
                .cacheSizeIndicator(budget).evictionSchedule(Eviction.Schedule.BUDGET, 1).build();
        d.start();
        return d;
    }

    public static void main(String[] args) {
        try {
            new SlowForceProbe().run();
        } catch (Throwable e) {
            e.printStackTrace();
            System.out.println("SLOW FORCE PROBE FAILED: " + e);
            System.exit(1);
        }
        System.exit(0);
    }
}
