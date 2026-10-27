package bergdb.core;

import bergdb.pub.util.Clock;
import bergdb.stream.MemoryStream;

/**
 * Probe for 005-53, question 3 (by Claude (Opus 5.5, Claude Code), 2026-10-27): which
 * startup distance does Reclaim use after a restart? A database is made with a startup
 * distance of 2000 bytes and written to; its stream is then started twice more, once with
 * the same distance in the builder and once with the builder's default (50 MB), and
 * the same writes follow. It prints the distance Db uses, the one Reclaim holds, and the
 * iterations each run completed and the bytes of the stream kept after the last cut.
 *
 * Run from java/ after build.sh (the probe goes first on the class path):
 *   javac -cp build/bergdb.jar -d <dir> ReclaimDistanceProbe.java
 *   java -ea -cp <dir>:build/bergdb.jar bergdb.core.ReclaimDistanceProbe
 */
public class ReclaimDistanceProbe {
    static long time = Clock.UNITS_PER_SEC;

    public static void main(String[] args) throws Exception {
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(time);
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(2000).start();
        run("create, builder 2000", db, clock);
        db.sync(SyncLevel.STRONG);
        db.stop();

        long t0 = time;
        for (int builderSd : new int[] {2000, -1}) {
            time = t0;
            MemoryStream s = stream.copy();
            CoreTestClock c = new CoreTestClock();
            c.setTime(time);
            DbBuilder b = Db.builder().testSetup(s).clock(c);
            if (builderSd > 0) {
                b.startupDistance(builderSd);
            }
            Db d = b.start();
            run("restart, builder " + (builderSd > 0 ? "2000" : "default"), d, c);
            d.stop();
        }
    }

    static void run(String name, Db db, CoreTestClock clock) throws Exception {
        db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
        java.util.Random r = new java.util.Random(1);
        long len0 = db.getStreamLength();
        Reclaim reclaim = db.internal().reclaim();
        long before = reclaim.getIterationCount();
        for (int i = 0; i < 6000; i++) {
            time += Clock.UNITS_PER_SEC / 20;
            clock.setTime(time);
            byte[] v = new byte[1 + r.nextInt(60)];
            db.execute(db.trans().put("/k/" + r.nextInt(50), v).build());
        }
        java.lang.reflect.Field f = Reclaim.class.getDeclaredField("initialStartupDistance");
        f.setAccessible(true);
        System.out.println(name + ": Db's distance " + db.getStartupDistance()
                + ", Reclaim's " + f.get(reclaim)
                + ", stream grew " + (db.getStreamLength() - len0) + " bytes"
                + ", iterations done " + (reclaim.getIterationCount() - before)
                + ", stream kept at the end " + (db.getStreamLength() - db.getFirstAvailablePos())
                + " bytes");
    }
}
