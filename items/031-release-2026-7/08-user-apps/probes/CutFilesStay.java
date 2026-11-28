import bergdb.pub.*;
import java.io.File;
import java.util.Random;

/**
 * 031-08, UA-1: after the commit that decides a cut, getStreamSize() counts from the new first
 * position at once, while the stream files before it stay on disk until the next commit or
 * maintain() call, also after a sync() and seconds of idle time.
 *
 * Usage: java -cp bergdb-release.jar:. CutFilesStay DIR [put|maintain]
 */
public class CutFilesStay {
    static long disk(File d) {
        long s = 0;
        for (File f : d.listFiles()) if (f.getName().endsWith(".bergdb")) s += f.length();
        return s;
    }

    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        String next = a.length > 1 ? a[1] : "put";
        TestClock clock = new TestClock();
        clock.setTime(Time.utc("2026-01-01"));
        Random r = new Random(1);
        try (Database db = Factory.database().create(dir.getPath()).clock(clock).start()) {
            db.setStartupDistanceInMb(5);
            db.setRetainDuration(Duration.seconds(1));
            Connection c = db.connection();
            long prev = db.getStreamSize();
            for (int i = 0; ; i++) {
                clock.setTime(Time.units(clock.getTime() + 2_000_000));      // 0.2 s a commit
                WBuilder w = c.w();
                for (int j = 0; j < 50; j++) {
                    byte[] v = new byte[r.nextInt(3000)];
                    r.nextBytes(v);
                    w.put("/p/k" + r.nextInt(3000) + ".bin", v);
                }
                w.execute();
                long ss = db.getStreamSize();
                if (ss < prev - 1_000_000 && ss > 10_000_000) {
                    System.out.println("commit " + i + " decided a cut: getStreamSize() " + prev + " -> " + ss);
                    break;
                }
                prev = ss;
            }
            db.sync();
            Thread.sleep(2000);
            System.out.println("after sync() and 2 s idle: getStreamSize() " + db.getStreamSize() + ", files " + disk(dir));
            if (next.equals("put")) c.put("/p/x.bin", new byte[1]);
            else db.maintain(100);
            db.sync();
            Thread.sleep(200);
            System.out.println("after one " + (next.equals("put") ? "put of 1 byte" : "maintain(100)") + ": getStreamSize() "
                    + db.getStreamSize() + ", files " + disk(dir));
        }
    }
}
