import bergdb.pub.*;
import java.io.File;
import java.util.*;

/**
 * 031-08, UA-11: the stream files of a file database written to MB of stream, emptied, and
 * given maintain() calls until they write nothing (a test clock moved past the retain
 * duration between calls): the files on disk against getStreamSize(), at once, after idle
 * seconds, and after a restart.
 *
 * Usage: java -cp bergdb-release.jar:. EmptiedDisk DIR [MB]
 */
public class EmptiedDisk {
    static long disk(File d) { long s = 0; for (File f : d.listFiles()) if (f.getName().endsWith(".bergdb")) s += f.length(); return s; }
    static String files(File d) {
        File[] fs = d.listFiles(); Arrays.sort(fs); StringBuilder sb = new StringBuilder(); int n = 0;
        for (File f : fs) if (f.getName().endsWith(".bergdb")) { n++; sb.append(' ').append(f.getName().replaceFirst("^0+", "")).append('=').append(f.length()); }
        return n + " files:" + sb;
    }

    public static void main(String[] a) throws Exception {
        File dir = new File(a[0]);
        int mb = a.length > 1 ? Integer.parseInt(a[1]) : 80;
        TestClock clock = new TestClock();
        clock.setTime(Time.utc("2026-01-01"));
        Random r = new Random(1);
        Database db = Factory.database().create(dir.getPath()).clock(clock).start();
        db.setStartupDistanceInMb(5);
        db.setRetainDuration(Duration.seconds(3600));     // the stream grows while it is written
        Connection c = db.connection();
        long most = 0;
        for (int i = 0; most < mb * 1_000_000L; i++) {
            clock.setTime(Time.units(clock.getTime() + 500_000));   // 50 ms a transaction
            WBuilder w = c.w();
            for (int j = 0; j < 100; j++) { byte[] v = new byte[r.nextInt(3000)]; r.nextBytes(v); w.put("/k/k" + r.nextInt(3000) + ".bin", v); }
            w.execute();
            most = Math.max(most, db.getStreamSize());
        }
        System.out.println("written: the most stream " + most + "; now " + db.getStreamSize() + ", files " + disk(dir));
        db.setRetainDuration(Duration.seconds(1));
        for (int i = 0; i < 3000; i += 300) { WBuilder w = c.w(); for (int j = i; j < i + 300; j++) w.delete("/k/k" + j + ".bin"); w.execute(); }
        long last = -1;
        int same = 0, calls = 0;
        while (same < 16) {
            clock.setTime(Time.units(clock.getTime() + 2_500_001));     // R/4
            db.maintain(100_000);
            calls++;
            long ss = db.getStreamSize();
            if (ss == last) same++; else same = 0;
            last = ss;
        }
        System.out.println("deleted, " + calls + " maintain() calls, quiet: getStreamSize() " + db.getStreamSize() + ", files " + disk(dir));
        Thread.sleep(5000);
        System.out.println("5 s later: files " + disk(dir) + ", " + files(dir));
        db.close();
        System.out.println("after close(): files " + disk(dir));
        db = Factory.database().open(dir.getPath()).clock(clock).start();
        System.out.println("after a start: getStreamSize() " + db.getStreamSize() + ", files " + disk(dir) + ", " + files(dir));
        db.maintain(100);
        System.out.println("after one maintain(100): files " + disk(dir));
        db.close();
    }
}
