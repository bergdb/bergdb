package bergdb.core;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * Review probe (031-06, review-main): a record's time is the clock's, raised above the last
 * record's time and above the last time a reader was given (DbClock.lastReadTime), which is
 * memory that a start does not rebuild. The same calls at the same clock values, with and
 * without a restart between a reader's currentTime() and the next commit, when the clock
 * does not pass the time the reader was given (it stands still, or goes back).
 *
 * args: still|back
 */
public class RmClockProbe {
    static final long SEC = Clock.UNITS_PER_SEC;

    public static void main(String[] a) throws Exception {
        final boolean back = a[0].equals("back");
        final byte[][] image = new byte[2][];
        final long[] tt = new long[2];
        for (int run = 0; run < 2; run++) {
            final AtomicLong time = new AtomicLong(10 * SEC);
            CutStream s = new CutStream();
            Db db = Db.builder().testSetup(s).clock(time::get).start();
            db.execute(db.trans().put("/a", new byte[] {1}).build());
            time.set(20 * SEC);
            final long read = db.currentTime();         // a reader is given the clock's time
            if (run == 1) {                             // a restart between two records
                db.close();
                s = s.copy();
                db = Db.builder().testSetup(s).clock(time::get).start();
            }
            if (back) time.set(15 * SEC);               // the clock goes back; else it stands
            final Trans t = db.trans().put("/b", new byte[] {2}).build();
            db.execute(t);
            tt[run] = t.tt;
            // A read at the time that the reader was given, after the commit.
            final byte[] seen = db.getOne(read, bergdb.dag.Keys.toSegments("/b"), db.newGetData());
            System.out.println("  a read of /b at the time given, " + read + ", after the commit: "
                    + (seen == null ? "no value (the state the reader was given)" : "the commit's value"));
            db.close();
            image[run] = new byte[(int) s.getLength()];
            s.read(0, image[run], 0, image[run].length);
            System.out.println((run == 0 ? "without a restart" : "with a restart   ") + ": the reader "
                    + "was given " + read + ", the clock at the commit " + time.get()
                    + ", the commit's time " + tt[run] + ", stream length " + s.getLength());
        }
        System.out.println(Arrays.equals(image[0], image[1]) ? "SAME STREAM" : "DIFFERENT STREAMS");
    }
}
