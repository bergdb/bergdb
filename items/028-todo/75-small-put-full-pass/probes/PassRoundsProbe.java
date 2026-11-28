package bergdb.core;

import java.util.Random;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 028-75: 031-06's RmPassProbe (review-main-probes) with the number of rounds and the
 * startup distance as arguments: what maintain(budget) calls write after each of ROUNDS puts
 * of one byte, a second apart, into a database of KEYS live values that its calls brought to
 * rest; the retain duration 1 s, a CutStream, a test clock.
 *
 * args: keys valueBytes budget rounds startupDistance
 */
public class PassRoundsProbe {
    static final long SEC = Clock.UNITS_PER_SEC;
    static long time = SEC;

    /** Calls maintain(budget), a second of database time apart, until 5 calls in a row write nothing. */
    static long[] rest(Db db, CoreTestClock clock, int budget) {
        long calls = 0, quiet = 0;
        final long l0 = db.getStreamLength();
        while (quiet < 5) {
            time += SEC;
            clock.setTime(time);
            final long before = db.getStreamLength();
            db.maintain(budget);
            calls++;
            quiet = db.getStreamLength() == before ? quiet + 1 : 0;
        }
        return new long[] {calls - 5, db.getStreamLength() - l0};
    }

    public static void main(String[] a) {
        final int keys = Integer.parseInt(a[0]), vb = Integer.parseInt(a[1]), budget = Integer.parseInt(a[2]);
        final CutStream s = new CutStream();
        final CoreTestClock clock = new CoreTestClock();
        clock.setTime(time);
        final Db db = Db.builder().testSetup(s).clock(clock).start();
        db.setStartupDistance(Integer.parseInt(a[4]));
        db.setRetainDuration(SEC);
        final Random r = new Random(1);
        long live = 0;
        for (int i = 0; i < keys; i += 100) {
            Trans.Builder b = db.trans();
            for (int j = i; j < i + 100 && j < keys; j++) {
                byte[] v = new byte[vb];
                r.nextBytes(v);
                b.put("/c/" + (j % 97) + "/" + j, v);
                live += vb + 16;
            }
            time += SEC / 100;
            clock.setTime(time);
            db.execute(b.build());
        }
        long[] first = rest(db, clock, budget);
        System.out.println(keys + " keys of " + vb + " bytes (about " + live / 1000 + " kB live); "
                + "to rest: " + first[0] + " calls of maintain(" + budget + ") wrote " + first[1]
                + " bytes; stream kept " + (db.getStreamLength() - db.getFirstAvailablePos()));
        for (int round = 0; round < Integer.parseInt(a[3]); round++) {
            time += SEC;
            clock.setTime(time);
            final long before = db.getStreamLength();
            db.execute(db.trans().put("/one", new byte[] {(byte) round}).build());
            final long put = db.getStreamLength() - before;
            long[] m = rest(db, clock, budget);
            System.out.println("one put of 1 byte (its record " + put + " bytes), then to rest: "
                    + m[0] + " calls wrote " + m[1] + " bytes; stream kept "
                    + (db.getStreamLength() - db.getFirstAvailablePos()));
        }
        db.close();
    }
}
