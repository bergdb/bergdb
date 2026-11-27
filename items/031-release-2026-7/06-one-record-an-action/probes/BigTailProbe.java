package bergdb.core;

import java.io.File;
import java.util.*;

import bergdb.pub.util.Clock;
import bergdb.stream.FileStream;

/**
 * bergdb 031-06, review 3, section 5, point 5: the time of a start of a file database whose
 * last record is large (100 MB and more). Since step 4 (028-67's C1 and C3) the recovery's
 * walk of the tail (RecoverableStream.walkTail) parses the stream's last record whole, and
 * the start parses it again. Kind: timing (the times are the result; run on a quiet
 * machine). It runs on main's jar and on this branch's.
 *
 * The record: KEYS keys of 20 bytes, 500 puts a transaction, on disk (FileStream, every
 * append forced, as by default), at the default startup distance, so that the tree's index
 * nodes are written; then, at the largest startup distance (Db.MAX_STARTUP_DISTANCE, 1 GB),
 * KEYS / 4 overwrites of random keys with 1 byte, 500 a transaction: they make most of the
 * tree's index nodes dirty with few own bytes, and no record takes them. Then the startup
 * distance is set to SD (1 MB) and one commit of three values of 8 MiB follows: its record
 * takes its share of the dirty set (TransSeq.take: in proportion to its own bytes over the
 * section's, times twice at most after a decrease), which with own bytes larger than the
 * section's is all of it. That record is the stream's last; the database is closed (a stop
 * writes nothing). Then STARTS starts and stops of the same files, each start timed
 * (Db.start(), from the call to its return), and the first get after it.
 *
 * Printed: the keys, the stream's length, the last record's size (the stream's length
 * after its commit less before), and each start's time. A last record under 100 MB is said
 * so (more KEYS: about 30 bytes of the tree's index nodes a key at node size 30).
 *
 * Usage: java -Xmx8g -cp OUT:JAR bergdb.core.BigTailProbe
 * Properties: keys=N (default 4,000,000), dir=D (build/bigtail, emptied first), starts=N
 * (3), sd=N (1,000,000). Prints BIG TAIL PROBE DONE.
 */
public class BigTailProbe {
    static final long SEC = Clock.UNITS_PER_SEC;

    public static void main(String[] args) throws Exception {
        final int keys = Integer.getInteger("keys", 4000 * 1000);
        final File dir = new File(System.getProperty("dir", "build/bigtail"));
        final int starts = Integer.getInteger("starts", 3);
        final int sd = Integer.getInteger("sd", 1000 * 1000);
        dir.mkdirs();
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) f.delete();
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        Db db = Db.builder().stream("main", new FileStream(dir)).testId().clock(clock).build();
        db.start();
        final long length0, length1;
        final long t0 = System.nanoTime();
        try {
            Random r = new Random(1);
            for (int i = 0; i < keys; i += 500) {
                time += SEC / 1000;
                clock.setTime(time);
                Trans.Builder tb = db.trans();
                for (int j = i; j < Math.min(keys, i + 500); j++) {
                    tb.put(key(j), value(r, 20));
                }
                db.execute(tb.build());
            }
            db.setStartupDistance(Db.MAX_STARTUP_DISTANCE);
            for (int i = 0; i < keys / 4; i += 500) {
                time += SEC / 1000;
                clock.setTime(time);
                Trans.Builder tb = db.trans();
                for (int j = 0; j < 500; j++) {
                    tb.put(key(r.nextInt(keys)), value(r, 1));
                }
                db.execute(tb.build());
            }
            db.setStartupDistance(sd);
            db.sync(bergdb.pub.util.SyncLevel.ORDINARY);
            length0 = db.getStreamLength();
            time += SEC / 1000;
            clock.setTime(time);
            Trans.Builder tb = db.trans();
            for (int j = 0; j < 3; j++) {
                tb.put("/last/" + j, value(r, Db.MAX_VALUE_BYTES - 1000));
            }
            db.execute(tb.build());
            db.sync(bergdb.pub.util.SyncLevel.ORDINARY);
            length1 = db.getStreamLength();
        } finally {
            db.close();
        }
        final long record = length1 - length0;
        System.out.println("BigTailProbe: " + keys + " keys of 20 bytes, made in "
                + (System.nanoTime() - t0) / 1000000 + " ms; a stream of " + length1 / 1000000
                + " MB, the last record " + String.format("%.1f", record / 1e6) + " MB"
                + (record < 100 * 1000 * 1000 ? " (under 100 MB: more keys)" : ""));
        for (int k = 1; k <= starts; k++) {
            time += SEC;
            clock.setTime(time);
            Db d = Db.builder().stream("main", new FileStream(dir)).testId().clock(clock)
                    .build();
            long a = System.nanoTime();
            d.start();
            long started = System.nanoTime() - a;
            try {
                a = System.nanoTime();
                byte[] v = d.getOne(Long.MAX_VALUE, bergdb.dag.Keys.toSegments("/last/0"),
                        d.newGetData()) == null ? null : new byte[0];
                long got = System.nanoTime() - a;
                System.out.println(String.format("  start %d: %.1f ms, the first get %.3f ms%s",
                        k, started / 1e6, got / 1e6, v == null ? " (no /last/0: wrong)" : ""));
            } finally {
                d.close();
            }
        }
        System.out.println("BIG TAIL PROBE DONE");
    }

    static String key(int j) {
        return String.format("/k/%08d", j);
    }

    static byte[] value(Random r, int n) {
        byte[] v = new byte[n];
        r.nextBytes(v);
        return v;
    }
}
