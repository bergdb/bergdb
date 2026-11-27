package bergdb.core;

import java.util.*;

import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06, landing step 3 (the pace): the review's RvPace (review-probes/), with
 * DbBuilder.maintenanceNone() called directly (it is package-private since step 0, which
 * RvPace's reflection does not find) and commits of several puts. COLD keys of VALUE bytes
 * put once (the live data), then N commits, DT_MS of database time apart, retain duration
 * 1 s, no maintain() calls. A commit is one put of COMMIT bytes at one of 8 hot keys, or with
 * -Dputs=K, K puts of COMMIT / K bytes at random keys among -Dhot=H (default 8) hot keys.
 * Printed: the stream written by the commits, and by the same run with
 * DbBuilder.maintenanceNone() (the difference is what reclaim wrote: copies, rows, tables
 * and their index nodes), reclaim's share of that growth against the internal fraction, 0.25;
 * the stream kept, its largest value in each third of the run, in bytes and in units of the
 * live data; the iterations ended and the largest record.
 *
 * Usage: java -cp OUT:JAR bergdb.core.PaceProbe COLD VALUE N COMMIT DT_MS [NODE]
 *   -Dsd=20000 (the startup distance) -Dputs=1 -Dhot=8
 *   -Ddeep=true (cold keys of seven segments on paths of their own)
 * Kind: functional (figures of size; no time is measured).
 */
public class PaceProbe {
    static final long SEC = Clock.UNITS_PER_SEC;

    public static void main(String[] args) throws Exception {
        int cold = Integer.parseInt(args[0]), value = Integer.parseInt(args[1]);
        int n = Integer.parseInt(args[2]), commit = Integer.parseInt(args[3]);
        long dt = Long.parseLong(args[4]) * SEC / 1000;
        int node = args.length > 5 ? Integer.parseInt(args[5]) : 0;
        long[] with = run(cold, value, n, commit, dt, node, false);
        long[] none = run(cold, value, n, commit, dt, node, true);
        long live = (long) cold * (value + 40);
        System.out.println("PaceProbe cold " + cold + " x " + value + " (live about " + live + "), "
                + n + " commits of " + commit + " bytes in " + Integer.getInteger("puts", 1)
                + " put(s), " + args[4] + " ms apart, node " + node + ", sd "
                + Integer.getInteger("sd", 20000) + ":");
        System.out.println("  written by the commits: " + with[0] + "; without reclaim " + none[0]
                + "; reclaim's share of the growth "
                + String.format("%.3f", (with[0] - none[0]) / (double) with[0])
                + " (the internal fraction: 0.250); write amplification "
                + String.format("%.2f", with[0] / (double) none[0]));
        System.out.println("  the stream kept, largest in each third: " + with[1] + ", " + with[2]
                + ", " + with[3] + " = " + String.format("%.1f, %.1f, %.1f", with[1] / (double) live,
                with[2] / (double) live, with[3] / (double) live) + " x live; cuts " + with[4]
                + "; iterations ended " + with[6] + "; largest record " + with[5]);
    }

    static long[] run(int cold, int value, int n, int commit, long dt, int node, boolean none) {
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        CutStream s = new CutStream();
        DbBuilder b = Db.builder().testSetup(s).clock(clock);
        if (node == 8) b.maxNodeSize8();
        if (node == 30) b.maxNodeSize30();
        if (none) b.maintenanceNone();
        Db db = b.start();
        try {
            db.setStartupDistance(Integer.getInteger("sd", 20000));
            db.setRetainDuration(SEC);
            Random r = new Random(1);
            for (int i = 0; i < cold; i += 20) {
                time += SEC / 100;
                clock.setTime(time);
                Trans.Builder tb = db.trans();
                for (int j = i; j < Math.min(cold, i + 20); j++) {
                    byte[] v = new byte[value];
                    r.nextBytes(v);
                    tb.put(Boolean.getBoolean("deep") ? String.format("/c/%03d/%05d/%07d/%07d/%07d/k",
                            (j * 7919) % 211, (j * 104729) % 9973, j % 1009, j, j)
                            : String.format("/c/%07d", j), v);
                }
                db.execute(tb.build());
            }
            final int puts = Integer.getInteger("puts", 1);
            final int hot = Integer.getInteger("hot", 8);
            long l0 = db.getStreamLength(), cuts = 0, lastFirst = db.getFirstAvailablePos();
            long maxRec = 0;
            long[] kept = new long[3];
            final long it0 = db.internal().reclaim().getIterationCount();
            for (int i = 0; i < n; i++) {
                time += dt;
                clock.setTime(time);
                long before = db.getStreamLength();
                Trans.Builder tb = db.trans();
                if (puts == 1) {
                    byte[] v = new byte[commit];
                    r.nextBytes(v);
                    tb.put("/h/" + r.nextInt(hot), v);
                } else {
                    final TreeSet<Integer> ks = new TreeSet<Integer>();
                    while (ks.size() < Math.min(puts, hot)) ks.add(r.nextInt(hot));
                    for (int k : ks) {
                        byte[] v = new byte[Math.max(1, commit / puts)];
                        r.nextBytes(v);
                        tb.put(String.format("/h/%07d", k), v);
                    }
                }
                db.execute(tb.build());
                maxRec = Math.max(maxRec, db.getStreamLength() - before);
                int third = (int) (3L * i / n);
                kept[third] = Math.max(kept[third], db.getStreamLength() - db.getFirstAvailablePos());
                if (db.getFirstAvailablePos() != lastFirst) {
                    cuts++;
                    lastFirst = db.getFirstAvailablePos();
                }
            }
            long written = db.getStreamLength() - l0;
            long its = db.internal().reclaim().getIterationCount() - it0;
            return new long[] {written, kept[0], kept[1], kept[2], cuts, maxRec, its};
        } finally {
            db.close();
        }
    }
}
