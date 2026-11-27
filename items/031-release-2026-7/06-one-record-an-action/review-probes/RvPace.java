package bergdb.core;

import java.util.*;

import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * Review probe of bergdb 031-06 (2026-11-27), reclaim's pace and the stream kept: COLD keys
 * of VALUE bytes put once (the live data), then N commits of one hot key each with a value
 * of COMMIT bytes, DT seconds of database time apart, retain duration 1 s, no maintain()
 * calls. Printed: the stream written by the commits, and the same run without reclaim where
 * the jar has DbBuilder.maintenanceNone (the difference is what reclaim wrote: copies, rows,
 * tables and their index nodes); the stream kept, its largest value in each third of the
 * run, in bytes and in units of the live data; the iterations begun.
 * Runs on 031-05's jar too (-Dproto315.eager=true: D2), by reflection for maintenanceNone.
 *
 * Usage: java -cp OUT:JAR bergdb.core.RvPace COLD VALUE N COMMIT DT_MS [NODE]
 *   -Dsd=20000 -Dcap=0 (CAP of the stated bound) -Ddeep=true (cold keys of seven segments on paths of their own)
 */
public class RvPace {
    static final long SEC = Clock.UNITS_PER_SEC;

    public static void main(String[] args) throws Exception {
        int cold = Integer.parseInt(args[0]), value = Integer.parseInt(args[1]);
        int n = Integer.parseInt(args[2]), commit = Integer.parseInt(args[3]);
        long dt = Long.parseLong(args[4]) * SEC / 1000;
        int node = args.length > 5 ? Integer.parseInt(args[5]) : 0;
        long[] with = run(cold, value, n, commit, dt, node, false);
        long[] none = null;
        try {
            none = run(cold, value, n, commit, dt, node, true);
        } catch (NoSuchMethodException e) {
        }
        long live = (long) cold * (value + 40);
        System.out.println("RvPace cold " + cold + " x " + value + " (live about " + live + "), " + n
                + " commits of " + commit + " bytes, " + args[4] + " ms apart, node " + node + ":");
        System.out.println("  written by the commits: " + with[0] + (none == null ? "" : "; without reclaim "
                + none[0] + "; reclaim's share of the growth " + String.format("%.3f", (with[0] - none[0]) / (double) with[0])
                + " (the internal fraction: 0.250); write amplification " + String.format("%.2f", with[0] / (double) none[0])));
        System.out.println("  the stream kept, largest in each third: " + with[1] + ", " + with[2] + ", " + with[3]
                + " = " + String.format("%.1f, %.1f, %.1f", with[1] / (double) live, with[2] / (double) live, with[3] / (double) live)
                + " x live; cuts " + with[4] + "; largest record " + with[5]
                + "; the stream kept at most " + with[6] / 10.0 + " % of 031-06's stated bound with CAP = " + Long.getLong("cap", 0)
                + " (W at most " + with[7] + ")");
    }

    static long[] run(int cold, int value, int n, int commit, long dt, int node, boolean none) throws Exception {
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        CutStream s = new CutStream();
        DbBuilder b = Db.builder().testSetup(s).clock(clock);
        if (node == 8) b.maxNodeSize8();
        if (none) DbBuilder.class.getMethod("maintenanceNone").invoke(b);
        Db db = b.start();
        db.setStartupDistance(Integer.getInteger("sd", 20000));
        db.setRetainDuration(SEC);
        Random r = new Random(1);
        for (int i = 0; i < cold; i += 20) {
            time += SEC / 100; clock.setTime(time);
            Trans.Builder tb = db.trans();
            for (int j = i; j < Math.min(cold, i + 20); j++) {
                byte[] v = new byte[value];
                r.nextBytes(v);
                tb.put(Boolean.getBoolean("deep") ? String.format("/c/%03d/%05d/%07d/%07d/%07d/k", (j * 7919) % 211, (j * 104729) % 9973, j % 1009, j, j)
                        : String.format("/c/%07d", j), v);
            }
            db.execute(tb.build());
        }
        long l0 = db.getStreamLength(), cuts = 0, lastFirst = db.getFirstAvailablePos(), maxRec = 0;
        long maxW = 0, maxOver1000 = 0;
        final long liveNodes = (long) cold * (value + 60);
        final java.util.ArrayDeque<long[]> win = new java.util.ArrayDeque<>();
        long[] kept = new long[3];
        for (int i = 0; i < n; i++) {
            time += dt; clock.setTime(time);
            byte[] v = new byte[commit];
            r.nextBytes(v);
            long before = db.getStreamLength();
            db.execute(db.trans().put("/h/" + r.nextInt(8), v).build());
            maxRec = Math.max(maxRec, db.getStreamLength() - before);
            int third = (int) (3L * i / n);
            kept[third] = Math.max(kept[third], db.getStreamLength() - db.getFirstAvailablePos());
            if (db.getFirstAvailablePos() != lastFirst) { cuts++; lastFirst = db.getFirstAvailablePos(); }
            // 031-06's stated bound of the stream kept (SafetyProbe.bound), with W the bytes
            // written in the last 1.5 retain durations and CAP from -Dcap (the record cap).
            win.add(new long[] {time, before});
            while (win.peekFirst()[0] < time - 3 * SEC / 2) win.pollFirst();
            maxW = Math.max(maxW, db.getStreamLength() - win.peekFirst()[1]);
            long bound = 2 * Math.max(8 * liveNodes, Math.max(maxW / 6, 2L * Integer.getInteger("sd", 20000)))
                    + 3 * maxW + 2 * 200000 + 2 * Long.getLong("cap", 0);
            maxOver1000 = Math.max(maxOver1000, (db.getStreamLength() - db.getFirstAvailablePos()) * 1000 / bound);
        }
        long written = db.getStreamLength() - l0;
        db.close();
        return new long[] {written, kept[0], kept[1], kept[2], cuts, maxRec, maxOver1000, maxW};
    }
}
