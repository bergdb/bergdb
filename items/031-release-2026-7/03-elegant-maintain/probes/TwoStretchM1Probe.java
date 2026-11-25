package bergdb.core;

import java.lang.reflect.Field;
import java.util.List;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-03's review probe (claim (a)), maintain()'s M1 alone beginning iterations (startup distance SD
 * large, so the commit rule never begins one): an emptied database stuck with two stretches
 * just below MIN_RELEASE. R = 1 s, test clock, calls 1 ms apart.
 *   /a (450 kB) put, deleted; calls until iteration 1 begins
 *   /b (450 kB) put, deleted; calls until iteration 2 begins (own 0, next >= MIN_RELEASE)
 *   /c (C bytes) put, deleted at once after iteration 2's begin
 *   calls until iteration 3 begins (own = P2 - P1 >= MIN_RELEASE)
 *   /d (D bytes) put, deleted at once after iteration 3's begin
 *   CALLS calls.
 *   java -ea -cp out:bergdb.jar bergdb.core.TwoStretchM1Probe C D SD CALLS
 */
public class TwoStretchM1Probe {
    static String w(Db d) {
        try {
            return "" + Reclaim.class.getDeclaredField("appW").get(d.internal().reclaim());
        } catch (ReflectiveOperationException e) {
            return "none";
        }
    }
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final AtomicLong time = new AtomicLong(SEC);
    static Field tableF, rowsF;

    @SuppressWarnings("unchecked")
    static List<Reclaim.IterationInfo> rows(Db d) throws Exception {
        return (List<Reclaim.IterationInfo>) rowsF.get(tableF.get(d.internal().reclaim()));
    }

    static void state(String label, Db d) throws Exception {
        StringBuilder b = new StringBuilder();
        for (Reclaim.IterationInfo r : rows(d)) {
            b.append("[pStart=" + r.pStart + " pCut=" + r.pCut + " rewritten=" + r.rewritten
                    + " done=" + r.done + " cut=" + r.cut + "]");
        }
        System.out.println(label + ": length=" + d.getStreamLength() + " fp="
                + d.getFirstAvailablePos() + " kept=" + (d.getStreamLength() - d.getFirstAvailablePos())
                + " w=" + w(d) + " rows=" + b);
    }

    static void exec(Db d, Trans.Builder b) {
        time.addAndGet(MS);
        d.execute(b.build());
    }

    static void callsUntilRows(Db d, int n) throws Exception {
        for (int i = 0; i < 100000 && rows(d).size() < n; i++) {
            time.addAndGet(MS);
            d.maintain();
        }
        if (rows(d).size() < n) throw new AssertionError("no iteration " + n);
    }

    public static void main(String[] a) throws Exception {
        tableF = Reclaim.class.getDeclaredField("table");
        tableF.setAccessible(true);
        rowsF = Class.forName("bergdb.core.Reclaim$IterationTable").getDeclaredField("rows");
        rowsF.setAccessible(true);
        int sc = Integer.parseInt(a[0]), sdd = Integer.parseInt(a[1]);
        int sd = Integer.parseInt(a[2]), calls = Integer.parseInt(a[3]);

        CutStream s = new CutStream();
        Db d = Db.builder().testSetup(s).clock(time::get).start();
        d.setStartupDistance(sd);
        d.setRetainDuration(SEC);
        exec(d, d.trans().put("/a", new byte[450000]));
        exec(d, d.trans().delete("/a"));
        callsUntilRows(d, 1);
        state("iteration 1 begun", d);
        exec(d, d.trans().put("/b", new byte[450000]));
        exec(d, d.trans().delete("/b"));
        callsUntilRows(d, 2);
        state("iteration 2 begun", d);
        exec(d, d.trans().put("/c", new byte[sc]));
        exec(d, d.trans().delete("/c"));
        callsUntilRows(d, 3);
        state("iteration 3 begun", d);
        exec(d, d.trans().put("/d", new byte[sdd]));
        exec(d, d.trans().delete("/d"));
        long lastWork = -1;
        for (int i = 0; i < calls; i++) {
            time.addAndGet(MS);
            long l = d.getStreamLength();
            boolean more = d.maintain();
            if (more || d.getStreamLength() != l) lastWork = i;
        }
        state("after " + calls + " calls (last with work " + lastWork + ")", d);
        d.close();
    }
}
