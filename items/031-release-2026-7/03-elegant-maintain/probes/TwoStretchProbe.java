package bergdb.core;

import java.lang.reflect.Field;
import java.util.List;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-03's review probe (claim (a)): an emptied database whose last two stretches (lastPStart - fp and
 * L - lastPStart) are each just below MIN_RELEASE keeps about 2 MIN_RELEASE for good.
 * R = 1 s, startup distance SD, test clock.
 *   put /a (A bytes) -> iteration 1 begins (commit rule); /a deleted; calls end iteration 1
 *   put /b (B bytes), deleted, within R/4 of iteration 1's start
 *   at R/4: a small put+delete -> iteration 2 begins at P2 (commit rule)
 *   put /d (D bytes), deleted, within R/4 of P2
 *   then CALLS maintain() calls, 1 ms apart.
 * Prints the stream kept, fp, rows; and a fresh database's kept.
 *   java -ea -cp out:bergdb.jar bergdb.core.TwoStretchProbe A B D SD CALLS
 */
public class TwoStretchProbe {
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

    static String rowsText(Db d) throws Exception {
        StringBuilder b = new StringBuilder();
        for (Reclaim.IterationInfo r : rows(d)) {
            b.append("[pStart=" + r.pStart + " pCut=" + r.pCut + " rewritten=" + r.rewritten
                    + " done=" + r.done + " cut=" + r.cut + "]");
        }
        return b.toString();
    }

    static void state(String label, Db d) throws Exception {
        System.out.println(label + ": length=" + d.getStreamLength() + " fp="
                + d.getFirstAvailablePos() + " kept=" + (d.getStreamLength() - d.getFirstAvailablePos())
                + " w=" + w(d) + " rows=" + rowsText(d));
    }

    static void exec(Db d, Trans.Builder b) {
        time.addAndGet(MS);
        d.execute(b.build());
    }

    public static void main(String[] a) throws Exception {
        tableF = Reclaim.class.getDeclaredField("table");
        tableF.setAccessible(true);
        rowsF = Class.forName("bergdb.core.Reclaim$IterationTable").getDeclaredField("rows");
        rowsF.setAccessible(true);
        int sa = Integer.parseInt(a[0]), sb = Integer.parseInt(a[1]), sdd = Integer.parseInt(a[2]);
        int sd = Integer.parseInt(a[3]), calls = Integer.parseInt(a[4]);

        CutStream fs = new CutStream();
        Db fresh = Db.builder().testSetup(fs).clock(time::get).start();
        fresh.setStartupDistance(sd);
        fresh.setRetainDuration(SEC);
        long freshKept = fresh.getStreamLength() - fresh.getFirstAvailablePos();
        fresh.close();

        CutStream s = new CutStream();
        Db d = Db.builder().testSetup(s).clock(time::get).start();
        d.setStartupDistance(sd);
        d.setRetainDuration(SEC);
        long t0 = time.get();
        exec(d, d.trans().put("/a", new byte[sa]));
        exec(d, d.trans().delete("/a"));
        state("after /a", d);
        for (int i = 0; i < 50 && rows(d).size() > 0 && !rows(d).get(rows(d).size() - 1).done; i++) {
            time.addAndGet(MS);
            d.maintain();
        }
        state("iteration 1 done", d);
        exec(d, d.trans().put("/b", new byte[sb]));
        exec(d, d.trans().delete("/b"));
        state("after /b", d);
        // At R/4 after iteration 1's start: a small commit begins iteration 2.
        long tStart1 = rows(d).get(rows(d).size() - 1).tStart;
        if (time.get() < tStart1 + SEC / 4) time.set(tStart1 + SEC / 4);
        exec(d, d.trans().put("/c", new byte[10]));
        exec(d, d.trans().delete("/c"));
        state("after /c (iteration 2?)", d);
        exec(d, d.trans().put("/d", new byte[sdd]));
        exec(d, d.trans().delete("/d"));
        state("after /d", d);
        long lastWork = -1;
        for (int i = 0; i < calls; i++) {
            time.addAndGet(MS);
            long l = d.getStreamLength();
            boolean more = d.maintain();
            if (more || d.getStreamLength() != l) lastWork = i;
        }
        state("after " + calls + " calls (last with work " + lastWork + ")", d);
        System.out.println("fresh kept " + freshKept + "; emptied kept - fresh kept = "
                + (d.getStreamLength() - d.getFirstAvailablePos() - freshKept));
        d.close();
    }
}
