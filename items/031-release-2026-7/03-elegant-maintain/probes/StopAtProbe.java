package bergdb.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.concurrent.atomic.AtomicLong;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-03's review probe: a deterministic scenario run once to note every record (its w and kind), then
 * once for each record j with db.stop() called from the hook at record j (a stop inside the
 * call that wrote it, so also inside a call that then cuts the stream); the stream, closed,
 * is started: its w must be the first run's at record j. Then CALLS calls more on the restarted
 * database: prints its stream kept and whether the filler KV is live, against the first run.
 * Scenario: R = 1 s, sd SD, a put of /a (VAL bytes), then maintain() calls 1 ms apart.
 *   java -ea -cp out:bergdb.jar bergdb.core.StopAtProbe SD VAL CALLS [KEYS [filler]]
 * With KEYS > 1: KEYS values put, then all deleted (an emptied database), then the calls;
 * "filler": stops only at the fillers' records.
 */
public class StopAtProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final long[] FILL = Keys.toSegments("/#i/dreclaim/-fill.txt");
    static final long[] TABLE = Keys.toSegments("/#i/dreclaim/-table.txt");

    static final class Rec { long w; String kind; }

    static String kind(TransNodes n, boolean internal) {
        boolean fill = false, table = false;
        for (int i = 0; i < n.valueCount; i++) {
            if (Arrays.equals(FILL, n.keys[i])) fill = true;
            if (Arrays.equals(TABLE, n.keys[i])) table = true;
        }
        return (internal ? "internal" : "app") + (fill ? (table ? " filler-put" : " filler-delete") : "")
                + " values " + n.valueCount;
    }

    static int sd, val, calls, keys = 1;
    static boolean fillerOnly;

    /** Runs the scenario; stops at record 'stopAt' (-1: never). Returns the stream. */
    static CutStream run(int stopAt, ArrayList<Rec> recs, AtomicLong time, Db[] out) {
        CutStream s = new CutStream();
        Db d = Db.builder().testSetup(s).clock(time::get).start();
        out[0] = d;
        d.setStartupDistance(sd);
        d.setRetainDuration(SEC);
        final int[] count = {0};
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                if (recs != null) {
                    Rec r = new Rec();
                    r.w = d.internal().reclaim().appW;
                    r.kind = kind(x.transNodes, x.trans.isInternal());
                    recs.add(r);
                }
                if (count[0]++ == stopAt) d.stop();
            }
            public void valueNodeCreated(ValueNode n, long[] k) {}
            public void nodeTouched(Node n) {}
            public void nodeReplaced(Node n) {}
        };
        try {
            for (int k = 0; k < keys; k++) {
                time.addAndGet(MS);
                d.execute(d.trans().put("/a" + k, new byte[val]).build());
            }
            for (int k = 0; k < keys && keys > 1; k++) {
                time.addAndGet(MS);
                d.execute(d.trans().delete("/a" + k).build());
            }
            for (int i = 0; i < 3000; i++) {
                time.addAndGet(MS);
                d.maintain();
            }
        } catch (RuntimeException e) {
            if (stopAt == -1) throw e;
        } finally {
            Db.testHooks = null;
        }
        return s;
    }

    public static void main(String[] a) throws Exception {
        sd = Integer.parseInt(a[0]);
        val = Integer.parseInt(a[1]);
        calls = Integer.parseInt(a[2]);
        if (a.length > 3) keys = Integer.parseInt(a[3]);
        fillerOnly = a.length > 4 && a[4].equals("filler");
        ArrayList<Rec> recs = new ArrayList<Rec>();
        AtomicLong t0 = new AtomicLong(SEC);
        Db[] out = new Db[1];
        run(-1, recs, t0, out);
        Db base = out[0];
        for (int i = 0; i < calls; i++) { t0.addAndGet(MS); base.maintain(); }
        long baseKept = base.getStreamLength() - base.getFirstAvailablePos();
        System.out.println("uninterrupted: " + recs.size() + " records; after " + calls
                + " calls more kept " + baseKept + ", filler live "
                + (base.getOne(Long.MAX_VALUE, FILL, base.newGetData()) != null));
        base.close();
        int wrong = 0;
        for (int j = 0; j < recs.size(); j++) {
            if (fillerOnly && !recs.get(j).kind.contains("filler")) continue;
            AtomicLong t = new AtomicLong(SEC);
            CutStream s = run(j, null, t, out);
            out[0].close();
            CutStream c = s.copy();
            Db d = Db.builder().testSetup(c).clock(t::get).start();
            long w = d.internal().reclaim().appW;
            String bad = w != recs.get(j).w ? "  WRONG w: run " + recs.get(j).w + " start " + w : "";
            if (!bad.isEmpty()) wrong++;
            for (int i = 0; i < calls; i++) { t.addAndGet(MS); d.maintain(); }
            long kept = d.getStreamLength() - d.getFirstAvailablePos();
            boolean fill = d.getOne(Long.MAX_VALUE, FILL, d.newGetData()) != null;
            if (!bad.isEmpty() || fill || Math.abs(kept - baseKept) > 50000) {
                System.out.println("stop at record " + j + " (" + recs.get(j).kind + "): kept " + kept
                        + " filler live " + fill + bad);
            }
            d.close();
        }
        System.out.println("records " + recs.size() + ", wrong w " + wrong);
    }
}
