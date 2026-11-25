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
 * bergdb 031-03's review probe of the padded table (M5 as one record). Scenario: R = 1 s, sd SD,
 * KEYS puts of /aK (VAL bytes), then (if DEL) their deletes, then CALLS maintain() calls 1 ms
 * apart. Notes every record; a "pad" is a record that stores the table and is larger than
 * 20,000 bytes. For each maintain() call with a pad: whether a cut was decided in the same
 * call (fp moved). Then, for each pad record j: a run stopped at j (db.stop() from the hook),
 * started again: w against the run's, then CALLS calls: the stream kept against the run's,
 * and the number of pads written after the restart.
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.PadProbe SD VAL KEYS DEL CALLS [quiet]
 */
public class PadProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final long[] TABLE = Keys.toSegments("/#i/dreclaim/-table.txt");
    static int sd, val, keys, calls;
    static boolean del, quiet;

    static final class Rec { long w, tpos, next; boolean pad; int call; }

    static boolean holdsTable(TransNodes n) {
        for (int i = 0; i < n.valueCount; i++) if (Arrays.equals(TABLE, n.keys[i])) return true;
        return false;
    }

    /** The spaces after the table's text in the record's table value, or -1 if none is stored. */
    static int padOf(TransNodes n) {
        for (int i = 0; i < n.valueCount; i++) {
            if (!Arrays.equals(TABLE, n.keys[i])) continue;
            byte[] v = n.valueNodes[i].getValue();
            int p = 0;
            while (p < v.length && v[v.length - 1 - p] == ' ') p++;
            return p;
        }
        return -1;
    }

    static int padsAfter;
    static long minPad = Long.MAX_VALUE;
    static int padCalls, padCallsWithoutCut, maxPadsPerIteration;

    static Db run(int stopAt, ArrayList<Rec> recs, AtomicLong time, CutStream[] sOut) {
        CutStream s = new CutStream();
        sOut[0] = s;
        Db d = Db.builder().testSetup(s).clock(time::get).start();
        d.setStartupDistance(sd);
        d.setRetainDuration(SEC);
        final int[] count = {0}, call = {-1}, padsInCall = {0};
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                boolean pad = padOf(x.transNodes) > 0;
                if (pad) minPad = Math.min(minPad, padOf(x.transNodes));
                if (pad) padsInCall[0]++;
                if (recs != null) {
                    Rec r = new Rec();
                    r.w = d.internal().reclaim().appW;
                    r.tpos = x.trans.tpos;
                    r.next = x.trans.nextPos;
                    r.pad = pad;
                    r.call = call[0];
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
            for (int k = 0; k < keys && del; k++) {
                time.addAndGet(MS);
                d.execute(d.trans().delete("/a" + k).build());
            }
            int pads = 0;
            for (int i = 0; i < 3000; i++) {
                time.addAndGet(MS);
                call[0] = i;
                padsInCall[0] = 0;
                long fp = d.getFirstAvailablePos();
                d.maintain();
                if (recs != null && padsInCall[0] > 0) {
                    padCalls++;
                    pads += padsInCall[0];
                    if (d.getFirstAvailablePos() == fp) {
                        padCallsWithoutCut++;
                        if (!quiet) System.out.println("  pad in call " + i + " without a cut: fp " + fp
                                + " length " + d.getStreamLength());
                    } else {
                        maxPadsPerIteration = Math.max(maxPadsPerIteration, pads);
                        pads = 0;
                    }
                }
            }
        } catch (RuntimeException e) {
            if (stopAt == -1) throw e;
        } finally {
            Db.testHooks = null;
        }
        return d;
    }

    public static void main(String[] a) throws Exception {
        sd = Integer.parseInt(a[0]);
        val = Integer.parseInt(a[1]);
        keys = Integer.parseInt(a[2]);
        del = a[3].equals("1");
        calls = Integer.parseInt(a[4]);
        quiet = a.length > 5;
        ArrayList<Rec> recs = new ArrayList<Rec>();
        AtomicLong t0 = new AtomicLong(SEC);
        CutStream[] so = new CutStream[1];
        Db base = run(-1, recs, t0, so);
        for (int i = 0; i < calls; i++) { t0.addAndGet(MS); base.maintain(); }
        long baseKept = base.getStreamLength() - base.getFirstAvailablePos();
        int pads = 0;
        long minFill = Long.MAX_VALUE;
        for (Rec r : recs) if (r.pad) { pads++; minFill = Math.min(minFill, r.next - r.tpos); }
        System.out.println("sd " + sd + " val " + val + " keys " + keys + " del " + del + ": " + recs.size()
                + " records, " + pads + " pads (smallest record " + minFill + ", smallest pad " + minPad + "), pad calls " + padCalls
                + ", without a cut in the call " + padCallsWithoutCut + ", most pads an iteration "
                + maxPadsPerIteration + "; kept after " + calls + " more calls " + baseKept);
        base.close();
        int wrong = 0, stops = 0;
        for (int j = 0; j < recs.size(); j++) {
            if (!recs.get(j).pad && !(j > 0 && recs.get(j - 1).pad)) continue;
            stops++;
            AtomicLong t = new AtomicLong(SEC);
            Db x = run(j, null, t, so);
            x.close();
            Db d = Db.builder().testSetup(so[0].copy()).clock(t::get).start();
            long w = d.internal().reclaim().appW;
            if (w != recs.get(j).w) {
                wrong++;
                System.out.println("  WRONG w after record " + j + ": run " + recs.get(j).w + " start " + w);
            }
            final int[] padsAfterRestart = {0};
            Db.testHooks = new Db.TestHooks() {
                public void transExecuted(Db.ExecuteData y) {
                    if (padOf(y.transNodes) > 0) padsAfterRestart[0]++;
                }
                public void valueNodeCreated(ValueNode n, long[] k) {}
                public void nodeTouched(Node n) {}
                public void nodeReplaced(Node n) {}
            };
            for (int i = 0; i < calls; i++) { t.addAndGet(MS); d.maintain(); }
            Db.testHooks = null;
            long kept = d.getStreamLength() - d.getFirstAvailablePos();
            if (!quiet || Math.abs(kept - baseKept) > 20000 || w != recs.get(j).w) {
                System.out.println("  stop after record " + j + (recs.get(j).pad ? " (pad)" : " (after a pad)")
                        + ": w ok " + (w == recs.get(j).w) + ", kept " + kept + " (run " + baseKept
                        + "), pads after the restart " + padsAfterRestart[0]);
            }
            d.close();
        }
        System.out.println("stops " + stops + ", wrong w " + wrong);
    }
}
