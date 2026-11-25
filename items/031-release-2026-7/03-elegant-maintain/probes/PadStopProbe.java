package bergdb.core;

import java.util.concurrent.atomic.AtomicLong;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.ValueNode;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-03's review probe: a stop right after the padded table (M5), then a restart and VARIANT:
 * "commit" a user put; "empty" an empty transaction; "forever" R set to forever, 3 R of calls,
 * R back to 1 s; "calls" calls only. Then 5 R of calls. Prints, after the restart and at the
 * end: the table value's length (a pad stays while it is long), fp, the stream kept, w.
 *   java -ea -cp OUT:build/bergdb.jar bergdb.core.PadStopProbe SD VAL VARIANT
 */
public class PadStopProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final long[] TABLE = Keys.toSegments("/#i/dreclaim/-table.txt");

    static void state(String label, Db d) {
        byte[] t = d.getOne(Long.MAX_VALUE, TABLE, d.newGetData());
        System.out.println(label + ": table " + (t == null ? -1 : t.length) + " bytes, fp "
                + d.getFirstAvailablePos() + ", length " + d.getStreamLength() + ", kept "
                + (d.getStreamLength() - d.getFirstAvailablePos()) + ", w " + d.internal().reclaim().appW);
    }

    public static void main(String[] a) throws Exception {
        int sd = Integer.parseInt(a[0]), val = Integer.parseInt(a[1]);
        String variant = a[2];
        AtomicLong time = new AtomicLong(SEC);
        CutStream s = new CutStream();
        final Db d0 = Db.builder().testSetup(s).clock(time::get).start();
        Db d = d0;
        d.setStartupDistance(sd);
        d.setRetainDuration(SEC);
        final long[] runW = {Long.MIN_VALUE};
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                for (int i = 0; i < x.transNodes.valueCount; i++) {
                    byte[] v = x.transNodes.valueNodes[i].getValue();
                    if (java.util.Arrays.equals(TABLE, x.transNodes.keys[i]) && v != null && v.length > 0
                            && v[v.length - 1] == ' ' && runW[0] == Long.MIN_VALUE) {
                        runW[0] = d0.internal().reclaim().appW;
                        d0.stop();
                    }
                }
            }
            public void valueNodeCreated(ValueNode n, long[] k) {}
            public void nodeTouched(Node n) {}
            public void nodeReplaced(Node n) {}
        };
        try {
            time.addAndGet(MS);
            d.execute(d.trans().put("/a", new byte[val]).build());
            for (int i = 0; i < 5000; i++) { time.addAndGet(MS); d.maintain(); }
        } catch (RuntimeException e) {
            // the stop
        }
        Db.testHooks = null;
        d.close();
        if (runW[0] == Long.MIN_VALUE) { System.out.println("no pad"); return; }
        d = Db.builder().testSetup(s.copy()).clock(time::get).start();
        System.out.println("w: run " + runW[0] + ", start " + d.internal().reclaim().appW);
        state("restarted", d);
        time.addAndGet(MS);
        if (variant.equals("commit")) d.execute(d.trans().put("/b", new byte[10]).build());
        if (variant.equals("empty")) d.execute(d.trans().build());
        if (variant.equals("forever")) {
            d.setRetainDuration(Long.MAX_VALUE);
            for (int i = 0; i < 3000; i++) { time.addAndGet(MS); d.maintain(); }
            state("after 3 R of calls with R forever", d);
            d.setRetainDuration(SEC);
        }
        state("after " + variant, d);
        long last = -1;
        for (int i = 0; i < 5000; i++) {
            time.addAndGet(MS);
            long l = d.getStreamLength();
            if (d.maintain() || d.getStreamLength() != l) last = i;
        }
        state("after 5 R of calls (last work " + last + ")", d);
        d.close();
    }
}
