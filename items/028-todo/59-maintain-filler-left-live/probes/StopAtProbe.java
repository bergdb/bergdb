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
 * bergdb 028-59's copy of 031-03's StopAtProbe, 2026-11-25, for main, 2026.6 and 2026.5: without
 * w (appW, only in 031-03's prototype), and with a crash as well as a stop.
 * A deterministic scenario run once to note every record and its kind, then once for each
 * record j, interrupted at record j from the hook transExecuted:
 *   stop:  db.stop() (a stop inside the call that wrote record j); the stream, closed, is
 *          started from a copy;
 *   crash: the hook waits 100 ms, so that the write buffer (10 ms) reaches the stream, and
 *          copies the stream as it is then, the bytes a crash right after record j leaves;
 *          then the database is stopped; the copy is started.
 * Then CALLS calls more on the started database: prints its stream kept and whether the
 * filler KV is live, against the run without interruption.
 * Scenario: R = 1 s, sd SD, a put of /a (VAL bytes), then maintain() calls 1 ms apart.
 *   java -ea -cp out:bergdb.jar bergdb.core.StopAtProbe SD VAL CALLS [KEYS [filler|all] [stop|crash [K2 V2]]]
 * With K2 and V2: before the CALLS calls, on the uninterrupted database and on each started
 * one, K2 values of V2 bytes put, then deleted, 1 ms apart: the application writes again and
 * empties the database again.
 * With KEYS > 1: KEYS values put, then all deleted (an emptied database), then the calls;
 * "filler": interrupts only at the fillers' records. SD as "bN": the startup distance N set by
 * the builder, not by Db.setStartupDistance(), which in 2026.5 raises it to 400 kB and writes a
 * live value of 200 kB that every iteration rewrites, so that no filler is needed; in 2026.6
 * and main, which have no such builder method (bergdb 028-13), by the setter.
 */
public class StopAtProbe {
    static final long SEC = Clock.UNITS_PER_SEC, MS = SEC / 1000;
    static final long[] FILL = Keys.toSegments("/#i/dreclaim/-fill.txt");

    static int fillRecords;

    /** The kind of a record; a record with the filler's key is its put and the next its delete. */
    static String kind(TransNodes n, boolean internal) {
        boolean fill = false;
        for (int i = 0; i < n.valueCount; i++) {
            if (Arrays.equals(FILL, n.keys[i])) fill = true;
        }
        String f = !fill ? "" : fillRecords++ % 2 == 0 ? " filler-put" : " filler-delete";
        return (internal ? "internal" : "app") + f + " values " + n.valueCount;
    }

    static int sd, val, calls, keys = 1;
    static boolean fillerOnly, crash, builderSd;
    static int k2, v2;

    /** The table's rows and the stream's first position and length, read by reflection. */
    @SuppressWarnings("unchecked")
    static String rows(Db d) {
        StringBuilder b = new StringBuilder("fp=" + d.getFirstAvailablePos() + " length=" + d.getStreamLength());
        try {
            java.lang.reflect.Field tf = Reclaim.class.getDeclaredField("table");
            tf.setAccessible(true);
            java.lang.reflect.Field rf = Class.forName("bergdb.core.Reclaim$IterationTable").getDeclaredField("rows");
            rf.setAccessible(true);
            for (Reclaim.IterationInfo r : (java.util.List<Reclaim.IterationInfo>) rf.get(tf.get(d.internal().reclaim()))) {
                b.append(" [pStart=" + r.pStart + " pCut=" + r.pCut + " rewritten=" + r.rewritten
                        + " done=" + r.done + " cut=" + r.cut + "]");
            }
        } catch (ReflectiveOperationException e) {
            b.append(" rows: " + e);
        }
        return b.toString();
    }

    /** K2 values put, then deleted. */
    static void writeAgain(Db d, AtomicLong time) {
        for (int k = 0; k < k2; k++) {
            time.addAndGet(MS);
            d.execute(d.trans().put("/b" + k, new byte[v2]).build());
        }
        for (int k = 0; k < k2; k++) {
            time.addAndGet(MS);
            d.execute(d.trans().delete("/b" + k).build());
        }
    }

    static Db start(CutStream s, AtomicLong time) {
        DbBuilder b = Db.builder().testSetup(s).clock(time::get);
        boolean byBuilder = false;
        if (builderSd) {
            try {       // 2026.5 has it; 2026.6 and main not (bergdb 028-13).
                DbBuilder.class.getMethod("startupDistance", int.class).invoke(b, sd);
                byBuilder = true;
            } catch (ReflectiveOperationException e) {}
        }
        Db d = b.start();
        if (!byBuilder) d.setStartupDistance(sd);
        d.setRetainDuration(SEC);
        return d;
    }

    /** Runs the scenario; interrupts at record 'at' (-1: never). Returns the stream to start. */
    static CutStream run(int at, ArrayList<String> recs, AtomicLong time, Db[] out) {
        CutStream s = new CutStream();
        Db d = start(s, time);
        out[0] = d;
        final int[] count = {0};
        final CutStream[] copy = {null};
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                if (recs != null) {
                    recs.add(kind(x.transNodes, x.trans.isInternal()));
                }
                if (count[0]++ == at) {
                    if (crash) {
                        try { Thread.sleep(100); } catch (InterruptedException e) {}
                        copy[0] = s.copy();
                    }
                    d.stop();
                }
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
            if (at == -1) throw e;
        } finally {
            Db.testHooks = null;
        }
        return crash && at != -1 ? copy[0] : s;
    }

    public static void main(String[] a) throws Exception {
        builderSd = a[0].startsWith("b");
        sd = Integer.parseInt(builderSd ? a[0].substring(1) : a[0]);
        val = Integer.parseInt(a[1]);
        calls = Integer.parseInt(a[2]);
        if (a.length > 3) keys = Integer.parseInt(a[3]);
        fillerOnly = a.length > 4 && a[4].equals("filler");
        crash = a.length > 5 && a[5].equals("crash");
        if (a.length > 7) { k2 = Integer.parseInt(a[6]); v2 = Integer.parseInt(a[7]); }
        ArrayList<String> recs = new ArrayList<String>();
        AtomicLong t0 = new AtomicLong(SEC);
        Db[] out = new Db[1];
        run(-1, recs, t0, out);
        Db base = out[0];
        writeAgain(base, t0);
        for (int i = 0; i < calls; i++) { t0.addAndGet(MS); base.maintain(); }
        long baseKept = base.getStreamLength() - base.getFirstAvailablePos();
        System.out.println((crash ? "crash" : "stop") + "; uninterrupted: " + recs.size()
                + " records; after " + calls + " calls more kept " + baseKept + ", filler live "
                + (base.getOne(Long.MAX_VALUE, FILL, base.newGetData()) != null) + "; " + rows(base));
        base.close();
        AtomicLong tf = new AtomicLong(SEC);
        Db fresh = start(new CutStream(), tf);
        System.out.println("fresh kept " + (fresh.getStreamLength() - fresh.getFirstAvailablePos()));
        fresh.close();
        int n = 0, live = 0;
        for (int j = 0; j < recs.size(); j++) {
            if (fillerOnly && !recs.get(j).contains("filler")) continue;
            n++;
            AtomicLong t = new AtomicLong(SEC);
            CutStream s = run(j, null, t, out);
            if (!crash) out[0].close();
            CutStream c = s.copy();
            Db d = Db.builder().testSetup(c).clock(t::get).start();
            boolean fillAtStart = d.getOne(Long.MAX_VALUE, FILL, d.newGetData()) != null;
            writeAgain(d, t);
            for (int i = 0; i < calls; i++) { t.addAndGet(MS); d.maintain(); }
            long kept = d.getStreamLength() - d.getFirstAvailablePos();
            boolean fill = d.getOne(Long.MAX_VALUE, FILL, d.newGetData()) != null;
            if (fill) live++;
            if (fill || fillAtStart || Math.abs(kept - baseKept) > 50000) {
                System.out.println("at record " + j + " (" + recs.get(j) + "): at the start filler live "
                        + fillAtStart + "; after the calls kept " + kept + ", filler live " + fill + "; " + rows(d));
            }
            d.close();
        }
        System.out.println("records " + recs.size() + ", interrupted " + n + ", filler live after the calls " + live);
    }
}
