package bergdb.core;

import java.util.*;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06, review 3, W2: the warm-up scans that maintain() makes while it gives way to
 * commits, and the copies of the running row that Reclaim.publishWarm makes, as counts. A
 * database larger than its cache budget: COLD keys of VALUE bytes put once; then WRITERS
 * threads make N commits of one put of COMMIT bytes at one of 8 hot keys without a pause,
 * the clock DT_MS on for each, while one thread calls maintain(BUDGET) until they are done.
 * Retain duration 1 s, startup distance 20,000 (-Dsd=).
 *
 * Counted: maintain()'s warm-up scans (the calls of Db.TestHooks.stepWarmup() on its
 * thread: each is followed by a scan of the part's range), its rounds that gave way
 * (TestHooks.givingWay()), its parts and those that carry a step (transExecuted, Trans.part);
 * the records, and the published rows (the identity of Reclaim's warm.row after each record,
 * by reflection): on main every record copies the row, since 031-06's review 3 only a
 * record that moves it. The counts vary from run to run with the threads; the stream is not
 * compared (several threads).
 *
 * Usage: java -cp OUT:JAR bergdb.core.HandoverWarmProbe COLD VALUE N COMMIT DT_MS CACHE
 *     WRITERS BUDGET
 * Kind: functional (counts; no time is measured).
 */
public class HandoverWarmProbe {
    static final long SEC = Clock.UNITS_PER_SEC;
    static volatile Thread maintainer;
    static final AtomicLong warmScans = new AtomicLong(), givingWay = new AtomicLong();
    static long records, parts, partSteps, commitSteps, rowCopies;
    static Object lastRow;
    static volatile Reclaim reclaim;
    static volatile boolean loading;

    public static void main(String[] args) throws Exception {
        final int cold = Integer.parseInt(args[0]), value = Integer.parseInt(args[1]);
        final int n = Integer.parseInt(args[2]), commit = Integer.parseInt(args[3]);
        final long dt = Long.parseLong(args[4]) * SEC / 1000;
        final long cache = Long.parseLong(args[5]);
        final int writers = Integer.parseInt(args[6]), budget = Integer.parseInt(args[7]);
        System.out.println("HandoverWarmProbe cold " + cold + " x " + value + ", " + n
                + " commits of " + commit + " bytes, " + args[4] + " ms apart, cache budget "
                + cache + ", writers " + writers + ", maintain(" + budget + ") in a loop:");
        final java.lang.reflect.Field warmField = Reclaim.class.getDeclaredField("warm");
        warmField.setAccessible(true);
        final java.lang.reflect.Field rowField =
                Class.forName("bergdb.core.Reclaim$Warm").getDeclaredField("row");
        rowField.setAccessible(true);
        Db.testHooks = new Db.TestHooks() {
            public boolean stepWarmup() {
                if (Thread.currentThread() == maintainer) warmScans.incrementAndGet();
                return true;
            }

            public void givingWay() {
                if (Thread.currentThread() == maintainer) givingWay.incrementAndGet();
            }

            public void transExecuted(Db.ExecuteData x) {     // under the write lock
                if (loading || reclaim == null) return;
                records++;
                if (x.trans.part) {
                    parts++;
                    if (x.plan != null && x.plan.touchKeys != null) partSteps++;
                } else if (x.plan != null && x.plan.touchKeys != null) {
                    commitSteps++;
                }
                try {
                    final Object w = warmField.get(reclaim);
                    final Object row = w == null ? null : rowField.get(w);
                    if (row != null && row != lastRow) rowCopies++;
                    lastRow = row;
                } catch (ReflectiveOperationException e) {
                    throw new RuntimeException(e);
                }
            }

            public void valueNodeCreated(bergdb.dag.ValueNode vn, long[] key) {}
            public void nodeTouched(bergdb.dag.Node nd) {}
            public void nodeReplaced(bergdb.dag.Node nd) {}
        };
        final AtomicLong clock = new AtomicLong(SEC);
        CutStream s = new CutStream();
        final Db db = Db.builder().testSetup(s).clock(clock::get).cacheSizeIndicator(cache)
                .start();
        reclaim = db.internal().reclaim();
        try {
            db.setStartupDistance(Integer.getInteger("sd", 20000));
            db.setRetainDuration(SEC);
            Random r = new Random(1);
            loading = true;
            final int per = Math.max(1, Math.min(100, 2000000 / (value + 100)));
            for (int i = 0; i < cold; i += per) {
                clock.addAndGet(SEC / 100);
                Trans.Builder tb = db.trans();
                for (int j = i; j < Math.min(cold, i + per); j++) {
                    byte[] v = new byte[value];
                    r.nextBytes(v);
                    tb.put(String.format("/c/%08d", j), v);
                }
                db.execute(tb.build());
            }
            loading = false;
            final AtomicLong left = new AtomicLong(n);
            final List<Thread> ts = new ArrayList<Thread>();
            final Throwable[] failure = new Throwable[1];
            for (int w = 0; w < writers; w++) {
                final Random rw = new Random(100 + w);
                ts.add(new Thread(() -> {
                    try {
                        while (left.decrementAndGet() >= 0) {
                            clock.addAndGet(dt);
                            byte[] v = new byte[commit];
                            rw.nextBytes(v);
                            db.execute(db.trans().put("/h/" + rw.nextInt(8), v).build());
                        }
                    } catch (Throwable e) {
                        synchronized (failure) {
                            if (failure[0] == null) failure[0] = e;
                        }
                    }
                }));
            }
            final long[] calls = new long[1];
            Thread m = new Thread(() -> {
                try {
                    while (left.get() > 0) {
                        db.maintain(budget);
                        calls[0]++;
                    }
                } catch (Throwable e) {
                    synchronized (failure) {
                        if (failure[0] == null) failure[0] = e;
                    }
                }
            });
            maintainer = m;
            for (Thread t : ts) t.start();
            m.start();
            for (Thread t : ts) t.join();
            m.join();
            if (failure[0] != null) {
                failure[0].printStackTrace(System.out);
                System.out.println("HANDOVER WARM PROBE FAILED: " + failure[0]);
                return;
            }
            System.out.println("  maintain(): " + calls[0] + " calls, " + givingWay.get()
                    + " rounds that gave way, " + parts + " parts (" + partSteps
                    + " with a step), " + warmScans.get() + " warm-up scans ("
                    + String.format("%.2f", parts == 0 ? 0.0 : warmScans.get() / (double) parts)
                    + " a part)");
            System.out.println("  records " + records + " (" + commitSteps
                    + " commits with a step), rows published by copy " + rowCopies
                    + "; stream " + s.getLength());
            System.out.println("HANDOVER WARM PROBE DONE");
        } finally {
            db.close();
            Db.testHooks = null;
        }
    }
}
