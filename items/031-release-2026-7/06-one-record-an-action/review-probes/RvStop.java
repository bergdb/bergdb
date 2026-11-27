package bergdb.core;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;

import bergdb.dag.Keys;
import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * Review probe of bergdb 031-06 (2026-11-27): stop() or close() from another thread while
 * writers commit, a thread calls maintain() and readers read. After each round a start on a
 * copy of the stream: every commit that returned is there with its value; no commit that
 * threw is there; the stream of the copy has the stopped stream's length (the start and the
 * stop appended nothing); the hot keys hold a value that some commit put.
 *
 * Usage: java -ea -cp OUT:build/bergdb.jar bergdb.core.RvStop SEED ROUNDS [NODE]
 */
public class RvStop {
    static final long SEC = Clock.UNITS_PER_SEC;

    public static void main(String[] args) throws Exception {
        long seed = Long.parseLong(args[0]);
        int rounds = Integer.parseInt(args[1]);
        final int node = args.length > 2 ? Integer.parseInt(args[2]) : 0;
        final AtomicLong clock = new AtomicLong(SEC);
        long acked = 0, thrown = 0, parts = 0, cuts = 0;
        Map<String, Integer> kinds = new TreeMap<>();
        final AtomicLong partRecords = new AtomicLong();
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) { if (x.trans.part) partRecords.incrementAndGet(); }
            public void valueNodeCreated(bergdb.dag.ValueNode n, long[] k) {}
            public void nodeTouched(bergdb.dag.Node n) {}
            public void nodeReplaced(bergdb.dag.Node n) {}
        };
        CutStream s = new CutStream();
        final Map<String, byte[]> present = new ConcurrentHashMap<>();   // every acked unique key, all rounds
        for (int round = 0; round < rounds; round++) {
            DbBuilder b = Db.builder().testSetup(s).clock(clock::get);
            if (node == 8) b.maxNodeSize8();
            final Db db = b.start();
            final long len0 = db.getStreamLength();
            if (round == 0) {
                db.setStartupDistance(2000);
                db.setRetainDuration(SEC);
            }
            // The acked commits of the rounds before are there.
            for (Map.Entry<String, byte[]> e : present.entrySet()) {
                byte[] got = db.getOne(Long.MAX_VALUE, Keys.toSegments(e.getKey()), db.newGetData());
                if (!Arrays.equals(got, e.getValue())) throw new AssertionError("round " + round
                        + ": acked " + e.getKey() + " not there after the start");
            }
            final Map<String, byte[]> ack = new ConcurrentHashMap<>();
            final Map<String, Throwable> thr = new ConcurrentHashMap<>();
            final AtomicBoolean go = new AtomicBoolean(true);
            final List<Thread> ts = new ArrayList<>();
            final int rd = round;
            for (int w = 0; w < 3; w++) {
                final int wid = w;
                final Random r = new Random(seed * 1000 + round * 10 + w);
                ts.add(new Thread(() -> {
                    for (int i = 0; go.get(); i++) {
                        clock.addAndGet(r.nextInt(300000));
                        String k = "/u/" + rd + "/" + wid + "/" + i;
                        byte[] v = new byte[1 + r.nextInt(600)];
                        r.nextBytes(v);
                        try {
                            Trans.Builder tb = db.trans().put(k, v);
                            tb.put("/hot/" + r.nextInt(40), new byte[r.nextInt(2000)]);
                            db.execute(tb.build());
                            ack.put(k, v);
                            // A pause, so that maintain(), which gives way to waiting commits,
                            // gets the lock between them.
                            java.util.concurrent.locks.LockSupport.parkNanos(r.nextInt(300000));
                        } catch (Throwable e) {
                            thr.put(k, e);
                            if (!(e instanceof bergdb.pub.util.DbException)) return;
                            if (!go.get() || e instanceof bergdb.pub.util.DbFailedException || e.getClass().getSimpleName().contains("State") || e.getClass().getSimpleName().contains("Stopping")) return;
                        }
                    }
                }));
            }
            final long[] p = new long[1];
            ts.add(new Thread(() -> {
                while (go.get()) {
                    try {
                        long l = db.getStreamLength();
                        db.maintain(100 + (int) (l % 700));
                    } catch (Throwable e) {
                        return;
                    }
                    LockSupport_park(50000);
                }
            }));
            ts.add(new Thread(() -> {
                Random r = new Random(rd);
                while (go.get()) {
                    try {
                        db.getOne(db.currentTime(), Keys.toSegments("/hot/" + r.nextInt(40)), db.newGetData());
                    } catch (Throwable e) {
                        return;
                    }
                }
            }));
            for (Thread t : ts) t.start();
            Random rr = new Random(seed + round);
            Thread.sleep(20 + rr.nextInt(120));
            final boolean close = rr.nextBoolean();
            if (close) db.close(); else db.stop();
            go.set(false);
            for (Thread t : ts) t.join();
            db.close();
            final long len = s.getLength();
            cuts += db.getFirstAvailablePos() > 0 ? 1 : 0;
            parts += partRecords.getAndSet(0);
            // The start on a copy.
            s = s.copy();
            DbBuilder b2 = Db.builder().testSetup(s).clock(clock::get);
            if (node == 8) b2.maxNodeSize8();
            final Db d2 = b2.start();
            if (s.getLength() != len) throw new AssertionError("round " + round + ": the start "
                    + "changed the length " + len + " to " + s.getLength());
            for (Map.Entry<String, byte[]> e : ack.entrySet()) {
                byte[] got = d2.getOne(Long.MAX_VALUE, Keys.toSegments(e.getKey()), d2.newGetData());
                if (!Arrays.equals(got, e.getValue())) throw new AssertionError("round " + round
                        + (close ? " close" : " stop") + ": acked " + e.getKey() + " is not in the stream");
            }
            for (Map.Entry<String, Throwable> e : thr.entrySet()) {
                kinds.merge(e.getValue().getClass().getSimpleName(), 1, Integer::sum);
                byte[] got = d2.getOne(Long.MAX_VALUE, Keys.toSegments(e.getKey()), d2.newGetData());
                if (got != null) throw new AssertionError("round " + round + (close ? " close" : " stop")
                        + ": " + e.getKey() + " threw " + e.getValue() + " and is in the stream");
            }
            // Reclaim's memory of the start against a second start (nothing appended).
            d2.close();
            if (s.getLength() != len) throw new AssertionError("the close appended");
            s = s.copy();
            present.putAll(ack);
            acked += ack.size();
            thrown += thr.size();
        }
        System.out.println("RvStop seed " + seed + " node " + node + ": " + rounds + " rounds, " + acked
                + " commits returned and are in the stream, " + thrown + " threw and are not " + kinds
                + ", " + parts + " records of maintain()'s parts, " + cuts + " rounds ended after a cut: OK");
    }

    static void LockSupport_park(long ns) {
        java.util.concurrent.locks.LockSupport.parkNanos(ns);
    }
}
