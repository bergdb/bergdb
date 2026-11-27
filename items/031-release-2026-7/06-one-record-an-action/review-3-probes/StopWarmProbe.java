package bergdb.core;

import java.util.*;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.pub.util.Clock;
import bergdb.stream.CutStream;

/**
 * bergdb 031-06, review 3: what execute() throws when the database is stopped while writers
 * commit and an iteration runs, without the warm-up of a step's reads before the lock
 * (Db.TestHooks.stepWarmup false) and with it. ROUNDS rounds each: a database of 3,000 cold
 * values of 200 bytes, every object evicted after every transaction (so the warm-up reads
 * from the stream), four writers of single puts, and a close() after 1 to 6 ms. Prints the
 * classes of the exceptions that execute() threw, with their counts and one message each.
 *
 * Usage: java -ea -cp OUT:JAR bergdb.core.StopWarmProbe ROUNDS
 * Kind: functional (counts).
 */
public class StopWarmProbe {
    static final long SEC = Clock.UNITS_PER_SEC;
    static volatile boolean warmup;

    public static void main(String[] a) throws Exception {
        int rounds = Integer.parseInt(a[0]);
        Db.testHooks = new Db.TestHooks() {
            public boolean stepWarmup() {
                return warmup;
            }
            public void transExecuted(Db.ExecuteData x) {}
            public void valueNodeCreated(bergdb.dag.ValueNode vn, long[] key) {}
            public void nodeTouched(bergdb.dag.Node nd) {}
            public void nodeReplaced(bergdb.dag.Node nd) {}
        };
        for (int pass = 0; pass < 2; pass++) {
            warmup = (pass == 1) != Boolean.getBoolean("reverse");
            final Map<String, int[]> seen = new TreeMap<String, int[]>();
            final Map<String, String> example = new TreeMap<String, String>();
            long commits = 0;
            for (int round = 0; round < rounds; round++) {
                final AtomicLong clock = new AtomicLong(SEC);
                final Db db = Db.builder().testSetup(new CutStream()).clock(clock::get)
                        .evictionSchedule(Eviction.Schedule.EVERY, 1).start();
                db.setStartupDistance(2000);
                db.setRetainDuration(SEC);
                Random r = new Random(round);
                for (int i = 0; i < 3000; i += 50) {
                    clock.addAndGet(SEC / 10);
                    Trans.Builder tb = db.trans();
                    for (int j = i; j < i + 50; j++) {
                        tb.put(String.format("/c/%06d", j), new byte[200]);
                    }
                    db.execute(tb.build());
                }
                final AtomicLong done = new AtomicLong();
                List<Thread> ts = new ArrayList<Thread>();
                for (int w = 0; w < 4; w++) {
                    final Random rw = new Random(round * 10 + w);
                    Thread t = new Thread(() -> {
                        while (true) {
                            clock.addAndGet(SEC / 50);
                            try {
                                db.execute(db.trans().put("/h/" + rw.nextInt(8),
                                        new byte[2000]).build());
                                done.incrementAndGet();
                            } catch (Throwable e) {
                                String k = e.getClass().getName();
                                synchronized (seen) {
                                    seen.computeIfAbsent(k, z -> new int[1])[0]++;
                                    example.putIfAbsent(k, String.valueOf(e.getMessage()));
                                }
                                return;
                            }
                        }
                    });
                    ts.add(t);
                    t.start();
                }
                long end = System.nanoTime() + (1 + r.nextInt(6)) * 1000000L;
                while (System.nanoTime() < end) Thread.onSpinWait();
                db.close();
                for (Thread t : ts) t.join();
                commits += done.get();
            }
            System.out.println((warmup ? "with" : "without") + " the warm-up: " + rounds
                    + " rounds, " + commits + " commits before the stops; execute() threw:");
            for (Map.Entry<String, int[]> e : seen.entrySet()) {
                String m = example.get(e.getKey());
                System.out.println("  " + e.getValue()[0] + " x " + e.getKey() + ": "
                        + m.substring(0, Math.min(110, m.length())));
            }
        }
        Db.testHooks = null;
    }
}
