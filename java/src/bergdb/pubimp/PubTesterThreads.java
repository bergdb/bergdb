package bergdb.pubimp;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.RwEnvironment;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.WBuilder;

/**
 * Threads that share what BergDB keeps per connection or per transaction (bergdb 020-24-11,
 * a hurried service; 021-21): an RwEnvironment used by several threads in its action and
 * after it. Misuse ends in an exception to the caller, never in a wrong value, a lost write
 * or a failed database.
 *
 * @author Frans Lundberg
 */
public class PubTesterThreads {

    // ======== Classes ========

    /** An object of the index's directory. */
    public static class Obj {
        public long n;

        public Obj() {}

        public Obj(long n) {
            this.n = n;
        }
    }

    // ======== U11-1: an RwEnvironment used by several threads in its action ========

    /**
     * U11-1 (bergdb 021-21): the action's reads made by 8 threads at once, each reading the
     * 32 keys, read the right values, and the database goes on. Before the fix the threads
     * shared the environment's GetData, read set and maps unsynchronized: reads gave
     * another key's value, and the database failed ("Bad value pointer -1").
     */
    @Nano
    public static void testEnvironmentReadByThreads() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            WBuilder w = c.w();
            for (int k = 0; k < 32; k++) {
                w.put("/p/k" + k + ".txt", Integer.toString(k));
            }
            w.execute();
            for (int round = 0; round < 20; round++) {
                Transaction t = c.rw(env -> {
                    final AtomicInteger bad = new AtomicInteger();
                    inThreads(8, i -> {
                        for (int r = 0; r < 4; r++) {
                            for (int k = 0; k < 32; k++) {
                                String v = env.get("/p/k" + k + ".txt", String.class);
                                if (!Integer.toString(k).equals(v)) {
                                    bad.incrementAndGet();
                                }
                            }
                        }
                    });
                    env.setOutput("bad", (long) bad.get());
                });
                Assert.assertEquals("round " + round, 0L, (long) t.getOutput("bad", Long.class));
            }
            Assert.assertEquals("31", c.get("/p/k31.txt", String.class));
        }
    }

    /**
     * U11-1 (bergdb 021-21): puts made by 8 threads at once in the action are all committed.
     * Before the fix the environment's HashMaps lost some (546 of 6,000 keys in 020-24-11's
     * ParallelEnv), and a transaction that returned normally committed only part of what its
     * action put.
     */
    @Nano
    public static void testEnvironmentWrittenByThreads() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            for (int round = 0; round < 30; round++) {
                final int r = round;
                c.rw(env -> {
                    inThreads(8, i -> {
                        for (int k = i; k < 200; k += 8) {
                            env.put("/q/r" + r + "-k" + k + ".txt", "v" + k);
                        }
                        env.setOutput("thread" + i, "done");
                    });
                });
            }
            int missing = 0;
            for (int round = 0; round < 30; round++) {
                for (int k = 0; k < 200; k++) {
                    String v = c.get("/q/r" + round + "-k" + k + ".txt", String.class);
                    if (!("v" + k).equals(v)) {
                        missing++;
                    }
                }
            }
            Assert.assertEquals("keys missing or wrong", 0, missing);
        }
    }

    // ======== U11-3: the environment after its action ========

    /**
     * U11-3 (bergdb 021-21): the environment is closed when the action returns, before the
     * commit: a put through it while the transaction computes its index entries throws
     * IllegalStateException, and nothing of it is written; the commit holds what the action
     * wrote, with its entries. Before the fix the environment was closed only after the
     * commit: the late put was taken, and an object put after the index set was read was
     * committed without its index entry (020-24-11, LeakedEnvIndex).
     */
    @Nano
    public static void testEnvironmentClosedAtTheActionsReturn() {
        try (Database db = Factory.database().memory().start()) {
            final DatabaseImp d = (DatabaseImp) db;
            final Connection c = db.connection();
            db.indexBuilder("o-n").dir("/o/").type("long").field("n").start().join();
            final AtomicReference<RwEnvironment> leaked = new AtomicReference<>();
            final AtomicReference<Throwable> late = new AtomicReference<>();
            final AtomicInteger calls = new AtomicInteger();
            d.getIndexManager().testHook = point -> {
                if (point.equals(IndexManager.WRITE_AFTER_SET) && leaked.get() != null
                        && calls.getAndIncrement() == 0) {
                    try {
                        leaked.get().put("/o/late", new Obj(7));
                    } catch (Throwable e) {
                        late.set(e);
                    }
                }
            };
            try {
                c.rw(env -> {
                    leaked.set(env);
                    env.put("/o/a", new Obj(1));
                });
            } finally {
                d.getIndexManager().testHook = null;
            }
            Assert.assertTrue("the late put threw " + late.get(),
                    late.get() instanceof IllegalStateException);
            Assert.assertNull(c.get("/o/late", Obj.class));
            Assert.assertEquals(1L, c.get("/o/a", Obj.class).n);
            int primary = 0;
            for (Kv<Obj> kv : c.usePrimary(Obj.class).dir("/o/").kvs()) {
                primary++;
            }
            int index = 0;
            for (Obj o : c.useIndex("o-n", Obj.class).objects()) {
                index++;
            }
            Assert.assertEquals("primary", 1, primary);
            Assert.assertEquals("index", 1, index);

            // Every call of a closed environment throws, from any thread.
            final RwEnvironment env = leaked.get();
            expectIllegalState(() -> env.get("/o/a", Obj.class));
            expectIllegalState(() -> env.exists("/o/a"));
            expectIllegalState(() -> env.put("/o/b", new Obj(2)));
            expectIllegalState(() -> env.delete("/o/a"));
            expectIllegalState(() -> env.setOutput("x", "y"));
        }
    }

    /**
     * U11-3 (bergdb 021-21): each run of an action has an environment of its own; one that
     * a run leaked is closed when that run returns, and a put through it in a later run
     * throws, as it is not that run's. Before the fix the runs shared one environment, and
     * a thread left by the first run put into the second.
     */
    @Nano
    public static void testEnvironmentOfAnEarlierRun() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            final Connection other = db.newConnection();
            c.put("/r/x.txt", "0");
            final List<RwEnvironment> envs = new ArrayList<>();
            final AtomicReference<Throwable> late = new AtomicReference<>();
            Transaction t = c.rw(env -> {
                envs.add(env);
                env.get("/r/x.txt", String.class);
                if (envs.size() == 1) {
                    other.put("/r/x.txt", "1");         // a conflict: the action runs again
                } else {
                    try {
                        envs.get(0).put("/r/late.txt", "late");
                    } catch (Throwable e) {
                        late.set(e);
                    }
                    env.put("/r/y.txt", "y");
                }
            });
            Assert.assertEquals(2, envs.size());
            Assert.assertTrue(envs.get(0) != envs.get(1));
            Assert.assertTrue("late: " + late.get(), late.get() instanceof IllegalStateException);
            Assert.assertNull(c.get("/r/late.txt", String.class));
            Assert.assertEquals("y", c.get("/r/y.txt", String.class));
            Assert.assertTrue(t != null);
        }
    }

    // ======== Helpers ========

    interface Body {
        void run(int i) throws Exception;
    }

    /** Runs body(0) to body(n - 1) in n threads at once, and throws the first's throwable. */
    static void inThreads(int n, Body body) {
        final CountDownLatch start = new CountDownLatch(1);
        final AtomicReference<Throwable> thrown = new AtomicReference<>();
        Thread[] threads = new Thread[n];
        for (int i = 0; i < n; i++) {
            final int index = i;
            threads[i] = new Thread(() -> {
                try {
                    await(start);
                    body.run(index);
                } catch (Throwable e) {
                    thrown.compareAndSet(null, e);
                }
            });
            threads[i].start();
        }
        start.countDown();
        for (Thread t : threads) {
            try {
                t.join();
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
        Throwable e = thrown.get();
        if (e instanceof RuntimeException) {
            throw (RuntimeException) e;
        } else if (e instanceof Error) {
            throw (Error) e;
        } else if (e != null) {
            throw new RuntimeException(e);
        }
    }

    interface Call {
        void run() throws Exception;
    }

    static void expectIllegalState(Call call) {
        try {
            call.run();
        } catch (IllegalStateException e) {
            return;
        } catch (Exception e) {
            throw new AssertionError("Expected IllegalStateException, got " + e, e);
        }
        throw new AssertionError("Expected IllegalStateException, the call returned");
    }

    static void await(CountDownLatch latch) {
        try {
            if (!latch.await(10, TimeUnit.SECONDS)) {
                throw new AssertionError("a latch timed out");
            }
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    static void sleep(long ms) {
        try {
            Thread.sleep(ms);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }
}
