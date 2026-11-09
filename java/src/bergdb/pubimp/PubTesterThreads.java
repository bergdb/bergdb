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
 * a hurried service; 021-21, 021-22): an RwEnvironment used by several threads in its action
 * and after it, a Connection, a WBuilder and an iterator shared by threads, and a Data Object
 * constructor that reads through the connection of its get. Misuse ends in an exception to
 * the caller, never in a wrong value, a lost write or a failed database.
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

    /** The gates of Slow's constructor, set by a test, null else. */
    static volatile CountDownLatch slowInside;
    static volatile CountDownLatch slowRelease;

    /**
     * A Data Object whose constructor, when a test has set the gates, says that it runs and
     * waits for the test: a thread then stays in the call that converts the value.
     */
    public static class Slow {
        public long n;

        public Slow() {
            CountDownLatch inside = slowInside;
            CountDownLatch release = slowRelease;
            if (inside != null && release != null) {
                inside.countDown();
                await(release);
            }
        }
    }

    /** The connection that Configured's constructor reads through, set by a test. */
    static volatile Connection configuredConnection;

    /** U11-5: a Data Object whose constructor reads its configuration through a connection. */
    public static class Configured {
        public long n;
        public String config;

        public Configured() {
            Connection c = configuredConnection;
            config = c == null ? null : c.get("/cfg/a.txt", String.class);
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

    // ======== U11-2: a Connection shared by threads ========

    /**
     * U11-2 (bergdb 021-22): while a thread is in a call of a connection, a call of another
     * thread on it throws IllegalStateException, changes nothing, and the database goes on;
     * once the first call has returned, the other thread may use the connection. Before the
     * fix the calls ran at once and shared the connection's GetData: reads returned another
     * key's value, and the database failed.
     */
    @Nano
    public static void testConnectionInACallOfAnotherThread() throws Exception {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.newConnection();
            c.put("/s/x.txt", "x");
            Slow slow = new Slow();
            slow.n = 5;
            c.put("/s/slow", slow);
            final CountDownLatch inside = new CountDownLatch(1);
            final CountDownLatch release = new CountDownLatch(1);
            slowInside = inside;
            slowRelease = release;
            final AtomicReference<Object> got = new AtomicReference<>();
            Thread a = new Thread(() -> got.set(c.get("/s/slow", Slow.class)));
            try {
                a.start();
                Assert.assertTrue(inside.await(10, TimeUnit.SECONDS));

                expectIllegalState(() -> c.get("/s/x.txt", String.class));
                expectIllegalState(() -> c.exists("/s/x.txt"));
                expectIllegalState(() -> c.transactionInfo());
                expectIllegalState(() -> c.put("/s/y.txt", "y"));
                expectIllegalState(() -> c.delete("/s/x.txt"));
                expectIllegalState(() -> c.w().put("/s/y.txt", "y").execute());
                expectIllegalState(() -> c.rw(env -> env.put("/s/y.txt", "y")));
                expectIllegalState(() -> c.usePrimary(String.class));
                expectIllegalState(() -> c.setLookupTime(Time.MAX));
                expectIllegalState(() -> c.freezeLookupTime());
                expectIllegalState(() -> c.sync());
            } finally {
                release.countDown();
                a.join(10_000);
                slowInside = null;
                slowRelease = null;
            }
            Assert.assertEquals(5L, ((Slow) got.get()).n);
            Assert.assertNull(c.get("/s/y.txt", String.class));
            Assert.assertEquals("x", c.get("/s/x.txt", String.class));
            c.put("/s/z.txt", "z");
            Assert.assertEquals("z", db.connection().get("/s/z.txt", String.class));
        }
    }

    /**
     * U11-2 (bergdb 021-22): 4 threads reading random keys through one connection: each
     * get returns the key's value or throws IllegalStateException; none returns another
     * value, and the database goes on. Before the fix: wrong values within a few hundred
     * gets, then DbFailedException (020-24-11, SharedReads).
     */
    @Nano
    public static void testConnectionSharedByReaders() throws Exception {
        try (Database db = Factory.database().memory().start()) {
            final int keys = 2000;
            WBuilder w = db.connection().w();
            for (int k = 0; k < keys; k++) {
                w.put("/k/k" + k + ".txt", "value of k" + k);
            }
            w.execute();
            final Connection shared = db.newConnection();
            final AtomicInteger wrong = new AtomicInteger();
            final AtomicInteger refused = new AtomicInteger();
            final AtomicInteger right = new AtomicInteger();
            final AtomicReference<Throwable> other = new AtomicReference<>();
            inThreads(4, i -> {
                java.util.Random random = new java.util.Random(i);
                for (int n = 0; n < 5000 && other.get() == null; n++) {
                    int k = random.nextInt(keys);
                    try {
                        String v = shared.get("/k/k" + k + ".txt", String.class);
                        if (("value of k" + k).equals(v)) {
                            right.incrementAndGet();
                        } else {
                            wrong.incrementAndGet();
                        }
                    } catch (IllegalStateException e) {
                        refused.incrementAndGet();
                    } catch (Throwable e) {
                        other.compareAndSet(null, e);
                    }
                }
            });
            Assert.assertTrue("another throwable: " + other.get(), other.get() == null);
            Assert.assertEquals("wrong values", 0, wrong.get());
            Assert.assertEquals(20000, right.get() + refused.get());
            Assert.assertEquals("value of k7", db.newConnection().get("/k/k7.txt", String.class));
        }
    }

    /**
     * U11-2 (bergdb 021-22): calls inside a call of the same thread are not refused: a
     * Data Object constructor reads and writes through the connection of its get.
     */
    @Nano
    public static void testConnectionInACallOfTheSameThread() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/cfg/a.txt", "A");
            c.put("/con/x", new Configured());
            configuredConnection = c;
            try {
                Configured got = c.get("/con/x", Configured.class);
                Assert.assertEquals("A", got.config);
                c.rw(env -> {
                    Assert.assertEquals("A", c.get("/cfg/a.txt", String.class));
                    c.put("/cfg/b.txt", "B");
                    env.put("/cfg/c.txt", "C");
                });
            } finally {
                configuredConnection = null;
            }
            Assert.assertEquals("B", c.get("/cfg/b.txt", String.class));
            Assert.assertEquals("C", c.get("/cfg/c.txt", String.class));
        }
    }

    // ======== U11-6: a WBuilder and an iterator shared by threads ========

    /**
     * U11-6 (bergdb 021-22): 4 threads putting into one WBuilder, then execute(): every put
     * is written. Before the fix the builder's HashMaps lost some (3,809 of 4,000 keys in
     * 020-24-11's H1), or a thread spun in a broken HashMap.
     */
    @Nano
    public static void testWBuilderSharedByThreads() throws Exception {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            for (int round = 0; round < 10; round++) {
                final int r = round;
                final WBuilder w = c.w();
                inThreads(4, i -> {
                    for (int k = i; k < 1000; k += 4) {
                        w.put("/w/r" + r + "-k" + k + ".txt", "v" + k);
                    }
                });
                w.execute();
            }
            int missing = 0;
            for (int round = 0; round < 10; round++) {
                for (int k = 0; k < 1000; k++) {
                    if (!("v" + k).equals(c.get("/w/r" + round + "-k" + k + ".txt",
                            String.class))) {
                        missing++;
                    }
                }
            }
            Assert.assertEquals("missing", 0, missing);
        }
    }

    /**
     * U11-6 (bergdb 021-22): while a thread is in next() of an iterator, a call of another
     * thread on the iterator throws IllegalStateException; the first goes on, and the
     * iterator gives every value once. Before the fix both ran: values were skipped or
     * given twice, and internal exceptions came (020-24-11, SharedIterator).
     */
    @Nano
    public static void testIteratorInACallOfAnotherThread() throws Exception {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.newConnection();
            for (int k = 0; k < 3; k++) {
                Slow s = new Slow();
                s.n = k;
                c.put("/i/k" + k, s);
            }
            final Iterator<Slow> it = c.usePrimary(Slow.class).dir("/i/").objects().iterator();
            final CountDownLatch inside = new CountDownLatch(1);
            final CountDownLatch release = new CountDownLatch(1);
            slowInside = inside;
            slowRelease = release;
            final AtomicReference<Slow> got = new AtomicReference<>();
            Thread a = new Thread(() -> got.set(it.next()));
            try {
                a.start();
                Assert.assertTrue(inside.await(10, TimeUnit.SECONDS));
                expectIllegalState(() -> it.hasNext());
                expectIllegalState(() -> it.next());
            } finally {
                slowInside = null;
                slowRelease = null;
                release.countDown();
                a.join(10_000);
            }
            Assert.assertEquals(0L, got.get().n);
            Assert.assertEquals(1L, it.next().n);
            Assert.assertEquals(2L, it.next().n);
            Assert.assertFalse(it.hasNext());
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
