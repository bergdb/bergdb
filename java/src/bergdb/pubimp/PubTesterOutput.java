package bergdb.pubimp;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import bergdb.common.EventToWaitFor;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.RwEnvironment;
import bergdb.pub.Transaction;

/**
 * Tests the outputs of transactions, RwEnvironment.setOutput() and Transaction.getOutput(),
 * and that an RwEnvironment is valid only while its action runs (bergdb 005-12).
 */
public class PubTesterOutput {

    public static class Item {
        public String key;

        public Item() {}

        public Item(String key) {
            this.key = key;
        }
    }

    private static class Abort extends RuntimeException {
        private static final long serialVersionUID = 1L;
    }

    @Nano
    public static void testOutputs() {
        Database db = Factory.database().memory().start();
        Connection c = db.connection();

        Transaction t = c.rw(new Action() {
            public void run(RwEnvironment env) {
                env.setOutput("a", "first");
                env.setOutput("b", 5L);
                env.setOutput("a", "second");
                env.put("/k", "v");
            }
        });

        Assert.assertEquals("second", t.getOutput("a", String.class));
        Assert.assertEquals(5L, (long) t.getOutput("b", Long.class));
        Assert.assertEquals(5L, t.getOutput("b", Number.class).longValue());
        Assert.assertEquals("second", t.getOutput("a", Object.class));
        Assert.assertEquals("v", c.get("/k", String.class));
        db.stop();
    }

    @Nano
    public static void testMissingOutput() {
        Database db = Factory.database().memory().start();
        Connection c = db.connection();

        Transaction t = c.rw(new Action() {
            public void run(RwEnvironment env) {
                env.setOutput("a", "x");
            }
        });
        Assert.assertNull(t.getOutput("b", String.class));
        Assert.assertNull(t.getOutput("A", String.class));

        Transaction none = c.rw(new Action() {
            public void run(RwEnvironment env) {
                env.put("/k", "v");
            }
        });
        Assert.assertNull(none.getOutput("a", String.class));

        // W-transactions have no outputs.
        Assert.assertNull(c.put("/k", "v2").getOutput("a", String.class));
        Assert.assertNull(c.delete("/k").getOutput("a", String.class));
        Assert.assertNull(c.w().put("/k", "v3").execute().getOutput("a", Object.class));
        Assert.assertNull(c.w().put("/items/a", new Item("/items/a")).execute()
                .getOutput("a", Object.class));
        db.stop();
    }

    @Nano
    public static void testRefused() {
        Database db = Factory.database().memory().start();
        Connection c = db.connection();

        assertSetOutputRefused(c, null, "v");
        assertSetOutputRefused(c, "", "v");
        assertSetOutputRefused(c, "a", null);
        Assert.assertNull(c.get("/refused", String.class));       // Nothing was committed.

        Transaction rw = c.rw(new Action() {
            public void run(RwEnvironment env) {
                env.setOutput("a", "x");
            }
        });
        Transaction w = c.put("/k", "v");

        for (Transaction t : new Transaction[] {rw, w}) {
            assertGetOutputRefused(t, null, String.class);
            assertGetOutputRefused(t, "", String.class);
            assertGetOutputRefused(t, "a", null);
        }
        db.stop();
    }

    private static void assertSetOutputRefused(Connection c, final String name,
            final Object value) {
        try {
            c.rw(new Action() {
                public void run(RwEnvironment env) {
                    env.put("/refused", "v");
                    env.setOutput(name, value);
                }
            });
            throw new AssertionError("no exception for name " + name + ", value " + value);
        } catch (IllegalArgumentException e) {
            // Expected.
        }
    }

    private static void assertGetOutputRefused(Transaction t, String name, Class<?> clazz) {
        try {
            t.getOutput(name, clazz);
            throw new AssertionError("no exception for name " + name + ", class " + clazz);
        } catch (IllegalArgumentException e) {
            // Expected.
        }
    }

    @Nano
    public static void testWrongClass() {
        Database db = Factory.database().memory().start();
        Connection c = db.connection();

        Transaction t = c.rw(new Action() {
            public void run(RwEnvironment env) {
                env.setOutput("balance", 100L);
            }
        });

        try {
            t.getOutput("balance", String.class);
            throw new AssertionError("no exception");
        } catch (ClassCastException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("'balance'")
                    && e.getMessage().contains("java.lang.Long"));
        }

        try {
            t.getOutput("balance", long.class);         // Boxed by setOutput(): Long.class.
            throw new AssertionError("no exception");
        } catch (ClassCastException e) {
            // Expected.
        }
        db.stop();
    }

    /**
     * An action that runs again: the caller gets the outputs of the run that committed only.
     * The first run reads "value1" and sets the output "first"; another connection then
     * changes the key, so the action runs again, reads "value1B" and sets "second" instead.
     */
    @Nano
    public static void testRerun() throws InterruptedException {
        Database db = Factory.database().memory().start();
        final Connection c1 = db.newConnection();
            // The other thread's; it was db.connection(), which this thread uses below: the
            // threads shared it (bergdb 021-22).
        c1.put("/key1", "value1");

        final EventToWaitFor readDone = new EventToWaitFor();
        final EventToWaitFor keyChanged = new EventToWaitFor();
        final Transaction[] result = new Transaction[1];

        Thread thread = new Thread(new Runnable() {
            public void run() {
                result[0] = c1.rw(new Action() {
                    public void run(RwEnvironment env) {
                        String value = env.get("/key1", String.class);
                        env.setOutput(value.equals("value1") ? "first" : "second", value);
                        env.setOutput("value", value);
                        readDone.happened();
                        keyChanged.waitForEvent();
                        env.put("/copy", value);
                    }
                });
            }
        });
        thread.start();

        readDone.waitForEvent();
        db.connection().put("/key1", "value1B");
        keyChanged.happened();
        thread.join();

        Transaction t = result[0];
        Assert.assertEquals(2, ((RwTransaction) t).getRunCount());
        Assert.assertNull(t.getOutput("first", String.class));
        Assert.assertEquals("value1B", t.getOutput("second", String.class));
        Assert.assertEquals("value1B", t.getOutput("value", String.class));
        Assert.assertEquals("value1B", c1.get("/copy", String.class));
        db.stop();
    }

    /**
     * Threads that increment one counter make each other's actions run again. Each action
     * sets the value it wrote as an output, and each caller gets the value of its committed
     * run: the outputs are 1 to n, each once.
     */
    @Nano
    public static void testThreads() throws InterruptedException {
        final int threadCount = 4;
        final int perThread = 25;
        final Database db = Factory.database().memory().start();
        db.connection().put("/counter", "0");
        final List<Long> outputs = Collections.synchronizedList(new ArrayList<Long>());

        Thread[] threads = new Thread[threadCount];
        for (int i = 0; i < threadCount; i++) {
            threads[i] = new Thread(new Runnable() {
                public void run() {
                    Connection c = db.connection();
                    for (int j = 0; j < perThread; j++) {
                        Transaction t = c.rw(new Action() {
                            public void run(RwEnvironment env) {
                                long value = Long.parseLong(env.get("/counter", String.class));
                                env.put("/counter", Long.toString(value + 1));
                                env.setOutput("value", value + 1);
                            }
                        });
                        outputs.add(t.getOutput("value", Long.class));
                    }
                }
            });
            threads[i].start();
        }

        for (Thread thread : threads) {
            thread.join();
        }

        int n = threadCount * perThread;
        Assert.assertEquals(n, outputs.size());
        boolean[] seen = new boolean[n + 1];
        for (long value : outputs) {
            Assert.assertTrue("value " + value, value >= 1 && value <= n && !seen[(int) value]);
            seen[(int) value] = true;
        }
        Assert.assertEquals(Long.toString(n), db.connection().get("/counter", String.class));
        db.stop();
    }

    /**
     * An action that keeps its environment cannot use it after the run: not to change the
     * outputs of the committed transaction, nor to put, delete or read. Also when the action
     * threw.
     */
    @Nano
    public static void testEnvironmentAfterRun() {
        Database db = Factory.database().memory().start();
        Connection c = db.connection();
        final RwEnvironment[] kept = new RwEnvironment[2];

        Transaction t = c.rw(new Action() {
            public void run(RwEnvironment env) {
                kept[0] = env;
                env.setOutput("a", "x");
            }
        });

        try {
            c.rw(new Action() {
                public void run(RwEnvironment env) {
                    kept[1] = env;
                    throw new Abort();
                }
            });
            throw new AssertionError("no exception");
        } catch (Abort e) {
            // Expected.
        }

        for (RwEnvironment env : kept) {
            for (int i = 0; i < 6; i++) {
                try {
                    switch (i) {
                    case 0: env.setOutput("a", "y"); break;
                    case 1: env.put("/k", "v"); break;
                    case 2: env.put("/items/b", new Item("/items/b")); break;
                    case 3: env.delete("/k"); break;
                    case 4: env.get("/k", String.class); break;
                    default: env.exists("/k"); break;
                    }
                    throw new AssertionError("no exception, case " + i);
                } catch (IllegalStateException e) {
                    // Expected.
                }
            }
        }

        Assert.assertEquals("x", t.getOutput("a", String.class));
        Assert.assertNull(c.get("/k", String.class));
        Assert.assertNull(c.get("/items/b", Item.class));
        db.stop();
    }
}
