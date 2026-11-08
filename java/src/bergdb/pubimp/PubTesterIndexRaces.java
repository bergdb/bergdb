package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import bergdb.common.StringUtil;
import bergdb.core.Db;
import bergdb.core.KeyTransformation;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.DataFormatException;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.util.Job;

/**
 * The races of index maintenance (bergdb 020-10, sections 5 and 9.2), and the writes that
 * keep the indexes (015-46). A write at an object key and a change of the directory's index
 * definitions (a creation, an activation, a deletion) meet at each of four points:
 * <ul>
 * <li>in the write, after its read time R is fixed and before it reads the directory's index
 *     set S (IndexManager.WRITE_BEFORE_SET), and after it read S (WRITE_AFTER_SET): the
 *     definition's change runs there, in the writer's thread;</li>
 * <li>in the definition's change, under the index manager's lock, before its transaction
 *     commits and after it (DEFINITION_BEFORE and DEFINITION_AFTER): the write runs in
 *     another thread, which fixes its read time there and then waits for the lock.</li>
 * </ul>
 * For each, a put of an object, a put of a String and a delete; then the raw entries of the
 * index equal the index's function over the directory's values at the latest time, and after
 * a deletion there are none, also when an index of the name is created again (015-28, 015-43,
 * S2-F12). The tests run on the layout of 2026.3 (step I1); step I2 changes the layout.
 *
 * @author Frans Lundberg
 */
public class PubTesterIndexRaces {
    private PubTesterIndexRaces() {}

    /** An object with an indexed field: a Data Object (bergdb 020-09, section 3). */
    public static class Item {
        public long n;

        public Item() {}

        public Item(long n) {
            this.n = n;
        }
    }

    private static final String DIR = "/r/";
    private static final String KEY = "/r/k";
    private static final String OTHER = "/r/o";
    private static final String NAME = "i";

    enum Change { CREATE, ACTIVATE, DELETE }

    enum Write { OBJECT, STRING, DELETE }

    enum Point { WRITE_BEFORE_SET, WRITE_AFTER_SET, DEFINITION_BEFORE, DEFINITION_AFTER }

    // ======== The races (020-10, section 9.2) ========

    /** A creation (with its build) meets each write at each point. */
    @Nano
    public static void testRacesCreate() {
        runAll(Change.CREATE);
    }

    /** An activation meets each write at each point. */
    @Nano
    public static void testRacesActivate() {
        runAll(Change.ACTIVATE);
    }

    /** A deletion meets each write at each point; then the name is created again. */
    @Nano
    public static void testRacesDelete() {
        runAll(Change.DELETE);
    }

    private static void runAll(Change change) {
        List<String> faults = new ArrayList<>();
        for (Point point : Point.values()) {
            for (Write write : Write.values()) {
                try {
                    runCase(change, point, write);
                } catch (AssertionError | RuntimeException e) {
                    faults.add(change + " at " + point + ", " + write + ": " + e);
                }
            }
        }
        if (!faults.isEmpty()) {
            throw new AssertionError(faults.size() + " of 12 cases failed: "
                    + String.join("; ", faults));
        }
    }

    /**
     * One case: the directory holds KEY (an object of n = 1) and OTHER (n = 5); the change of
     * the index NAME on n and the write of KEY meet at the point; then the entries are
     * checked.
     */
    static void runCase(Change change, Point point, Write write) {
        Database database = Factory.database().memory().start();
        try {
            DatabaseImp d = (DatabaseImp) database;
            IndexManager m = d.getIndexManager();
            ConnectionImp c = (ConnectionImp) database.newConnection();

            // Before: for ACTIVATE an index in state creating whose entries the writes made;
            // for DELETE an active index, built.
            IndexManager.Index creating = null;
            if (change == Change.ACTIVATE) {
                creating = m.addIndex(c, NAME, new String[] {PubKeys.udir2idir(DIR)},
                        new FieldRef[][] {{new FieldRef("n")}}, new String[] {"long"});
            }
            c.w().put(KEY, new Item(1)).put(OTHER, new Item(5)).execute();
            if (change == Change.DELETE) {
                create(database).join();
            }
            if (creating != null || change == Change.DELETE) {
                checkEntries(d, "before");
            }

            final IndexManager.Index toActivate = creating;
            final Job[] jobs = new Job[1];
            final boolean[] fired = new boolean[1];
            final Throwable[] writerFault = new Throwable[1];
            Runnable doChange = () -> {
                switch (change) {
                case CREATE:
                    jobs[0] = create(database);
                    break;
                case ACTIVATE:
                    m.setIndexStateToActive(c, toActivate);
                    break;
                default:
                    jobs[0] = database.deleteIndex(NAME);
                    break;
                }
            };
            Connection w = database.newConnection();
            Runnable doWrite = () -> write(w, write);

            if (point == Point.WRITE_BEFORE_SET || point == Point.WRITE_AFTER_SET) {
                // The change runs in the writer's thread, at the writer's point; once.
                String at = point == Point.WRITE_BEFORE_SET ? IndexManager.WRITE_BEFORE_SET
                        : IndexManager.WRITE_AFTER_SET;
                m.testHook = p -> {
                    if (p.equals(at) && !fired[0]) {
                        fired[0] = true;
                        doChange.run();
                        if (jobs[0] != null) {
                            jobs[0].join();
                        }
                    }
                };
                doWrite.run();
                m.testHook = null;
                Assert.assertTrue("the write reached the point " + at, fired[0]);
            } else {
                // The write runs in another thread, which fixes its read time at the
                // definition's point, under the manager's lock, and then waits for the lock.
                String at = definitionPoint(change, point);
                CountDownLatch reached = new CountDownLatch(1);
                Thread[] writer = new Thread[1];
                m.testHook = p -> {
                    if (p.equals(IndexManager.WRITE_BEFORE_SET)) {
                        reached.countDown();
                    } else if (p.equals(at) && !fired[0]) {
                        fired[0] = true;
                        writer[0] = new Thread(() -> {
                            try {
                                doWrite.run();
                            } catch (Throwable e) {
                                writerFault[0] = e;
                            }
                        });
                        writer[0].start();
                        await(reached, "the write's point " + IndexManager.WRITE_BEFORE_SET);
                    }
                };
                doChange.run();
                Assert.assertTrue("the change reached the point " + at, fired[0]);
                join(writer[0]);
                m.testHook = null;
                if (writerFault[0] != null) {
                    throw new AssertionError("the write: " + writerFault[0], writerFault[0]);
                }
            }
            if (jobs[0] != null) {
                jobs[0].join();
            }

            // After: the entries are the function of the values at the latest time.
            if (change == Change.DELETE) {
                Assert.assertEquals("entries after the deletion", "[]",
                        rawEntries(d.getDb(), NAME).toString());
                create(database).join();            // S2-F12: a new index of the name
                checkEntries(d, "the new index of the name");
            } else {
                checkEntries(d, "after");
            }
        } finally {
            database.close();
        }
    }

    private static String definitionPoint(Change change, Point point) {
        String what = change == Change.CREATE ? "create" : change == Change.ACTIVATE
                ? "activate" : "delete";
        return (point == Point.DEFINITION_BEFORE ? IndexManager.DEFINITION_BEFORE
                : IndexManager.DEFINITION_AFTER) + what;
    }

    private static Job create(Database database) {
        return database.indexBuilder(NAME).type("long").dir(DIR).field("n").start();
    }

    private static void write(Connection w, Write write) {
        switch (write) {
        case OBJECT:
            w.w().put(KEY, new Item(2)).execute();
            break;
        case STRING:
            w.w().put(KEY, "text").execute();
            break;
        default:
            w.w().delete(KEY).execute();
            break;
        }
    }

    // ======== 015-46: every write at an object key keeps the indexes ========

    /**
     * 015-46 (020-10, section 5.1): a String or a byte[] put over an indexed object deletes
     * its entries, and an object put over a String or a byte[] puts its own, in w() and rw();
     * a byte[] that is a stored object is an object (020-10, 3.3); a delete after them.
     */
    @Nano
    public static void testStringOverObject() {
        Database database = Factory.database().memory().start();
        try {
            DatabaseImp d = (DatabaseImp) database;
            create(database).join();
            Connection c = database.newConnection();
            c.put(KEY, new Item(1));
            checkEntries(d, "an object");
            Assert.assertEquals(1, rawEntries(d.getDb(), NAME).size());

            c.put(KEY, "text");
            checkEntries(d, "a String over an object");
            Assert.assertEquals(0, rawEntries(d.getDb(), NAME).size());
            Assert.assertFalse("no object in the index",
                    c.useIndex(NAME, DbObject.class).objects().iterator().hasNext());

            c.put(KEY, new Item(2));
            checkEntries(d, "an object over a String");
            c.put(KEY, new byte[] {1, 2, 3});
            checkEntries(d, "a byte[] over an object");
            c.put(KEY, new Item(3));
            checkEntries(d, "an object over a byte[]");
            c.rw(env -> env.put(KEY, "text in rw()"));
            checkEntries(d, "a String over an object in rw()");
            c.rw(env -> env.put(KEY, new Item(4)));
            checkEntries(d, "an object over a String in rw()");

            byte[] stored = DbObject.toDbObject(new Item(7)).getBytes();
            c.put(KEY, stored);
            checkEntries(d, "a byte[] that is a stored object");
            Assert.assertEquals(1, rawEntries(d.getDb(), NAME).size());
            c.delete(KEY);
            checkEntries(d, "a delete");
            Assert.assertEquals(0, rawEntries(d.getDb(), NAME).size());

            // The last call on a key in a transaction wins (015-41).
            c.w().put(KEY, new Item(8)).put(KEY, "x").execute();
            checkEntries(d, "an object, then a String");
            c.w().put(KEY, "y").put(KEY, new Item(9)).execute();
            checkEntries(d, "a String, then an object");
            Assert.assertEquals(9, c.get(KEY, Item.class).n);
            c.w().put(KEY, new Item(10)).delete(KEY).put(KEY, new byte[] {5}).execute();
            checkEntries(d, "an object, a delete, a byte[]");
            Assert.assertArrayEquals(new byte[] {5}, c.get(KEY, byte[].class));

            // A key with a suffix keeps no index, whatever its value.
            c.put("/r/k.txt", "t");
            c.put("/r/k.txt", stored);
            checkEntries(d, "a key with a suffix");
        } finally {
            database.close();
        }
    }

    /**
     * An object of format 1 (2026.3's: "bergo" and the version 1) at an object key: a write
     * over it in an indexed directory, and a byte[] put of it there, are refused with
     * DataFormatException naming the key (020-08, step 3; 020-10, section 5.1, step 4); in a
     * directory without an index the byte[] is stored.
     */
    @Nano
    public static void testFormat1InIndexedDirectory() {
        Database database = Factory.database().memory().start();
        try {
            DatabaseImp d = (DatabaseImp) database;
            Connection c = database.newConnection();
            byte[] format1 = {'b', 'e', 'r', 'g', 'o', 1, 0, 0};
            c.put("/u/k", format1);
            Assert.assertArrayEquals(format1, c.get("/u/k", byte[].class));

            create(database).join();
            try {
                c.put(KEY, format1);
                throw new AssertionError("a byte[] of format 1 put in an indexed directory");
            } catch (DataFormatException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("/dr/-k"));
            }
            Assert.assertNull(c.get(KEY, byte[].class));

            // Written through the Core, as an old database holds it; a write over it.
            Db db = d.getDb();
            db.execute(db.trans().put(Keys.toBytes(PubKeys.u2i(KEY)), format1).build());
            for (Runnable r : new Runnable[] {() -> c.put(KEY, new Item(1)),
                    () -> c.put(KEY, "s"), () -> c.delete(KEY)}) {
                try {
                    r.run();
                    throw new AssertionError("a write over an object of format 1");
                } catch (DataFormatException e) {
                    Assert.assertTrue(e.getMessage(), e.getMessage().contains("/dr/-k"));
                }
            }
            Assert.assertArrayEquals(format1, c.get(KEY, byte[].class));
        } finally {
            database.close();
        }
    }

    /**
     * 015-28: a w() of a String at an object key in a directory without an index reads no
     * value, but has a read time and the directory's hash: an index created after its read
     * time and before its commit makes it run again (020-10, section 5.1, steps 1 and 2).
     */
    @Nano
    public static void testWriteWithoutIndexRunsAgainAfterCreation() {
        Database database = Factory.database().memory().start();
        try {
            DatabaseImp d = (DatabaseImp) database;
            IndexManager m = d.getIndexManager();
            Connection c = database.newConnection();
            c.put(KEY, new Item(1));
            int[] runs = new int[1];
            m.testHook = p -> {
                if (p.equals(IndexManager.WRITE_AFTER_SET) && runs[0]++ == 0) {
                    create(database).join();
                }
            };
            c.w().put(KEY, new Item(2)).execute();
            m.testHook = null;
            Assert.assertEquals("the write's runs", 2, runs[0]);
            checkEntries(d, "after");
        } finally {
            database.close();
        }
    }

    // ======== Helpers ========

    /**
     * The raw entries of the index NAME equal its function over the values of DIR at the
     * latest time (020-10, section 9.2), computed apart from the write path: each value that
     * is a stored object gives the entries of RwEnvironmentImp.setIndexEntry.
     */
    static void checkEntries(DatabaseImp d, String what) {
        IndexManager.Index index = d.getIndexManager().getIndex(NAME);
        Assert.assertTrue(what + ": the index", index != null);
        Db db = d.getDb();
        TreeSet<String> want = new TreeSet<>();
        for (String ukey : new String[] {KEY, OTHER}) {
            String ikey = PubKeys.u2i(ukey);
            byte[] value = db.getOne(Long.MAX_VALUE, Keys.toSegments(ikey), db.newGetData());
            if (value != null && ObjectFormat.isStoredObject(value)) {
                RwEnvironmentImp.setIndexEntry(new DbObject(value),
                        ikey.substring(ikey.lastIndexOf('/') + 1), index, 0,
                        new RwEnvironmentImp.IndexSetter() {
                            public void setIndexKey(byte[] key, KeyTransformation kt) {
                                want.add(StringUtil.toHex(key));
                            }
                        }, false);
            }
        }
        Assert.assertEquals(what + ": the index's entries", want.toString(),
                rawEntries(db, NAME).toString());
    }

    /** The keys under the index's entries' directory at the latest time, in hexadecimal. */
    static TreeSet<String> rawEntries(Db db, String name) {
        final byte[] dir = IndexManager.getIndexDbDirAsBytes(name);
        final long[] dirKey = Keys.toSegments(dir);
        TreeSet<String> keys = new TreeSet<>();
        GetMany g = db.newGetMany();
        g.startKey = dirKey;
        g.inclusive = false;
        g.lookupTime = Long.MAX_VALUE;
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                return Keys.isPrefix(dirKey, kvt.key) ? GetMany.StopCondition.ADD
                        : GetMany.StopCondition.STOP;
            }

            public void eod() {}
        };
        db.getMany(g);
        for (Kvt kvt : g.result) {
            keys.add(StringUtil.toHex(Keys.toBytes(kvt.key)));
        }
        return keys;
    }

    private static void await(CountDownLatch latch, String what) {
        try {
            if (!latch.await(2, TimeUnit.SECONDS)) {
                throw new AssertionError(what + " not reached in 2 s");
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError(e);
        }
    }

    private static void join(Thread t) {
        if (t == null) {
            return;
        }
        try {
            t.join(5000);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError(e);
        }
        Assert.assertFalse("the writer's thread ended", t.isAlive());
    }
}
