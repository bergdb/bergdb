package bergdb.pubimp;

import java.util.TimeZone;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.DataFormatException;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.ReadInterface;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.WBuilder;
import bergdb.pub.util.BadFormatException;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DatabaseMissingException;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.IndexBuildException;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.storage.StreamFormatException;
import bergdb.stream.MemoryStream;

/**
 * The Pub API's Javadoc checked against its behaviour, promise by promise, for the classes
 * that bergdb 020-19 left (bergdb 020-25): WBuilder, RwEnvironment, ReadInterface, Action,
 * Transaction, Factory, DatabaseBuilder, Time, Duration, TestClock, Clock and the
 * exceptions; CryptoKey's tests are internal since 2026.4, which has no encryption in its
 * API (bergdb 020-28). Each test names the class and the promise it shows; the promises that other
 * testers show are listed in 020-25, section 3.
 *
 * @author Frans Lundberg
 */
public class PubTesterJavadocRest {

    /** 'call' throws an exception of the class 'expected'; returns it. */
    private static <T extends Throwable> T assertThrows(String what, Class<T> expected,
            Runnable call) {
        return PubTesterJavadoc.assertThrows(what, expected, call);
    }

    /** Not a Data Object: a class of the Java platform. */
    private static final Class<?> NOT_A_DATA_OBJECT = Thread.class;


    // ======== WBuilder, Transaction ========

    /**
     * WBuilder: its puts and deletes are one transaction, all of them at its time and none
     * before it; execute() returns when it has committed, so another connection reads it
     * at once; a delete of a key without an entry has no effect; a byte[] is copied at the
     * put, so a change of the array before execute() is not stored; put() refuses an object
     * at a key with a suffix other than ".obj" ("Bad key"), a null value, and a null or
     * invalid key, at once, and delete() a null or invalid key; a refused call spoils its
     * builder, whose execute() then throws IllegalStateException (bergdb 024-26, U26-5;
     * 024-27), so each refused call has a builder of its own; of several puts and deletes
     * of one key, the last one counts. Transaction: a
     * w-transaction has no outputs, null for every name; getOutput() refuses a null or empty
     * name and a null class.
     */
    @Nano
    public static void testWBuilderOneTransaction() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/w/b.txt", "b");
            byte[] bytes = {1, 2, 3};
            WBuilder w = c.w().put("/w/a.txt", "a").delete("/w/b.txt").put("/w/c.bin", bytes)
                    .delete("/w/none.txt");
            bytes[0] = 9;
            final Transaction t = w.execute();

            Connection other = db.newConnection();
            Assert.assertEquals("a", other.get("/w/a.txt", String.class));
            Assert.assertNull(other.get("/w/b.txt", String.class));
            Assert.assertEquals(1, other.get("/w/c.bin", byte[].class)[0]);
            Assert.assertFalse(other.exists("/w/none.txt"));
            other.setLookupTime(Time.units(t.getTime().units() - 1));
            Assert.assertNull(other.get("/w/a.txt", String.class));
            Assert.assertEquals("b", other.get("/w/b.txt", String.class));
            Assert.assertNull(other.get("/w/c.bin", byte[].class));
            other.setLookupTime(t.getTime());
            Assert.assertEquals("a", other.get("/w/a.txt", String.class));
            Assert.assertNull(other.get("/w/b.txt", String.class));

            Assert.assertNull(t.getOutput("x", Object.class));
            assertThrows("null name", IllegalArgumentException.class,
                    () -> t.getOutput(null, Object.class));
            assertThrows("empty name", IllegalArgumentException.class,
                    () -> t.getOutput("", Object.class));
            assertThrows("null class", IllegalArgumentException.class,
                    () -> t.getOutput("x", null));

            final WBuilder w2 = c.w();
            IllegalArgumentException e = assertThrows("an object at .txt",
                    IllegalArgumentException.class,
                    () -> w2.put("/w/d.txt", new PubTesterJavadoc.Account("A", 1)));
            Assert.assertTrue(e.getMessage(), e.getMessage().startsWith("Bad key"));
            assertThrows("spoiled", IllegalStateException.class, () -> w2.execute());
            String[] badKeys = {null, "w/a.txt", "/w/", "//a.txt", "/", "/w//a.txt"};
            for (String key : badKeys) {
                assertThrows("put " + key, IllegalArgumentException.class,
                        () -> c.w().put(key, "v"));
                assertThrows("delete " + key, IllegalArgumentException.class,
                        () -> c.w().delete(key));
            }
            assertThrows("null value", IllegalArgumentException.class,
                    () -> c.w().put("/w/e.txt", null));

            c.w().put("/w/f.txt", "f").delete("/w/f.txt").delete("/w/g.txt").put("/w/g.txt", "g")
                    .put("/w/h.txt", "1").put("/w/h.txt", "2").execute();
            Assert.assertNull(c.get("/w/f.txt", String.class));
            Assert.assertEquals("g", c.get("/w/g.txt", String.class));
            Assert.assertEquals("2", c.get("/w/h.txt", String.class));
        }
    }

    /**
     * Transaction.getTime(): the time when the transaction was executed, unique among the
     * database's transactions: with a TestClock, the clock's time when it is later than the
     * last transaction's, else the next clock unit; a put, a delete, a w(), an empty w() and
     * an rw() each have a time of their own, increasing. Connection.transactionInfo() gives
     * the same time for the value it wrote. sync(SyncLevel) of a Transaction, a Connection
     * and a Database refuses null with IllegalArgumentException. The creation takes the
     * clock's time and the next unit, for its record of the startup distance (bergdb
     * 028-15), so the first transaction's time is t0 + 2.
     */
    @Nano
    public static void testTransactionTimes() {
        TestClock clock = new TestClock();
        final long t0 = Time.utc("2020-01-01").units();
        clock.setTime(Time.units(t0));
        try (Database db = Factory.database().memory().clock(clock).start()) {
            Connection c = db.connection();
            Transaction[] ts = {c.put("/a.txt", "a"), c.delete("/a.txt"),
                    c.w().put("/b.txt", "b").execute(), c.w().execute(),
                    c.rw(env -> env.put("/c.txt", "c"))};
            for (int i = 0; i < ts.length; i++) {
                Assert.assertEquals("transaction " + i, t0 + 2 + i, ts[i].getTime().units());
            }
            clock.setTime(Time.units(t0 + 1000));
            Transaction t = c.put("/d.txt", "d");
            Assert.assertEquals("the clock's time", t0 + 1000, t.getTime().units());
            c.get("/c.txt", String.class);
            Assert.assertEquals(ts[4].getTime(), c.transactionInfo().time());

            final Transaction last = t;
            assertThrows("Transaction.sync(null)", IllegalArgumentException.class,
                    () -> last.sync(null));
            assertThrows("Connection.sync(null)", IllegalArgumentException.class,
                    () -> c.sync(null));
            assertThrows("Database.sync(null)", IllegalArgumentException.class,
                    () -> db.sync(null));
        }
    }


    // ======== RwEnvironment, ReadInterface, Action ========

    /**
     * RwEnvironment: the action's reads read one state, and do not see the transaction's
     * own puts and deletes, get() nor exists(); a byte[] is copied at the put, so a change
     * of the array after it is not stored. ReadInterface: one method reads through a
     * Connection and through an RwEnvironment alike.
     */
    @Nano
    public static void testRwEnvironmentReadsOneState() {
        try (Database db = Factory.database().memory().start()) {
            Connection c = db.connection();
            c.put("/a.txt", "a");
            Transaction t = c.rw(env -> {
                byte[] bytes = {1};
                env.put("/c.bin", bytes);
                bytes[0] = 9;
                env.put("/b.txt", "b");
                env.delete("/a.txt");
                env.setOutput("b", String.valueOf(env.get("/b.txt", String.class)));
                env.setOutput("b exists", env.exists("/b.txt"));
                env.setOutput("a", String.valueOf(env.get("/a.txt", String.class)));
                env.setOutput("a exists", env.exists("/a.txt"));
                env.setOutput("read", read(env));
            });
            Assert.assertEquals("null", t.getOutput("b", String.class));
            Assert.assertEquals(Boolean.FALSE, t.getOutput("b exists", Boolean.class));
            Assert.assertEquals("a", t.getOutput("a", String.class));
            Assert.assertEquals(Boolean.TRUE, t.getOutput("a exists", Boolean.class));
            Assert.assertEquals("a true", t.getOutput("read", String.class));
            Assert.assertEquals("null false", read(c));
            Assert.assertEquals("b", c.get("/b.txt", String.class));
            Assert.assertEquals(1, c.get("/c.bin", byte[].class)[0]);
        }
    }

    /** A composable read: the value of /a.txt and whether it exists. */
    private static String read(ReadInterface r) {
        return r.get("/a.txt", String.class) + " " + r.exists("/a.txt");
    }

    /**
     * Action.run(): a RuntimeException that it throws is thrown by rw(), the same object;
     * nothing of the transaction is written, and the database goes on. RwEnvironment.get():
     * an ObjectCreationException, for a class that is not a Data Object, ends the action as
     * its own exception, with the same outcome.
     */
    @Nano
    public static void testActionExceptions() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/x.txt", "0");
            final RuntimeException mine = new IllegalStateException("the action's");
            RuntimeException e = assertThrows("the action's exception", RuntimeException.class,
                    () -> c.rw(env -> {
                        env.put("/x.txt", "1");
                        throw mine;
                    }));
            Assert.assertTrue("the same object", e == mine);
            Assert.assertEquals("0", c.get("/x.txt", String.class));
            assertThrows("a get as a class that is not a Data Object",
                    ObjectCreationException.class, () -> c.rw(env -> {
                        env.put("/x.txt", "2");
                        env.get("/x.txt", NOT_A_DATA_OBJECT);
                    }));
            Assert.assertEquals("0", c.get("/x.txt", String.class));
            c.put("/x.txt", "3");
            Assert.assertEquals("3", c.get("/x.txt", String.class));
        }
    }


    /**
     * RwEnvironment: put(), delete() and exists() refuse a null or invalid key, put() a
     * null value and an object at a key with a suffix other than ".obj" ("Bad key"), and
     * setOutput() a null or empty name and a null value, each with IllegalArgumentException,
     * which ends the action: rw() throws it, nothing is written, and the database goes on.
     */
    @Nano
    public static void testRwEnvironmentRefusals() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            final Object account = new PubTesterJavadoc.Account("A", 1);
            final String[] cases = {"put null key", "put bad key", "put null value",
                    "put object at .txt", "delete null key", "delete bad key",
                    "exists null key", "exists bad key", "setOutput null name",
                    "setOutput empty name", "setOutput null value"};
            for (final String what : cases) {
                IllegalArgumentException e = assertThrows(what,
                        IllegalArgumentException.class, () -> c.rw(env -> {
                            env.put("/written.txt", "x");
                            switch (what) {
                            case "put null key": env.put(null, "v"); break;
                            case "put bad key": env.put("a.txt", "v"); break;
                            case "put null value": env.put("/a.txt", null); break;
                            case "put object at .txt": env.put("/a.txt", account); break;
                            case "delete null key": env.delete(null); break;
                            case "delete bad key": env.delete("/a/"); break;
                            case "exists null key": env.exists(null); break;
                            case "exists bad key": env.exists("//a"); break;
                            case "setOutput null name": env.setOutput(null, "v"); break;
                            case "setOutput empty name": env.setOutput("", "v"); break;
                            default: env.setOutput("x", null); break;
                            }
                        }));
                if (what.equals("put object at .txt")) {
                    Assert.assertTrue(e.getMessage(), e.getMessage().startsWith("Bad key"));
                }
                Assert.assertFalse(what, c.exists("/written.txt"));
            }
            c.put("/written.txt", "y");
            Assert.assertEquals("y", c.get("/written.txt", String.class));
        }
    }


    // ======== Clock, TestClock ========

    /**
     * TestClock: its time is 0 until setTime(); setTime() takes the current time again and a
     * later one, and refuses an earlier one and null with IllegalArgumentException, the
     * time unchanged.
     */
    @Nano
    public static void testTestClock() {
        final TestClock clock = new TestClock();
        Assert.assertEquals(0, clock.getTime());
        final Time t = Time.utc("2020-01-01");
        clock.setTime(t);
        Assert.assertEquals(t.units(), clock.getTime());
        clock.setTime(t);
        Assert.assertEquals(t.units(), clock.getTime());
        assertThrows("earlier", IllegalArgumentException.class,
                () -> clock.setTime(Time.units(t.units() - 1)));
        assertThrows("null", IllegalArgumentException.class, () -> clock.setTime(null));
        Assert.assertEquals(t.units(), clock.getTime());
        clock.setTime(Time.MAX);
        Assert.assertEquals(Time.MAX.units(), clock.getTime());
        Assert.assertEquals(10000000L, Clock.UNITS_PER_SEC);
    }

    /**
     * Clock and DbException: a clock time outside 0 to 2^56 - 1 refuses the transaction
     * with a DbException that is not a DbFailedException: nothing is written, and the
     * database goes on; a start that creates a database with the clock out of range throws
     * a DbException (an existing one's: testStartWithTheClockOutOfRange). The last
     * 1024 clock units are kept for the database's own transactions: a user transaction
     * needs a time of 2^56 - 1025 or less (bergdb 015-55), so a TestClock at Time.MAX
     * refuses it, in the same way. A clock that goes back gives the next unit after the
     * last transaction's time.
     */
    @Nano
    public static void testClockOutOfRangeRefused() {
        final AtomicLong time = new AtomicLong(-1);
        final Clock clock = () -> time.get();
        assertThrows("a start at -1", DbException.class,
                () -> Factory.database().memory().clock(clock).start().close());
        time.set(1000);
        try (Database db = Factory.database().memory().clock(clock).start()) {
            final Connection c = db.connection();
            c.put("/a.txt", "a");
            long[] bad = {-1, 1L << 56, Long.MAX_VALUE, Long.MIN_VALUE};
            for (long v : bad) {
                time.set(v);
                DbException e = assertThrows("clock " + v, DbException.class,
                        () -> c.put("/b.txt", "b"));
                Assert.assertFalse("a refusal, not a failure: " + e,
                        e instanceof DbFailedException);
                Assert.assertNull(c.get("/b.txt", String.class));
            }
            time.set(2000);
            c.put("/b.txt", "b");
            Assert.assertEquals("b", c.get("/b.txt", String.class));
            time.set(500);
            Assert.assertEquals("a clock that goes back", 2001, c.put("/c.txt", "c").getTime()
                    .units());
            Assert.assertEquals(2001, c.currentTime().units());
            Assert.assertEquals(2002, c.put("/c.txt", "c").getTime().units());
        }

        final TestClock testClock = new TestClock();
        final long lastUser = Time.MAX.units() - 1024;
        // The creation takes two times, its record of the startup distance the second
        // (bergdb 028-15).
        testClock.setTime(Time.units(lastUser - 2));
        try (Database db = Factory.database().memory().clock(testClock).start()) {
            final Connection c = db.connection();
            Assert.assertEquals(lastUser, c.put("/a.txt", "a").getTime().units());
            DbException e = assertThrows("no time left", DbException.class,
                    () -> c.put("/b.txt", "b"));
            Assert.assertFalse(e.toString(), e instanceof DbFailedException);
            testClock.setTime(Time.MAX);
            assertThrows("at Time.MAX", DbException.class, () -> c.put("/b.txt", "b"));
            Assert.assertEquals("a", c.get("/a.txt", String.class));
            Assert.assertNull(c.get("/b.txt", String.class));
        }
    }

    /**
     * Connection.currentTime() with a clock that goes back (bergdb 020-23, Z1): the time
     * returned is before every later transaction's time, so a read at it gives the same
     * value after a later put; a later currentTime() is not before it. A second
     * currentTime() with the clock back gave the clock's earlier time, and a put after it
     * took a time before the first one returned, which then read the put's value.
     */
    @Nano
    public static void testCurrentTimeWithAClockThatGoesBack() {
        final AtomicLong time = new AtomicLong(1000);
        final Clock clock = () -> time.get();
        try (Database db = Factory.database().memory().clock(clock).start()) {
            final Connection c = db.connection();
            c.put("/a.txt", "before");
            time.set(2000);
            final Time first = c.currentTime();
            Assert.assertEquals(2000, first.units());
            time.set(1500);
            Assert.assertEquals(2000, c.currentTime().units());
            Assert.assertEquals(2000, db.currentTime().units());
            final long written = c.put("/a.txt", "after").getTime().units();
            Assert.assertTrue("a put after currentTime() " + first.units() + " at " + written,
                    written > first.units());
            c.setLookupTime(first);
            Assert.assertEquals("before", c.get("/a.txt", String.class));
            c.setLookupTime(Time.MAX);
            Assert.assertEquals("after", c.get("/a.txt", String.class));
        }
    }

    /**
     * Clock.getTime(), currentTime() with the clock out of range (bergdb 021-26): the
     * transactions are refused while the clock is out of range, and go on when it is back.
     * A currentTime() while it was out of range gave 2^56-1025 and kept it as the time that
     * the next transaction must pass, so that every put after it was refused until a
     * restart; found by a black-box user of the C port (022), U2-1.
     */
    @Nano
    public static void testCurrentTimeWithTheClockOutOfRange() {
        final AtomicLong time = new AtomicLong(1000);
        final Clock clock = () -> time.get();
        try (Database db = Factory.database().memory().clock(clock).start()) {
            final Connection c = db.connection();
            final long first = c.put("/a.txt", "a").getTime().units();
            time.set(Time.MAX.units() + 1);
            Assert.assertEquals(first, c.currentTime().units());
            Assert.assertEquals(first, db.currentTime().units());
            DbException e = assertThrows("out of range", DbException.class,
                    () -> c.put("/b.txt", "b"));
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("outside the range"));
            time.set(2000);
            Assert.assertEquals(2000, c.put("/b.txt", "b").getTime().units());
            Assert.assertEquals(2000, c.currentTime().units());
            Assert.assertEquals("b", c.get("/b.txt", String.class));
        }
    }

    /**
     * Clock.getTime(), a start with the clock out of range (bergdb 020-23, Z3): a start that
     * creates a database is refused, as it writes the database's first transaction; a start
     * of an existing one does not read the clock and succeeds, its reads work, and its
     * transactions are refused until the clock is back in the range. Clock's Javadoc said
     * that a start is refused.
     */
    @Nano
    public static void testStartWithTheClockOutOfRange() {
        final AtomicLong time = new AtomicLong(1L << 56);
        final Clock clock = () -> time.get();
        final MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        final DatabaseBuilder creation = builder.clock(clock);
        DbException e = assertThrows("a creation", DbException.class,
                () -> creation.start().close());
        Assert.assertTrue(e.getMessage(), e.getMessage().contains("outside the range"));
        
        final MemoryStream stream2 = new MemoryStream();
        builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream2);
        time.set(1000);
        try (Database db = builder.clock(clock).start()) {
            db.connection().put("/a.txt", "a");
        }
        for (long t : new long[] {1L << 56, -1}) {
            time.set(t);
            builder = Factory.database();
            ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream2.copy());
            try (Database db = builder.clock(clock).start()) {
                final Connection c = db.connection();
                Assert.assertEquals("a", c.get("/a.txt", String.class));
                e = assertThrows("a put at " + t, DbException.class, () -> c.put("/b.txt", "b"));
                Assert.assertFalse(e.toString(), e instanceof DbFailedException);
                time.set(2000);
                Assert.assertEquals(2000, c.put("/b.txt", "b").getTime().units());
            }
        }
    }


    // ======== DbFailedException, the exceptions ========

    /**
     * DbFailedException: after a failure (an Error in an action), a read and a transaction
     * throw it with the Error as the cause; sync() still works for the transactions before
     * the failure, Transaction's, Connection's and Database's, and so do stop() and close().
     */
    @Nano
    public static void testFailedDatabaseSyncsAndCloses() {
        Database db = Factory.database().memory().start();
        try {
            final Connection c = db.connection();
            final Transaction t = c.put("/a.txt", "a");
            final AssertionError error = new AssertionError("an Error of the action");
            Error thrown = assertThrows("the Error", AssertionError.class,
                    () -> c.rw(env -> {
                        throw error;
                    }));
            Assert.assertTrue(thrown == error);
            DbFailedException e = assertThrows("a read", DbFailedException.class,
                    () -> c.get("/a.txt", String.class));
            Assert.assertTrue(e.getCause() == error);
            e = assertThrows("a put", DbFailedException.class, () -> c.put("/b.txt", "b"));
            Assert.assertTrue(e.getCause() == error);
            t.sync();
            c.sync();
            db.sync();
            db.stop();
        } finally {
            db.close();
        }
    }

    /**
     * The exceptions' kinds, as their Javadoc gives them: a refusal or a failure is a
     * DbException (DatabaseMissingException, DatabaseNotCreatedException,
     * DataFormatException, IllegalDbStateException; DbFailedException is an
     * IllegalDbStateException); LookupTimeNotAvailableException is an
     * IllegalArgumentException; IndexBuildException is no DbException, nor are
     * ObjectCreationException, NoSuchIndexException, IndexAlreadyExistsException and
     * BadFormatException. BadCryptoKey and CryptoKey.FormatException left the API with the
     * encryption (bergdb 020-28).
     */
    @Nano
    public static void testExceptionKinds() {
        Class<?>[] dbExceptions = {DatabaseMissingException.class,
                DatabaseNotCreatedException.class, DataFormatException.class,
                IllegalDbStateException.class, DbFailedException.class};
        for (Class<?> c : dbExceptions) {
            Assert.assertTrue(c.getName(), DbException.class.isAssignableFrom(c));
        }
        Assert.assertTrue(IllegalDbStateException.class.isAssignableFrom(
                DbFailedException.class));
        Assert.assertTrue(IllegalArgumentException.class.isAssignableFrom(
                LookupTimeNotAvailableException.class));
        Class<?>[] others = {IndexBuildException.class, ObjectCreationException.class,
                NoSuchIndexException.class, IndexAlreadyExistsException.class,
                BadFormatException.class};
        for (Class<?> c : others) {
            Assert.assertFalse(c.getName(), DbException.class.isAssignableFrom(c));
            Assert.assertTrue(c.getName(), RuntimeException.class.isAssignableFrom(c));
        }
    }


    // ======== Factory, DatabaseBuilder ========

    /**
     * Factory.database(): a new builder at each call, whose databases are apart.
     * DatabaseBuilder: create(null), open(null) and clock(null) throw
     * IllegalArgumentException; start() without create(), open() or memory() throws
     * IllegalStateException; an existing database keeps the startup distance stored in its
     * stream, as setStartupDistanceInMb() set it (the builder has no setting since bergdb
     * 028-13).
     */
    @Nano
    public static void testDatabaseBuilderRules() {
        DatabaseBuilder b1 = Factory.database();
        DatabaseBuilder b2 = Factory.database();
        Assert.assertTrue(b1 != b2);
        try (Database d1 = b1.memory().start(); Database d2 = b2.memory().start()) {
            d1.connection().put("/a.txt", "1");
            Assert.assertNull(d2.connection().get("/a.txt", String.class));
        }
        final DatabaseBuilder b = Factory.database();
        assertThrows("create(null)", IllegalArgumentException.class, () -> b.create(null));
        assertThrows("open(null)", IllegalArgumentException.class, () -> b.open(null));
        assertThrows("clock(null)", IllegalArgumentException.class, () -> b.clock(null));
        assertThrows("no database given", IllegalStateException.class, () -> b.start());

        MemoryStream m = new MemoryStream();
        try (Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m)
                .start()) {
            d.setStartupDistanceInMb(100);
            Assert.assertEquals(100, d.getStartupDistanceInMb());
            d.connection().put("/a.txt", "a");
        }
        try (Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m.copy())
                .start()) {
            Assert.assertEquals("the stream's", 100, d.getStartupDistanceInMb());
        }
    }


    /**
     * DatabaseBuilder.cacheSizeInMb(): the default is a fifth of the JVM's maximum heap,
     * within the clamp of 4 to 100,000 MB as a value given is, or 100 MB for a JVM without
     * a maximum (bergdb 020-25, C3): a heap under 20 MB gave 2 or 3, and one over 500 GB more
     * than 100,000.
     */
    @Nano
    public static void testDefaultCacheSizeClamped() {
        final long mb = 1000000;
        Assert.assertEquals(100, DatabaseBuilderImp.defaultCacheSizeInMb(Long.MAX_VALUE));
        Assert.assertEquals(200, DatabaseBuilderImp.defaultCacheSizeInMb(1000 * mb));
        Assert.assertEquals(4, DatabaseBuilderImp.defaultCacheSizeInMb(20 * mb));
        Assert.assertEquals(4, DatabaseBuilderImp.defaultCacheSizeInMb(16 * mb));
        Assert.assertEquals(4, DatabaseBuilderImp.defaultCacheSizeInMb(1 * mb));
        Assert.assertEquals(100000, DatabaseBuilderImp.defaultCacheSizeInMb(500000 * mb));
        Assert.assertEquals(100000, DatabaseBuilderImp.defaultCacheSizeInMb(2000000 * mb));
        try (Database db = Factory.database().memory().start()) {
            Assert.assertEquals(
                    DatabaseBuilderImp.defaultCacheSizeInMb(Runtime.getRuntime().maxMemory()),
                    db.getCacheSizeInMb());
        }
    }


    /**
     * DatabaseBuilder.start(): a stream that does not begin as a BergDB stream, here 100 bytes
     * of 'x', is refused with a StreamFormatException whose message names the likely causes,
     * among them a stream that an earlier release encrypted, and the start writes nothing
     * (bergdb 020-28; BadCryptoKey until 2026.4, with a crypto key and without one).
     */
    @Nano
    public static void testForeignStreamRefused() throws java.io.IOException {
        byte[] bytes = new byte[100];
        java.util.Arrays.fill(bytes, (byte) 'x');
        final MemoryStream m = new MemoryStream();
        m.append(bytes, 0, bytes.length);
        final DatabaseBuilder b = ((DatabaseBuilderImp) Factory.database()).mainStream(m);
        StreamFormatException e = assertThrows("a foreign stream", StreamFormatException.class,
                () -> b.start().close());
        String message = e.getMessage();
        Assert.assertTrue(message, message.startsWith("Invalid magic bytes in stream: the "
                + "stream is not a BergDB stream, or it is damaged; or an earlier release"));
        Assert.assertEquals(100, m.getLength());
    }
    
    /**
     * BergDB has no encryption in its API since release 2026.4 (bergdb 020-28): DatabaseBuilder
     * has no cryptoKey(), and neither bergdb.pub.CryptoKey nor bergdb.pub.util.BadCryptoKey
     * exists.
     */
    @Nano
    public static void testNoEncryptionInTheApi() {
        for (java.lang.reflect.Method method : DatabaseBuilder.class.getMethods()) {
            Assert.assertFalse(method.toString(), 
                    method.getName().toLowerCase(java.util.Locale.ROOT).contains("crypt"));
        }
        for (String name : new String[] {"bergdb.pub.CryptoKey", 
                "bergdb.pub.util.BadCryptoKey"}) {
            try {
                Class.forName(name);
                throw new AssertionError(name + " exists");
            } catch (ClassNotFoundException e) {
                // Expected.
            }
        }
    }


    // ======== Time, Duration ========

    /**
     * Time.resolve(): the examples of its Javadoc as they are written, each giving the time
     * of its comment; and the grammar's absolute time of a year and a month with a time of
     * day ("2013-08 14:29", with a space or "T").
     */
    @Nano
    public static void testTimeExamples() {
        final TimeZone utc = Time.UTC;
        final Time now = Time.utc("2013-08-21 10:00");
        String[][] examples = {
                {"2013-08-19 14:29:10.1234567", "2013-08-19 14:29:10.1234567"},
                {"2013-08-19 14:29", "2013-08-19 14:29:00.0000000"},
                {"2013-08-19", "2013-08-19 00:00:00.0000000"},
                {"2013-08", "2013-08-01 00:00:00.0000000"},
                {"2013-01", "2013-01-01 00:00:00.0000000"},
                {"14:29:10.1234567", "2013-08-21 14:29:10.1234567"},
                {"14:29", "2013-08-21 14:29:00.0000000"},
                {"-1.5 s", "2013-08-21 09:59:58.5000000"},
                {"-30 m", "2013-08-21 09:30:00.0000000"},
                {"-2 h", "2013-08-21 08:00:00.0000000"},
                {"-3 d", "2013-08-18 10:00:00.0000000"},
                {"-2 d 14:29", "2013-08-19 14:29:00.0000000"},
                {"now", "2013-08-21 10:00:00.0000000"},
                {"2013-08 14:29", "2013-08-01 14:29:00.0000000"},
                {"2013-08T14:29", "2013-08-01 14:29:00.0000000"},
        };
        for (String[] e : examples) {
            Assert.assertEquals(e[0], e[1], Time.resolve(utc, now, e[0]).toUtcString());
        }
    }

    /**
     * Time.resolve(): a time of day is today in the given time zone, which may be another
     * day than in UTC; a minus time's day is 24 hours, also across a change to summer time;
     * a minus time with a time of day takes the day of the time it gives, in the zone.
     * resolve(TimeZone, String) and utc() take an absolute time only. A day has 86,400
     * seconds, no leap second. Time: MAX is 2198-05-04 23:50:03.7927935 UTC, units(0)
     * 1970-01-01; toUtcString() gives seven digits of the second's fraction; isBetween()
     * includes both ends; equal times have equal hash codes; add() past MAX throws
     * IllegalArgumentException.
     */
    @Nano
    public static void testTimeInTheZone() {
        TimeZone stockholm = TimeZone.getTimeZone("Europe/Stockholm");
        Time now = Time.utc("2020-06-15 23:30");          // 2020-06-16 01:30 in Stockholm
        Assert.assertEquals(Time.utc("2020-06-16 12:29"),
                Time.resolve(stockholm, now, "14:29"));
        Assert.assertEquals(Time.utc("2020-06-15 14:29"), Time.resolve(Time.UTC, now, "14:29"));
        Time sunday = Time.utc("2013-03-31 10:00");       // summer time from 01:00 UTC
        Assert.assertEquals(Time.utc("2013-03-30 10:00"),
                Time.resolve(stockholm, sunday, "-1 d"));
        Assert.assertEquals(Time.utc("2013-03-30 11:00"),
                Time.resolve(stockholm, sunday, "-1 d 12:00"));
        Assert.assertEquals(Time.utc("2013-03-29 11:00"),
                Time.resolve(stockholm, sunday, "-2 d 12:00"));

        String[] notAbsolutes = {"now", "14:29", "14:29:00", "-1 s", "-1 d 12:00"};
        for (String notAbsolute : notAbsolutes) {
            assertThrows(notAbsolute, BadFormatException.class,
                    () -> Time.resolve(stockholm, notAbsolute));
            assertThrows(notAbsolute, BadFormatException.class, () -> Time.utc(notAbsolute));
        }
        Assert.assertEquals("no leap second", Time.utc("2017-01-01"),
                Time.utc("2016-12-31 23:59:59").add(Duration.seconds(1)));

        Assert.assertEquals("2198-05-04 23:50:03.7927935", Time.MAX.toUtcString());
        Assert.assertEquals("2198-05-04 23:50:03.7927935", Time.MAX.toString());
        Assert.assertEquals("1970-01-01 00:00:00.0000000", Time.units(0).toUtcString());
        Assert.assertEquals((1L << 56) - 1, Time.MAX.units());
        Time a = Time.units(10);
        Time b = Time.units(20);
        Assert.assertTrue(a.isBetween(a, b) && b.isBetween(a, b));
        Assert.assertFalse(Time.units(9).isBetween(a, b) || Time.units(21).isBetween(a, b));
        Assert.assertEquals(Time.units(10).hashCode(), a.hashCode());
        Assert.assertEquals(Time.units(10), a);
        Assert.assertEquals(Time.MAX, Time.units(1).add(Duration.units(Time.MAX.units() - 1)));
        assertThrows("past MAX", IllegalArgumentException.class,
                () -> Time.units(1).add(Duration.units(Time.MAX.units())));
        assertThrows("MAX past MAX", IllegalArgumentException.class,
                () -> Time.units(1).add(Duration.MAX));
    }

    /**
     * Time.add() and isBetween() refuse a null argument with IllegalArgumentException, as
     * every null argument of the API (bergdb 020-25, C2; 020-21, 3): they threw a
     * NullPointerException. RwEnvironment.get() with a null class: the message names the
     * argument, clazz, as Connection.get()'s does.
     */
    @Nano
    public static void testTimeNullArguments() {
        final Time t = Time.units(10);
        assertThrows("add(null)", IllegalArgumentException.class, () -> t.add(null));
        assertThrows("isBetween(null, t)", IllegalArgumentException.class,
                () -> t.isBetween(null, t));
        assertThrows("isBetween(t, null)", IllegalArgumentException.class,
                () -> t.isBetween(t, null));
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/a.txt", "a");
            IllegalArgumentException e = assertThrows("env.get(key, null)",
                    IllegalArgumentException.class,
                    () -> c.rw(env -> env.get("/a.txt", null)));
            Assert.assertTrue(e.getMessage(), e.getMessage().startsWith("clazz == null"));
        }
    }

    /**
     * Duration: units() refuses a negative value with IllegalArgumentException; seconds()
     * rounds to the nearest clock unit; MAX is Long.MAX_VALUE units, and seconds() of
     * infinity equals it; equal durations have equal hash codes.
     */
    @Nano
    public static void testDurationRules() {
        assertThrows("units(-1)", IllegalArgumentException.class, () -> Duration.units(-1));
        assertThrows("seconds(-1e-7)", IllegalArgumentException.class,
                () -> Duration.seconds(-1e-7));
        Assert.assertEquals(15000000L, Duration.seconds(1.5).units());
        Assert.assertEquals(1L, Duration.seconds(0.6e-7).units());
        Assert.assertEquals(0L, Duration.seconds(0.4e-7).units());
        Assert.assertEquals(0L, Duration.units(0).units());
        Assert.assertEquals(Long.MAX_VALUE, Duration.MAX.units());
        Assert.assertEquals(Duration.MAX, Duration.seconds(Double.POSITIVE_INFINITY));
        Assert.assertEquals(Duration.seconds(1), Duration.units(Clock.UNITS_PER_SEC));
        Assert.assertEquals(Duration.seconds(1).hashCode(),
                Duration.units(Clock.UNITS_PER_SEC).hashCode());
    }
}
