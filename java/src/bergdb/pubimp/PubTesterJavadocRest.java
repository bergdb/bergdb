package bergdb.pubimp;

import java.util.TimeZone;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.CryptoKey;
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
import bergdb.pub.util.BadCryptoKey;
import bergdb.pub.util.BadFormatException;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DatabaseMissingException;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.IndexBuildException;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.MemoryStream;

/**
 * The Pub API's Javadoc checked against its behaviour, promise by promise, for the classes
 * that bergdb 020-19 left (bergdb 020-25): WBuilder, RwEnvironment, ReadInterface, Action,
 * Transaction, Factory, DatabaseBuilder, Time, Duration, CryptoKey, TestClock, Clock and the
 * exceptions. Each test names the class and the promise it shows; the promises that other
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
     * invalid key, at once, and delete() a null or invalid key; of several puts and deletes
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
            String[] badKeys = {null, "w/a.txt", "/w/", "//a.txt", "/", "/w//a.txt"};
            for (String key : badKeys) {
                assertThrows("put " + key, IllegalArgumentException.class,
                        () -> w2.put(key, "v"));
                assertThrows("delete " + key, IllegalArgumentException.class,
                        () -> w2.delete(key));
            }
            assertThrows("null value", IllegalArgumentException.class,
                    () -> w2.put("/w/e.txt", null));

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
     * and a Database refuses null with IllegalArgumentException.
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
                Assert.assertEquals("transaction " + i, t0 + 1 + i, ts[i].getTime().units());
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
     * database goes on; a start whose clock is out of range throws a DbException. The last
     * 1024 clock units are kept for the database's own transactions: a user transaction
     * needs a time of 2^56 - 1025 or less (bergdb 015-55), so a TestClock at Time.MAX
     * refuses it, in the same way.
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
        }

        final TestClock testClock = new TestClock();
        final long lastUser = Time.MAX.units() - 1024;
        testClock.setTime(Time.units(lastUser - 1));
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
     * DbException (BadCryptoKey, DatabaseMissingException, DatabaseNotCreatedException,
     * DataFormatException, IllegalDbStateException; DbFailedException is an
     * IllegalDbStateException); LookupTimeNotAvailableException is an
     * IllegalArgumentException; IndexBuildException is no DbException, nor are
     * ObjectCreationException, NoSuchIndexException, IndexAlreadyExistsException,
     * BadFormatException and CryptoKey.FormatException.
     */
    @Nano
    public static void testExceptionKinds() {
        Class<?>[] dbExceptions = {BadCryptoKey.class, DatabaseMissingException.class,
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
                BadFormatException.class, CryptoKey.FormatException.class};
        for (Class<?> c : others) {
            Assert.assertFalse(c.getName(), DbException.class.isAssignableFrom(c));
            Assert.assertTrue(c.getName(), RuntimeException.class.isAssignableFrom(c));
        }
    }


    // ======== Factory, DatabaseBuilder ========

    /**
     * Factory.database(): a new builder at each call, whose databases are apart.
     * DatabaseBuilder: create(null), open(null), clock(null) and cryptoKey(null) throw
     * IllegalArgumentException; start() without create(), open() or memory() throws
     * IllegalStateException; an existing database keeps the startup distance stored in its
     * stream, whatever the builder's.
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
        assertThrows("cryptoKey(null)", IllegalArgumentException.class,
                () -> b.cryptoKey(null));
        assertThrows("no database given", IllegalStateException.class, () -> b.start());

        MemoryStream m = new MemoryStream();
        try (Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m)
                .startupDistanceInMb(100).start()) {
            Assert.assertEquals(100, d.getStartupDistanceInMb());
            d.connection().put("/a.txt", "a");
        }
        try (Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m.copy())
                .startupDistanceInMb(7).start()) {
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


    // ======== Time, Duration ========

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


    // ======== CryptoKey ========

    /**
     * CryptoKey: generate() gives a 'salsa' key of 40 bytes (a nonce of 8 and a key of 32),
     * a copy at each getKeyData(); serialize() and parse() round-trip, the parsed key equal
     * with an equal hash code; toString() is toStringWithMaskedKey(), which has "****" in
     * place of the key data; NULL is null, with no key data, and round-trips; parse()
     * refuses a string that is not of serialize()'s parts with FormatException, and null
     * with IllegalArgumentException.
     */
    @Nano
    public static void testCryptoKeyRules() {
        CryptoKey key = CryptoKey.generate();
        Assert.assertEquals("salsa", key.getAlgo());
        Assert.assertFalse(key.isNull());
        Assert.assertEquals(40, key.getKeyData().length);
        Assert.assertTrue(key.getKeyData() != key.getKeyData());
        String s = key.serialize();
        String[] parts = s.split("-");
        Assert.assertEquals(3, parts.length);
        Assert.assertEquals("salsa", parts[1]);
        Assert.assertEquals(80, parts[2].length());
        CryptoKey parsed = CryptoKey.parse(s);
        Assert.assertEquals(key, parsed);
        Assert.assertEquals(key.hashCode(), parsed.hashCode());
        Assert.assertEquals(key.toStringWithMaskedKey(), key.toString());
        Assert.assertEquals(parts[0] + "-salsa-****", key.toString());
        Assert.assertFalse(key.toString().contains(parts[2]));
        Assert.assertFalse(key.equals(CryptoKey.generate()));

        Assert.assertTrue(CryptoKey.NULL.isNull());
        Assert.assertEquals(0, CryptoKey.NULL.getKeyData().length);
        Assert.assertTrue(CryptoKey.parse(CryptoKey.NULL.serialize()) == CryptoKey.NULL);
        String hex = parts[2];
        String[] bad = {"", "a", "a-salsa", "-salsa-" + hex, "a--" + hex, "a-salsa-x" + hex,
                "a-salsa-" + hex.substring(2), "a-salsa-" + hex + "00"};
        for (String b : bad) {
            assertThrows("'" + b + "'", CryptoKey.FormatException.class,
                    () -> CryptoKey.parse(b));
        }
        assertThrows("null", IllegalArgumentException.class, () -> CryptoKey.parse(null));
    }

    /**
     * CryptoKey.parse() refuses with FormatException a string that is not in serialize()'s
     * format by having more than its three parts, the name, the algorithm and the key data:
     * an extra part, also an empty one after a trailing '-' (bergdb 020-25, C1). Before, the
     * parts after the third were ignored, and such a string gave the key. The key data's hex
     * digits are taken in either case: the same key.
     */
    @Nano
    public static void testCryptoKeyParseExact() {
        final String s = CryptoKey.generate().serialize();
        final String[] parts = s.split("-");
        final String hex = parts[2];
        String[] bad = {s + "-x", s + "-", s + "--", "a-salsa-" + hex + "-" + hex};
        for (String b : bad) {
            assertThrows("'" + b + "'", CryptoKey.FormatException.class,
                    () -> CryptoKey.parse(b));
        }
        Assert.assertEquals(s, CryptoKey.parse(s).serialize());
        Assert.assertEquals(CryptoKey.parse(s),
                CryptoKey.parse(parts[0] + "-salsa-" + hex.toUpperCase(java.util.Locale.US)));
        Assert.assertNull(CryptoKey.NULL.getAlgo());
    }
}
