package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.io.UnsupportedEncodingException;
import java.util.Arrays;
import java.util.Iterator;
import java.util.Locale;
import java.util.Set;
import java.util.function.Consumer;

import bergdb.common.Bytes;
import bergdb.common.EventToWaitFor;
import bergdb.common.StringUtil;
import bergdb.common.Util;
import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.DbConstants;
import bergdb.core.DbStoppingException;
import bergdb.core.DbTester;
import bergdb.core.DbTesterFailure;
import bergdb.core.Eviction;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.CryptoKey;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.DbObject;
import bergdb.pub.DbString;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.RwEnvironment;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.TransactionInfo;
import bergdb.pub.WBuilder;
import bergdb.pub.util.BadCryptoKey;
import bergdb.pub.util.DatabaseMissingException;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.BufferedStream;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.storage.VersioningStreamException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.DirectoryInUseException;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;
import bergdb.stream.MemoryStream;
import bergdb.stream.SalsaStream;
import bergdb.stream.StrictStream;

/**
 * General test class for Layer Pub.
 * Secondary indexing is tested by PubTesterIndex.
 * 
 * @author Frans Lundberg
 */
public class PubTester {
    
    /**
     * bergdb 019-10 (Frans, 2026-11-06, 10:18 and 10:31): an Error during a call fails the
     * database and reaches the Pub API's caller as it is: an Error of the application's
     * Action, which runs before the Core's transaction, and one of a read of the storage,
     * which the Core throws. Every later put and get is refused with a DbFailedException
     * whose cause is the Error. Before, both left the database going on.
     */
    @Nano
    public static void testErrorFailsTheDatabase() {
        Database db = Factory.database().memory().start();
        try {
            final Connection c = db.connection();
            c.put("/a", "a0");
            final AssertionError error = new AssertionError("the Action's Error");
            Throwable thrown = null;
            try {
                c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        env.put("/a", "a1");
                        throw error;
                    }
                });
            } catch (Throwable e) {
                thrown = e;
            }
            Assert.assertTrue("the Action's Error itself: " + thrown, thrown == error);
            assertFailedBy(c, error);
        } finally {
            db.close();
        }
        
        final StrictStream s = new StrictStream(new MemoryStream());
        final Error readError = new Error("an Error in a read of the storage");
        final java.util.concurrent.atomic.AtomicBoolean fail =
                new java.util.concurrent.atomic.AtomicBoolean();
        s.setHook((op, n) -> {
            if (op == StrictStream.Op.READ && fail.get()) {
                throw readError;
            }
        });
        db = DatabaseImp.createAndStart(Db.builder().testSetup(s).maxNodeSize8()
                .startupDistance(1000).evictionSchedule(Eviction.Schedule.EVERY, 1).build());
        try {
            final Connection c = db.connection();
            for (int i = 0; i < 100; i++) {
                c.put("/k" + (1000 + i), "v" + i);
            }
            db.sync();      // Read from the stream, not from the write buffer.
            fail.set(true);
            Throwable thrown = null;
            try {
                c.get("/k1050", String.class);
            } catch (Throwable e) {
                thrown = e;
            }
            fail.set(false);
            Assert.assertTrue("the read's Error itself: " + thrown, thrown == readError);
            assertFailedBy(c, readError);
        } finally {
            db.close();
        }
    }
    
    /** Every later put and get throws a DbFailedException with 'cause' as its cause. */
    private static void assertFailedBy(Connection c, Throwable cause) {
        for (int i = 0; i < 2; i++) {
            DbFailedException refused = null;
            try {
                if (i == 0) {
                    c.put("/later", "x");
                } else {
                    c.get("/a", String.class);
                }
            } catch (DbFailedException e) {
                refused = e;
            }
            Assert.assertTrue("refused, " + i + ": " + refused,
                    refused != null && refused.getCause() == cause);
        }
    }

    /** A class to get an object as, for assertGetRefused. */
    private static class WithObject {
        Object o;
    }

    /**
     * bergdb 021-07: a value that is not a well-formed object, such as one from another
     * writer, gives a get of an object an ObjectCreationException (the reader's
     * BadFormatException), inside rw() and outside, and the database goes on. Before, a
     * nested object of size -1 gave an AssertionError (with -ea), which failed the
     * database inside rw() (019-10). In format 2 (bergdb 020-07; 020-08, step 2): a nested
     * object whose field ends past its extent.
     */
    @Nano
    public static void testMalformedObjectRefused() {
        DbObject inner = new DbObject.Builder().addLong("i", 1).build();
        final byte[] b = new DbObject.Builder().addObject("o", inner).build().getBytes();
        // The header, {o: {i: 1}}: the outer object, its field "o", the nested object.
        Assert.assertEquals("82480109" + "016f" + "48010401691001",
                bergdb.common.StringUtil.toHex(b));
        b[8] = 9;       // the nested object's end, 4, past its field
        assertGetRefused(b);
    }

    /**
     * bergdb 021-08: a value nested deeper than the writer writes, such as one from another
     * writer, is refused as 021-07's faults are. Before, the reader's recursion ended in a
     * StackOverflowError, or for objects, which it copies at each level, an
     * OutOfMemoryError, Errors that fail the database inside rw() (019-10).
     */
    @Nano
    public static void testDeepObjectRefused() {
        assertGetRefused(DbObjectTester.nestedArrays(100 * 1000));
        assertGetRefused(DbObjectTester.nestedObjects(100 * 1000));
    }

    /**
     * A get of the object 'b' as a class and as a DbObject throws ObjectCreationException,
     * outside rw() and inside, and the database goes on. A get as Object gives the bytes:
     * they start with the header of format 2 but are not a stored object (bergdb 020-08,
     * section 3).
     */
    private static void assertGetRefused(byte[] b) {
        Database db = Factory.database().memory().start();
        try {
            final Connection c = db.connection();
            c.put("/bad", b);
            Object asObject = c.get("/bad", Object.class);
            Assert.assertTrue("a get as Object: " + asObject, asObject instanceof byte[]
                    && Arrays.equals(b, (byte[]) asObject));
            Class<?>[] classes = {WithObject.class, DbObject.class};
            for (final Class<?> clazz : classes) {
                Throwable thrown = null;
                try {
                    c.get("/bad", clazz);
                } catch (Throwable e) {
                    thrown = e;
                }
                Assert.assertTrue("a get as " + clazz.getName() + ": " + thrown,
                        thrown instanceof ObjectCreationException);

                thrown = null;
                try {
                    c.rw(new Action() {
                        public void run(RwEnvironment env) {
                            env.put("/a", "a1");
                            env.get("/bad", clazz);
                        }
                    });
                } catch (Throwable e) {
                    thrown = e;
                }
                Assert.assertTrue("a get as " + clazz.getName() + " in rw(): " + thrown,
                        thrown instanceof ObjectCreationException);
            }
            c.put("/later", "x");      // not failed
            Assert.assertEquals("x", c.get("/later", String.class));
            Assert.assertNull(c.get("/a", String.class));     // no rw() committed
        } finally {
            db.close();
        }
    }
    
    @Nano
    public static void test1() {
        Database db = Factory.database().memory().start();
        Connection c = db.connection();
        c.w().put("/key1", "value1").execute();
        
        String value = c.get("/key1", String.class);
        Assert.assertEquals("value1", value);
        db.stop();
    }
    
    /**
     * bergdb 005-56: Time's range, which TestClock checks against, is the core's
     * (Klong.MIN_TIME to MAX_TIME); pub has its own copy, as pub does not use dag.
     */
    @Nano
    public static void testTimeRangeIsTheCores() {
        Assert.assertEquals(Klong.MAX_TIME, Time.MAX.units());
        Assert.assertEquals(Klong.MIN_TIME, Time.units(Klong.MIN_TIME).units());
        try {
            Time.units(Klong.MIN_TIME - 1);
            throw new AssertionError("expected IllegalArgumentException");
        } catch (IllegalArgumentException e) {
            // Expected.
        }
    }
    
    /**
     * Regression test for bergdb 015-58 (016-06's R8-F3): TestClock.setTime() refused the
     * clock's current time, which its Javadoc allows ("larger than or equal to"), also time
     * 0 on a new clock. An earlier time is still refused.
     */
    @Nano
    public static void testTestClockSetTimeEqual() {
        TestClock clock = new TestClock();
        clock.setTime(Time.units(0));
        Assert.assertEquals(0, clock.getTime());
        clock.setTime(Time.units(1000));
        clock.setTime(Time.units(1000));
        Assert.assertEquals(1000, clock.getTime());
        try {
            clock.setTime(Time.units(999));
            throw new AssertionError("an earlier time was taken");
        } catch (IllegalArgumentException e) {
            Assert.assertEquals(1000, clock.getTime());
        }
    }
    
    /**
     * bergdb 005-59: Database is AutoCloseable, and its close() waits. A try-with-resources
     * block closes the database when it ends, also when it throws: with a buffer time of a
     * minute nothing is written before the close, and right after the block the stream is
     * closed and holds every transaction.
     */
    @Nano
    public static void testTryWithResourcesCloses() {
        for (int c = 0; c < 2; c++) {
            MemoryStream s = new MemoryStream();
            DbBuilder b = Db.builder();
            b.testSetupExceptStream();
            b.stream("main", s, 100 * 1000, 60 * 1000);
            boolean caught = false;
            try (Database d = DatabaseImp.createAndStart(b.build())) {
                Connection con = d.connection();
                for (int i = 0; i < 20; i++) {
                    con.w().put("/k" + i, "v" + i).execute();
                }
                if (c == 1) {
                    throw new IllegalStateException("the block throws");
                }
            } catch (IllegalStateException e) {
                caught = true;
            }
            Assert.assertEquals("block " + c + " threw", c == 1, caught);
            DbTesterFailure.assertClosed(s);
            
            Database d2 = DatabaseImp.createAndStart(Db.builder().testSetup(s.copy()).build());
            for (int i = 0; i < 20; i++) {
                Assert.assertEquals("block " + c, "v" + i, 
                        d2.connection().get("/k" + i, String.class));
            }
            d2.close();
        }
    }
    
    /**
     * bergdb 005-59: Database.close() after stop(), and close() twice, are safe, here through
     * a try-with-resources block: the second call waits for the close, or returns, and the
     * stream is closed.
     */
    @Nano
    public static void testCloseAfterStopAndTwice() {
        for (int c = 0; c < 2; c++) {
            MemoryStream s = new MemoryStream();
            try (Database d = DatabaseImp.createAndStart(Db.builder().testSetup(s).build())) {
                d.connection().w().put("/a", "a").execute();
                if (c == 0) {
                    d.stop();
                } else {
                    d.close();
                }
            }
            DbTesterFailure.assertClosed(s);
            
            Database d2 = DatabaseImp.createAndStart(Db.builder().testSetup(s.copy()).build());
            Assert.assertEquals("call " + c, "a", d2.connection().get("/a", String.class));
            d2.close();
        }
    }
    
    /**
     * bergdb 019-09: through the Pub API, a failed write of the storage thread that no call
     * met is thrown by Database.close() as StreamIoException, here at the end of a
     * try-with-resources block; when the block throws, the close's exception is added to the
     * block's as suppressed. Before, close() returned normally.
     */
    @Nano
    public static void testCloseReportsBackgroundWriteFailure() throws Exception {
        for (int c = 0; c < 2; c++) {
            final FailingStream s = new FailingStream();
            Throwable thrown = null;
            try (Database d = DatabaseImp.createAndStart(Db.builder().testSetup(s).build())) {
                d.connection().put("/a", "a0");
                d.sync();
                s.fail = true;
                d.connection().put("/a", "a1");
                final long end = System.nanoTime() + 10L * 1000 * 1000 * 1000;
                while (!((DatabaseImp) d).getDb().internal().storageFailed()) {
                    Assert.assertTrue("the storage fails", System.nanoTime() < end);
                    Thread.sleep(1);
                }
                if (c == 1) {
                    throw new IllegalStateException("the block throws");
                }
            } catch (StreamIoException | IllegalStateException e) {
                thrown = e;
            }
            Throwable fromClose = thrown;
            if (c == 1) {
                Assert.assertTrue("the block's exception: " + thrown,
                        thrown instanceof IllegalStateException);
                Assert.assertEquals("suppressed", 1, thrown.getSuppressed().length);
                fromClose = thrown.getSuppressed()[0];
            }
            Assert.assertTrue("close() throws StreamIoException (block " + c + "): "
                    + fromClose, fromClose instanceof StreamIoException);
            Assert.assertTrue("the write's failure: " + fromClose.getCause(),
                    String.valueOf(fromClose.getCause()).contains("a failed append"));
        }
    }
    
    /**
     * bergdb 005-63: a start on a directory whose database is still closing after stop() is
     * refused at once, with DirectoryInUseException as the cause; after close() it starts.
     * The close waits here for a write whose force is held on a latch.
     */
    @Nano
    public static void testStartWhileStoppingRefused(TestEnvironment env) throws Exception {
        final String dir = env.createTempDir().getPath();
        final java.util.concurrent.CountDownLatch release = new java.util.concurrent.CountDownLatch(1);
        final java.util.concurrent.atomic.AtomicBoolean hold = 
                new java.util.concurrent.atomic.AtomicBoolean();
        FileStreamIo io = new FileStreamIo() {
            protected void forceFile(File file, RandomAccessFile handle) throws IOException {
                if (hold.get()) {
                    try {
                        release.await(30, java.util.concurrent.TimeUnit.SECONDS);
                    } catch (InterruptedException e) {
                        throw new IOException(e);
                    }
                }
                super.forceFile(file, handle);
            }
        };
        Database d = ((DatabaseBuilderImp) Factory.database())
                .mainStream(new FileStream(new File(dir), io)).start();
        d.connection().put("/a", "a");
        d.sync();
        hold.set(true);
        d.connection().put("/b", "b");      // Its write waits for the latch.
        d.stop();
        
        try {
            Factory.database().create(dir).start().close();
            throw new AssertionError("a database started while the other was closing");
        } catch (StreamIoException e) {
            Assert.assertTrue("the cause, " + e.getCause(), 
                    e.getCause() instanceof DirectoryInUseException);
        }
        
        release.countDown();
        d.close();
        Database d2 = Factory.database().create(dir).start();
        Assert.assertEquals("a", d2.connection().get("/a", String.class));
        Assert.assertEquals("b", d2.connection().get("/b", String.class));
        d2.close();
    }
    
    /**
     * bergdb 005-66: the builder opens its directories in start(). create() of a directory
     * that a database holds returns, and start() is refused; create() of a new directory
     * creates nothing; a builder that is dropped, and the first of two create(), hold
     * nothing. Until 005-66 the builder's dir(), create() since 015-05, opened the
     * directory, and those held its lock until the JVM ended.
     */
    @Nano
    public static void testBuilderOpensInStart(TestEnvironment env) throws Exception {
        File tmp = env.createTempDir();
        String a = new File(tmp, "a").getPath();
        File b = new File(tmp, "b");
        
        Database d = Factory.database().create(a).start();
        DatabaseBuilder held = Factory.database().create(a);
        try {
            held.start().close();
            throw new AssertionError("started on a directory that a database holds");
        } catch (StreamIoException e) {
            Assert.assertTrue("the cause, " + e.getCause(), 
                    e.getCause() instanceof DirectoryInUseException);
        }
        d.close();
        
        Factory.database().create(b.getPath());        // Dropped.
        Assert.assertFalse("create() created the directory", b.exists());
        
        Database d2 = Factory.database().create(a).create(b.getPath()).start();
        d2.connection().put("/k", "b");
        Database d3 = Factory.database().create(a).start();   // The first create() holds nothing.
        Assert.assertTrue(d3.connection().get("/k", String.class) == null);
        d3.close();
        d2.close();
        
        Database d4 = Factory.database().create(b.getPath()).start();
        Assert.assertEquals("b", d4.connection().get("/k", String.class));
        d4.close();
    }
    
    /**
     * Regression test for bergdb 015-56 (review R8, R8-F10): a second start() of a builder
     * whose database runs is refused, as one of another builder on the directory is, and the
     * refusal leaves the running database as it was: its stream, its lock and its files.
     * Until 015-56 the refused start closed the streams that the builder still held from the
     * first start, the running database's: its next sync failed the database, which lost
     * "/b", and its lock was released.
     */
    @Nano
    public static void testSecondStartOfOneBuilder(TestEnvironment env) throws Exception {
        File dir = new File(env.createTempDir(), "db");
        DatabaseBuilder builder = Factory.database().create(dir.getPath());
        Database d = builder.start();
        d.connection().put("/a", "a0");
        d.sync();
        String files = filesAndLengths(dir);
        
        assertStartRefused("the same builder", builder);
        Assert.assertEquals("the files", files, filesAndLengths(dir));
        d.connection().put("/b", "b0");
        d.sync();
        assertStartRefused("another builder", Factory.database().create(dir.getPath()));
        Assert.assertEquals("b0", d.connection().get("/b", String.class));
        d.close();
        
        Database again = builder.start();
        Assert.assertEquals("a0", again.connection().get("/a", String.class));
        Assert.assertEquals("b0", again.connection().get("/b", String.class));
        again.close();
    }
    
    /**
     * Regression test for bergdb 015-65: a second start() of a memory() builder whose
     * database runs is refused, without and with a crypto key, and the running database runs
     * on as before; memory() again gives the builder a new stream, and a new database. Until
     * 015-65 the second start gave the first database's MemoryStream to a second database
     * (with a key, it wrapped the first's SalsaStream again): both appended to it, each missed
     * the other's puts, and the close of one closed the stream of the other.
     */
    @Nano
    public static void testSecondStartOfMemoryBuilder() {
        for (boolean crypto : new boolean[] {false, true}) {
            String what = crypto ? "with a crypto key" : "without a crypto key";
            DatabaseBuilder builder = Factory.database().memory();
            if (crypto) {
                builder.cryptoKey(CryptoKey.generate());
            }
            Database d = builder.start();
            d.connection().put("/a", "a0");
            
            Database second;
            try {
                second = builder.start();
            } catch (IllegalStateException e) {
                second = null;
            }
            if (second != null) {
                closeQuietly(second);
                closeQuietly(d);
                throw new AssertionError("the second start returned, " + what);
            }
            
            d.connection().put("/b", "b0");
            d.sync();
            Assert.assertEquals("a0", d.connection().get("/a", String.class));
            Assert.assertEquals("b0", d.connection().get("/b", String.class));
            
            Database other = builder.memory().start();
            Assert.assertTrue("a new database, " + what,
                    other.connection().get("/a", String.class) == null);
            other.close();
            d.close();
        }
    }
    
    /**
     * Regression test for bergdb 015-49, S2-F24 (review S2): a key with a lone surrogate is
     * refused with IllegalArgumentException, by put(), get(), exists() and delete(); until
     * then the UTF-8 encoder stored it with '?' in the surrogate's place (005-26), so
     * "/k/a" followed by U+D800 and "/k/a?" were one key, and a put of one overwrote the
     * other. A key with a surrogate pair is taken and kept, as before.
     */
    @Nano
    public static void testKeyWithLoneSurrogateRefused() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            c.put("/k/a?", "question mark");
            String[] bad = {"/k/a\uD800", "/k/\uDC00a", "/k\uD800/a", "/k/\uDC00\uD800"};
            for (String key : bad) {
                assertKeyRefused("put", key, () -> c.put(key, "lone"));
                assertKeyRefused("get", key, () -> c.get(key, String.class));
                assertKeyRefused("exists", key, () -> c.exists(key));
                assertKeyRefused("delete", key, () -> c.delete(key));
                assertKeyRefused("w().put", key, () -> c.w().put(key, "lone").execute());
            }
            Assert.assertEquals("question mark", c.get("/k/a?", String.class));

            String pair = "/k/\uD83D\uDE00";        // U+1F600, a surrogate pair
            c.put(pair, "pair");
            Assert.assertEquals("pair", c.get(pair, String.class));
            Assert.assertEquals("question mark", c.get("/k/a?", String.class));
        } finally {
            d.close();
        }
    }

    /**
     * Regression test for bergdb 019-44: a String value with a lone surrogate is refused with
     * IllegalArgumentException, by put(), w().put() and an rw-transaction's put(), as a key
     * with one is (bergdb 015-49); before, its UTF-8 bytes had '?' in its place, silently,
     * and get() returned another string than was put. A value with a surrogate pair is
     * taken and kept.
     */
    @Nano
    public static void testValueWithLoneSurrogateRefused() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            String[] bad = {"a\uD800", "\uDC00a", "a\uD800b", "\uDC00\uD800", "\uD83D\uD83D\uDE00"};
            for (String value : bad) {
                assertKeyRefused("put", value, () -> c.put("/k", value));
                assertKeyRefused("w().put", value, () -> c.w().put("/k", value).execute());
                assertKeyRefused("rw put", value, () -> c.rw(env -> env.put("/k", value)));
            }
            Assert.assertTrue("nothing put", !c.exists("/k"));

            String pair = "a\uD83D\uDE00b";        // U+1F600, a surrogate pair
            c.put("/k", pair);
            Assert.assertEquals(pair, c.get("/k", String.class));
        } finally {
            d.close();
        }
    }

    /**
     * bergdb 019-44: TestClock's time is volatile, as the database's threads read it while
     * the test's thread sets it.
     */
    @Nano
    public static void testTestClockTimeIsVolatile() throws NoSuchFieldException {
        int modifiers = TestClock.class.getDeclaredField("time").getModifiers();
        Assert.assertTrue("TestClock.time is volatile",
                java.lang.reflect.Modifier.isVolatile(modifiers));
    }

    /**
     * Asserts that 'call' throws IllegalArgumentException for 'key' (bergdb 015-49, S2-F24),
     * or for a value (bergdb 019-44).
     */
    private static void assertKeyRefused(String what, String key, Runnable call) {
        try {
            call.run();
        } catch (IllegalArgumentException e) {
            return;
        }
        StringBuilder escaped = new StringBuilder();
        for (char ch : key.toCharArray()) {
            escaped.append(ch < 128 ? String.valueOf(ch) : String.format("\\u%04X", (int) ch));
        }
        throw new AssertionError(what + " took a lone surrogate, " + escaped);
    }

    /** Closes 'd'; what the close throws is dropped. */
    private static void closeQuietly(Database d) {
        try {
            d.close();
        } catch (RuntimeException e) {
            // Dropped.
        }
    }
    
    /**
     * Asserts that start() of 'builder' is refused as its directory is in use (bergdb
     * 005-63); a database that starts is closed.
     */
    private static void assertStartRefused(String what, DatabaseBuilder builder) {
        Database started;
        try {
            started = builder.start();
        } catch (StreamIoException e) {
            Assert.assertTrue(what + ", the cause, " + e.getCause(), 
                    e.getCause() instanceof DirectoryInUseException);
            return;
        }
        started.close();
        throw new AssertionError("started, " + what);
    }
    
    /** The names and lengths of the files in 'dir', sorted by name. */
    private static String filesAndLengths(File dir) {
        File[] files = dir.listFiles();
        Arrays.sort(files);
        StringBuilder sb = new StringBuilder();
        for (File f : files) {
            sb.append(f.getName()).append(' ').append(f.length()).append('\n');
        }
        return sb.toString();
    }
    
    private static String v1;
    private static String v2;
    
    @Nano
    public static void testRw1() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        c.w().put("/key1", "value1").put("/key2", "value2..").execute();
        
        c.rw(new Action() { 
            public void run(RwEnvironment env) {
                v1 = env.get("/key1", String.class);
                v2 = env.get("/key2", String.class);
                env.put("/length", "" + (v1.length() + v2.length()));
            }
        });
        
        Assert.assertEquals("value1", v1);
        Assert.assertEquals("value2..", v2);
        Assert.assertEquals("14", c.get("/length", String.class));
        database.stop();
    }
    
    @Nano
    public static void testRw2() throws InterruptedException {
        //
        // An RW transaction that should result in an STM rerun of the transaction since another
        // thread modified one of the KVs in the read set.
        //
        
        Database db = Factory.database().memory().start();
        final Connection c1 = db.connection();
        c1.w().put("/key1", "value1").put("/key2", "value2..").execute();
        
        final EventToWaitFor modifiedKey1 = new EventToWaitFor();
        final EventToWaitFor getDone = new EventToWaitFor();
        
        final Action action = new Action() { 
            public void run(RwEnvironment env) {
                v1 = env.get("/key1", String.class);
                v2 = env.get("/key2", String.class);
                getDone.happened();
                modifiedKey1.waitForEvent();
                String lengthString = "" + (v1.length() + v2.length());
                env.put("/length", lengthString);
            }
        };
        
        Connection c2 = db.connection();
        final Transaction[] transactionArray = new Transaction[1];
        
        Thread thread = new Thread(new Runnable() {
            public void run() {
                transactionArray[0] = c1.rw(action);
            }
        });
        thread.start();
        
        getDone.waitForEvent();
        c2.w().put("/key1", "value1B").execute();
        modifiedKey1.happened();
        
        thread.join();
        
        Assert.assertEquals(2, ((RwTransaction) transactionArray[0]).getRunCount());
        Assert.assertEquals("value2..", v2);
        Assert.assertEquals("15", c1.get("/length", String.class));
        db.stop();
    }
    
    private static void assertNoEntry(String what, String value) {
        Assert.assertTrue(what + ": expected no entry, got '" + value + "'.", value == null);
    }
    
    /**
     * bergdb 015-40 (review 016-06/S1, S1-F1): in an rw-transaction, a put and then a delete
     * of a key with a suffix leave no entry. Until 015-40 the put stayed: MapKey.equals was
     * never true, so kvOps held both operations, and Trans.Builder.build keeps a put over a
     * delete.
     */
    @Nano
    public static void testRwPutThenDelete() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            c.put("/a.txt", "old");
            c.rw(new Action() {
                public void run(RwEnvironment env) {
                    env.put("/a.txt", "new");
                    env.delete("/a.txt");
                }
            });
            assertNoEntry("rw: put then delete", c.get("/a.txt", String.class));
        } finally {
            db.close();
        }
    }
    
    /** bergdb 015-40: the same through WBuilder; and a delete and then a put leave the put. */
    @Nano
    public static void testWPutThenDelete() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            c.put("/b.txt", "old");
            c.w().put("/b.txt", "new").delete("/b.txt").execute();
            assertNoEntry("w: put then delete", c.get("/b.txt", String.class));
            c.w().delete("/b.txt").put("/b.txt", "again").execute();
            Assert.assertEquals("w: delete then put", "again", c.get("/b.txt", String.class));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-40 (S1-F1): of many puts of one key in an rw-transaction, the last wins.
     * Until 015-40 each put was an entry of its own in kvOps, all in one bin; once the bin
     * was a tree (more than 8 entries), the iteration order was not the order of the puts,
     * and Trans.Builder.build keeps the last one it is given.
     */
    @Nano
    public static void testRwManyPutsOfOneKey() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            for (int round = 0; round < 20; round++) {
                final int n = 40;
                c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        for (int i = 0; i < n; i++) {
                            env.put("/c.txt", "v" + i);
                        }
                    }
                });
                Assert.assertEquals("round " + round, "v" + (n - 1), c.get("/c.txt", String.class));
            }
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-41 (review 016-06/S1, S1-F2): in an rw-transaction, a String put and then a
     * delete of a key without a suffix leave no entry. Until 015-41 the put stayed: the put
     * went to kvOps and the delete of an object key to objectOps, and Trans.Builder.build
     * keeps a put over a delete. A delete and then a put, and a put, a delete and a put,
     * leave the last put.
     */
    @Nano
    public static void testRwStringPutThenDeleteOfObjectKey() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            c.put("/d", "old");
            c.rw(new Action() {
                public void run(RwEnvironment env) {
                    env.put("/d", "new");
                    env.delete("/d");
                }
            });
            assertNoEntry("rw: String put, then delete", c.get("/d", String.class));
            c.w().put("/d", "new").delete("/d").execute();
            assertNoEntry("w: String put, then delete", c.get("/d", String.class));
            c.w().put("/d", new byte[] {1}).delete("/d").execute();
            Assert.assertTrue("w: byte[] put, then delete", c.get("/d", byte[].class) == null);
            c.w().delete("/d").put("/d", "again").execute();
            Assert.assertEquals("w: delete, then put", "again", c.get("/d", String.class));
            c.w().put("/d", "1").delete("/d").put("/d", "2").execute();
            Assert.assertEquals("w: put, delete, put", "2", c.get("/d", String.class));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-41 (S1-F2, its second half): an object put and then a String put of one key
     * leave the String. Until 015-41 the object stayed: objectOps is added to the
     * transaction after kvOps, and Trans.Builder.build keeps the later put. An object put is
     * experimental in 2026.3 (bergdb 018-01, D6).
     */
    @Nano
    public static void testRwObjectPutThenStringPut() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            c.rw(new Action() {
                public void run(RwEnvironment env) {
                    env.put("/e", new Person("Ann"));
                    env.put("/e", "text");
                }
            });
            Assert.assertEquals("object put, then String put", "text",
                    c.get("/e", String.class));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-40: a delete and then a put of a key with ${transactionTime}: the put wins,
     * with its key transformation. A HashMap keeps its first key object when a put replaces
     * an entry, so RwEnvironmentImp removes the key first; without that, the delete's MapKey,
     * which has no transformation, would store the value at the key as written.
     */
    @Nano
    public static void testWDeleteThenPutOfReplacedKey() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            c.setEnableKeyReplace(true);
            String key = "/t/${transactionTime}.txt";
            Transaction t = c.w().delete(key).put(key, "v").execute();
            String replaced = String.format(Locale.US, "/t/%018d.txt", t.getTime().units());
            Assert.assertEquals("the replaced key", "v", c.get(replaced, String.class));
            assertNoEntry("the key as written", c.get(key, String.class));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-64: key replace replaces every "${transactionTime}" of a key, as
     * Connection.setEnableKeyReplace() says ("occurrences"); before 015-64, only the last.
     */
    @Nano
    public static void testKeyReplaceEveryOccurrence() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            c.setEnableKeyReplace(true);
            String key = "/a/${transactionTime}/b/${transactionTime}${transactionTime}.txt";
            Transaction t = c.put(key, "v");
            String time = String.format(Locale.US, "%018d", t.getTime().units());
            String replaced = "/a/" + time + "/b/" + time + time + ".txt";
            Assert.assertEquals("every occurrence replaced", "v", c.get(replaced, String.class));
            assertNoEntry("only the last two replaced", 
                    c.get("/a/${transactionTime}/b/" + time + time + ".txt", String.class));
            assertNoEntry("only the last replaced", 
                    c.get("/a/${transactionTime}/b/${transactionTime}" + time + ".txt", 
                    String.class));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-47: a byte[] value is copied at its put, not at its get (Frans's option
     * (c), 2026-11-05). A change of the array of a put, after the put, by Connection.put,
     * WBuilder.put or RwEnvironment.put, does not change the stored value; before 015-47,
     * the value in memory was the caller's array. A get returns the database's own array,
     * zero-copy, as its Javadoc says: two gets of a value in memory return the same array.
     */
    @Nano
    public static void testByteArrayCopiedAtPutNotAtGet() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            final byte[] b1 = {1, 2, 3};
            final byte[] b2 = {1, 2, 3};
            final byte[] b3 = {1, 2, 3};
            c.put("/b1.bin", b1);
            c.w().put("/b2.bin", b2).execute();
            c.rw(new Action() {
                public void run(RwEnvironment env) {
                    env.put("/b3.bin", b3);
                }
            });
            b1[0] = 9;
            b2[0] = 9;
            b3[0] = 9;
            
            for (String key : new String[] {"/b1.bin", "/b2.bin", "/b3.bin"}) {
                Assert.assertEquals("the value at " + key, "[1, 2, 3]", 
                        Arrays.toString(c.get(key, byte[].class)));
            }
            Assert.assertTrue("a get returns the database's own array", 
                    c.get("/b1.bin", byte[].class) == c.get("/b1.bin", byte[].class));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 019-05: exists() of a key that does not follow the allowed format throws
     * IllegalArgumentException, as get() does, in a connection and in an rw-transaction
     * alike: an empty key, one without the leading '/', '/' alone, one ending with '/'
     * and one with "//". Until 019-05 a connection's exists() answered false for it; an
     * rw-transaction's threw, and c.rw() throws it (the test pins that).
     */
    @Nano
    public static void testExistsOfMalformedKeyThrows() {
        Database db = Factory.database().memory().start();
        try {
            final Connection c = db.connection();
            c.put("/a/b", "v");
            for (final String key : new String[] {"", "a/b", "/", "/a/", "/a//b"}) {
                String k = "key '" + key + "'";
                assertIllegalKey(k + ", connection get()", () -> c.get(key, String.class));
                assertIllegalKey(k + ", connection exists()", () -> c.exists(key));
                assertIllegalKey(k + ", rw-transaction get()", () -> c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        env.get(key, String.class);
                    }
                }));
                assertIllegalKey(k + ", rw-transaction exists()", () -> c.rw(new Action() {
                    public void run(RwEnvironment env) {
                        env.exists(key);
                    }
                }));
            }
            Assert.assertTrue("a valid key after the refused ones", c.exists("/a/b"));
        } finally {
            db.close();
        }
    }
    
    private static void assertIllegalKey(String what, Runnable read) {
        try {
            read.run();
        } catch (IllegalArgumentException e) {
            return;
        }
        throw new AssertionError(what + ": expected IllegalArgumentException");
    }
    
    public static class Person {
        public String name;
        
        public Person() {}
        
        public Person(String name) {
            this.name = name;
        }
    }
    
    @Nano
    public static void testDirManyObjects1() {
        // Lookup of large number of objects. DB.getMany() must be called several times.   
        manyObjects(233);
    }
    
    @Nano
    public static void testDirManyObjects2() {
        // Lookup of large number of objects. Exactly 200 objects (same as precisely 2 DB.getMany
        // calls).
        manyObjects(200);
    }
    
    private static void manyObjects(int count) {        
        Database db = Factory.database().memory().start();
        Connection c = db.connection();
        
        WBuilder b = c.w();
        for (int i = 0; i < count; i++) {
            b.put("/persons/" + (1000 + i), new Person("P" + (1000 + i)));
        }
        b.execute();
        
        Iterator<Person> persons = c.usePrimary(Person.class).dir("/persons/").objects().iterator();
        
        for (int i = 0; i < count; i++) {
            Assert.assertTrue(persons.hasNext());
            Person p = persons.next();
            Assert.assertEquals("P" + (1000 + i), p.name);
        }
        
        Assert.assertFalse(persons.hasNext());
        db.stop();
    }
    
    
    public static class Payment {
        public String from;
        public String to;
        public long amount;
        
        @SuppressWarnings("unused")
        public Payment() {}
        
        public Payment(String from, String to, long amount) {
            this.from = from;
            this.to = to;
            this.amount = amount;
        }
        public String toString() {
            return amount + " paid from " + from + " to " + to + ".";
        }
    }
    
    public static class MyDouble {
        public double value;
        public String key;
        
        public MyDouble() {}
        
        public MyDouble(double v) {
            value = v;
        }
    }
    
    
    public static class MyString {
        public String s;
        
        public MyString() {}
        
        public MyString(String s) {
            this.s = s;
        }
        
        public String toString() {
            return s;
        }
    }
    
    public static class House {
        public House() {}
        public String key;
        public String name;
        public long area;
    }
    
    
    
    @Nano
    public static void testKeyReplace1() {
        // Two write transactions. transactionTime used in key.
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        String key = "/payments/${transactionTime}";
        Payment p1 = new Payment("100", "105", 120);
        Payment p2 = new Payment("100", "105", 200);
        
        c.setEnableKeyReplace(true);
        c.w().put(key, p1).execute();
        c.w().put(key, p2).execute();
        
        Iterator<Kv<Payment>> iter = c.usePrimary(Payment.class).dir("/payments/").kvs().iterator();
        
        String key1;
        String key2;
        Assert.assertTrue(iter.hasNext());
        Kv<Payment> kv = iter.next();
        key1 = kv.key();
        Assert.assertTrue(key1.startsWith("/payments/"));
        long t1 = Long.parseLong(key1.substring("/payments/".length()));
        Assert.assertTrue(iter.hasNext());
        
        kv = iter.next();
        key2 = kv.key();
        Assert.assertTrue(key2.startsWith("/payments/"));
        long t2 = Long.parseLong(key2.substring("/payments/".length()));
        Assert.assertFalse(iter.hasNext());
        Assert.assertFalse(key1.equals(key2));
        
        Assert.assertTrue(t2 > t1);
        database.stop();
    }
    
    @Nano
    public static void testFreezeLookupTime1() {
        TestClock clock = new TestClock();
        Database database = Factory.database().memory().clock(clock).start();
        Connection c1 = database.connection();
        
        clock.setTime(Time.units(100));
        c1.w().put("/a", "1").put("/b", "2").execute();
        c1.freezeLookupTime();
        c1.get("/a", String.class);
        
        Connection c2 = database.newConnection();
        clock.setTime(Time.units(200));
        c2.w().put("/b", "2b").put("/c", "3b").execute();
        
        Assert.assertEquals("2", c1.get("/b", String.class));
        Assert.assertNull(c1.get("/c", String.class));
        
        c1.setLookupTime(Time.MAX);
        Assert.assertEquals("2b", c1.get("/b", String.class));
        Assert.assertEquals("3b", c1.get("/c", String.class));
        database.stop();
    }
    
    /**
     * bergdb 015-42 (016-06, S1-F3): Connection.freezeLookupTime(): "The lookup time of
     * this Connection will not change until setLookupTime() is called or this method is
     * called again." An rw() whose action read, on the same connection, set the frozen time
     * to the rw's read time, the latest.
     */
    @Nano
    public static void testRwKeepsFrozenLookupTime() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            Connection other = db.newConnection();
            c.put("/f.txt", "1");
            c.freezeLookupTime();
            Assert.assertEquals("1", c.get("/f.txt", String.class));
            other.put("/f.txt", "2");
            Assert.assertEquals("frozen before rw", "1", c.get("/f.txt", String.class));
            c.rw(new Action() {
                public void run(RwEnvironment env) {
                    env.get("/g.txt", String.class);
                }
            });
            Assert.assertEquals("frozen after rw", "1", c.get("/f.txt", String.class));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-42 (016-06, S1-F3), through a w-transaction: the put of an object in a
     * directory with an index reads the object's previous value, and that read set the
     * frozen time too.
     */
    @Nano
    public static void testObjectPutKeepsFrozenLookupTime() {
        Database db = Factory.database().memory().start();
        try {
            db.indexBuilder("area").dir("/houses/").type("long").field("area").start().join();
            Connection c = db.connection();
            Connection other = db.newConnection();
            c.put("/f.txt", "1");
            c.freezeLookupTime();
            Assert.assertEquals("1", c.get("/f.txt", String.class));
            other.put("/f.txt", "2");
            House h = new House();
            h.area = 120;
            c.put("/houses/h1", h);
            Assert.assertEquals("frozen after an object put", "1", c.get("/f.txt", String.class));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-42 (016-06, S1-F3): Connection.transactionInfo() is of "the last value
     * retrieved with the get() method"; after an rw() whose action read, it was of the rw's
     * last read.
     */
    @Nano
    public static void testRwKeepsTransactionInfo() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.connection();
            final long ta = c.put("/a.txt", "a").getTime().units();
            final long tb = c.put("/b.txt", "b").getTime().units();
            Assert.assertTrue("tb differs", tb != ta);
            Assert.assertEquals("a", c.get("/a.txt", String.class));
            Assert.assertEquals("before rw", ta, c.transactionInfo().time().units());
            c.rw(new Action() {
                public void run(RwEnvironment env) {
                    env.get("/b.txt", String.class);
                }
            });
            Assert.assertEquals("after rw", ta, c.transactionInfo().time().units());
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-48 (016-06, S1-F9): freezeLookupTime(), then exists() as the first read.
     * exists() froze the time of the read before it, or -1 if there was none, and read at
     * the time asked for. Now the frozen time is that of the exists(), as for a get().
     */
    @Nano
    public static void testFreezeThenExists() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            Connection other = db.newConnection();
            other.put("/a.txt", "1");
            c.freezeLookupTime();
            Assert.assertTrue("exists, no read before", c.exists("/a.txt"));
            Assert.assertEquals("get after exists, no read before", "1", 
                    c.get("/a.txt", String.class));
            
            Connection c2 = db.newConnection();
            Assert.assertEquals("1", c2.get("/a.txt", String.class));
            other.put("/a.txt", "2");
            c2.freezeLookupTime();
            Assert.assertTrue("exists, a read before", c2.exists("/a.txt"));
            Assert.assertEquals("get after exists, a read before", "2", 
                    c2.get("/a.txt", String.class));
            other.put("/a.txt", "3");
            Assert.assertEquals("frozen", "2", c2.get("/a.txt", String.class));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 018-04, Q2 (Frans, 2026-11-06, option (c)): each call of freezeLookupTime()
     * freezes anew, at the latest state as of the next read; setLookupTime() and
     * freezeLookupTime() each undo the other. A second call on a frozen connection changed
     * nothing: the reads after it kept the first frozen time, and missed a write made since.
     */
    @Nano
    public static void testFreezeAgainReadsNewState() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            Connection other = db.newConnection();
            Time t1 = other.put("/a.txt", "1").getTime();
            c.freezeLookupTime();
            Assert.assertEquals("first freeze", "1", c.get("/a.txt", String.class));
            Assert.assertEquals("frozen at t1", t1, c.getLookupTime());
            Time t2 = other.put("/a.txt", "2").getTime();
            Assert.assertEquals("frozen", "1", c.get("/a.txt", String.class));
            
            c.freezeLookupTime();
            Assert.assertEquals("second freeze, before a read", Time.MAX, c.getLookupTime());
            Assert.assertEquals("second freeze", "2", c.get("/a.txt", String.class));
            Assert.assertEquals("frozen at t2", t2, c.getLookupTime());
            other.put("/a.txt", "3");
            Assert.assertEquals("frozen again", "2", c.get("/a.txt", String.class));
            
            c.setLookupTime(t1);
            Assert.assertEquals("setLookupTime(t1)", "1", c.get("/a.txt", String.class));
            c.freezeLookupTime();
            Assert.assertEquals("freeze after setLookupTime(t1): the latest state", "3", 
                    c.get("/a.txt", String.class));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-60 (review 016-06/R8, R8-F5): Database.connection() keeps no connection for
     * a thread that has ended. Until 015-60 a map of each thread's connection kept every
     * thread that had called it, and its connection, until the database stopped: memory
     * without a bound in a program whose threads come and go.
     */
    @Nano
    public static void testConnectionOfEndedThreadNotKept() throws Exception {
        final Database db = Factory.database().memory().start();
        try {
            final int n = 20;
            final java.util.List<java.lang.ref.WeakReference<Connection>> refs =
                    new java.util.ArrayList<java.lang.ref.WeakReference<Connection>>();
            for (int i = 0; i < n; i++) {
                Thread t = new Thread(new Runnable() {
                    public void run() {
                        refs.add(new java.lang.ref.WeakReference<Connection>(db.connection()));
                    }
                });
                t.start();
                t.join();
            }
            int kept = n;
            for (int round = 0; round < 50 && kept > 0; round++) {
                System.gc();
                db.connection();
                kept = 0;
                for (java.lang.ref.WeakReference<Connection> ref : refs) {
                    if (ref.get() != null) {
                        kept++;
                    }
                }
            }
            Assert.assertEquals("the threads' connections", n, refs.size());
            Assert.assertEquals("connections of ended threads kept", 0, kept);
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-59 (016-06, R8-F4): the requested lookup time of a connection is Time.MAX
     * by default (Connection.setLookupTime()). A new connection had Long.MAX_VALUE, above
     * Time's range, and getLookupTime() threw IllegalArgumentException.
     */
    @Nano
    public static void testNewConnectionLookupTime() {
        Database db = Factory.database().memory().start();
        try {
            db.connection().put("/a", "1");
            Connection c = db.newConnection();
            Assert.assertEquals("newConnection()", Time.MAX, c.getLookupTime());
            Assert.assertEquals("1", c.get("/a", String.class));
            Assert.assertEquals("connection()", Time.MAX, db.connection().getLookupTime());
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-62 (016-06, R8-F7): transactionInfo() after a get() that found no entry,
     * on a connection whose gets have retrieved no value, threw IllegalArgumentException
     * (from Db.getTrans(0)). It is IllegalStateException, as when no get() has been made.
     */
    @Nano
    public static void testTransactionInfoAfterGetOfMissingKey() {
        Database db = Factory.database().memory().start();
        try {
            Connection c = db.newConnection();
            c.put("/a", "1");
            Assert.assertNull(c.get("/missing", String.class));
            try {
                c.transactionInfo();
                throw new AssertionError("transactionInfo() returned");
            } catch (IllegalStateException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("found no entry"));
            }
            
            Assert.assertEquals("1", c.get("/a", String.class));
            Assert.assertEquals("1", new String(c.transactionInfo().kvs().get(0).value(), 
                    java.nio.charset.StandardCharsets.UTF_8));
        } finally {
            db.close();
        }
    }
    
    @Nano
    public static void nullStringField() {
        // Tests storing an object with a null field.
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        MyString s1 = new MyString(null);
        c.w().put("/d/s", s1).execute();
        MyString s2 = c.get("/d/s", MyString.class);
        Assert.assertNull(s2.s);
        d.stop();
    }
    
    public static class StringArrayClass {
        public String[] strings;
    }
    
    @Nano
    public static void nullStringArrayField1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        StringArrayClass a = new StringArrayClass();
        a.strings = null;
        c.w().put("/d/a", a).execute();
        StringArrayClass b = c.get("/d/a", StringArrayClass.class);
        Assert.assertNull(b.strings);
        d.stop();
    }
    
    /** A null array element is refused (bergdb 020-04, section 2.1; 020-09, section 4.3). */
    @Nano
    public static void nullStringArrayField2() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        StringArrayClass a = new StringArrayClass();
        a.strings = new String[]{"", null};
        try {
            c.w().put("/d/a", a).execute();
            throw new AssertionError("no exception");
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("'strings[1]'"));
        }
        Assert.assertNull(c.get("/d/a", Object.class));
        d.stop();
    }
    
    /**
     * bergdb 020-04, N5: a put of a refused object writes nothing, also of the valid objects
     * of its transaction; inside rw(), the refusal is the action's exception, and the
     * database goes on.
     */
    @Nano
    public static void testRefusedObjectWritesNothing() {
        Database d = Factory.database().memory().start();
        try {
            final Connection c = d.connection();
            final StringArrayClass good = new StringArrayClass();
            good.strings = new String[]{"a"};
            final StringArrayClass bad = new StringArrayClass();
            bad.strings = new String[]{"a", null};
            for (int i = 0; i < 2; i++) {
                try {
                    if (i == 0) {
                        c.w().put("/good", good).put("/bad", bad).execute();
                    } else {
                        c.rw(new Action() {
                            public void run(RwEnvironment env) {
                                env.put("/good", good);
                                env.put("/bad", bad);
                            }
                        });
                    }
                    throw new AssertionError("no exception, " + i);
                } catch (IllegalArgumentException e) {
                    Assert.assertTrue(e.getMessage(), e.getMessage().contains("'strings[1]'"));
                }
                Assert.assertNull(c.get("/good", Object.class));
                Assert.assertNull(c.get("/bad", Object.class));
            }
            c.put("/good", good);
            Assert.assertArrayEquals(good.strings, 
                    c.get("/good", StringArrayClass.class).strings);
        } finally {
            d.close();
        }
    }
    
    public static class IntV {
        public int v;
        public IntV() {}
        public IntV(int v) {
            this.v = v;
        }
    }
    
    public static class LongV {
        public long v;
        public LongV() {}
        public LongV(long v) {
            this.v = v;
        }
    }
    
    /**
     * bergdb 020-08, T10: one integer (020-02, section 4.7): an int field and a long field
     * of one value give one sort key in a long index, and are found by it in its order.
     */
    @Nano
    public static void testLongIndexOverOneInteger() {
        Database d = Factory.database().memory().start();
        try {
            d.indexBuilder("v").dir("/t/").type("long").field("v").start().join();
            Connection c = d.connection();
            c.w().put("/t/a", new IntV(7)).put("/t/b", new LongV(7)).put("/t/c", 
                    new LongV(1L << 40)).put("/t/d", new IntV(-3)).put("/t/e", 
                    new LongV(Long.MIN_VALUE)).execute();
            StringBuilder keys = new StringBuilder();
            for (Kv<DbObject> kv : c.useIndex("v", DbObject.class).kvs()) {
                keys.append(kv.key()).append(' ').append(kv.value().getLong("v")).append(';');
            }
            Assert.assertEquals("/t/e -9223372036854775808;/t/d -3;/t/a 7;/t/b 7;"
                    + "/t/c 1099511627776;", keys.toString());
            keys.setLength(0);
            for (Kv<DbObject> kv : c.useIndex("v", DbObject.class).eq(7).kvs()) {
                keys.append(kv.key()).append(';');
            }
            Assert.assertEquals("/t/a;/t/b;", keys.toString());
        } finally {
            d.close();
        }
    }
    
    public static class IntClass {
        public int field;
    }
    
    @Nano
    public static void intField() {
        IntClass o1 = new IntClass();
        o1.field = 1234567890;
        
        Database d = Factory.database().memory().start();
        d.connection().w().put("/d/o1", o1).execute();
        IntClass o2 = d.connection().get("/d/o1", IntClass.class);
        Assert.assertEquals(o2.field, o1.field);
        d.stop();
    }
    
    @Nano
    public static void testRetainDuration1() {
        Database d = Factory.database().memory().start();
        
        Duration duration = d.getRetainDuration();
        Assert.assertTrue(duration.units() > 0);
        
        d.setRetainDuration(Duration.seconds(123.0));
        Assert.assertEquals(Duration.seconds(123.0), d.getRetainDuration());
        d.stop();
    }
    
    @Nano
    public static void testRetainDuration2() {
        DatabaseBuilder builder = Factory.database().memory();
        Database d = builder.start();
        d.connection().w().put("/key", "value").execute();
        d.setRetainDuration(Duration.seconds(21));
        
        d.connection().w().put("/key2", "value2").execute();
        Assert.assertEquals(Duration.seconds(21.0), d.getRetainDuration());
        d.stop();
    }

    /**
     * The startup distance set while the database runs (Database.setStartupDistanceInMb,
     * bergdb 005-53, option E): in force when the call returns, written to the stream with
     * the call's own transaction (a value of 200 kB), and kept by a restart whose builder
     * passes its default; a call with the setting in force appends nothing; the value clamped
     * to 5 to 1000 MB, as the builder clamps it. A call after stop() throws and leaves the
     * setting as it was. Until 005-53 the core's setter wrote its transaction also for the
     * setting in force, and changed the setting before it checked the state.
     */
    @Nano
    public static void testSetStartupDistanceInMb() {
        MemoryStream m = new MemoryStream();
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m).start();
        Db db = ((DatabaseImp) d).getDb();
        Assert.assertEquals(50, d.getStartupDistanceInMb());
        d.connection().w().put("/a", "1").execute();
        
        long length = db.getStreamLength();
        d.setStartupDistanceInMb(20);
        Assert.assertEquals(20, d.getStartupDistanceInMb());
        Assert.assertEquals(20 * 1000000, db.getStartupDistance());
        Assert.assertTrue("the call's transaction", 
                db.getStreamLength() - length >= RecoverableStream.META_BLOCK_DISTANCE);
        
        length = db.getStreamLength();
        d.setStartupDistanceInMb(20);
        Assert.assertEquals("the setting in force: nothing appended", length, 
                db.getStreamLength());
        
        d.setStartupDistanceInMb(1);
        Assert.assertEquals(5, d.getStartupDistanceInMb());
        d.setStartupDistanceInMb(5000);
        Assert.assertEquals(1000, d.getStartupDistanceInMb());
        d.setStartupDistanceInMb(20);
        d.connection().w().put("/a", "2").execute();
        d.sync();
        d.stop();
        
        IllegalDbStateException ex = null;
        try {
            d.setStartupDistanceInMb(30);
        } catch (IllegalDbStateException e) {
            ex = e;
        }
        Assert.assertTrue("a call after stop() throws", ex != null);
        Assert.assertEquals("the refused call changed the setting", 20, 
                d.getStartupDistanceInMb());
        d.close();
        
        d = ((DatabaseBuilderImp) Factory.database()).mainStream(m.copy()).start();
        Assert.assertEquals("kept by the restart", 20, d.getStartupDistanceInMb());
        Assert.assertEquals("2", d.connection().get("/a", String.class));
        d.stop();
    }
    
    /**
     * The retain duration through the Pub API (bergdb 015-87): set only by
     * setRetainDuration, after the start, and kept in the stream, so a restart keeps it,
     * forever (Duration.MAX) too; a call with the value in force appends nothing; a call
     * with less than one second, or after stop(), throws and changes nothing. Before 015-87
     * a start took the builder's value, forever by default.
     */
    @Nano
    public static void testSetRetainDurationKept() {
        MemoryStream m = new MemoryStream();
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m).start();
        Db db = ((DatabaseImp) d).getDb();
        Assert.assertEquals("forever when never set", Duration.MAX, d.getRetainDuration());
        d.connection().w().put("/a", "1").execute();
        
        long length = db.getStreamLength();
        d.setRetainDuration(Duration.seconds(30));
        Assert.assertEquals(Duration.seconds(30), d.getRetainDuration());
        Assert.assertTrue("the call's transaction", db.getStreamLength() > length);
        length = db.getStreamLength();
        d.setRetainDuration(Duration.seconds(30));
        Assert.assertEquals("the value in force: nothing appended", length,
                db.getStreamLength());
        
        IllegalArgumentException tooShort = null;
        try {
            d.setRetainDuration(Duration.seconds(0.5));
        } catch (IllegalArgumentException e) {
            tooShort = e;
        }
        Assert.assertTrue("less than one second throws", tooShort != null);
        Assert.assertEquals("unchanged", Duration.seconds(30), d.getRetainDuration());
        Assert.assertEquals("nothing appended", length, db.getStreamLength());
        d.connection().w().put("/a", "2").execute();
        d.sync();
        d.stop();
        
        IllegalDbStateException ex = null;
        try {
            d.setRetainDuration(Duration.seconds(40));
        } catch (IllegalDbStateException e) {
            ex = e;
        }
        Assert.assertTrue("a call after stop() throws", ex != null);
        Assert.assertEquals("the refused call changed nothing", Duration.seconds(30),
                d.getRetainDuration());
        d.close();
        
        m = m.copy();
        d = ((DatabaseBuilderImp) Factory.database()).mainStream(m).start();
        Assert.assertEquals("kept by the restart", Duration.seconds(30), d.getRetainDuration());
        Assert.assertEquals("2", d.connection().get("/a", String.class));
        d.setRetainDuration(Duration.MAX);
        d.sync();
        d.stop();
        
        d = ((DatabaseBuilderImp) Factory.database()).mainStream(m.copy()).start();
        Assert.assertEquals("forever kept by the restart", Duration.MAX, d.getRetainDuration());
        d.stop();
    }
    
    /**
     * A decrease of the startup distance through the Pub API pays the startup section's
     * index nodes over several records (bergdb 007-03, D4:B; 007-07; 005-53): a database at
     * 50 MB, 15,000 transactions of 20 puts of small values over a million keys (a section of
     * about 22 MB, all of the stream), lowered to 5 MB, then 300 commits. No record from the
     * call on is more than a third of what the records wrote until they were back near their
     * size before the call; with the deadline at twice the new setting at once, the call's
     * own record would take most of it.
     */
    @Nano("f")
    public static void testDecreaseOfStartupDistanceInMbF() {
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(new MemoryStream())
                .startupDistanceInMb(50).start();
        Db db = ((DatabaseImp) d).getDb();
        java.util.Random r = new java.util.Random(1);
        long before = 0;
        for (int i = 0; i < 15000; i++) {
            long length = db.getStreamLength();
            WBuilder w = d.connection().w();
            for (int j = 0; j < 20; j++) w.put("/k/" + r.nextInt(1000 * 1000), "vvvv");
            w.execute();
            if (i >= 14800) before = Math.max(before, db.getStreamLength() - length);
        }
        
        long length = db.getStreamLength();
        d.setStartupDistanceInMb(5);
        long largest = db.getStreamLength() - length;
        long paid = largest;
        boolean back = false;
        for (int i = 0; i < 300; i++) {
            length = db.getStreamLength();
            WBuilder w = d.connection().w();
            for (int j = 0; j < 20; j++) w.put("/k/" + r.nextInt(1000 * 1000), "vvvv");
            w.execute();
            long record = db.getStreamLength() - length;
            back = back || record < 10 * before;
            if (!back) {
                paid += record;
                largest = Math.max(largest, record);
            }
        }
        d.stop();
        Assert.assertTrue("back near the size before the call", back);
        Assert.assertTrue("paid " + paid, paid > 4 * 1000 * 1000);
        Assert.assertTrue("largest record " + largest + " of " + paid, largest < paid / 3);
    }
    
    /**
     * The cache size set while the database runs (Database.setCacheSizeInMb, bergdb 005-52,
     * option B): in force when the call returns, as the core's budget and Cache3's indicator;
     * clamped to 4 to 100,000 MB, as the builder clamps it; nothing written to the stream;
     * no exception after close(); and for the run only: a restart takes the builder's value.
     */
    @Nano
    public static void testSetCacheSizeInMb() {
        MemoryStream m = new MemoryStream();
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m).cacheSizeInMb(64)
                .start();
        Db db = ((DatabaseImp) d).getDb();
        Assert.assertEquals(64, d.getCacheSizeInMb());
        d.connection().w().put("/a", "1").execute();
        long length = db.getStreamLength();
        
        d.setCacheSizeInMb(32);
        Assert.assertEquals(32, d.getCacheSizeInMb());
        Assert.assertEquals(32L * 1000000, db.getCacheSizeIndicator());
        Assert.assertEquals(32L * 1000000, db.internal().eviction().budget());
        Assert.assertEquals(32L * 1000000, db.internal().cache().getSizeIndicator());
        d.setCacheSizeInMb(1);
        Assert.assertEquals(4, d.getCacheSizeInMb());
        d.setCacheSizeInMb(200 * 1000);
        Assert.assertEquals(100 * 1000, d.getCacheSizeInMb());
        Assert.assertEquals(100L * 1000 * 1000000, db.internal().eviction().budget());
        Assert.assertEquals("nothing written", length, db.getStreamLength());
        d.sync();
        d.close();
        d.setCacheSizeInMb(16);
        
        d = ((DatabaseBuilderImp) Factory.database()).mainStream(m.copy()).cacheSizeInMb(64)
                .start();
        Assert.assertEquals("the builder's value after a restart", 64, d.getCacheSizeInMb());
        d.stop();
    }
    
    /**
     * A lowered cache size gives the memory back on a database that is not used (bergdb
     * 005-52): 20,000 values of 1 kB written with a budget of 100 MB, so that the resident
     * bytes hold about 20 MB; the cache size lowered to 4 MB and no other call: the eviction
     * thread, which the call wakes, brings the resident bytes to at most 4 MB within 5 s.
     * Until 005-52 nothing ran until the next commit or load (005-51).
     */
    @Nano("f")
    public static void testLoweredCacheSizeWhileIdleF() throws InterruptedException {
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(new MemoryStream())
                .startupDistanceInMb(5).cacheSizeInMb(100).start();
        Db db = ((DatabaseImp) d).getDb();
        char[] chars = new char[1000];
        java.util.Arrays.fill(chars, 'v');
        String value = new String(chars);
        for (int i = 0; i < 20000; i += 100) {
            WBuilder w = d.connection().w();
            for (int k = i; k < i + 100; k++) w.put("/k/" + k, value);
            w.execute();
        }
        d.sync();
        long full = db.internal().cache().residents().bytes();
        Assert.assertTrue("resident " + full, full > 15 * 1000 * 1000);
        
        d.setCacheSizeInMb(4);
        long end = System.nanoTime() + 5000L * 1000 * 1000;
        long bytes = full;
        while (System.nanoTime() < end) {
            bytes = db.internal().cache().residents().bytes();
            if (bytes <= 4 * 1000 * 1000) break;
            Thread.sleep(1);
        }
        d.stop();
        Assert.assertTrue("resident " + bytes + " of " + full, bytes <= 4 * 1000 * 1000);
    }
    
    /**
     * Database.getFirstAvailableLookupTime() with infinite retention, the default: nothing is
     * reclaimed, so the time stays while the clock moves on (bergdb 005-10: the method
     * returned the current time).
     */
    @Nano
    public static void testFirstAvailableLookupTime1() {
        TestClock clock = new TestClock();
        Database d = Factory.database().memory().clock(clock).start();
        Connection c = d.connection();
        clock.setTime(Time.units(100));
        c.w().put("/a", "1").execute();
        Time first = d.getFirstAvailableLookupTime();
        
        clock.setTime(Time.units(1000 * 1000));
        c.w().put("/a", "2").execute();
        Assert.assertEquals(first, d.getFirstAvailableLookupTime());
        Assert.assertEquals(((DatabaseImp) d).getDb().getFirstAvailableLookupTime(), 
                d.getFirstAvailableLookupTime().units());
        Assert.assertTrue(d.getFirstAvailableLookupTime().units() < d.currentTime().units());
        
        c.setLookupTime(Time.units(100));
        Assert.assertEquals("1", c.get("/a", String.class));
        d.stop();
    }
    
    /**
     * Database.getFirstAvailableLookupTime() with a finite retain duration: reclaim moves the
     * time forward, never back, and keeps the retain duration; a lookup at the time works, one
     * before it throws LookupTimeNotAvailableException. The database is made with the core's
     * builder, as the Pub API's sets a startup distance of at least 5 MB, and reclaim only
     * cuts in front of the startup section: with 2000 bytes the first cut comes soon.
     */
    @Nano
    public static void testFirstAvailableLookupTime2() {
        TestClock clock = new TestClock();
        Db db = Db.builder().testSetup(new CutStream()).clock(clock).maxNodeSize8()
                .startupDistance(2000).build();
        Database d = DatabaseImp.createAndStart(db);
        Duration retain = Duration.seconds(1);
        d.setRetainDuration(retain);
        Connection c = d.connection();
        
        long sec = Duration.seconds(1).units();
        long time = sec;
        long last = 0;
        java.util.Random r = new java.util.Random(1);
        for (int i = 0; i < 20000 && last == 0; i++) {
            time += sec / 20;
            clock.setTime(Time.units(time));
            c.w().put("/k/" + r.nextInt(50), "v" + i).execute();
            long first = d.getFirstAvailableLookupTime().units();
            Assert.assertTrue("moved back: " + first + " < " + last, first >= last);
            last = first;
        }
        
        Assert.assertTrue("the first available lookup time never moved", last > 0);
        Assert.assertTrue("the retain duration is not kept: " + last + ", now " + time, 
                last <= time - retain.units());
        Assert.assertEquals(db.getFirstAvailableLookupTime(), last);
        
        c.setLookupTime(Time.units(last));
        c.get("/k/0", String.class);
        
        c.setLookupTime(Time.units(last - 1));
        LookupTimeNotAvailableException ex = null;
        try {
            c.get("/k/0", String.class);
        } catch (LookupTimeNotAvailableException e) {
            ex = e;
        }
        Assert.assertTrue("a lookup before the first available lookup time did not throw", 
                ex != null);
        d.stop();
    }
    
    @Nano
    public static void testObjectInRootDir() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        c.w().put("/myDouble", new MyDouble(12.3)).execute();
        MyDouble myDouble = c.get("/myDouble", MyDouble.class);
        
        Assert.assertEquals(12.3, myDouble.value, 0.00001);
        d.stop();
    }
    
    @Nano
    public static void minimalCodeToStoreObject() {
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        // With database creation, and a stop when the database is no longer used.
        Database database = Factory.database().memory().start();
        database.connection().w().put("/a", a).execute();
        database.stop();
        
        database = Factory.database().memory().start();
        Connection c = database.connection();
        
        // Given connection, it is a short one-liner to store an object at its key.
        c.w().put("/a", a).execute();
        
        // To retrieve it.
        c.get("/a", MyDouble.class);
        
        
        // To update in a atomic read-write transaction
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                MyDouble a = env.get("/a", MyDouble.class);
                a.value = a.value + 2.0;
                env.put("/a", a);
            }
        });
        database.stop();
    }
    
    @Nano
    public static void testSync1() {
        // Tests Transaction.sync().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put("/a", a).execute();
        t.sync();
        
        assertThatTransWrittenCompletely(d, t);
        d.stop();
    }

    private static void assertThatTransWrittenCompletely(Database d, Transaction t) {
        long lastStreamPos = ((DatabaseImp) d).getDb().getStreamLength() - 1;
        long lastTransPos = ((WTransaction)t).getTrans().lastPos;
        Assert.assertTrue(lastStreamPos >= lastTransPos);
    }
    
    @Nano
    public static void testSync2() {
        // Tests Transaction.sync(SyncLevel); STRONG until 2026-11-04 (bergdb 005-11).
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put("/a", a).execute();
        t.sync(SyncLevel.ORDINARY);
     
        assertThatTransWrittenCompletely(d, t);
        d.stop();
    }
    
    @Nano
    public static void testSync3() {
        // Tests Connection.sync().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put("/a", a).execute();
        c.sync();
        
        assertThatTransWrittenCompletely(d, t);
        d.stop();
    }
    
    @Nano
    public static void testSync4() {
        // Tests Connection.sync(SyncLevel); STRONG until 2026-11-04 (bergdb 005-11).
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put("/a", a).execute();
        c.sync(SyncLevel.ORDINARY);
        
        assertThatTransWrittenCompletely(d, t);
        d.stop();
    }
    
    @Nano
    public static void testSync5() {
        // Tests Database.sync().
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put("/a", a).execute();
        d.sync();
        
        assertThatTransWrittenCompletely(d, t);
        d.stop();
    }
    
    @Nano
    public static void testSync6() {
        // Tests Database.sync(SyncLevel); STRONG until 2026-11-04 (bergdb 005-11).
        
        MyDouble a = new MyDouble(1.2);
        a.key = "/a";
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        Transaction t = c.w().put("/a", a).execute();
        d.sync(SyncLevel.ORDINARY);
        
        assertThatTransWrittenCompletely(d, t);
        d.stop();
    }
    
    public static class A {
        public String key;
        public String name;
        public A() {}
        public A(String key, String name) {
            this.key = key;
            this.name = name;
        }
    }
    
    private static class A2 {
        private String key;
        private String name;
    }
    
    
    @Nano
    public static void testKeyField0() {
        // Uses key field, get.
        
        A a0 = new A();
        a0.name = "Saltis";
        
        Database d = Factory.database().memory().start();
        d.connection().w().put("/a", a0).execute();
        
        A a1 = d.connection().get("/a", A.class);
        Assert.assertEquals("Saltis", a1.name);
        Assert.assertNull(a1.key);      // an ordinary field (bergdb 020-02, section 5.1b)
        d.stop();
    }
    
    /**
     * A class with private fields is not a Data Object (bergdb 020-09, V1 and V3; Frans,
     * 2026-11-08, 20:44: public fields only): a put is refused, and a get too, also at a key
     * without a value.
     */
    @Nano
    public static void testKeyField0Private() {
        A2 a0 = new A2();
        a0.name = "Saltis";
        
        Database d = Factory.database().memory().start();
        try {
            try {
                d.connection().w().put("/a", a0).execute();
                throw new AssertionError("no exception");
            } catch (IllegalArgumentException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("A2"));
            }
            try {
                d.connection().get("/a", A2.class);
                throw new AssertionError("no exception");
            } catch (ObjectCreationException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("A2"));
            }
        } finally {
            d.stop();
        }
    }
    
    @Nano
    public static void testKeyField1() {
        // Uses key field, set.
        
        A a0 = new A();
        a0.name = "Saltis";
        a0.key = "/a";
        
        Database d = Factory.database().memory().start();
        d.connection().w().put("/a", a0).execute();
        
        A a1 = d.connection().get("/a", A.class);
        Assert.assertEquals("Saltis", a1.name);
        Assert.assertEquals("/a", a1.key);
        d.stop();
    }
    
    
    
    @Nano
    public static void testKeyField2() {
        // Uses key field, rw get.
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        final House h0 = new House();
        h0.key = null;
        h0.area = 120;
        h0.name = "MyHome";
        
        c.w().put("/h", h0).execute();
        
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                House h = env.get("/h", House.class);
                Assert.assertNull(h.key);       // an ordinary field (bergdb 020-02)
                Assert.assertEquals("MyHome", h.name);
            }
        });
        
        database.stop();
    }
    
    
    @Nano
    public static void testKeyField3() {
        // Uses key field, rw set.
        
        // Arrange
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        final House house = new House();
        house.key = "/h";
        house.area = 120;
        house.name = "MyHome";
        
        // Act
        
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                env.put("/h", house);
            }
        });
        
        // Assert
        
        House house2 = c.get("/h", House.class);
        Assert.assertEquals("MyHome", house2.name);
        Assert.assertEquals("/h", house2.key);
        
        database.stop();
    }
    
    public static class S {
        public String key;
    }
    
    public static class D extends S {
        public String s;
    }
    
    @Nano
    public static void testKeyFieldInSuperClass0() {
        // key field in super class, set
        
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        D obj0 = new D();
        obj0.key = "/k";
        obj0.s = "hello";
        
        c.w().put("/k", obj0).execute();
        
        D obj1 = c.get("/k", D.class);
        Assert.assertEquals("/k", obj1.key);
        Assert.assertEquals("hello", obj1.s);
        
        database.stop();
    }
    
    @Nano
    public static void testKeyFieldInSuperClass1() {
        // key field in super class, get
        
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        D obj0 = new D();
        obj0.key = null;
        obj0.s = "hello";
        
        c.w().put("/k", obj0).execute();
        
        D obj1 = c.get("/k", D.class);
        Assert.assertNull(obj1.key);    // an ordinary field (bergdb 020-02, section 5.1b)
        Assert.assertEquals("hello", obj1.s);
        
        d.stop();
    }
    
    @Nano
    public static void testKeyFieldWithIterator() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/dir/a0", new A(null, "a0"))
             .put("/dir/a1", new A(null, "a1")).execute();
        
        int index = 0;
        for (A a : c.usePrimary(A.class).dir("/dir/").objects()) {
            Assert.assertNull(a.key);   // an ordinary field (bergdb 020-02, section 5.1b)
            Assert.assertEquals("a" + index, a.name);
            index++;
        }
        Assert.assertEquals(2, index);
        
        d.stop();
    }
    
    public static class Named {
        public String name;
        public int b;
        public String key;
        public Named() {}
        public Named(String name, int b, String key) {
            this.name = name;
            this.b = b;
            this.key = key;
        }
    }
    
    @Nano
    public static void testKeyFieldWithDbObject0() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/a", new Named("Carl", 0, null)).execute();
        DbObject dbo = c.get("/a", DbObject.class);
        
        Assert.assertNull(dbo.getString("key"));    // the stored object (bergdb 020-02)
        Assert.assertEquals(2, dbo.getFieldCount());
        Assert.assertEquals("Carl", dbo.getString("name"));
        
        d.stop();
    }
    
    @Nano
    public static void testKeyFieldWithDbObject1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        DbObject dbo0 = new DbObject.Builder().addString("key", "/a").addInt("b", 123).build();
        c.w().put("/a", dbo0).execute();
        
        DbObject dbo1 = c.get("/a", DbObject.class);
        
        Assert.assertEquals("/a", dbo1.getString("key"));
        Assert.assertEquals(123, dbo1.getInt("b"));
        
        d.stop();
    }
    
    /**
     * An anonymous class is not a Data Object (bergdb 020-09, V1 and K16): its put is refused,
     * naming the class, and writes nothing; a public class with the same fields is stored.
     */
    @Nano
    @SuppressWarnings("unused")
    public static void testAnonymous0() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            Object anonymous = new Object() { public String name = "Gustav"; public int b = 123; };
            try {
                c.w().put("/a", anonymous).execute();
                throw new AssertionError("no exception");
            } catch (IllegalArgumentException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains(
                        anonymous.getClass().getName()));
            }
            Assert.assertNull(c.get("/a", Object.class));
            
            c.w().put("/a", new Named("Gustav", 123, null)).execute();
            DbObject dbo = c.get("/a", DbObject.class);
            
            Assert.assertEquals("Gustav", dbo.getString("name"));
            Assert.assertEquals(123, dbo.getInt("b"));
        } finally {
            d.stop();
        }
    }
    
    @Nano
    public static void testAnonymous1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/a", new Named(null, 123, "/a")).execute();
        DbObject dbo = c.get("/a", DbObject.class);
        
        Assert.assertEquals("/a", dbo.getString("key"));
        Assert.assertEquals(123, dbo.getInt("b"));
        d.stop();
    }
    
    public static class K {
        public String key;
        public int n;
        public K() {}
    }
    
    /**
     * bergdb 020-02, section 5.1b; 020-09, G113 and W31: a field named 'key' is an ordinary
     * field, at a put and at a get, and a DbObject read at a key is the stored object
     * exactly; put(Object) and MissingKeyFieldException are gone (Frans, 2026-11-08, 19:21).
     */
    @Nano
    public static void testKeyIsAnOrdinaryField() throws ReflectiveOperationException {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            K k = new K();
            k.n = 1;
            c.put("/k", k);
            Assert.assertNull(c.get("/k", K.class).key);
            DbObject dbo = c.get("/k", DbObject.class);
            Assert.assertNull(dbo.getString("key"));
            Assert.assertEquals('z', dbo.getType("key"));
            Assert.assertFalse(dbo.has("key", DbObject.STRING));
            Assert.assertEquals(1, dbo.getFieldCount());
            Assert.assertTrue(dbo.getDbValue("key") == null);
            Assert.assertArrayEquals(DbObject.toDbObject(k).getBytes(), dbo.getBytes());
            
            k.key = "x";
            c.put("/k", k);
            Assert.assertEquals("x", c.get("/k", K.class).key);
            Assert.assertEquals("x", c.get("/k", DbObject.class).getString("key"));
            Assert.assertEquals("x", ((DbObject) c.get("/k", Object.class)).getString("key"));
        } finally {
            d.close();
        }
        
        for (Class<?> api : new Class<?>[] {WBuilder.class, RwEnvironment.class}) {
            try {
                api.getMethod("put", Object.class);
                throw new AssertionError(api.getName() + ".put(Object) exists");
            } catch (NoSuchMethodException e) {
                // Expected.
            }
        }
        try {
            Class.forName("bergdb.pub.MissingKeyFieldException");
            throw new AssertionError("MissingKeyFieldException exists");
        } catch (ClassNotFoundException e) {
            // Expected.
        }
    }
    
    @Nano
    public static void testDbObject0() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        DbObject dbo = new DbObject.Builder().addInt("i", 123).addString("s", "hello").build();
        c.w().put("/a", dbo).execute();
        DbObject o = c.get("/a", DbObject.class);
        
        Assert.assertEquals("hello", o.getString("s"));
        Assert.assertEquals(123, o.getInt("i"));
        
        d.stop();
    }
    
    @Nano
    public static void testDbObject1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        DbObject dbo = new DbObject.Builder()
            .addInt("i", 123)
            .addString("key", "/a")
            .build();
        
        c.w().put("/a", dbo).execute();
        DbObject o = c.get("/a", DbObject.class);
        
        Assert.assertEquals("/a", o.getString("key"));
        Assert.assertEquals(123, o.getInt("i"));
        
        d.stop();
    }
    
    @Nano
    public static void testBadKey() {
        IllegalArgumentException ex = null;
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        try {
            c.w().put("k", "v");
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        d.stop();
        Assert.assertTrue(ex != null);
    }
    
    @Nano
    public static void testStoreArray() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/strings", new String[]{"adam", "eve"}).execute();
        String[] strings = c.get("/strings", String[].class);
        d.stop();
        
        Assert.assertEquals(2, strings.length);
        Assert.assertEquals("adam", strings[0]);
        Assert.assertEquals("eve", strings[1]);
    }
    
    @Nano
    public static void testStorePrimitive() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        
        c.w().put("/myInt", 123).execute();
        int myInt = c.get("/myInt", int.class);
        d.stop();
        
        Assert.assertEquals(123, myInt);
    }
    
    @Nano
    public static void testSetLookupWithTimeString1() {
        Database d = Factory.database().memory().start();
        Connection c = d.connection();
        c.setLookupTime(Time.resolve(Time.UTC, "1970-01-01 00:00:01"));
        c.get("/key", String.class);
        Time time = c.getLookupTime();
        Assert.assertEquals(Time.millis(1000), time);
        d.stop();
    }
    
    @Nano
    public static void testSetLookupWithTimeString2() {
        TestClock clock = new TestClock();
        clock.setTime(Time.utc("1970-01-01 00:02:03.000"));       // UTC 1970-01-01 00:02:03.000
        Database d = Factory.database().memory().clock(clock).start();
        Time dbTime = d.currentTime();
        Time time1 = Time.resolve(Time.UTC, dbTime, "00:01");
        Time time2 = Time.millis(60 * 1000);
        Assert.assertEquals(time2, time1);
        d.stop();
    }
    
    @Nano
    public static void testCurrentTime() {
        TestClock clock = new TestClock();
        Time t0 = Time.utc("2010-01-01 00:02:03.0000000");
        clock.setTime(t0);
        Database d = Factory.database().memory().clock(clock).start();
        Transaction t = d.connection().put("/key", "value");
        Time t1 = t0.add(Duration.units(10));
        Time transTime = t.getTime();
        
        Assert.assertTrue(transTime.isBetween(t0, t1));
        d.stop();
    }
    
    @Nano
    public static void testHistoric1() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        c.put("/key", "v1");
        Time t1 = database.currentTime();
        c.put("/key", "v2");
        Time t2 = database.currentTime();
        c.put("/key", "v3");
        Time t3 = database.currentTime();
        
        c.setLookupTime(t1);
        Assert.assertEquals("v1", c.get("/key", String.class));
        c.setLookupTime(t2);
        Assert.assertEquals("v2", c.get("/key", String.class));
        c.setLookupTime(t3);
        Assert.assertEquals("v3", c.get("/key", String.class));
        
        database.stop();
    }
    
    // ---- Tests Connection.delete() ----
    
    @Nano
    public static void testThatSimpleDeleteWorks() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        String key = "/key";
        c.put(key, "v1");
        Assert.assertTrue(c.exists(key));
        c.delete(key);
        Assert.assertFalse(c.exists(key));
        
        database.stop();
    }
    
    @Nano
    public static void testDeleteWithNullNotPossible() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        String key = "/key";
        c.put(key, "v1");
        Assert.assertTrue(c.exists(key));
        
        IllegalArgumentException ex = null;
        try {
            c.put(key, null);
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
        database.stop();
    }
    
    @Nano
    public static void testDeleteInW() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        c.w().put("/k1", "v1").put("/k2", "v2").execute();
        c.w().put("/k3", "v3").delete("/k1").execute();
        
        Assert.assertFalse(c.exists("/k1"));
        Assert.assertTrue(c.exists("/k2"));
        Assert.assertTrue(c.exists("/k3"));
        
        database.stop();
    }
    
    @Nano
    public static void testDeleteInRW() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        c.w().put("/k1", "v1").put("/k2", "v2").execute();
        
        c.rw(new Action() {
            public void run(RwEnvironment env) {
                env.delete("/k2");
                env.delete("/k9");
            }
        });
        
        Assert.assertTrue(c.exists("/k1"));
        Assert.assertFalse(c.exists("/k2"));
        Assert.assertEquals(1, countEntries(c));
        
        database.stop();
    }
    
    @SuppressWarnings("unused")
    private static int countEntries(Connection c) {
        int count = 0;
        
        for (byte[] value : c.usePrimary(byte[].class).dir("/").objects()) {
            count++;
        }
        
        return count;
    }
    
    @Nano
    public static void testDeleteOfNonExistantEntry() {
        Database database = Factory.database().memory().start();
        Connection c = database.connection();
        
        c.w().put("/k1", "v1").put("/k2", "v2").execute();
        c.delete("/k1");
        c.delete("/k5");
        
        Assert.assertEquals(1, countEntries(c));
        database.stop();
    }
    
    @Nano
    public static void testStartupInfoTime() {
        Database database = Factory.database().memory().start();        
        double time = database.getStartupInfo().getStartupDuration();
        Assert.assertTrue("time:" + time, time > 0.0);
        
        database.stop();
    }
    
    @Nano
    public static void testEncrypted1() throws IOException {
        // Creates an encrypted database, makes sure beginning of encrypted bytes not
        // same as unencrypted bytes.
        
        CryptoKey cryptoKey = CryptoKey.parse("8184a9f2-salsa-75ac20b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c");
        
        Database database = Factory.database().memory().cryptoKey(cryptoKey).start();
        
        DatabaseImp imp = (DatabaseImp) database;
        BufferedStream buffered = (BufferedStream) imp.getDb().internal().getMainStream();
        SalsaStream salsa = (SalsaStream) buffered.getUnderlyingStream();
        MemoryStream memory = (MemoryStream) salsa.getUnderlyingStream();
        
        Connection c = database.connection();
        c.put("/s1", "Hej!");
        c.sync();
        
        byte[] firstEncryptedBytes = new byte[8];
        memory.read(0, firstEncryptedBytes, 0, firstEncryptedBytes.length);
        
        byte[] firstUnencryptedBytes = new byte[8];
        salsa.read(0, firstUnencryptedBytes, 0, firstUnencryptedBytes.length);
        
        String magic = new String(firstUnencryptedBytes, 0, 4, "UTF-8");
        
        Assert.assertEquals("berg", magic);
        Assert.assertFalse(Util.areEqual(firstUnencryptedBytes, firstEncryptedBytes));
        database.stop();
    }
    
    @Nano
    public static void testEncrypted2() throws IOException {
        // Creates an encrypted database, writes to it, closes it, and reopens it.
        
        CryptoKey cryptoKey = CryptoKey.parse("8184a9f2-salsa-75ac20b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c");
        
        Database database = Factory.database().memory().cryptoKey(cryptoKey).start();
        
        DatabaseImp imp = (DatabaseImp) database;
        BufferedStream buffered = (BufferedStream) imp.getDb().internal().getMainStream();
        SalsaStream salsa = (SalsaStream) buffered.getUnderlyingStream();
        MemoryStream memory = (MemoryStream) salsa.getUnderlyingStream();
        
        Connection c = database.connection();
        c.put("/s1", "Hej!");
        c.sync();
        
        database.stop();
        
        // --- Re-opens database
        
        MemoryStream m = memory.copy();
        DatabaseBuilderImp builder = (DatabaseBuilderImp) Factory.database();
        builder.stream("main", m);
        builder.cryptoKey(CryptoKey.parse("8184a9f2-salsa-75ac20b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c"));
        Database database2 = builder.start();
        
        String s = database2.connection().get("/s1", String.class);
        
        Assert.assertEquals("Hej!", s);
        database2.stop();
    }
    
    @Nano
    public static void testEncrypted3() throws IOException {
        // Creates an encrypted database, writes to it, closes it, and reopens it
        // with the wrong crypto key. BadCryptoKey should be thrown.
        
        CryptoKey cryptoKey = CryptoKey.parse("8184a9f2-salsa-75ac20b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c");
        
        Database database = Factory.database().memory().cryptoKey(cryptoKey).start();
        
        DatabaseImp imp = (DatabaseImp) database;
        BufferedStream buffered = (BufferedStream) imp.getDb().internal().getMainStream();
        SalsaStream salsa = (SalsaStream) buffered.getUnderlyingStream();
        MemoryStream memory = (MemoryStream) salsa.getUnderlyingStream();
        
        Connection c = database.connection();
        c.put("/s1", "Hej!");
        c.sync();
        
        database.stop();
        
        // --- Re-opens database
        
        MemoryStream m = memory.copy();
        DatabaseBuilderImp builder = (DatabaseBuilderImp) Factory.database();
        builder.stream("main", m);
        builder.cryptoKey(CryptoKey.parse("8184a9f2-salsa-222222b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c"));
        
        BadCryptoKey ex = null;
        
        try { 
            builder.start();
        } catch (BadCryptoKey e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    /**
     * Regression test for bergdb 005-40: a start with a wrong crypto key, or with none, on a
     * database whose stream a crash had cut where a meta block starts, filled out that meta
     * block through the key before it found the key wrong; the right key then read garbage
     * there, and the database never started again. Now such a start writes nothing.
     */
    @Nano
    private static void testWrongKeyAfterCrashAtMetaBlock() {
        CryptoKey right = CryptoKey.generate();
        MemoryStream m = new MemoryStream();
        Database d = builderOn(m, right).start();
        Connection c = d.connection();
        String big = new String(new char[100 * 1000]).replace('\0', 'b');
        for (int i = 0; i < 3; i++) {
            c.put("/k" + i, big);           // Past the meta block at 200,000.
        }
        d.sync();
        ((DatabaseImp) d).getDb().close();
        final long cut = RecoverableStream.META_BLOCK_DISTANCE;
        Assert.assertTrue("length " + m.getLength(),
                m.getLength() > cut + RecoverableStream.META_BLOCK_SIZE);
        MemoryStream crashed = m.copy();
        crashed.truncate(cut);              // A crash just before the meta block (005-27).
        
        for (CryptoKey wrong : new CryptoKey[] {CryptoKey.generate(), null}) {
            MemoryStream m2 = crashed.copy();
            try {
                builderOn(m2, wrong).start();
                throw new AssertionError("started with a wrong key");
            } catch (BadCryptoKey e) {
                // Expected.
            }
            Assert.assertEquals("the stream as it was", cut, m2.getLength());
            
            Database d2 = builderOn(m2.copy(), right).start();
            Assert.assertEquals(big, d2.connection().get("/k0", String.class));
            ((DatabaseImp) d2).getDb().close();
        }
    }
    
    /**
     * Bergdb 005-33: a crash while the database is created, through the Pub API, with and
     * without a crypto key. At each cut of the creation the start throws a
     * DatabaseNotCreatedException and writes nothing; the whole creation starts. A stream of
     * zero bytes, as a power loss can leave, gives a BadCryptoKey whose message names a wrong
     * key only when a key is used; until 2026-10-25, also without one.
     */
    @Nano
    private static void testCrashInCreation() throws IOException {
        for (CryptoKey key : new CryptoKey[] {null, CryptoKey.generate()}) {
            MemoryStream m = new MemoryStream();
            ((DatabaseImp) builderOn(m, key).start()).getDb().close();
            final long length = m.getLength();
            
            for (long cut : new long[] {1, 64, 127, 128, 129, 132, 200, length - 1}) {
                MemoryStream m2 = m.copy();
                m2.truncate(cut);
                try {
                    builderOn(m2, key).start();
                    throw new AssertionError("started, cut at " + cut);
                } catch (DatabaseNotCreatedException e) {
                    // Expected.
                }
                Assert.assertEquals("cut at " + cut, cut, m2.getLength());
            }
            
            MemoryStream zeros = new MemoryStream();
            zeros.append(new byte[128], 0, 128);
            try {
                builderOn(zeros, key).start();
                throw new AssertionError("started on zero bytes");
            } catch (BadCryptoKey e) {
                Assert.assertTrue(e.getMessage(),
                        e.getMessage().contains("wrong crypto key") == (key != null));
            }
            
            Database d = builderOn(m.copy(), key).start();
            d.connection().put("/k", "v");
            Assert.assertEquals("v", d.connection().get("/k", String.class));
            ((DatabaseImp) d).getDb().close();
        }
    }
    
    /**
     * Bergdb 005-50: the Pub API, which uses maximum node size 30, refuses a database that
     * the core API created with another size, with the core's StreamFormatException, which
     * says what to do, and writes nothing.
     */
    @Nano
    private static void testOtherNodeSizeRefused() {
        MemoryStream m = new MemoryStream();
        Db db = Db.builder().testSetup(m).maxNodeSize8().start();
        db.execute(db.trans().put("key", "value"));
        db.sync(SyncLevel.ORDINARY);
        db.close();
        final long length = m.getLength();
        try {
            builderOn(m, null).start();
            throw new AssertionError("started with node size 30, created with 8");
        } catch (StreamFormatException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains(
                    "maximum node size is 8, and this start uses 30."));
        }
        Assert.assertEquals("the stream as it was", length, m.getLength());
    }
    
    /** A builder of a database on the stream m, with the crypto key unless it is null. */
    private static DatabaseBuilder builderOn(MemoryStream m, CryptoKey key) {
        DatabaseBuilderImp b = (DatabaseBuilderImp) Factory.database();
        b.mainStream(m);
        if (key != null) {
            b.cryptoKey(key);
        }
        return b;
    }
    
    @Nano
    private static void testCreatedTxt1(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        
        File dir = env.createTempDir();
        CryptoKey cryptoKey = CryptoKey.parse("8184a9f2-salsa-75ac20b68ccdbf95b9999287bc4da0caf67b4c8edc40d7615bebf1beae3578b800cfc3dfbaad319c");
        
        Database database = Factory.database().create(dir.getPath()).cryptoKey(cryptoKey).start();
        database.stop();
        
        File file = new File(dir, "created.txt");
        Assert.assertTrue(file.exists());
        
        String s = new String(Util.fileToBytes(file.getPath()), "UTF-8");
        Assert.assertTrue(s.contains("8184a9f2"));
    }
    
    @Nano
    private static void testCreatedTxt2(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        
        File dir = env.createTempDir();
        Database database = Factory.database().create(dir.getPath()).start();
        database.stop();
        
        File file = new File(dir, "created.txt");
        Assert.assertTrue(file.exists());
        
        String s = new String(Util.fileToBytes(file.getPath()), "UTF-8");
        Assert.assertTrue(s.contains("creation date"));
    }
    
    /**
     * A directory that held a database, its stream's files removed (bergdb 015-01): start()
     * throws a DatabaseMissingException and opens, creates and writes nothing; the
     * directory's files and created.txt's bytes are as they were. Before, the start created
     * a new, empty database there, and said nothing.
     */
    @Nano
    private static void testStreamFilesRemoved(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = createdWithData(env);
        for (File f : streamFiles(dir)) {
            Assert.assertTrue(f.delete());
        }
        assertMissing(dir);
    }
    
    /** As testStreamFilesRemoved, with the one stream file emptied (bergdb 015-01). */
    @Nano
    private static void testOnlyStreamFileEmptied(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = createdWithData(env);
        File[] streams = streamFiles(dir);
        Assert.assertEquals(1, streams.length);
        try (RandomAccessFile f = new RandomAccessFile(streams[0], "rw")) {
            f.setLength(0);
        }
        assertMissing(dir);
    }
    
    /**
     * The remedy that DatabaseMissingException's message gives (bergdb 015-01): with
     * created.txt removed too, start() creates a new, empty database, as for any directory
     * without created.txt.
     */
    @Nano
    private static void testMissingStreamRemedy(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = createdWithData(env);
        for (File f : streamFiles(dir)) {
            Assert.assertTrue(f.delete());
        }
        assertMissing(dir);
        Assert.assertTrue(new File(dir, "created.txt").delete());
        Database d = Factory.database().create(dir.getPath()).start();
        Assert.assertNull(d.connection().get("/k", String.class));
        d.close();
        Assert.assertTrue("a new created.txt", new File(dir, "created.txt").isFile());
    }
    
    /**
     * A creation that crashed before its first write (bergdb 005-33, row 0 of its table): the
     * directory holds bergdb.lock and an empty first stream file, and no created.txt. start()
     * creates the database, as before 015-01.
     */
    @Nano
    private static void testCrashedCreationBeforeFirstWrite(TestEnvironment env)
            throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = env.createTempDir();
        crashedBeforeFirstWrite(dir);
        Assert.assertTrue(new File(dir, "bergdb.lock").isFile());
        File[] streams = streamFiles(dir);
        Assert.assertTrue(streams.length == 1 && streams[0].length() == 0);
        Database d = Factory.database().create(dir.getPath()).start();
        d.connection().put("/k", "v");
        d.close();
        Assert.assertTrue("created.txt", new File(dir, "created.txt").isFile());
        Database d2 = Factory.database().create(dir.getPath()).start();
        Assert.assertEquals("v", d2.connection().get("/k", String.class));
        d2.close();
    }
    
    /**
     * A database whose created.txt was lost gets one at its next start (bergdb 015-01, A+),
     * with the creation date unknown and its own database ID; from then on a start refuses
     * the directory if its stream goes missing. Before, none was written.
     */
    @Nano
    private static void testCreatedTxtWrittenAtStart(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = createdWithData(env);
        File txt = new File(dir, "created.txt");
        String before = new String(Util.fileToBytes(txt.getPath()), "UTF-8");
        Assert.assertTrue(txt.delete());
        Database d = Factory.database().create(dir.getPath()).start();
        Assert.assertEquals("v", d.connection().get("/k", String.class));
        d.close();
        Assert.assertTrue("created.txt written", txt.isFile());
        String after = new String(Util.fileToBytes(txt.getPath()), "UTF-8");
        Assert.assertTrue(after, after.contains("creation date: unknown"));
        Assert.assertEquals("the database ID", line(before, "database ID:"),
                line(after, "database ID:"));
        Assert.assertTrue(after, line(after, "database ID:").length() > "database ID:".length());
    }
    
    /**
     * A creation whose force fails writes no created.txt, and the start fails (bergdb
     * 015-01): the creation is made durable before created.txt is written. Before,
     * created.txt was written at once, before any byte of the stream reached its file, and
     * the start returned. Through the core API, as DbTesterStream.testCreatedTxt.
     */
    @Nano
    private static void testNoCreatedTxtWithoutForce(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = env.createTempDir();
        final java.util.concurrent.atomic.AtomicBoolean fail =
                new java.util.concurrent.atomic.AtomicBoolean(false);
        FileStreamIo io = new FileStreamIo() {
            protected void forceFile(File file, RandomAccessFile handle) throws IOException {
                if (fail.get()) {
                    throw new IOException("PubTester: a force that fails, as set (015-01)");
                }
                super.forceFile(file, handle);
            }
        };
        FileStream fs = new FileStream(dir, io);
        fail.set(true);
        Db db = null;
        boolean failed = false;
        try {
            db = Db.builder().testSetup(fs).createdTxt(dir, null).start();
        } catch (StreamIoException e) {
            failed = true;
        } finally {
            if (db != null) {
                try {
                    db.close();     // Before 015-01: the start returned.
                } catch (RuntimeException e) {
                    // The failed force.
                }
            }
        }
        Assert.assertTrue("no created.txt", !new File(dir, "created.txt").exists());
        Assert.assertTrue("the start failed", failed);
    }
    
    /**
     * A start refused for its crypto key, of an unknown algorithm, creates nothing (bergdb
     * 015-06): an empty directory stays empty, and a missing one is not created. Before, the start opened the directory first, which created it, its lock
     * file and an empty first stream file, and left them.
     */
    @Nano
    private static void testRefusedStartCreatesNothing(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File empty = env.createTempDir();
        File missing = new File(env.createTempDir(), "db");
        CryptoKey other = CryptoKey.parse("8184a9f2-other-75ac20b68ccdbf95b9999287bc4da0caf67b4c8e"
                + "dc40d7615bebf1beae3578b800cfc3dfbaad319c");
        for (File dir : new File[] {empty, missing}) {
            try {
                Factory.database().create(dir.getPath()).cryptoKey(other).start();
                throw new AssertionError("started");
            } catch (IllegalStateException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("other"));
            }
        }
        Assert.assertEquals("the empty directory: " + listing(empty), 0, empty.list().length);
        Assert.assertTrue("the missing directory", !missing.exists());
    }
    
    /**
     * A start refused after the open creates no stream file (bergdb 015-06): its clock is out
     * of range at the creation (bergdb 005-18), on an empty directory and on a missing one.
     * Only bergdb.lock is left, which is never deleted (bergdb 005-63), and a start then
     * creates the database. Before, the open created an empty first stream file,
     * 00000000000000.bergdb, and the refused start left it, which breaks the restore in
     * place of a database whose first file has another name.
     */
    @Nano
    private static void testRefusedStartAfterOpenCreatesNoStreamFile(TestEnvironment env)
            throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File empty = env.createTempDir();
        File missing = new File(env.createTempDir(), "db");
        for (File dir : new File[] {empty, missing}) {
            try {
                Factory.database().create(dir.getPath()).clock(() -> -1).start();
                throw new AssertionError("started");
            } catch (RuntimeException e) {
                Assert.assertTrue(e.toString(), e.getMessage().contains("outside the range"));
            }
            Assert.assertTrue(dir + ": " + listing(dir),
                    Arrays.equals(new String[] {"bergdb.lock"}, dir.list()));
            
            Database d = Factory.database().create(dir.getPath()).start();
            d.connection().put("/k", "v");
            d.close();
            Assert.assertEquals(1, streamFiles(dir).length);
        }
    }
    
    /**
     * Makes 'dir' as a creation that crashed before its first write leaves it (bergdb 005-33):
     * bergdb.lock and an empty first stream file. The first append makes the file and forces
     * it before it writes; the open makes none (bergdb 015-06), so it is made here.
     */
    private static void crashedBeforeFirstWrite(File dir) throws IOException {
        new FileStream(dir).close();
        Assert.assertTrue(new File(dir, "00000000000000.bergdb").createNewFile());
    }
    
    /** A database with /k = v in a new temporary directory, closed (bergdb 015-01's tests). */
    private static File createdWithData(TestEnvironment env) throws IOException {
        File dir = env.createTempDir();
        Database d = Factory.database().create(dir.getPath()).start();
        d.connection().put("/k", "v");
        d.close();
        Assert.assertTrue(new File(dir, "created.txt").isFile());
        return dir;
    }
    
    /** The directory's stream files (*.bergdb). */
    private static File[] streamFiles(File dir) {
        File[] fs = dir.listFiles((d, name) -> name.endsWith(".bergdb"));
        return fs == null ? new File[0] : fs;
    }
    
    /** The directory's files, sorted, each with its length. */
    private static String listing(File dir) {
        String[] names = dir.list();
        if (names == null) {
            return "(none)";
        }
        java.util.Arrays.sort(names);
        StringBuilder sb = new StringBuilder();
        for (String n : names) {
            sb.append(n).append(':').append(new File(dir, n).length()).append(' ');
        }
        return sb.toString();
    }
    
    /** The line of 's' that starts with 'prefix', or null. */
    private static String line(String s, String prefix) {
        for (String l : s.split("\n")) {
            if (l.startsWith(prefix)) {
                return l;
            }
        }
        return null;
    }
    
    /**
     * A start on 'dir' throws a DatabaseMissingException, and the directory's files and
     * created.txt's bytes are as before (bergdb 015-01).
     */
    private static void assertMissing(File dir) throws IOException {
        String before = listing(dir);
        byte[] txt = Util.fileToBytes(new File(dir, "created.txt").getPath());
        try {
            Database d = Factory.database().create(dir.getPath()).start();
            d.close();
            throw new AssertionError("a new database started in " + dir);
        } catch (DatabaseMissingException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("015-01"));
        }
        Assert.assertEquals("the directory's files", before, listing(dir));
        Assert.assertArrayEquals(txt, Util.fileToBytes(new File(dir, "created.txt").getPath()));
    }
    
    /**
     * bergdb 015-05: open() of a missing directory, here with a missing parent too, is
     * refused, and creates nothing; also when it follows a create() of the directory (the
     * last call counts). Before 015-05 there was no open(); dir(), now create(), created the
     * directory, its parents and a new, empty database.
     */
    @Nano
    private static void testOpenRefusesMissingDirectory(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File tmp = env.createTempDir();
        File p = new File(new File(tmp, "parent"), "db");
        assertOpenRefused(tmp, Factory.database().open(p.getPath()), "does not exist");
        assertOpenRefused(tmp, Factory.database().create(p.getPath()).open(p.getPath()),
                "does not exist");
        Assert.assertTrue("the parent", !p.getParentFile().exists());
    }
    
    /** bergdb 015-05: open() of a file, not a directory, is refused; the file is unchanged. */
    @Nano
    private static void testOpenRefusesFile(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File tmp = env.createTempDir();
        File p = new File(tmp, "db");
        Util.bytesToFile(new byte[] {1, 2, 3}, p.getPath());
        assertOpenRefused(tmp, Factory.database().open(p.getPath()), "not a directory");
    }
    
    /**
     * bergdb 015-05: open() of an empty directory, as an unmounted volume's mount point, is
     * refused and leaves it empty; so is a directory with other files, or with an empty
     * first stream file (a creation that crashed before its first write, bergdb 005-33),
     * which create() makes a database in.
     */
    @Nano
    private static void testOpenRefusesDirectoryWithoutStream(TestEnvironment env)
            throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File tmp = env.createTempDir();
        File p = new File(tmp, "mnt");
        Assert.assertTrue(p.mkdir());
        assertOpenRefused(tmp, Factory.database().open(p.getPath()), "no stream file");
        Assert.assertEquals("the empty directory", 0, p.list().length);
        
        Util.bytesToFile(new byte[] {1, 2, 3}, new File(p, "other.txt").getPath());
        assertOpenRefused(tmp, Factory.database().open(p.getPath()), "no stream file");
        
        File crashed = env.createTempDir();
        crashedBeforeFirstWrite(crashed);
        File[] streams = streamFiles(crashed);
        Assert.assertTrue(streams.length == 1 && streams[0].length() == 0);
        assertOpenRefused(crashed, Factory.database().open(crashed.getPath()), "no stream file");
        Database d = Factory.database().create(crashed.getPath()).start();
        d.close();
        Assert.assertTrue("created.txt", new File(crashed, "created.txt").isFile());
    }
    
    /**
     * bergdb 015-05: open() of a directory with created.txt and no stream byte, a database
     * whose stream files were removed, is refused with 015-01's message, and writes nothing.
     */
    @Nano
    private static void testOpenRefusesCreatedTxtWithoutStream(TestEnvironment env)
            throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = createdWithData(env);
        for (File f : streamFiles(dir)) {
            Assert.assertTrue(f.delete());
        }
        assertOpenRefused(dir, Factory.database().open(dir.getPath()), "015-01");
    }
    
    /**
     * bergdb 015-05: open() opens a database that create() made, with its data, and the
     * database takes writes; create() opens it again, and does not make a new one.
     */
    @Nano
    private static void testOpenExisting(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = createdWithData(env);
        Database d = Factory.database().open(dir.getPath()).start();
        Assert.assertEquals("v", d.connection().get("/k", String.class));
        d.connection().put("/k2", "v2");
        d.close();
        
        Database d2 = Factory.database().create(dir.getPath()).start();
        Assert.assertEquals("v", d2.connection().get("/k", String.class));
        Assert.assertEquals("v2", d2.connection().get("/k2", String.class));
        d2.close();
    }
    
    /**
     * bergdb 015-05: create() makes a missing directory with its missing parents, and an
     * empty directory, into a new database; open() then opens each.
     */
    @Nano
    private static void testCreateMissingAndEmpty(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File missing = new File(new File(new File(env.createTempDir(), "a"), "b"), "db");
        File empty = env.createTempDir();
        for (File p : new File[] {missing, empty}) {
            Database d = Factory.database().create(p.getPath()).start();
            Assert.assertNull(d.connection().get("/k", String.class));
            d.connection().put("/k", "v");
            d.close();
            Assert.assertTrue("created.txt in " + p, new File(p, "created.txt").isFile());
            Database d2 = Factory.database().open(p.getPath()).start();
            Assert.assertEquals("v", d2.connection().get("/k", String.class));
            d2.close();
        }
    }
    
    /** bergdb 015-05: open() of an encrypted database, with its key, opens it. */
    @Nano
    private static void testOpenEncrypted(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = new File(env.createTempDir(), "db");
        CryptoKey key = CryptoKey.generate();
        Database d = Factory.database().create(dir.getPath()).cryptoKey(key).start();
        d.connection().put("/k", "secret");
        d.close();
        
        Database d2 = Factory.database().open(dir.getPath()).cryptoKey(key).start();
        Assert.assertEquals("secret", d2.connection().get("/k", String.class));
        d2.close();
    }
    
    /**
     * Asserts that the start of 'builder', an open(), throws a DatabaseMissingException
     * whose message has 'expected', and that the files under 'root' are as they were: the
     * start created and wrote nothing (bergdb 015-05).
     */
    private static void assertOpenRefused(File root, DatabaseBuilder builder, String expected)
            throws IOException {
        String before = tree(root);
        try {
            Database d = builder.start();
            d.close();
            throw new AssertionError("a database started under " + root);
        } catch (DatabaseMissingException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains(expected));
        }
        Assert.assertEquals("the files under " + root, before, tree(root));
    }
    
    /** The files and directories under 'root', sorted, each file with its length and bytes. */
    private static String tree(File root) throws IOException {
        StringBuilder sb = new StringBuilder();
        tree(root, "", sb);
        return sb.toString();
    }
    
    private static void tree(File f, String path, StringBuilder sb) throws IOException {
        if (f.isDirectory()) {
            sb.append(path).append("/\n");
            String[] names = f.list();
            java.util.Arrays.sort(names);
            for (String n : names) {
                tree(new File(f, n), path + "/" + n, sb);
            }
        } else {
            byte[] bytes = Util.fileToBytes(f.getPath());
            sb.append(path).append(' ').append(bytes.length).append(' ')
                    .append(java.util.Arrays.hashCode(bytes)).append('\n');
        }
    }
    
    @Nano
    private static void testTransactionInfo1() throws UnsupportedEncodingException {
        TestClock clock = new TestClock();
        Database db = Factory.database().clock(clock).memory().start();
        Connection c = db.connection();
        
        clock.setTime(Time.units(1000));
        Transaction trans1 = c.w()
                .put("/key1", "v1")
                .put("/key2", "v2")
                .execute();
        
        c.get("/key1", byte[].class);
        TransactionInfo tinfo = c.transactionInfo();
        db.stop();
        
        Assert.assertEquals(trans1.getTime(), tinfo.time());
        Assert.assertEquals(2, tinfo.kvs().size());
        Assert.assertArrayEquals("v1".getBytes("UTF-8"), tinfo.kvs().get(0).value());
        Assert.assertArrayEquals("v2".getBytes("UTF-8"), tinfo.kvs().get(1).value());
        Assert.assertEquals("/key1", tinfo.kvs().get(0).key());
        Assert.assertEquals("/key2", tinfo.kvs().get(1).key());
    }
    
    /**
     * Regression test for bergdb 005-34: after a restart, transactionInfo() read at the
     * value's own position and threw StreamFormatException, as startup's rerun of the
     * transaction did not give the value its transaction's position.
     */
    @Nano
    private static void testTransactionInfoAfterRestart() {
        MemoryStream m = new MemoryStream();
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m).start();
        Connection c = d.connection();
        Transaction t = c.w().put("/key1", "v1").put("/key2", "v2").execute();
        d.sync();
        d.stop();
        
        d = ((DatabaseBuilderImp) Factory.database()).mainStream(m.copy()).start();
        c = d.connection();
        Assert.assertEquals("v2", c.get("/key2", String.class));
        TransactionInfo tinfo = c.transactionInfo();
        Assert.assertEquals(t.getTime(), tinfo.time());
        Assert.assertEquals(2, tinfo.kvs().size());
        Assert.assertEquals("/key2", tinfo.kvs().get(1).key());
        d.stop();
    }
    
    /**
     * Regression test for bergdb 005-42: a transaction that wrote an index entry gave it
     * among its KVs, and its key() threw IllegalArgumentException. Now the KVs are the
     * user's, also when a put replaces an index entry.
     */
    @Nano
    private static void testTransactionInfoWithIndex() {
        Database db = Factory.database().memory().start();
        db.indexBuilder("area").dir("/houses/").type("long").field("area").start().join();
        Connection c = db.connection();
        House h = new House();
        h.area = 120;
        c.put("/houses/h1", h);
        h.area = 130;
        Transaction t = c.w().put("/houses/h1", h).put("/other", "x").execute();
        
        Assert.assertEquals(130, c.get("/houses/h1", House.class).area);
        TransactionInfo tinfo = c.transactionInfo();
        Assert.assertEquals(t.getTime(), tinfo.time());
        Set<String> keys = new java.util.HashSet<String>();
        for (Kv<byte[]> kv : tinfo.kvs()) {
            keys.add(kv.key());
        }
        Assert.assertEquals(2, tinfo.kvs().size());
        Assert.assertTrue("keys: " + keys, keys.contains("/houses/h1") && keys.contains("/other"));
        db.stop();
    }
    
    /**
     * Regression test for bergdb 005-42: for a value that reclaim had rewritten,
     * transactionInfo() described reclaim's step, with its time and its row, whose key()
     * threw. Now it throws LookupTimeNotAvailableException, as for a transaction that reclaim
     * has removed; a value written after the cut still gives its transaction. Made with the
     * core's builder, as testFirstAvailableLookupTime2, so that reclaim cuts soon.
     */
    @Nano
    private static void testTransactionInfoAfterReclaim() {
        TestClock clock = new TestClock();
        Db db = Db.builder().testSetup(new CutStream()).clock(clock).maxNodeSize8()
                .startupDistance(2000).build();
        Database d = DatabaseImp.createAndStart(db);
        d.setRetainDuration(Duration.seconds(1));
        Connection c = d.connection();
        
        long sec = Duration.seconds(1).units();
        long time = sec;
        clock.setTime(Time.units(time));
        long t0 = c.w().put("/a", "a0").execute().getTime().units();
        java.util.Random r = new java.util.Random(1);
        for (int i = 0; i < 20000 && d.getFirstAvailableLookupTime().units() <= t0; i++) {
            time += sec / 20;
            clock.setTime(Time.units(time));
            c.w().put("/k/" + r.nextInt(50), "v" + i).execute();
        }
        Assert.assertTrue("no cut after /a", d.getFirstAvailableLookupTime().units() > t0);
        
        Assert.assertEquals("a0", c.get("/a", String.class));
        String gave = null;
        try {
            gave = "a transaction at " + c.transactionInfo().time().units();
        } catch (LookupTimeNotAvailableException e) {
            // Expected.
        }
        Assert.assertTrue("a value that reclaim rewrote gave " + gave + "; /a was put at " + t0,
                gave == null);
        
        clock.setTime(Time.units(time + sec));
        Transaction t1 = c.w().put("/b", "b1").execute();
        Assert.assertEquals("b1", c.get("/b", String.class));
        TransactionInfo tinfo = c.transactionInfo();
        Assert.assertEquals(t1.getTime(), tinfo.time());
        Assert.assertEquals(1, tinfo.kvs().size());
        Assert.assertEquals("/b", tinfo.kvs().get(0).key());
        d.stop();
    }
    
    /**
     * Regression test for bergdb 005-45: a w-transaction's sync(level) waited for the
     * database's last transaction, not for its own, as its sync() and an rw-transaction's
     * sync(level) do. Here the stream holds back the appends of a later transaction, and the
     * first one's sync(level) returns at once, as that one is durable.
     */
    @Nano
    private static void testWSyncLevelWaitsForItsOwn() throws InterruptedException {
        final HeldStream s = new HeldStream();
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(s).start();
        Connection c = d.connection();
        final Transaction t1 = c.w().put("/a", "1").execute();
        t1.sync();
        s.hold();
        c.w().put("/b", "2").execute();
        
        Thread syncer = new Thread() {
            public void run() {
                t1.sync(SyncLevel.ORDINARY);
            }
        };
        syncer.start();
        syncer.join(5000);
        final boolean returned = !syncer.isAlive();
        s.release();
        syncer.join();
        Assert.assertTrue("sync(ORDINARY) waited for a later transaction", returned);
        d.stop();
    }
    
    /** A MemoryStream whose appends fail once 'fail' is set (bergdb 019-09). */
    private static class FailingStream implements AppendOnlyStream {
        private final MemoryStream inner = new MemoryStream();
        volatile boolean fail = false;
        
        public long getLength() {
            return inner.getLength();
        }
        
        public long getFirstPos() {
            return inner.getFirstPos();
        }
        
        public void read(long position, byte[] dest, int destOffset, int length) 
                throws IOException {
            inner.read(position, dest, destOffset, length);
        }
        
        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            if (fail) {
                throw new IOException("a failed append");
            }
            inner.append(source, sourceOffset, length);
        }
        
        public void pretruncate(long position) throws IOException {
            inner.pretruncate(position);
        }
        
        public void close() {
            inner.close();
        }
    }
    
    /** A MemoryStream whose appends wait while it is held (bergdb 005-45). */
    private static class HeldStream implements AppendOnlyStream {
        private final MemoryStream inner = new MemoryStream();
        private boolean held = false;
        
        synchronized void hold() {
            held = true;
        }
        
        synchronized void release() {
            held = false;
            notifyAll();
        }
        
        public long getLength() {
            return inner.getLength();
        }
        
        public long getFirstPos() {
            return inner.getFirstPos();
        }
        
        public void read(long position, byte[] dest, int destOffset, int length) 
                throws IOException {
            inner.read(position, dest, destOffset, length);
        }
        
        public synchronized void append(byte[] source, int sourceOffset, int length) 
                throws IOException {
            while (held) {
                try {
                    wait();
                } catch (InterruptedException e) {
                    throw new IOException("interrupted");
                }
            }
            inner.append(source, sourceOffset, length);
        }
        
        public void pretruncate(long position) throws IOException {
            inner.pretruncate(position);
        }
        
        public void close() {
            inner.close();
        }
    }
    
    /**
     * Regression test for bergdb 005-32: a start through the Pub API that throws, here with a
     * wrong crypto key, left its storage's thread and open file until the garbage collector
     * finalized the Db. Now ten such starts leave none, counted at once; then the right key
     * starts.
     */
    @Nano
    private static void testFailedStartsLeaveNothing(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = env.createTempDir();
        CryptoKey right = CryptoKey.generate();
        Database d = Factory.database().create(dir.getPath()).cryptoKey(right).start();
        d.connection().put("/k", "v");
        d.sync();
        ((DatabaseImp) d).getDb().close();
        
        Set<Thread> before = DbTesterFailure.storageThreads();
        long files = openFiles();
        for (int i = 0; i < 10; i++) {
            try {
                Factory.database().create(dir.getPath()).cryptoKey(CryptoKey.generate()).start();
                throw new AssertionError("started with a wrong key");
            } catch (BadCryptoKey e) {
                // Expected.
            }
        }
        DbTesterFailure.assertNoNewStorageThreads(before);
        if (files >= 0) {
            Assert.assertTrue("open files " + openFiles() + ", before " + files, 
                    openFiles() <= files);
        }
        
        Database d2 = Factory.database().create(dir.getPath()).cryptoKey(right).start();
        Assert.assertEquals("v", d2.connection().get("/k", String.class));
        ((DatabaseImp) d2).getDb().close();
    }
    
    /**
     * bergdb 005-32: a directory whose start failed, here as its creation crashed (005-33),
     * can be removed and created again at once: the failed start has closed its files.
     */
    @Nano
    private static void testFailedStartsDirectoryRemoved(TestEnvironment env) 
            throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File d = new File(env.createTempDir(), "db");
        Database first = Factory.database().create(d.getPath()).start();
        first.sync();
        ((DatabaseImp) first).getDb().close();
        File[] streams = d.listFiles();
        File stream = null;
        for (File f : streams) {
            if (f.getName().endsWith(".bergdb")) {
                stream = f;
            }
        }
        RandomAccessFile raf = new RandomAccessFile(stream, "rw");
        raf.setLength(200);                 // In the creation's first transaction.
        raf.close();
        
        Set<Thread> before = DbTesterFailure.storageThreads();
        long files = openFiles();
        try {
            Factory.database().create(d.getPath()).start();
            throw new AssertionError("started");
        } catch (DatabaseNotCreatedException e) {
            // Expected (005-33; until 2026-10-25 a StreamFormatException, 005-28).
        }
        Assert.assertEquals("the stream as it was", 200, stream.length());
        DbTesterFailure.assertNoNewStorageThreads(before);
        if (files >= 0) {
            Assert.assertTrue("open files " + openFiles() + ", before " + files, 
                    openFiles() <= files);
        }
        for (File f : d.listFiles()) {
            Assert.assertTrue("removed " + f, f.delete());
        }
        Assert.assertTrue("removed " + d, d.delete());
        
        Database again = Factory.database().create(d.getPath()).start();
        again.connection().put("/a", "a0");
        Assert.assertEquals("a0", again.connection().get("/a", String.class));
        ((DatabaseImp) again).getDb().close();
    }
    
    /**
     * bergdb 005-32: when anything throws after db.start() in DatabaseImp.createAndStart()
     * (here a test hook), the Db is closed; it ran on until the garbage collector stopped it.
     */
    @Nano
    private static void testExceptionAfterStartClosesDb() {
        final Db[] started = new Db[1];
        DatabaseImp.testHookAfterStart = new Consumer<Db>() {
            public void accept(Db db) {
                started[0] = db;
                throw new IllegalStateException("the test hook");
            }
        };
        Set<Thread> before = DbTesterFailure.storageThreads();
        MemoryStream m = new MemoryStream();
        try {
            ((DatabaseBuilderImp) Factory.database()).mainStream(m).start();
            throw new AssertionError("started");
        } catch (IllegalStateException e) {
            Assert.assertEquals("the test hook", e.getMessage());
        } finally {
            DatabaseImp.testHookAfterStart = null;
        }
        DbTesterFailure.assertNoNewStorageThreads(before);
        DbTesterFailure.assertClosed(m);
        try {
            started[0].execute(started[0].trans().put("/a", "a0").build());
            throw new AssertionError("a transaction was taken");
        } catch (DbStoppingException e) {
            // Expected.
        }
    }
    
    /**
     * bergdb 005-32: a start that throws before the Db is built, here for a crypto key of an
     * unknown algorithm, closes the file that dir() opened.
     */
    @Nano
    private static void testUnknownCryptoAlgorithmClosesFile(TestEnvironment env) 
            throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = env.createTempDir();
        CryptoKey key = CryptoKey.parse("8184a9f2-other-75ac20b68ccdbf95b9999287bc4da0caf67b4c8e"
                + "dc40d7615bebf1beae3578b800cfc3dfbaad319c");
        long files = openFiles();
        for (int i = 0; i < 3; i++) {
            try {
                Factory.database().create(dir.getPath()).cryptoKey(key).start();
                throw new AssertionError("started");
            } catch (IllegalStateException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("other"));
            }
        }
        if (files >= 0) {
            Assert.assertTrue("open files " + openFiles() + ", before " + files, 
                    openFiles() <= files);
        }
    }
    
    /**
     * Regression test for bergdb 005-35: Database.stop() lost the transactions still in the
     * write buffer, all of them in a quick run. Now, once its close has ended, the stream
     * holds every one, and it is closed.
     */
    @Nano
    private static void testStopWritesAll() throws Exception {
        MemoryStream m = new MemoryStream();
        Database d = ((DatabaseBuilderImp) Factory.database()).mainStream(m).start();
        Connection c = d.connection();
        for (int i = 0; i < 300; i++) {
            c.put("/k" + i, "v" + i);
        }
        Set<Thread> before = DbTester.closeThreads();
        d.stop();
        DbTester.joinNew(before);
        DbTesterFailure.assertClosed(m);
        
        Database d2 = ((DatabaseBuilderImp) Factory.database()).mainStream(m.copy()).start();
        for (int i = 0; i < 300; i++) {
            Assert.assertEquals("v" + i, d2.connection().get("/k" + i, String.class));
        }
        ((DatabaseImp) d2).getDb().close();
    }
    
    /**
     * bergdb 005-35: a program that called Database.stop() and returned from main kept only
     * what had been flushed, as the storage threads are daemons. Now stop()'s close runs in
     * a thread that is not, and the JVM ends after it: the files hold all transactions.
     */
    @Nano("f")
    private static void testStopThenReturnFromMain(TestEnvironment env) throws Exception {
        if (Util.runsAndroid()) {
            return;
        }
        File tmp = env.createTempDir();
        File dir = new File(tmp, "db");
        File out = new File(tmp, "child.txt");
        String javaBin = System.getProperty("java.home") + "/bin/java";
        String cp = System.getProperty("java.class.path");
        Process p = new ProcessBuilder(javaBin, "-cp", cp, StopAndReturn.class.getName(), 
                dir.getPath()).redirectErrorStream(true).redirectOutput(out).start();
        Assert.assertTrue("the child ends", p.waitFor(60, java.util.concurrent.TimeUnit.SECONDS));
        String output = new String(Util.fileToBytes(out.getPath()), "UTF-8");
        Assert.assertEquals("the child's exit, " + output, 0, p.exitValue());
        
        Database d = Factory.database().open(dir.getPath()).start();
        Connection c = d.connection();
        int found = 0;
        for (int i = 0; i < StopAndReturn.N; i++) {
            if (c.get("/k" + i, String.class) != null) {
                found++;
            }
        }
        ((DatabaseImp) d).getDb().close();
        Assert.assertEquals("the keys in the files", StopAndReturn.N, found);
    }
    
    /** testStopThenReturnFromMain's child: puts, Database.stop(), and returns from main. */
    public static class StopAndReturn {
        static final int N = 2000;
        
        public static void main(String[] args) {
            Database d = Factory.database().create(args[0]).start();
            Connection c = d.connection();
            for (int i = 0; i < N; i++) {
                c.put("/k" + i, "v" + i);
            }
            d.stop();
        }
    }
    
    /** Open file descriptors of this JVM, or -1 where it cannot be told (bergdb 005-32). */
    private static long openFiles() {
        java.lang.management.OperatingSystemMXBean os = 
                java.lang.management.ManagementFactory.getOperatingSystemMXBean();
        if (os instanceof com.sun.management.UnixOperatingSystemMXBean) {
            return ((com.sun.management.UnixOperatingSystemMXBean) os)
                    .getOpenFileDescriptorCount();
        }
        return -1;
    }

    // ---- bergdb 020-08, step 3: objects of 2026.3 and before (format 1) refused ----
    
    /** Payment {from "1001", to "1002", amount 500} as 2026.3 wrote it (020-07's vectors). */
    static byte[] format1Payment() {
        return ObjectFormatTester.unhex("626572676f010300391c1a0000007d1b2b000000131d3a0000006c"
                + "0600616d6f756e74f40100000000000073040066726f6d0400000031303031730200746f04"
                + "00000031303032");
    }
    
    /** Throws 'expected' from 'r', its message naming format 1. */
    private static void assertFormat1(String what, Class<? extends Throwable> expected, 
            Runnable r) {
        try {
            r.run();
        } catch (Throwable e) {
            Assert.assertTrue(what + ": " + e, expected.isInstance(e));
            Assert.assertTrue(what + ": " + e.getMessage(), e.getMessage().contains("format 1"));
            return;
        }
        throw new AssertionError(what + ": no exception");
    }
    
    /**
     * T8 (020-08, section 6.2; 020-02, section 4.11): an object of format 1 at a key is
     * refused with a message that names the format: a get as a class, as DbObject and as
     * Object throws ObjectCreationException, in rw() too, and the database goes on; a primary
     * scan of objects throws it for that object and goes on; a byte[] put of it in an indexed
     * directory gives DataFormatException; a build over a directory holding it ends failed,
     * with the message. A put over it and a delete of it work, also in an indexed directory and
     * in one whose build failed: a previous value of format 1 has no entries, as no index of
     * 2026.4 ever indexed one (2026-11-09, the review of e92a95a: such a key could not be
     * written or deleted while the index existed).
     */
    @Nano
    public static void testFormat1ObjectRefused() {
        Database d = Factory.database().memory().start();
        try {
            final Connection c = d.connection();
            c.put("/p/a", new Payment("1", "2", 3));
            c.put("/p/b", format1Payment());
            c.put("/p/c", new Payment("4", "5", 6));
            for (final Class<?> clazz : new Class<?>[] {Payment.class, DbObject.class, 
                    Object.class}) {
                assertFormat1("a get as " + clazz.getName(), ObjectCreationException.class,
                        () -> c.get("/p/b", clazz));
                assertFormat1("a get in rw() as " + clazz.getName(), 
                        ObjectCreationException.class, () -> c.rw(new Action() {
                            public void run(RwEnvironment env) {
                                env.put("/written", "x");
                                env.get("/p/b", clazz);
                            }
                        }));
            }
            Assert.assertNull(c.get("/written", String.class));
            
            for (final Class<?> clazz : new Class<?>[] {Payment.class, DbObject.class}) {
                final Iterator<?> it = c.usePrimary(clazz).dir("/p/").objects().iterator();
                Assert.assertTrue(it.next() != null);
                assertFormat1("a primary scan as " + clazz.getName(), 
                        ObjectCreationException.class, () -> it.next());
                Assert.assertTrue(it.next() != null);
                Assert.assertFalse(it.hasNext());
            }
            Assert.assertArrayEquals(format1Payment(), c.get("/p/b", byte[].class));
            
            JobStatus status = d.indexBuilder("from").dir("/p/").type("string").field("from")
                    .start().join();
            Assert.assertTrue(status.note(), status.state() == JobStatus.State.FAILED
                    && status.reason().contains("format 1") && status.reason().contains("/p/b"));
            c.delete("/p/b");       // the user cleans up after the failed build
            Assert.assertNull(c.get("/p/b", byte[].class));
            assertFormat1("a byte[] put of it where the build failed",    // the index kept
                    bergdb.pub.DataFormatException.class, () -> c.put("/p/b", format1Payment()));
            c.put("/p/b", new Payment("7", "8", 9));
            Assert.assertEquals(9L, c.get("/p/b", Payment.class).amount);
            
            c.put("/q/a", new Payment("1", "2", 3));
            d.indexBuilder("q-from").dir("/q/").type("string").field("from").start().join();
            assertFormat1("a byte[] put of it in an indexed directory", 
                    bergdb.pub.DataFormatException.class, () -> c.put("/q/x", format1Payment()));
            Db db = ((DatabaseImp) d).getDb();     // written as 2026.3 wrote it
            db.execute(db.trans().put(Keys.toBytes(PubKeys.u2i("/q/b")), format1Payment())
                    .build());
            c.put("/q/b", new Payment("7", "8", 9));        // a put over it, with its entry
            Assert.assertEquals(9L, c.useIndex("q-from", Payment.class).eq("7").kvs()
                    .iterator().next().value().amount);
            db.execute(db.trans().put(Keys.toBytes(PubKeys.u2i("/q/c")), format1Payment())
                    .build());
            c.w().delete("/q/c").execute();                 // a delete of it
            Assert.assertNull(c.get("/q/c", byte[].class));
            db.execute(db.trans().put(Keys.toBytes(PubKeys.u2i("/q/d")), format1Payment())
                    .build());
            c.put("/q/d", "a String over it");
            Assert.assertEquals("a String over it", c.get("/q/d", String.class));
            int n = 0;
            for (Payment p : c.useIndex("q-from", Payment.class).objects()) {
                n += p.from.equals("1") || p.from.equals("7") ? 1 : 100;
            }
            Assert.assertEquals(2, n);
            
            c.put("/later", "x");      // not failed
            Assert.assertEquals("x", c.get("/later", String.class));
        } finally {
            d.close();
        }
    }
    
    /**
     * T8: a database whose index definition is in format 1 does not start: the start throws
     * VersioningStreamException with a message that names the format and says what to do
     * (020-08, section 5), and closes the database.
     */
    @Nano
    public static void testFormat1IndexDefinitionRefused() {
        MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        Database d = builder.start();
        try {
            d.indexBuilder("old").dir("/p/").type("long").field("amount").start().join();
            Db db = ((DatabaseImp) d).getDb();
            byte[] key = Util.concat(Keys.toBytes(DbConstants.INTERNAL_PREFIX + "dii/"), 
                    Keys.toBytes("-old"));
            db.execute(db.trans().put(key, ObjectFormatTester.unhex("626572676f010000"))
                    .build());
        } finally {
            d.close();
        }
        
        builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream.copy());
        try {
            builder.start();
            throw new AssertionError("started");
        } catch (VersioningStreamException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("format 1")
                    && e.getMessage().contains("Make the database again"));
        }
    }
    
    /**
     * T9 (020-08, sections 3 and 6.2): a String value is never an object; a byte[] that starts
     * with the header of format 2 but is not a stored object is a byte[] to a get as Object
     * and is skipped by a build; a stored object's complete bytes put as a byte[] at an object
     * key is an object, to a get and to a primary scan as DbObject and as its class (the
     * guess of UsePrimaryBuilder's Javadoc, 020-01, N4).
     */
    @Nano
    public static void testKindOfValue() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            c.put("/v/s", "x");
            Assert.assertArrayEquals(new byte[] {'x'}, (byte[]) c.get("/v/s", Object.class));
            byte[] notObject = {DbObject.HEADER, 0x48, 1};
            c.put("/v/t", notObject);
            Assert.assertArrayEquals(notObject, (byte[]) c.get("/v/t", Object.class));
            byte[] object = DbObject.toDbObject(new Payment("1", "2", 3)).getBytes();
            c.put("/v/u", object);
            Assert.assertEquals("1", ((DbObject) c.get("/v/u", Object.class)).getString("from"));
            
            int n = 0;
            for (DbObject o : c.usePrimary(DbObject.class).dir("/v/").objects()) {
                Assert.assertArrayEquals(object, o.getBytes());
                n++;
            }
            Assert.assertEquals(1, n);
            n = 0;
            for (Payment p : c.usePrimary(Payment.class).dir("/v/").objects()) {
                Assert.assertEquals(3L, p.amount);
                n++;
            }
            Assert.assertEquals(1, n);
            
            JobStatus status = d.indexBuilder("from").dir("/v/").type("string").field("from")
                    .start().join();
            Assert.assertTrue(status.note(), status.state() == JobStatus.State.ACTIVE);
            n = 0;
            for (Payment p : c.useIndex("from", Payment.class).objects()) {
                Assert.assertEquals("1", p.from);
                n++;
            }
            Assert.assertEquals(1, n);
        } finally {
            d.close();
        }
    }
    
    /** The keys that a primary scan of 'type' lists in 'dir', in order, and the values' kinds. */
    private static String listed(Connection c, Class<?> type, String dir) {
        StringBuilder b = new StringBuilder();
        for (Kv<?> kv : c.usePrimary(type).dir(dir).kvs()) {
            b.append(b.length() == 0 ? "" : " ").append(kv.key()).append(':')
                    .append(kv.value().getClass().getSimpleName());
        }
        return b.toString();
    }
    
    /**
     * A String value that starts with format 1's first six bytes, "bergo" and the version 1,
     * is a String (bergdb 020-08, section 3; the review of step 3, night 006-15): format 1 is
     * told by its structure, and a String put is never taken for it. A get as String, byte[]
     * and Object (bytes); a primary scan as String, Object, DbObject and a class; in an indexed
     * directory a put of it, in rw() too, a byte[] put of its bytes, a put over it and a
     * delete of it; a build over a directory that holds it. Last, the guess that remains: a
     * stored value whose bytes are a whole object of format 1 is taken for one, also a String
     * put, by a get; the put itself is not refused, nor a put over it or a delete of it.
     */
    @Nano
    public static void testStringThatStartsAsFormat1() {
        final String text = "bergo\u0001 a user's text";
        final byte[] bytes = StringUtil.toBytes(text);
        Database d = Factory.database().memory().start();
        try {
            final Connection c = d.connection();
            c.put("/s/a", text);
            c.put("/s/b", "plain");
            c.put("/s/c", new Payment("1", "2", 3));
            Assert.assertEquals(text, c.get("/s/a", String.class));
            Assert.assertArrayEquals(bytes, c.get("/s/a", byte[].class));
            Assert.assertArrayEquals(bytes, (byte[]) c.get("/s/a", Object.class));
            Assert.assertEquals("/s/a:String /s/b:String", listed(c, String.class, "/s/"));
            Assert.assertEquals("/s/a:byte[] /s/b:byte[] /s/c:DbObject", 
                    listed(c, Object.class, "/s/"));
            Assert.assertEquals("/s/c:DbObject", listed(c, DbObject.class, "/s/"));
            Assert.assertEquals("/s/c:Payment", listed(c, Payment.class, "/s/"));
            
            c.put("/i/x", new Payment("x", "y", 1));
            JobStatus status = d.indexBuilder("from").dir("/i/").type("string").field("from")
                    .start().join();
            Assert.assertTrue(status.note(), status.state() == JobStatus.State.ACTIVE);
            c.put("/i/a", text);
            c.rw(new Action() {
                public void run(RwEnvironment env) {
                    env.put("/i/b", text);
                }
            });
            c.put("/i/c", bytes);
            c.put("/i/a", "new");
            c.delete("/i/b");
            c.put("/i/c", new Payment("c", "y", 2));
            Assert.assertEquals("new", c.get("/i/a", String.class));
            Assert.assertNull(c.get("/i/b", String.class));
            int n = 0;
            for (Payment p : c.useIndex("from", Payment.class).objects()) {
                Assert.assertEquals(n == 0 ? "c" : "x", p.from);
                n++;
            }
            Assert.assertEquals(2, n);
            
            c.put("/j/a", text);
            c.put("/j/x", new Payment("x", "y", 1));
            status = d.indexBuilder("j").dir("/j/").type("string").field("from").start().join();
            Assert.assertTrue(status.note(), status.state() == JobStatus.State.ACTIVE);
            Assert.assertEquals(1L, c.useIndex("j", Payment.class).eq("x").kvs().iterator()
                    .next().value().amount);
            c.put("/j/a", text + " again");
            c.delete("/j/a");
            Assert.assertNull(c.get("/j/a", String.class));
            
            final String whole = "bergo\u0001\u0000\u0000";     // an empty object of format 1
            c.put("/i/g", whole);
            Assert.assertEquals(whole, c.get("/i/g", String.class));
            assertFormat1("a get as Object of the guess", ObjectCreationException.class, 
                    () -> c.get("/i/g", Object.class));
            c.put("/i/g", "x");     // a put over the guess: no entries, as format 1 has none
            Assert.assertEquals("x", c.get("/i/g", String.class));
            c.put("/i/h", whole);
            c.delete("/i/h");
            Assert.assertNull(c.get("/i/h", String.class));
            
            c.put("/later", "x");       // not failed
            Assert.assertEquals("x", c.get("/later", String.class));
        } finally {
            d.close();
        }
    }
    
    /**
     * A String value's UTF-8 is counted before it is made (bergdb 020-08, section 3; the
     * review of step 3, night 006-15): above the limit, IllegalArgumentException, not the
     * OutOfMemoryError of an encoding past Java's largest array. Here with small limits;
     * testHugeStringRefused (night) with 2^31 bytes.
     */
    @Nano
    public static void testStringValueCountedFirst() {
        Assert.assertArrayEquals(new byte[] {'a', 'b'}, RwEnvironmentImp.stringValue("ab", 2));
        Assert.assertEquals(3, RwEnvironmentImp.stringValue("a\u00e9", 3).length);
        Assert.assertEquals(4, RwEnvironmentImp.stringValue("\ud83d\ude00", 4).length);
        for (final String[] t : new String[][] {{"abc", "2"}, {"a\u00e9", "2"}, 
                {"\ud83d\ude00", "3"}, {"\u0800", "2"}}) {
            PubTesterPrimary.assertThrows(IllegalArgumentException.class, 
                    () -> RwEnvironmentImp.stringValue(t[0], Long.parseLong(t[1])));
        }
        PubTesterPrimary.assertThrows(IllegalArgumentException.class,      // lone surrogate
                () -> RwEnvironmentImp.stringValue("x\ud800", 100));
        // With a small limit, the path of a String counted first (3 bytes a char over the
        // limit), which encodes into an array of its counted size (the review of e92a95a):
        // the same bytes as getBytes().
        for (String t : new String[] {"a\u00e9", "\u00e9" + "a".repeat(40), "\u0800x", 
                "\ud83d\ude00", "abc"}) {
            byte[] b = StringUtil.toBytes(t);
            Assert.assertArrayEquals(b, RwEnvironmentImp.stringValue(t, b.length));
        }
    }
    
    /**
     * A String whose UTF-8 fits, 2^30 + 1 bytes (a String of 2^30 chars, one of them U+00E9,
     * so Latin-1 of 1 GiB), is encoded into an array of its size, as a value and as a
     * DbString (the review of e92a95a: String.getBytes() allocated 2 bytes a char for such a
     * String, more than Java's largest array, and threw OutOfMemoryError). Skipped in a JVM
     * of less than 3 GiB of heap.
     */
    @Nano("night")
    public static void testLargeStringThatFits() {
        if (Runtime.getRuntime().maxMemory() < (3L << 30)) {
            System.out.println("PubTester.testLargeStringThatFits: skipped, heap below 3 GiB");
            return;
        }
        final String large = "\u00e9" + "a".repeat((1 << 30) - 1);
        byte[] b = RwEnvironmentImp.stringValue(large, ObjectFormat.MAX_ARRAY);
        Assert.assertEquals((1 << 30) + 1, b.length);
        Assert.assertTrue((b[0] & 0xff) == 0xc3 && (b[1] & 0xff) == 0xa9 && b[2] == 'a'
                && b[b.length - 1] == 'a');
        b = null;
        DbString v = new DbString(large);
        Assert.assertEquals(5 + (1 << 30) + 1, v.getByteSize());
        Assert.assertTrue(v.toStringValue() == large);
    }
    
    /**
     * A String of 2^31 UTF-8 bytes (2^30 chars of U+00E9, a String of 1 GiB): a put of it as
     * a value and as an object's field throws IllegalArgumentException before it is encoded,
     * not an OutOfMemoryError in rw(), an Error that fails the database (bergdb 019-10), and
     * the database goes on (bergdb 020-08, section 3; the review of step 3, night 006-15).
     * Skipped in a JVM of less than 3 GiB of heap.
     */
    @Nano("night")
    public static void testHugeStringRefused() {
        if (Runtime.getRuntime().maxMemory() < (3L << 30)) {
            System.out.println("PubTester.testHugeStringRefused: skipped, heap below 3 GiB");
            return;
        }
        final String huge = "\u00e9".repeat(1 << 30);
        Database d = Factory.database().memory().start();
        try {
            final Connection c = d.connection();
            PubTesterPrimary.assertThrows(IllegalArgumentException.class,      // a value
                    () -> c.put("/v", huge));
            PubTesterPrimary.assertThrows(IllegalArgumentException.class,      // a field
                    () -> c.put("/o", new Payment(huge, "2", 3)));
            c.put("/later", "x");       // not failed
            Assert.assertEquals("x", c.get("/later", String.class));
        } finally {
            d.close();
        }
    }
    
    /**
     * A put of a DbObject stores a copy of its bytes (the review of B3, F1): a change of the
     * array that getBytes() gave, after the commit, changes neither the stored value nor the
     * index's entry; it changed the value in memory until a restart, and the index found it
     * by neither value.
     */
    @Nano
    public static void testDbObjectPutStoresACopy() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            d.indexBuilder("n").dir("/o/").type("long").field("n").start().join();
            DbObject o = new DbObject.Builder().addLong("n", 5).build();
            c.put("/o/a", o);
            byte[] b = o.getBytes();
            b[b.length - 1] = 6;        // the integer's value, 5
            Assert.assertEquals(5L, c.get("/o/a", DbObject.class).getLong("n"));
            Assert.assertEquals(5L, o.getLong("n"));
            int n = 0;
            for (DbObject x : c.useIndex("n", DbObject.class).eq(5L).objects()) {
                Assert.assertEquals(5L, x.getLong("n"));
                n++;
            }
            Assert.assertEquals(1, n);
        } finally {
            d.close();
        }
    }
    
    public static class Inner12 {
        public String name;
        public Inner12() {}
    }
    
    public static class N12 {
        public Long v;
        public Inner12 inner;
        public N12() {}
        public N12(Long v, Inner12 inner) {
            this.v = v;
            this.inner = inner;
        }
    }
    
    public static class Other12 {
        public int other = 1;
        public Other12() {}
    }
    
    private static Inner12 inner12(String name) {
        Inner12 i = new Inner12();
        i.name = name;
        return i;
    }
    
    private static String indexKeys(Connection c, String index) {
        StringBuilder keys = new StringBuilder();
        for (Kv<DbObject> kv : c.useIndex(index, DbObject.class).kvs()) {
            keys.append(kv.key()).append(' ');
        }
        return keys.toString();
    }
    
    /**
     * bergdb 020-04, N12: one index rule. An object has an entry when each indexed field is
     * present with a type its level takes: a field absent from the class, null (so absent),
     * or below a null object gives none, and the put is taken; by maintenance at a put and by
     * a build alike. Until format 2 a null String in a string index refused the put (019-42).
     */
    @Nano
    public static void testOneIndexRule() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            d.indexBuilder("v").dir("/n/").type("long").field("v").start().join();
            d.indexBuilder("name").dir("/n/").type("string").nestedField("inner.name").start()
                    .join();
            for (int pass = 0; pass < 2; pass++) {
                c.w().put("/n/1", new N12(5L, inner12("x")))
                        .put("/n/2", new N12(null, null))
                        .put("/n/3", new N12(7L, inner12(null)))
                        .put("/n/4", new Other12())
                        .put("/n/5", new N12(null, inner12("y"))).execute();
                Assert.assertEquals("/n/1 /n/3 ", indexKeys(c, pass == 0 ? "v" : "v2"));
                Assert.assertEquals("/n/1 /n/5 ", indexKeys(c, pass == 0 ? "name" : "name2"));
                if (pass == 0) {
                    d.indexBuilder("v2").dir("/n/").type("long").field("v").start().join();
                    d.indexBuilder("name2").dir("/n/").type("string")
                            .nestedField("inner.name").start().join();
                }
            }
            Assert.assertArrayEquals(DbObject.toDbObject(new Other12()).getBytes(),
                    c.get("/n/4", byte[].class));
        } finally {
            d.close();
        }
    }
}
