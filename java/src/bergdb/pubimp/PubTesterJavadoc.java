package bergdb.pubimp;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Random;

import bergdb.core.Db;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.DataFormatException;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.DbArray;
import bergdb.pub.DbBoolean;
import bergdb.pub.DbByteArray;
import bergdb.pub.DbDouble;
import bergdb.pub.DbLong;
import bergdb.pub.DbObject;
import bergdb.pub.DbString;
import bergdb.pub.DbValue;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.Kv;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.TransactionInfo;
import bergdb.pub.UseIndexBuilder;
import bergdb.pub.UsePrimaryBuilder;
import bergdb.pub.WBuilder;
import bergdb.pub.util.BadFormatException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.IndexBuildException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;
import bergdb.stream.MemoryStream;

/**
 * The Pub API's Javadoc checked against its behaviour, promise by promise (bergdb 020-19):
 * the examples of the package page and of the class comments, as they are written, and the
 * promises of the classes that release 2026.4 changed most that no other tester showed.
 * Each test names the class and the promise it shows.
 *
 * @author Frans Lundberg
 */
public class PubTesterJavadoc {

    // ======== The classes of the examples ========

    /** The package page's class, as it is written there. */
    public static class Account {
        public String owner;
        public long balance;

        public Account() {}

        public Account(String owner, long balance) {
            this.owner = owner;
            this.balance = balance;
        }
    }

    /** For UseIndexBuilder's example: the index "by-from-amount". */
    public static class Payment {
        public String from;
        public long amount;

        public Payment() {}

        public Payment(String from, long amount) {
            this.from = from;
            this.amount = amount;
        }
    }

    /** For UseIndexBuilder's example: the index "by-name". */
    public static class Person {
        public String name;

        public Person() {}

        public Person(String name) {
            this.name = name;
        }
    }

    /** For IndexBuilder's example: the index "by-salary". */
    public static class Employee {
        public long salary;

        public Employee() {}

        public Employee(long salary) {
            this.salary = salary;
        }
    }

    /** Fields of every kind an index level takes, and some it does not. */
    public static class Kinds {
        public int i;
        public char ch;
        public long l;
        public float f;
        public double d;
        public boolean b;
        public String s;
        public byte[] bs;
        public int[] arr;
        public Integer absent;
    }

    /** For toDbObject()'s message: inner.names[3]. */
    public static class Names {
        public String[] names;
    }

    /** For toDbObject()'s message: inner.names[3]. */
    public static class Holder {
        public Names inner;
    }

    /** Not a Data Object: no public no-argument constructor. */
    public static class NoConstructor {
        public long x;

        public NoConstructor(long x) {
            this.x = x;
        }
    }

    /** A Data Object whose constructor throws an Error. */
    public static class ErrorInConstructor {
        public long balance;

        public ErrorInConstructor() {
            throw new AssertionError("an Error from the constructor");
        }
    }

    /** A Data Object whose constructor throws. */
    public static class Throws {
        public long x;

        public Throws() {
            throw new IllegalStateException("from the constructor");
        }
    }

    // ======== Helpers ========

    /** 'call' throws an exception of the class 'expected'; returns it. */
    static <T extends Throwable> T assertThrows(String what, Class<T> expected, Runnable call) {
        try {
            call.run();
        } catch (Throwable e) {
            if (expected.isInstance(e)) {
                return expected.cast(e);
            }
            throw new AssertionError(what + ": " + expected.getSimpleName() + " expected, got "
                    + e, e);
        }
        throw new AssertionError(what + ": " + expected.getSimpleName() + " expected, none");
    }

    /** A database on 'stream', which a copy of it restarts. */
    private static Database start(MemoryStream stream) {
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        return builder.start();
    }

    private static <T> List<T> list(Iterable<T> it) {
        List<T> result = new ArrayList<>();
        for (T t : it) {
            result.add(t);
        }
        return result;
    }

    private static String owners(Iterable<Account> accounts) {
        StringBuilder sb = new StringBuilder();
        for (Account a : accounts) {
            sb.append(sb.length() == 0 ? "" : " ").append(a.owner).append(' ')
                    .append(a.balance);
        }
        return sb.toString();
    }

    private static String keys(Iterable<? extends Kv<?>> kvs) {
        StringBuilder sb = new StringBuilder();
        for (Kv<?> kv : kvs) {
            sb.append(sb.length() == 0 ? "" : " ").append(kv.key());
        }
        return sb.toString();
    }

    // ======== The examples ========

    /**
     * The package page's examples, in order, in one try block, as the page says they run:
     * each comment's output is checked (bergdb.pub's package page, "A first program" to
     * "Indexes").
     */
    @Nano
    public static void testPackageExamples() {
        try (Database db = Factory.database().memory().start()) {
            Connection c = db.connection();
            c.put("/a.txt", "Hello world!");
            Assert.assertEquals("Hello world!", c.get("/a.txt", String.class));

            // Text and bytes
            c.put("/notes/a.txt", "Hello world!");
            c.put("/data/b.bin", new byte[] {1, 2, 3});
            Assert.assertEquals("Hello world!", c.get("/notes/a.txt", String.class));
            Assert.assertEquals(3, c.get("/data/b.bin", byte[].class).length);
            c.delete("/data/b.bin");
            Assert.assertNull(c.get("/data/b.bin", byte[].class));
            // "a get as Object.class gives a String at a ".txt" key, a byte[] at a ".bin" key"
            c.put("/data/c.bin", new byte[] {4});
            Assert.assertEquals("Hello world!", c.get("/notes/a.txt", Object.class));
            Assert.assertTrue(c.get("/data/c.bin", Object.class) instanceof byte[]);

            // Objects
            c.put("/acc/1001", new Account("Ann", 100));
            Account a = c.get("/acc/1001", Account.class);
            Assert.assertEquals("Ann 100", a.owner + " " + a.balance);

            // Several writes at once
            c.w().put("/acc/1002", new Account("Bob", 20))
                 .put("/acc/1003", new Account("Cecilia", 60))
                 .execute();

            // Read, then write
            c.rw(env -> {
                Account from = env.get("/acc/1001", Account.class);
                Account to = env.get("/acc/1002", Account.class);
                from.balance -= 30;
                to.balance += 30;
                env.put("/acc/1001", from);
                env.put("/acc/1002", to);
            });
            Assert.assertEquals(50, c.get("/acc/1002", Account.class).balance);

            // Earlier states
            Time t = c.currentTime();
            c.put("/notes/a.txt", "Hello again!");
            c.setLookupTime(t);
            Assert.assertEquals("Hello world!", c.get("/notes/a.txt", String.class));
            c.setLookupTime(Time.MAX);
            Assert.assertEquals("Hello again!", c.get("/notes/a.txt", String.class));

            // The keys of a directory, in order
            List<String> lines = new ArrayList<>();
            for (Kv<Account> kv : c.usePrimary(Account.class).dir("/acc/").kvs()) {
                lines.add(kv.key() + " " + kv.value().owner + " " + kv.value().balance);
            }
            Assert.assertEquals("[/acc/1001 Ann 70, /acc/1002 Bob 50, /acc/1003 Cecilia 60]",
                    lines.toString());

            // Indexes
            db.indexBuilder("by-balance").dir("/acc/").type("long").field("balance").start()
                    .join();
            Assert.assertEquals("Cecilia 60 Ann 70", owners(c.useIndex("by-balance",
                    Account.class).from(60, true).objects()));
        }
    }

    /**
     * The examples of the class comments: Database's try block, IndexBuilder's "by-salary",
     * UseIndexBuilder's "by-from-amount" and "by-name", each with data that shows what the
     * text says of it.
     */
    @Nano
    public static void testClassExamples() {
        // Database: a try-with-resources block closes it.
        Database closed;
        try (Database db = Factory.database().memory().start()) {
            db.connection().put("/a.txt", "Hello world!");
            closed = db;
        }
        final Database d0 = closed;
        assertThrows("a put after the block", IllegalDbStateException.class,
                () -> d0.connection().put("/b.txt", "x"));

        try (Database database = Factory.database().memory().start()) {
            Connection c = database.connection();
            c.put("/employees/e1", new Employee(300));
            c.put("/employees/e2", new Employee(100));
            database.indexBuilder("by-salary").dir("/employees/").type("long").field("salary")
                    .start().join();
            Assert.assertEquals("/employees/e2 /employees/e1", keys(c.useIndex("by-salary",
                    Employee.class).kvs()));

            c.put("/payments/p1", new Payment("1001", 100));
            c.put("/payments/p2", new Payment("1001", 500));
            c.put("/payments/p3", new Payment("1001", 499));
            c.put("/payments/p4", new Payment("1002", 200));
            c.put("/payments/p5", new Payment("1001", 99));
            database.indexBuilder("by-from-amount").dir("/payments/").type("string")
                    .field("from").type("long").field("amount").start().join();
            List<Long> amounts = new ArrayList<>();
            for (Payment p : c.useIndex("by-from-amount", Payment.class).eq("1001")
                    .from(100, true).to(500, false).objects()) {
                amounts.add(p.amount);
            }
            Assert.assertEquals("[100, 499]", amounts.toString());

            c.put("/persons/1", new Person("Anna"));
            c.put("/persons/2", new Person("Bo"));
            c.put("/persons/3", new Person("Ann"));
            c.put("/persons/4", new Person("Annika"));
            database.indexBuilder("by-name").dir("/persons/").type("string").field("name")
                    .start().join();
            List<String> names = new ArrayList<>();
            for (Kv<Person> kv : c.useIndex("by-name", Person.class).prefix("Ann").backward()
                    .kvs()) {
                names.add(kv.key() + "=" + kv.value().name);
            }
            Assert.assertEquals("[/persons/4=Annika, /persons/1=Anna, /persons/3=Ann]",
                    names.toString());
        }
    }

    // ======== Connection ========

    /**
     * Connection.getLookupTime(): Time.MAX by default, t after setLookupTime(t); after
     * freezeLookupTime(), Time.MAX until the next read and the frozen time after it, which
     * another connection can then read at. freezeLookupTime() after setLookupTime(t) freezes
     * the latest state, not t.
     */
    @Nano
    public static void testLookupTimeAndFreeze() {
        try (Database db = Factory.database().memory().start()) {
            Connection c = db.newConnection();
            Assert.assertEquals(Time.MAX, c.getLookupTime());
            Time t1 = c.put("/a.txt", "1").getTime();
            Time t2 = c.put("/a.txt", "2").getTime();
            c.setLookupTime(t1);
            Assert.assertEquals(t1, c.getLookupTime());
            Assert.assertEquals("1", c.get("/a.txt", String.class));

            c.freezeLookupTime();
            Assert.assertEquals(Time.MAX, c.getLookupTime());
            Assert.assertEquals("2", c.get("/a.txt", String.class));
            Time frozen = c.getLookupTime();
            Assert.assertTrue(frozen + " " + t2, frozen.units() >= t2.units());
            Assert.assertTrue(!frozen.equals(Time.MAX));
            c.put("/a.txt", "3");
            Assert.assertEquals("2", c.get("/a.txt", String.class));

            Connection other = db.newConnection();
            other.setLookupTime(frozen);
            Assert.assertEquals("2", other.get("/a.txt", String.class));
        }
    }

    /**
     * Connection.currentTime() and Database.currentTime(): at or after the last completed
     * transaction's time, and before the time of any later transaction.
     */
    @Nano
    public static void testCurrentTime() {
        try (Database db = Factory.database().memory().start()) {
            Connection c = db.connection();
            for (int i = 0; i < 20; i++) {
                Time t1 = c.put("/a.txt", "x" + i).getTime();
                Time now = (i % 2 == 0) ? c.currentTime() : db.currentTime();
                Time t2 = c.put("/b.txt", "y" + i).getTime();
                Assert.assertTrue(t1 + " " + now, t1.units() <= now.units());
                Assert.assertTrue(now + " " + t2, now.units() < t2.units());
            }
        }
    }

    /**
     * Connection.get(key, Object.class): a DbObject for a stored object at an object key (no
     * suffix, or ".obj"), a String at a ".txt" key, else the value's bytes; a byte[] put
     * whose bytes are a stored object, at an object key, is read as one.
     */
    @Nano
    public static void testGetAsObjectByKind() {
        try (Database db = Factory.database().memory().start()) {
            Connection c = db.connection();
            byte[] object = DbObject.toDbObject(new Account("Ann", 1)).getBytes();
            c.put("/k", new Account("Ann", 1));
            c.put("/k.obj", new Account("Bo", 2));
            c.put("/s", "text at an object key");
            c.put("/t.txt", new byte[] {'h', 'i'});
            c.put("/o.bin", object);
            c.put("/b", object);
            c.put("/d/x.", new Account("Cy", 3));
            Assert.assertEquals("Ann", ((DbObject) c.get("/k", Object.class)).getString("owner"));
            Assert.assertEquals("Bo", ((DbObject) c.get("/k.obj", Object.class))
                    .getString("owner"));
            Assert.assertEquals("Cy", ((DbObject) c.get("/d/x.", Object.class))
                    .getString("owner"));
            Assert.assertTrue(c.get("/s", Object.class) instanceof byte[]);
            Assert.assertEquals("hi", c.get("/t.txt", Object.class));
            Assert.assertTrue(c.get("/o.bin", Object.class) instanceof byte[]);
            Assert.assertTrue(c.get("/b", Object.class) instanceof DbObject);
            Assert.assertNull(c.get("/none", Object.class));
        }
    }

    /**
     * Connection.get(): "a primitive, its wrapper or an array class for a value put as one";
     * DbObject.class gives the stored object exactly. RwEnvironment.get() and ReadInterface:
     * the same classes (bergdb 020-19, J3: their Javadoc named Data Object classes only).
     */
    @Nano
    public static void testGetOfPrimitivesAndArrays() {
        try (Database db = Factory.database().memory().start()) {
            Connection c = db.connection();
            c.put("/n", 5);
            c.put("/l", 7L);
            c.put("/arr", new int[] {1, 2});
            c.put("/s", new String[] {"a", "b"});
            Assert.assertEquals(5, (int) c.get("/n", Integer.class));
            Assert.assertEquals(5, (int) c.get("/n", int.class));
            Assert.assertEquals(7L, (long) c.get("/l", Long.class));
            Assert.assertArrayEquals(new int[] {1, 2}, c.get("/arr", int[].class));
            Assert.assertArrayEquals(new String[] {"a", "b"}, c.get("/s", String[].class));
            Assert.assertEquals(5, c.get("/n", DbObject.class).getLong("p"));
            Assert.assertEquals(2, c.get("/arr", DbObject.class).getArray("array").getSize());
            Transaction t = c.rw(env -> {
                env.setOutput("n", env.get("/n", Integer.class));
                env.setOutput("arr", env.get("/arr", int[].class));
            });
            Assert.assertEquals(5, (int) t.getOutput("n", Integer.class));
            Assert.assertArrayEquals(new int[] {1, 2}, t.getOutput("arr", int[].class));
        }
    }

    /**
     * Connection.get(): ObjectCreationException for a class that is not a Data Object, also
     * at a key without a value; for a constructor that throws, with its exception as the
     * cause; for a value that is not a stored object. Connection.usePrimary() and
     * useIndex(): the same for the class, whatever the data.
     */
    @Nano
    public static void testGetRefusesWhatIsNotAnObject() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/s", "a String at an object key");
            c.put("/t/x", new Account("Ann", 1));
            db.indexBuilder("i").dir("/t/").type("long").field("balance").start().join();

            assertThrows("get, no value", ObjectCreationException.class,
                    () -> c.get("/none", NoConstructor.class));
            assertThrows("get of a String", ObjectCreationException.class,
                    () -> c.get("/s", Account.class));
            ObjectCreationException e = assertThrows("get, constructor",
                    ObjectCreationException.class, () -> c.get("/t/x", Throws.class));
            Assert.assertTrue(String.valueOf(e.getCause()),
                    e.getCause() instanceof IllegalStateException);
            assertThrows("usePrimary", ObjectCreationException.class,
                    () -> c.usePrimary(NoConstructor.class));
            assertThrows("useIndex", ObjectCreationException.class,
                    () -> c.useIndex("i", NoConstructor.class));
            assertThrows("useIndex, no index", ObjectCreationException.class,
                    () -> c.useIndex("none", NoConstructor.class));
            assertThrows("useIndex, no index", NoSuchIndexException.class,
                    () -> c.useIndex("none", Account.class));
        }
    }

    /** Connection: a null argument is refused with IllegalArgumentException. */
    @Nano
    public static void testNullArgumentsRefused() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            assertThrows("get(null, )", IllegalArgumentException.class,
                    () -> c.get(null, String.class));
            assertThrows("get(, null)", IllegalArgumentException.class,
                    () -> c.get("/a", null));
            assertThrows("exists(null)", IllegalArgumentException.class, () -> c.exists(null));
            assertThrows("put(null, )", IllegalArgumentException.class, () -> c.put(null, "x"));
            assertThrows("put(, null)", IllegalArgumentException.class, () -> c.put("/a", null));
            assertThrows("delete(null)", IllegalArgumentException.class, () -> c.delete(null));
            assertThrows("useIndex(null, )", IllegalArgumentException.class,
                    () -> c.useIndex(null, Account.class));
            assertThrows("useIndex(, null)", IllegalArgumentException.class,
                    () -> c.useIndex("i", null));
            assertThrows("usePrimary(null)", IllegalArgumentException.class,
                    () -> c.usePrimary(null));
            for (String key : new String[] {"", "a", "/", "/a/", "/a//b", "/a\ud800"}) {
                assertThrows("get " + key, IllegalArgumentException.class,
                        () -> c.get(key, String.class));
                assertThrows("put " + key, IllegalArgumentException.class,
                        () -> c.put(key, "x"));
            }
        }
    }

    /**
     * Connection.put(): an object only at an object key ("Bad key" at another); a String or
     * a byte[] at any key. The suffix follows the name's last '.'; a '.' in a directory's
     * name is not a suffix.
     */
    @Nano
    public static void testObjectKeys() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            for (String key : new String[] {"/a.txt", "/a.bin", "/d/.h", "/a.obj.x"}) {
                IllegalArgumentException e = assertThrows(key, IllegalArgumentException.class,
                        () -> c.put(key, new Account("A", 1)));
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("Bad key"));
                assertThrows(key, IllegalArgumentException.class,
                        () -> c.w().put(key, new Account("A", 1)));
                c.put(key, "a String");
                c.put(key, new byte[] {1});
            }
            for (String key : new String[] {"/a", "/a.obj", "/d/x.", "/v1.2/k"}) {
                c.put(key, new Account("A", 1));
                Assert.assertEquals("A", c.get(key, Account.class).owner);
            }
        }
    }

    /**
     * Connection.transactionInfo(): IllegalStateException before a get() has retrieved a
     * value, also after a get() that finds no entry; an exists() that finds the key counts
     * as a get(). Its KVs are the user's: a delete with value null, a delete of a key without
     * an entry left out, an index's entries left out.
     */
    @Nano
    public static void testTransactionInfo() {
        try (Database db = Factory.database().memory().start()) {
            final Connection c = db.newConnection();
            assertThrows("no get", IllegalStateException.class, () -> c.transactionInfo());
            Assert.assertNull(c.get("/none", String.class));
            assertThrows("a get of no entry", IllegalStateException.class,
                    () -> c.transactionInfo());

            c.put("/x/a.txt", "old");
            db.indexBuilder("i").dir("/x/").type("long").field("balance").start().join();
            Transaction t = c.w().put("/x/a.txt", "new").delete("/x/none").put("/x/k",
                    new Account("A", 5)).delete("/x/a.txt").put("/x/b.txt", "b").execute();
            Assert.assertTrue(c.exists("/x/k"));
            TransactionInfo info = c.transactionInfo();
            Assert.assertEquals(t.getTime(), info.time());
            List<String> kvs = new ArrayList<>();
            for (Kv<byte[]> kv : info.kvs()) {
                kvs.add(kv.key() + "=" + (kv.value() == null ? "null" : "" + kv.value().length));
            }
            Collections.sort(kvs);
            Assert.assertEquals("[/x/a.txt=null, /x/b.txt=1, /x/k="
                    + DbObject.toDbObject(new Account("A", 5)).getBytes().length + "]",
                    kvs.toString());
            Assert.assertNull(c.get("/none", String.class));
            Assert.assertEquals(t.getTime(), c.transactionInfo().time());
        }
    }

    /**
     * IndexBuilder, rule 1, and DataFormatException: a byte[] put of an object of BergDB
     * 2026.3 and before (format 1) in an indexed directory is refused with
     * DataFormatException, by Connection.put(), by WBuilder.execute() (not by its put()) and
     * by Connection.rw(); nothing of the transaction is written, and the database goes on.
     */
    @Nano
    public static void testFormat1PutRefusedInEveryPath() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            final byte[] format1 = {'b', 'e', 'r', 'g', 'o', 1, 0, 0};
            c.put("/u/k", format1);
            db.indexBuilder("i").dir("/i/").type("long").field("balance").start().join();
            assertThrows("put()", DataFormatException.class,
                    () -> c.put("/i/a", format1));
            final WBuilder w = c.w().put("/i/x.txt", "x").put("/i/b", format1);
            assertThrows("execute()", DataFormatException.class, () -> w.execute());
            assertThrows("rw()", DataFormatException.class, () -> c.rw(env -> {
                env.put("/i/y.txt", "y");
                env.put("/i/c", format1);
            }));
            for (String key : new String[] {"/i/a", "/i/b", "/i/c", "/i/x.txt", "/i/y.txt"}) {
                Assert.assertTrue(key, c.get(key, byte[].class) == null);
            }
            c.put("/i/d", new Account("D", 4));
            Assert.assertEquals("D 4", owners(c.useIndex("i", Account.class).objects()));
            Assert.assertArrayEquals(format1, c.get("/u/k", byte[].class));
        }
    }

    /**
     * Database, "Errors": the conversion of a read value to the caller's object is not the
     * database's read; what it throws, an Error too, fails only that call (bergdb 019-40).
     * Connection.get(): a constructor that throws gives ObjectCreationException with its
     * exception as the cause; so do usePrimary()'s and useIndex()'s next(), and a get in an
     * rw-transaction's action, which ends the action; the database goes on.
     */
    @Nano
    public static void testConversionErrorFailsOnlyTheCall() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/t/1", new Account("A", 1));
            db.indexBuilder("i").dir("/t/").type("long").field("balance").start().join();
            Runnable[] calls = {
                () -> c.get("/t/1", ErrorInConstructor.class),
                () -> c.usePrimary(ErrorInConstructor.class).dir("/t/").objects().iterator()
                        .next(),
                () -> c.useIndex("i", ErrorInConstructor.class).objects().iterator().next(),
                () -> c.rw(env -> env.put("/t/2", env.get("/t/1", ErrorInConstructor.class))),
                () -> c.get("/t/1", DbObject.class).toJavaObject(ErrorInConstructor.class),
            };
            for (int i = 0; i < calls.length; i++) {
                ObjectCreationException e = assertThrows("call " + i,
                        ObjectCreationException.class, calls[i]);
                Assert.assertTrue("call " + i + ": " + e.getCause(),
                        e.getCause() instanceof AssertionError);
                c.put("/ok.txt", "call " + i);
            }
            Assert.assertNull(c.get("/t/2", Account.class));
            Assert.assertEquals("call 4", c.get("/ok.txt", String.class));
        }
    }

    /**
     * Connection.put(), WBuilder.execute(), Connection.rw(): a transaction too large is
     * refused with DbException, nothing of it written, and the database goes on (DbException,
     * "A refusal"; bergdb 005-17): its values and keys take more than 7/8 of the record limit
     * in the stream, about 1.88 GB; here the limit is lowered to 1 MB, as the Core's tests
     * lower it.
     */
    @Nano
    public static void testTooLargeRefused() throws Exception {
        java.lang.reflect.Field limit = bergdb.core.StoredTrans.class
                .getDeclaredField("recordLimit");
        limit.setAccessible(true);
        long saved = limit.getLong(null);
        limit.setLong(null, 1000 * 1000);
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            final byte[] big = new byte[900 * 1000];
            Runnable[] calls = {
                () -> c.put("/a.bin", big),
                () -> c.w().put("/b.txt", "b").put("/b.bin", big).execute(),
                () -> c.rw(env -> {
                    env.put("/c.txt", "c");
                    env.put("/c.bin", big);
                }),
            };
            for (int i = 0; i < calls.length; i++) {
                DbException e = assertThrows("call " + i, DbException.class, calls[i]);
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("too large"));
            }
            for (String key : new String[] {"/a.bin", "/b.txt", "/b.bin", "/c.txt", "/c.bin"}) {
                Assert.assertTrue(key, c.get(key, byte[].class) == null);
            }
            c.put("/d.bin", new byte[700 * 1000]);
            Assert.assertEquals(700 * 1000, c.get("/d.bin", byte[].class).length);
        } finally {
            limit.setLong(null, saved);
        }
    }

    /**
     * Database, "Interrupts": an rw() that waits to run again after a conflict, when the
     * thread is interrupted, throws a DbException and is not run; its writes are not made,
     * the flag is set, and the database goes on.
     */
    @Nano
    public static void testRwInterruptedAfterConflict() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            final Connection other = db.newConnection();
            c.put("/x.txt", "0");
            final int[] runs = new int[1];
            DbException e = assertThrows("rw", DbException.class, () -> c.rw(env -> {
                runs[0]++;
                String x = env.get("/x.txt", String.class);
                other.put("/x.txt", x + "+other");
                env.put("/y.txt", "from the action");
                Thread.currentThread().interrupt();
            }));
            Assert.assertTrue("flag", Thread.interrupted());
            Assert.assertEquals(1, runs[0]);
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("not run"));
            Assert.assertNull(c.get("/y.txt", String.class));
            Assert.assertEquals("0+other", c.get("/x.txt", String.class));
            c.rw(env -> env.put("/y.txt", env.get("/x.txt", String.class)));
            Assert.assertEquals("0+other", c.get("/y.txt", String.class));
        } finally {
            Thread.interrupted();
        }
    }

    // ======== Database ========

    /**
     * Database.connection(): the same object for one thread, another for another thread;
     * each call sets its lookup time to Time.MAX, which also ends a freeze.
     * newConnection(): a new object, Time.MAX.
     */
    @Nano
    public static void testConnections() throws InterruptedException {
        try (final Database db = Factory.database().memory().start()) {
            Connection c = db.connection();
            Assert.assertTrue(c == db.connection());
            final Connection[] other = new Connection[1];
            Thread thread = new Thread(() -> other[0] = db.connection());
            thread.start();
            thread.join();
            Assert.assertTrue(other[0] != null && other[0] != c);

            Time t1 = c.put("/a.txt", "1").getTime();
            c.put("/a.txt", "2");
            c.setLookupTime(t1);
            Assert.assertEquals(Time.MAX, db.connection().getLookupTime());
            Assert.assertEquals("2", c.get("/a.txt", String.class));
            c.freezeLookupTime();
            c.get("/a.txt", String.class);
            c.put("/a.txt", "3");
            Assert.assertEquals("2", c.get("/a.txt", String.class));
            Assert.assertTrue(db.connection() == c);
            Assert.assertEquals("3", c.get("/a.txt", String.class));

            Connection n = db.newConnection();
            Assert.assertTrue(n != c && n != db.newConnection() && n != db.connection());
            Assert.assertEquals(Time.MAX, n.getLookupTime());
        }
    }

    /**
     * Database.stop(): no transaction or read starts after it (IllegalDbStateException, as
     * setRetainDuration() says "as a transaction does"); called twice it has no more effect;
     * close() after it works. setRetainDuration() and setStartupDistanceInMb() then throw
     * IllegalDbStateException and change nothing; setCacheSizeInMb() only sets the value
     * (bergdb 020-19, J1: the Javadoc said it had no effect).
     */
    @Nano
    public static void testCallsAfterStop() {
        final Database db = Factory.database().memory().start();
        final Connection c = db.connection();
        c.put("/a.txt", "1");
        db.stop();
        db.stop();
        assertThrows("put", IllegalDbStateException.class, () -> c.put("/b.txt", "x"));
        assertThrows("get", IllegalDbStateException.class, () -> c.get("/a.txt", String.class));
        assertThrows("exists", IllegalDbStateException.class, () -> c.exists("/a.txt"));
        assertThrows("rw", IllegalDbStateException.class, () -> c.rw(env -> env.put("/c.txt",
                "x")));
        assertThrows("setRetainDuration", IllegalDbStateException.class,
                () -> db.setRetainDuration(Duration.seconds(10)));
        Assert.assertEquals(Duration.MAX, db.getRetainDuration());
        int sd = db.getStartupDistanceInMb();
        assertThrows("setStartupDistanceInMb", IllegalDbStateException.class,
                () -> db.setStartupDistanceInMb(sd == 5 ? 6 : 5));
        Assert.assertEquals(sd, db.getStartupDistanceInMb());
        int cache = db.getCacheSizeInMb() == 4 ? 5 : 4;
        db.setCacheSizeInMb(cache);
        Assert.assertEquals(cache, db.getCacheSizeInMb());
        db.close();
        db.close();
    }

    /**
     * Database.getRetainDuration(): Duration.MAX until setRetainDuration() is called, which
     * refuses less than a second; the startup distance is clamped to 5 to 1000 MB, the cache
     * size to 4 to 100,000 MB.
     */
    @Nano
    public static void testSettings() {
        try (final Database db = Factory.database().memory().start()) {
            Assert.assertEquals(Duration.MAX, db.getRetainDuration());
            assertThrows("999 ms", IllegalArgumentException.class,
                    () -> db.setRetainDuration(Duration.seconds(0.999)));
            db.setRetainDuration(Duration.seconds(1));
            Assert.assertEquals(Duration.seconds(1), db.getRetainDuration());
            db.setStartupDistanceInMb(1);
            Assert.assertEquals(5, db.getStartupDistanceInMb());
            db.setStartupDistanceInMb(5000);
            Assert.assertEquals(1000, db.getStartupDistanceInMb());
            db.setCacheSizeInMb(1);
            Assert.assertEquals(4, db.getCacheSizeInMb());
            db.setCacheSizeInMb(Integer.MAX_VALUE);
            Assert.assertEquals(100000, db.getCacheSizeInMb());
        }
    }

    /**
     * DatabaseBuilder: the startup distance is 50 MB by default and clamped to 5 to 1000;
     * the cache size is a fifth of the JVM's maximum heap by default and clamped to 4 to
     * 100,000 (Database's getters give them).
     */
    @Nano
    public static void testBuilderSettings() {
        long max = Runtime.getRuntime().maxMemory();
        int cache = max == Long.MAX_VALUE ? 100 : Math.max(2, (int) (max / 1000000) / 5);
        try (Database db = Factory.database().memory().start()) {
            Assert.assertEquals(50, db.getStartupDistanceInMb());
            Assert.assertEquals(cache, db.getCacheSizeInMb());
        }
        try (Database db = Factory.database().memory().startupDistanceInMb(1).cacheSizeInMb(1)
                .start()) {
            Assert.assertEquals(5, db.getStartupDistanceInMb());
            Assert.assertEquals(4, db.getCacheSizeInMb());
        }
        try (Database db = Factory.database().memory().startupDistanceInMb(5000)
                .cacheSizeInMb(Integer.MAX_VALUE).start()) {
            Assert.assertEquals(1000, db.getStartupDistanceInMb());
            Assert.assertEquals(100000, db.getCacheSizeInMb());
        }
    }

    /**
     * Database.indexBuilder(name): a name of 1 to 255 UTF-8 bytes, without '/', whitespace
     * or a lone surrogate, else IllegalArgumentException; "primary" is a name like any
     * other; whether an index of the name exists is checked at start(), not here.
     */
    @Nano
    public static void testIndexNames() {
        try (final Database db = Factory.database().memory().start()) {
            String[] bad = {null, "", "a/b", "a b", "a\tb", "a b", "a\ud800",
                    "a".repeat(256), "é".repeat(128)};
            for (String name : bad) {
                assertThrows("name " + name, IllegalArgumentException.class,
                        () -> db.indexBuilder(name));
            }
            db.indexBuilder("a".repeat(255));
            db.indexBuilder("é".repeat(127) + "a");
            db.indexBuilder("primary").dir("/p/").type("long").field("x").start().join();
            db.indexBuilder("primary");       // exists: checked at start()
            assertThrows("exists", IndexAlreadyExistsException.class,
                    () -> db.indexBuilder("primary").dir("/q/").type("long").field("x")
                    .start());
            assertThrows("deleteIndex", NoSuchIndexException.class,
                    () -> db.deleteIndex("none"));
            assertThrows("indexJob", NoSuchIndexException.class, () -> db.indexJob("none"));
        }
    }

    /**
     * Database.deleteIndex(): when it returns, the index is gone at every later lookup time
     * and its name is free; a scan at a lookup time when it was active still works, also a
     * builder made before the deletion (Connection.useIndex()), after the cleanup of its
     * entries.
     */
    @Nano
    public static void testDeleteIndexKeepsEarlierScans() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/acc/1", new Account("Ann", 5));
            c.put("/acc/2", new Account("Bo", 3));
            db.indexBuilder("i").dir("/acc/").type("long").field("balance").start().join();
            Time before = c.currentTime();
            UseIndexBuilder<Account> made = c.useIndex("i", Account.class);
            db.deleteIndex("i");
            PubTesterIndexRaces.awaitCleanups(((DatabaseImp) db).getIndexManager());
            assertThrows("deleted", NoSuchIndexException.class,
                    () -> c.useIndex("i", Account.class));
            assertThrows("deleted", NoSuchIndexException.class, () -> db.indexJob("i"));
            assertThrows("deleted twice", NoSuchIndexException.class, () -> db.deleteIndex("i"));
            Assert.assertEquals("Bo 3 Ann 5", owners(made.objects()));
            c.setLookupTime(before);
            Assert.assertEquals("Bo 3 Ann 5", owners(c.useIndex("i", Account.class)
                    .objects()));
            c.setLookupTime(Time.MAX);
            db.indexBuilder("i").dir("/acc/").type("string").field("owner").start().join();
            Assert.assertEquals("Ann 5 Bo 3", owners(c.useIndex("i", Account.class)
                    .objects()));
        }
    }

    /**
     * Connection.useIndex(): every iterator of the builder reads at its time t, also when the
     * index was deleted since t, until the first available lookup time passes t: then the
     * iterator throws LookupTimeNotAvailableException from hasNext() or next(); and a
     * useIndex() at a lookup time before it, a read, throws it too (setLookupTime()).
     */
    @Nano
    public static void testIndexScanBehindCut() {
        TestClock clock = new TestClock();
        Db core = Db.builder().testSetup(new CutStream())
                .clock(clock).maxNodeSize8().startupDistance(2000).build();
        final Database d = DatabaseImp.createAndStart(core);
        try {
            d.setRetainDuration(Duration.seconds(1));
            final Connection c = d.connection();
            long sec = Duration.seconds(1).units();
            long time = sec;
            clock.setTime(Time.units(time));
            WBuilder w = c.w();
            for (int i = 0; i < 150; i++) {
                w.put(String.format("/s/%03d", i), new Account("A", i));
            }
            w.execute();
            d.indexBuilder("i").dir("/s/").type("long").field("balance").start().join();
            final Time t0 = c.currentTime();
            Iterator<Account> it = c.useIndex("i", Account.class).objects().iterator();
            Assert.assertEquals(0, it.next().balance);
            d.deleteIndex("i");
            Assert.assertEquals(1, it.next().balance);

            Random r = new Random(1);
            for (int i = 0; i < 20000 && d.getFirstAvailableLookupTime().units()
                    <= t0.units(); i++) {
                time += sec / 20;
                clock.setTime(Time.units(time));
                c.w().put("/k/" + r.nextInt(50) + ".txt", "v" + i).execute();
            }
            Assert.assertTrue("no cut after the scan's time",
                    d.getFirstAvailableLookupTime().units() > t0.units());
            int n = 2;
            LookupTimeNotAvailableException ex = null;
            try {
                while (it.hasNext()) {
                    it.next();
                    n++;
                }
            } catch (LookupTimeNotAvailableException e) {
                ex = e;
            }
            Assert.assertTrue("a scan behind the cut listed " + n + " values", ex != null);
            c.setLookupTime(t0);
            assertThrows("useIndex() behind the cut",
                    LookupTimeNotAvailableException.class,
                    () -> c.useIndex("i", Account.class));
        } finally {
            d.close();
        }
    }

    // ======== IndexBuilder ========

    /**
     * IndexBuilder: each call is checked at once, in the order given: dir() once, first;
     * type() after dir() and after the level before has its field, at most 8 levels, one of
     * four names; field() and nestedField() once per level, after type(), with their name
     * rules; start() needs a directory and complete levels; the builder is spent after
     * start(), whatever it threw.
     */
    @Nano
    public static void testIndexBuilderChecks() {
        try (final Database db = Factory.database().memory().start()) {
            final IndexBuilder b = db.indexBuilder("i");
            assertThrows("type first", IllegalStateException.class, () -> b.type("long"));
            assertThrows("field first", IllegalStateException.class, () -> b.field("x"));
            assertThrows("dir null", IllegalArgumentException.class, () -> b.dir(null));
            for (String dir : new String[] {"", "a/", "/a", "/a//", "/a\ud800/"}) {
                assertThrows("dir " + dir, IllegalArgumentException.class, () -> b.dir(dir));
            }
            b.dir("/d/");
            assertThrows("dir twice", IllegalStateException.class, () -> b.dir("/e/"));
            assertThrows("field before type", IllegalStateException.class, () -> b.field("x"));
            assertThrows("nestedField before type", IllegalStateException.class,
                    () -> b.nestedField("a.b"));
            assertThrows("start without a level", IllegalStateException.class, () -> b.start());
            assertThrows("spent", IllegalStateException.class, () -> b.type("long"));

            final IndexBuilder b2 = db.indexBuilder("i").dir("/d/");
            for (String type : new String[] {null, "int", "Long", "String", ""}) {
                assertThrows("type " + type, IllegalArgumentException.class,
                        () -> b2.type(type));
            }
            b2.type("long");
            assertThrows("type without field", IllegalStateException.class,
                    () -> b2.type("long"));
            for (String name : new String[] {null, "", "a".repeat(256), "a\udc00"}) {
                assertThrows("field " + name, IllegalArgumentException.class,
                        () -> b2.field(name));
            }
            assertThrows("nestedField null", IllegalArgumentException.class,
                    () -> b2.nestedField((String) null));
            assertThrows("nestedField empty part", IllegalArgumentException.class,
                    () -> b2.nestedField("a..b"));
            assertThrows("nestedField 17 parts", IllegalArgumentException.class,
                    () -> b2.nestedField("a.".repeat(16) + "a"));
            assertThrows("nestedField(null[])", IllegalArgumentException.class,
                    () -> b2.nestedField((String[]) null));
            assertThrows("nestedField(new String[0])", IllegalArgumentException.class,
                    () -> b2.nestedField(new String[0]));
            assertThrows("nestedField([null])", IllegalArgumentException.class,
                    () -> b2.nestedField(new String[] {"a", null}));
            b2.field("a.b");
            assertThrows("field twice", IllegalStateException.class, () -> b2.field("x"));
            assertThrows("nestedField after field", IllegalStateException.class,
                    () -> b2.nestedField("x"));
            for (int i = 2; i <= 8; i++) {
                b2.type("double").nestedField(new String[] {"p.q", "r"});
            }
            assertThrows("a 9th level", IllegalStateException.class, () -> b2.type("long"));
            b2.start().join();
            assertThrows("start twice", IllegalStateException.class, () -> b2.start());

            final IndexBuilder b3 = db.indexBuilder("i").dir("/e/").type("bytes").field("x");
            assertThrows("exists", IndexAlreadyExistsException.class, () -> b3.start());
            assertThrows("spent after a refused start", IllegalStateException.class,
                    () -> b3.type("long"));
            assertThrows("spent after a refused start", IllegalStateException.class,
                    () -> b3.start());
            final IndexBuilder b4 = db.indexBuilder("j").dir("/e/").type("string");
            assertThrows("last level without field", IllegalStateException.class,
                    () -> b4.start());
            db.indexBuilder("j").dir("/e/").type("string").field("a.b").start().join();
        }
    }

    /**
     * IndexBuilder, the index function: an integer for "long" (Java's int, char and long), a
     * double but NaN for "double" (Java's double and float); no kind converted to another;
     * a boolean, an array, an object or an absent field gives no entry; a key with a suffix
     * other than ".obj" gives no entry, a ".obj" key does; a subdirectory's values give none.
     */
    @Nano
    public static void testIndexFunction() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            Kinds k = new Kinds();
            k.i = 1;
            k.ch = 'x';
            k.l = 3;
            k.f = 1.5f;
            k.d = Double.NaN;
            k.s = "s";
            k.bs = new byte[] {1};
            k.arr = new int[] {1};
            c.put("/k/a", k);
            c.put("/k/b.obj", k);
            c.put("/k/c.bin", DbObject.toDbObject(k).getBytes());
            c.put("/k/d", DbObject.toDbObject(k).getBytes());
            c.put("/k/sub/e", k);
            String[][] cases = {
                {"long", "i", "/k/a /k/b.obj /k/d"},
                {"long", "ch", "/k/a /k/b.obj /k/d"},
                {"long", "l", "/k/a /k/b.obj /k/d"},
                {"double", "f", "/k/a /k/b.obj /k/d"},
                {"double", "d", ""},
                {"double", "l", ""},
                {"long", "f", ""},
                {"string", "s", "/k/a /k/b.obj /k/d"},
                {"bytes", "bs", "/k/a /k/b.obj /k/d"},
                {"string", "bs", ""},
                {"bytes", "s", ""},
                {"long", "b", ""},
                {"long", "arr", ""},
                {"long", "absent", ""},
            };
            int n = 0;
            for (String[] x : cases) {
                String name = "i" + n++;
                db.indexBuilder(name).dir("/k/").type(x[0]).field(x[1]).start().join();
                Assert.assertEquals(x[0] + " " + x[1], x[2],
                        keys(c.useIndex(name, DbObject.class).kvs()));
            }
        }
    }

    /**
     * IndexBuilder, the order of a level: "double" by the numbers, -0.0 as 0.0 (one key, so
     * the keys order them), -infinity the least, +infinity the greatest; "string" by code
     * points, not by Java's chars; "bytes" by unsigned bytes. UseIndexBuilder: -0.0 as an
     * argument is 0.0; backward() reverses the keys too.
     */
    @Nano
    public static void testIndexOrder() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            double[] ds = {Double.POSITIVE_INFINITY, 0.0, -1.5, -0.0, Double.NEGATIVE_INFINITY,
                    2.5, -0.0};
            for (int i = 0; i < ds.length; i++) {
                Kinds k = new Kinds();
                k.d = ds[i];
                c.put("/d/" + i, k);
            }
            db.indexBuilder("d").dir("/d/").type("double").field("d").start().join();
            Assert.assertEquals("/d/4 /d/2 /d/1 /d/3 /d/6 /d/5 /d/0",
                    keys(c.useIndex("d", Kinds.class).kvs()));
            Assert.assertEquals("/d/0 /d/5 /d/6 /d/3 /d/1 /d/2 /d/4",
                    keys(c.useIndex("d", Kinds.class).backward().kvs()));
            Assert.assertEquals("/d/1 /d/3 /d/6", keys(c.useIndex("d", Kinds.class).eq(-0.0)
                    .kvs()));
            Assert.assertEquals("/d/1 /d/3 /d/6 /d/5 /d/0", keys(c.useIndex("d", Kinds.class)
                    .from(-0.0, true).kvs()));

            String[] ss = {"😀", "￿", "a", "é"};
            for (int i = 0; i < ss.length; i++) {
                Kinds k = new Kinds();
                k.s = ss[i];
                k.bs = new byte[] {(byte) (0x7e + i)};
                c.put("/s/" + i, k);
            }
            db.indexBuilder("s").dir("/s/").type("string").field("s").start().join();
            Assert.assertEquals("/s/2 /s/3 /s/1 /s/0", keys(c.useIndex("s", Kinds.class)
                    .kvs()));
            Assert.assertEquals("/s/0", keys(c.useIndex("s", Kinds.class).from("￿", false)
                    .kvs()));
            Assert.assertEquals("/s/1", keys(c.useIndex("s", Kinds.class).prefix("￿")
                    .kvs()));
            db.indexBuilder("b").dir("/s/").type("bytes").field("bs").start().join();
            Assert.assertEquals("/s/0 /s/1 /s/2 /s/3", keys(c.useIndex("b", Kinds.class)
                    .kvs()));
            Assert.assertEquals("/s/2 /s/3", keys(c.useIndex("b", Kinds.class)
                    .from(new byte[] {(byte) 0x80}, true).kvs()));
        }
    }

    // ======== UseIndexBuilder ========

    /**
     * UseIndexBuilder's grammar: an argument of another type than the level's, a null, a NaN
     * or a lone surrogate is refused with IllegalArgumentException; a call out of the
     * grammar with IllegalStateException; after objects() or kvs() every other call throws,
     * and they may be called again, each iterator from the beginning; a from() above the
     * to() gives an empty scan.
     */
    @Nano
    public static void testUseIndexGrammar() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            for (int i = 0; i < 4; i++) {
                c.put("/p/" + i, new Payment(i % 2 == 0 ? "a" : "b", i));
            }
            db.indexBuilder("i").dir("/p/").type("string").field("from").type("long")
                    .field("amount").start().join();
            assertThrows("eq(long) on a string level", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).eq(1L));
            assertThrows("eq(double) on a string level", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).eq(1.0));
            assertThrows("eq(byte[]) on a string level", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).eq(new byte[0]));
            assertThrows("eq(null)", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).eq((String) null));
            assertThrows("eq lone surrogate", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).eq("\ud800"));
            assertThrows("prefix lone surrogate", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).prefix("\ud800"));
            assertThrows("from lone surrogate", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).from("a\udc00", true));
            assertThrows("from(null)", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).from((String) null, true));
            assertThrows("to(long) on a string level", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).to(1L, true));
            assertThrows("prefix(byte[]) on a string level", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).prefix(new byte[0]));
            assertThrows("eq after a bound", IllegalStateException.class,
                    () -> c.useIndex("i", Payment.class).from("a", true).eq("a"));
            assertThrows("a second from", IllegalStateException.class,
                    () -> c.useIndex("i", Payment.class).from("a", true).from("b", true));
            assertThrows("a second to", IllegalStateException.class,
                    () -> c.useIndex("i", Payment.class).to("a", true).to("b", true));
            assertThrows("prefix after from", IllegalStateException.class,
                    () -> c.useIndex("i", Payment.class).from("a", true).prefix("b"));
            assertThrows("from after prefix", IllegalStateException.class,
                    () -> c.useIndex("i", Payment.class).prefix("a").from("b", true));
            assertThrows("a second prefix", IllegalStateException.class,
                    () -> c.useIndex("i", Payment.class).prefix("a").prefix("b"));
            assertThrows("a second backward", IllegalStateException.class,
                    () -> c.useIndex("i", Payment.class).backward().backward());
            assertThrows("a level past the index's", IllegalStateException.class,
                    () -> c.useIndex("i", Payment.class).eq("a").eq(1L).eq(1L));
            assertThrows("a bound past the index's levels", IllegalStateException.class,
                    () -> c.useIndex("i", Payment.class).eq("a").eq(1L).from(1L, true));
            assertThrows("NaN", IllegalArgumentException.class,
                    () -> c.useIndex("i", Payment.class).eq("a").from(Double.NaN, true));

            final UseIndexBuilder<Payment> u = c.useIndex("i", Payment.class).eq("a")
                    .from(0, true);
            Iterable<Payment> objects = u.objects();
            assertThrows("after objects()", IllegalStateException.class, () -> u.to(9, true));
            assertThrows("after objects()", IllegalStateException.class, () -> u.backward());
            Assert.assertEquals(2, list(objects).size());
            Assert.assertEquals(2, list(objects).size());
            Assert.assertEquals(2, list(u.kvs()).size());
            Assert.assertEquals(2, list(u.objects()).size());

            Assert.assertEquals("", keys(c.useIndex("i", Payment.class).eq("a").from(3, true)
                    .to(1, true).kvs()));
            Assert.assertEquals("", keys(c.useIndex("i", Payment.class).from("b", false)
                    .to("a", false).kvs()));
            Assert.assertEquals("/p/3", keys(c.useIndex("i", Payment.class).eq("b").eq(3)
                    .backward().kvs()));
            Assert.assertEquals("/p/3 /p/1", keys(c.useIndex("i", Payment.class).eq("b")
                    .backward().kvs()));
        }
    }

    // ======== UsePrimaryBuilder ========

    /**
     * UsePrimaryBuilder: dir() first, once; inclusive(), backward() and startAt() after it,
     * each at most once; startAt() refuses null, an empty name, a '/' and a lone surrogate;
     * objects() and kvs() need dir(), may be called again, and after them every other call
     * throws IllegalStateException.
     */
    @Nano
    public static void testUsePrimaryGrammar() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/d/a.txt", "a");
            c.put("/d/b.txt", "b");
            c.put("/d/c.txt", "c");
            assertThrows("objects() first", IllegalStateException.class,
                    () -> c.usePrimary(String.class).objects());
            assertThrows("kvs() first", IllegalStateException.class,
                    () -> c.usePrimary(String.class).kvs());
            assertThrows("startAt first", IllegalStateException.class,
                    () -> c.usePrimary(String.class).startAt("a"));
            assertThrows("backward first", IllegalStateException.class,
                    () -> c.usePrimary(String.class).backward());
            assertThrows("inclusive first", IllegalStateException.class,
                    () -> c.usePrimary(String.class).inclusive(true));
            assertThrows("dir null", IllegalArgumentException.class,
                    () -> c.usePrimary(String.class).dir(null));
            assertThrows("dir twice", IllegalStateException.class,
                    () -> c.usePrimary(String.class).dir("/d/").dir("/d/"));
            for (String name : new String[] {null, "", "a/b", "a\ud800"}) {
                assertThrows("startAt " + name, IllegalArgumentException.class,
                        () -> c.usePrimary(String.class).dir("/d/").startAt(name));
            }
            assertThrows("startAt twice", IllegalStateException.class,
                    () -> c.usePrimary(String.class).dir("/d/").startAt("a").startAt("b"));
            assertThrows("backward twice", IllegalStateException.class,
                    () -> c.usePrimary(String.class).dir("/d/").backward().backward());
            assertThrows("inclusive twice", IllegalStateException.class,
                    () -> c.usePrimary(String.class).dir("/d/").inclusive(true)
                    .inclusive(true));
            Assert.assertEquals("/d/b.txt /d/a.txt", keys(c.usePrimary(String.class)
                    .dir("/d/").inclusive(true).backward().startAt("b.txt").kvs()));
            Assert.assertEquals("/d/c.txt", keys(c.usePrimary(String.class)
                    .dir("/d/").inclusive(false).startAt("b.txt").kvs()));
            Assert.assertEquals("/d/a.txt /d/b.txt /d/c.txt", keys(c.usePrimary(String.class)
                    .dir("/d/").inclusive(false).kvs()));
            final UsePrimaryBuilder<String> u = c.usePrimary(String.class).dir("/d/");
            Iterable<Kv<String>> kvs = u.kvs();
            assertThrows("after kvs()", IllegalStateException.class, () -> u.backward());
            Assert.assertEquals(3, list(kvs).size());
            Assert.assertEquals(3, list(u.objects()).size());
            Assert.assertEquals(3, list(kvs).size());
        }
    }

    // ======== Job, JobStatus ========

    /**
     * Job: join(millis) returns BUILDING when the time is up; getStatus() is a snapshot;
     * the reason is null unless FAILED; a job of an index that was active at the start
     * (Database.indexJob()) is ACTIVE with count 0 and join() returns at once. While it
     * builds, an index is not scanned (NoSuchIndexException) and its name is taken
     * (IndexAlreadyExistsException).
     */
    @Nano
    public static void testJobStatus() {
        MemoryStream stream = new MemoryStream();
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        Database db = builder.start();
        try {
            Connection c = db.connection();
            for (int i = 0; i < 3; i++) {
                c.put("/acc/" + i, new Account("A", i));
            }
            PubTesterIndexJobs.Gate gate = new PubTesterIndexJobs.Gate();
            ((DatabaseImp) db).getIndexManager().testHook = p -> gate.at(p,
                    IndexManager.BUILD_STEP);
            Job job = db.indexBuilder("i").dir("/acc/").type("long").field("balance").start();
            gate.awaitReached();
            JobStatus building = job.getStatus();
            JobStatus timedOut = job.join(20);
            Assert.assertEquals(JobStatus.State.BUILDING, timedOut.state());
            Assert.assertNull(timedOut.reason());
            Assert.assertTrue(db.indexJob("i") == job);
            final Database d0 = db;
            assertThrows("building", IndexAlreadyExistsException.class,
                    () -> d0.indexBuilder("i").dir("/b/").type("long").field("x").start());
            final Connection c0 = c;
            assertThrows("building", NoSuchIndexException.class,
                    () -> c0.useIndex("i", Account.class));
            gate.open();
            JobStatus active = job.join();
            Assert.assertEquals(JobStatus.State.ACTIVE, active.state());
            Assert.assertEquals(3, active.count());
            Assert.assertNull(active.reason());
            Assert.assertEquals(JobStatus.State.BUILDING, building.state());
            Assert.assertEquals(0, building.count());
            Assert.assertTrue(active.note(), active.note().indexOf('\n') < 0);
            Assert.assertEquals(JobStatus.State.ACTIVE, job.join(0).state());
        } finally {
            ((DatabaseImp) db).getIndexManager().testHook = null;
            db.close();
        }
        builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        db = builder.start();
        try {
            Job job = db.indexJob("i");
            JobStatus s = job.getStatus();
            Assert.assertEquals(JobStatus.State.ACTIVE, s.state());
            Assert.assertEquals(0, s.count());
            Assert.assertEquals(JobStatus.State.ACTIVE, job.join(1).state());
        } finally {
            db.close();
        }
    }

    /**
     * Database, "Interrupts": an interrupt of the calling thread never fails the database;
     * every call but sync(), Job.join() and an rw() that waits after a conflict ignores it
     * until it is done, and the thread's interrupt flag is set when the call returns. A
     * Job's join() returns the status at once, BUILDING while the build goes on.
     */
    @Nano
    public static void testInterruptFlagKept(TestEnvironment env)
            throws Exception {
        String dir = new File(env.createTempDir(), "db").getPath();
        final Database db = Factory.database().create(dir).start();
        try {
            Connection c = db.connection();
            for (int i = 0; i < 3; i++) {
                c.put("/acc/" + i, new Account("A" + i, i));
            }
            List<String> lost = new ArrayList<>();
            Runnable[] calls = {
                () -> c.put("/a.txt", "x"),
                () -> c.get("/a.txt", String.class),
                () -> c.exists("/a.txt"),
                () -> c.delete("/b.txt"),
                () -> c.w().put("/acc/9", new Account("Z", 9)).delete("/acc/9").execute(),
                () -> c.rw(e -> e.put("/c.txt", e.get("/a.txt", String.class))),
                () -> list(c.usePrimary(Account.class).dir("/acc/").objects()),
                () -> db.indexBuilder("i").dir("/acc/").type("long").field("balance").start(),
                () -> {
                    for (int i = 0; i < 1000 && db.indexJob("i").getStatus().state()
                            != JobStatus.State.ACTIVE; i++) {
                        try {
                            Thread.sleep(1);
                        } catch (InterruptedException e) {
                            Thread.currentThread().interrupt();
                        }
                    }
                },
                () -> list(c.useIndex("i", Account.class).objects()),
                () -> db.deleteIndex("i"),
                () -> db.setRetainDuration(Duration.seconds(3600)),
                () -> db.setStartupDistanceInMb(6),
                () -> db.setCacheSizeInMb(10),
                () -> db.currentTime(),
            };
            for (int i = 0; i < calls.length; i++) {
                Thread.currentThread().interrupt();
                calls[i].run();
                if (!Thread.interrupted()) {
                    lost.add("call " + i);
                }
            }
            Assert.assertEquals("[]", lost.toString());
            Assert.assertEquals("A2", list(c.usePrimary(Account.class).dir("/acc/").objects())
                    .get(2).owner);
            Thread.currentThread().interrupt();
            db.close();
            Assert.assertTrue("close() keeps the flag", Thread.interrupted());
        } finally {
            Thread.interrupted();
            db.close();
        }
        Database db2 = Factory.database().open(dir).start();
        try {
            Assert.assertEquals("x", db2.connection().get("/c.txt", String.class));
            Assert.assertEquals(6, db2.getStartupDistanceInMb());
        } finally {
            db2.close();
        }
    }

    /**
     * Connection.freezeLookupTime(): a useIndex() as the first read after it fixes the
     * frozen time; later reads, a get() and another scan, read at it.
     */
    @Nano
    public static void testFreezeByUseIndex() {
        try (final Database db = Factory.database().memory().start()) {
            Connection c = db.newConnection();
            c.put("/acc/1", new Account("Ann", 1));
            db.indexBuilder("i").dir("/acc/").type("long").field("balance").start().join();
            c.freezeLookupTime();
            UseIndexBuilder<Account> u = c.useIndex("i", Account.class);
            Assert.assertTrue(!c.getLookupTime().equals(Time.MAX));
            c.put("/acc/2", new Account("Bo", 2));
            Assert.assertEquals("Ann 1", owners(u.objects()));
            Assert.assertEquals("Ann 1", owners(c.useIndex("i", Account.class).objects()));
            Assert.assertNull(c.get("/acc/2", Account.class));
            Assert.assertEquals(1, list(c.usePrimary(Account.class).dir("/acc/").objects())
                    .size());
        }
    }

    /**
     * Connection.setEnableKeyReplace(): off by default; when on, "${transactionTime}" in the
     * key of a put is replaced, in a w() and in an rw() alike, by a time unique for each
     * transaction; a delete's key is taken as written.
     */
    @Nano
    public static void testKeyReplace() {
        try (final Database db = Factory.database().memory().start()) {
            Connection c = db.newConnection();
            Assert.assertFalse(c.getEnableKeyReplace());
            c.put("/r/${transactionTime}.txt", "literal");
            Assert.assertEquals("literal", c.get("/r/${transactionTime}.txt", String.class));
            c.setEnableKeyReplace(true);
            Assert.assertTrue(c.getEnableKeyReplace());
            c.put("/r/a${transactionTime}.txt", "w");
            c.rw(e -> e.put("/r/a${transactionTime}.txt", "rw"));
            c.delete("/r/${transactionTime}.txt");
            List<String> values = new ArrayList<>();
            List<String> keys = new ArrayList<>();
            for (Kv<String> kv : c.usePrimary(String.class).dir("/r/").kvs()) {
                values.add(kv.value());
                keys.add(kv.key());
            }
            Assert.assertEquals(keys.toString(), "[w, rw]", values.toString());
            Assert.assertFalse(keys.get(0).equals(keys.get(1)));
            Assert.assertFalse(keys.get(0).contains("$"));
        }
    }

    /**
     * IndexBuildException: an index whose build failed over values that it cannot index (here
     * an object of format 1) stays, building; after the values are replaced, the next start
     * builds it, and it is active with every value's entry.
     */
    @Nano
    public static void testReplaceWhatTheBuildCannotIndex() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        try {
            Connection c = db.connection();
            c.put("/p/1", new Person("Ann"));
            c.put("/p/2", PubTester.format1Payment());
            c.put("/p/3", new Person("Cy"));
            final Job job = db.indexBuilder("i").dir("/p/").type("string").field("name")
                    .start();
            IndexBuildException e = assertThrows("join", IndexBuildException.class,
                    () -> job.join());
            Assert.assertTrue(String.valueOf(e.getCause()),
                    e.getCause() instanceof DataFormatException);
            Assert.assertEquals(JobStatus.State.FAILED, job.getStatus().state());
            c.put("/p/2", new Person("Bo"));
            final Connection c0 = c;
            assertThrows("building", NoSuchIndexException.class,
                    () -> c0.useIndex("i", Person.class));
        } finally {
            db.close();
        }
        db = start(stream.copy());
        try {
            Assert.assertEquals(JobStatus.State.ACTIVE, db.indexJob("i").join().state());
            List<String> names = new ArrayList<>();
            for (Person p : db.connection().useIndex("i", Person.class).objects()) {
                names.add(p.name);
            }
            Assert.assertEquals("[Ann, Bo, Cy]", names.toString());
        } finally {
            db.close();
        }
    }

    /**
     * IndexBuilder.field(): a top-level field name, one part, a '.' in it part of the name;
     * nestedField() splits at '.'.
     */
    @Nano
    public static void testFieldNameWithADot() {
        try (final Database db = Factory.database().memory().start()) {
            Connection c = db.connection();
            c.put("/d/flat", new DbObject.Builder().addLong("a.b", 1).build());
            c.put("/d/nested", new DbObject.Builder().addObject("a", new DbObject.Builder()
                    .addLong("b", 2).build()).build());
            db.indexBuilder("flat").dir("/d/").type("long").field("a.b").start().join();
            db.indexBuilder("nested").dir("/d/").type("long").nestedField("a.b").start().join();
            db.indexBuilder("parts").dir("/d/").type("long").nestedField(new String[] {"a.b"})
                    .start().join();
            Assert.assertEquals("/d/flat", keys(c.useIndex("flat", DbObject.class).kvs()));
            Assert.assertEquals("/d/nested", keys(c.useIndex("nested", DbObject.class).kvs()));
            Assert.assertEquals("/d/flat", keys(c.useIndex("parts", DbObject.class).kvs()));
        }
    }

    /**
     * Database, "Interrupts": sync() only waits, and an interrupt ends the wait: it throws a
     * DbException (a StreamIoException whose cause is an InterruptedIOException), the
     * transaction stays committed, and the flag is set. So do Connection.sync() and
     * Transaction.sync(), with or without a level; SyncLevel.NONE does not wait.
     */
    @Nano
    public static void testSyncInterrupted(TestEnvironment env) throws Exception {
        String dir = new File(env.createTempDir(), "db").getPath();
        Database db = Factory.database().create(dir).start();
        try {
            final Database d = db;
            final Connection c = db.connection();
            List<Runnable> syncs = new ArrayList<>();
            for (int i = 0; i < 6; i++) {
                final Transaction t = c.put("/a" + i + ".txt", "v" + i);
                Runnable[] calls = {() -> d.sync(), () -> d.sync(SyncLevel.ORDINARY),
                        () -> c.sync(), () -> c.sync(SyncLevel.ORDINARY), () -> t.sync(),
                        () -> t.sync(SyncLevel.ORDINARY)};
                Thread.currentThread().interrupt();
                DbException e = assertThrows("sync " + i, DbException.class, calls[i]);
                Assert.assertTrue("flag " + i, Thread.interrupted());
                Assert.assertTrue(String.valueOf(e.getCause()),
                        e.getCause() instanceof java.io.InterruptedIOException);
                syncs.add(calls[i]);
            }
            Thread.currentThread().interrupt();
            c.sync(SyncLevel.NONE);
            Assert.assertTrue(Thread.interrupted());
            for (Runnable r : syncs) {
                r.run();
            }
        } finally {
            Thread.interrupted();
            db.close();
        }
        db = Factory.database().open(dir).start();
        try {
            Assert.assertEquals("v5", db.connection().get("/a5.txt", String.class));
        } finally {
            db.close();
        }
    }

    /**
     * Time.resolve()'s grammar: an absolute time with "T" or a space before the time of day;
     * a time of day "HH:MM:SS.d", "HH:MM:SS" or "HH:MM"; a minus time with a time of day.
     * IllegalArgumentException for a time outside Time's range: units(), millis(), add(),
     * and an absolute time string before 1970 or after 2198-05-04 (bergdb 020-19, J7).
     */
    @Nano
    public static void testTimeStrings() {
        final Time now = Time.utc("2020-06-15 12:00");
        Assert.assertEquals(Time.utc("2013-08-19 14:29"), Time.utc("2013-08-19T14:29"));
        Assert.assertEquals(Time.utc("2013-08-19 14:29:10.0"), Time.utc("2013-08-19T14:29:10"));
        Assert.assertEquals(Time.utc("2020-06-15 14:29:10.5"),
                Time.resolve(Time.UTC, now, "14:29:10.5"));
        Assert.assertEquals(Time.utc("2020-06-15 14:29:10"),
                Time.resolve(Time.UTC, now, "14:29:10"));
        Assert.assertEquals(Time.utc("2020-06-13 14:29:10"),
                Time.resolve(Time.UTC, now, "-2 d 14:29:10"));
        Assert.assertEquals(Time.utc("2020-06-15 11:59:58.5"),
                Time.resolve(Time.UTC, now, "-1.5 s"));
        for (final String s : new String[] {"1969-12-31", "2198-05-05", "2300-01-01 00:00"}) {
            assertThrows(s, IllegalArgumentException.class, () -> Time.utc(s));
            assertThrows(s, IllegalArgumentException.class,
                    () -> Time.resolve(Time.UTC, now, s));
        }
        assertThrows("-1 units", IllegalArgumentException.class, () -> Time.units(-1));
        assertThrows("2^56 units", IllegalArgumentException.class, () -> Time.units(1L << 56));
        assertThrows("-1 ms", IllegalArgumentException.class, () -> Time.millis(-1));
        assertThrows("MAX + 1", IllegalArgumentException.class,
                () -> Time.MAX.add(Duration.units(1)));
        assertThrows("MAX + MAX", IllegalArgumentException.class,
                () -> Time.MAX.add(Duration.MAX));
        assertThrows("a minus time before 1970", BadFormatException.class,
                () -> Time.resolve(Time.UTC, now, "-30000 d"));
        assertThrows("bad", BadFormatException.class, () -> Time.utc("2013-1-01"));
        Assert.assertEquals(Time.MAX, Time.units(Time.MAX.units()));
    }

    // ======== DbObject ========

    /**
     * DbObject: every getter and has() refuses a null name with IllegalArgumentException; a
     * name that no field can have (empty, more than 255 bytes, a lone surrogate) is absent.
     */
    @Nano
    public static void testDbObjectNames() {
        final DbObject o = new DbObject.Builder().addLong("a", 1).addString("s", "x").build();
        Runnable[] nulls = {
            () -> o.getBoolean(null), () -> o.getInt((String) null),
            () -> o.getLong((String) null), () -> o.getDouble((String) null),
            () -> o.getString((String) null), () -> o.getByteArray(null),
            () -> o.getArray(null), () -> o.getObject(null), () -> o.getDbValue(null),
            () -> o.getType(null), () -> o.has((String) null, DbObject.LONG),
        };
        for (int i = 0; i < nulls.length; i++) {
            assertThrows("null name, call " + i, IllegalArgumentException.class, nulls[i]);
        }
        for (String name : new String[] {"", "a".repeat(256), "a\ud800", "\udc00"}) {
            Assert.assertEquals('z', o.getType(name));
            Assert.assertEquals(0, o.getLong(name));
            Assert.assertNull(o.getString(name));
            Assert.assertNull(o.getDbValue(name));
            Assert.assertFalse(o.has(name, DbObject.LONG));
            Assert.assertEquals(0, o.getLong(new String[] {name}));
        }
    }

    /**
     * DbObject: the typed getters give the value for a field of their type, else false, 0,
     * 0.0 or null, never a throw; has() and getType() tell absent from another type; INT is
     * an integer within int's range; getType() is LONG for every integer; getDbValue() gives
     * the value of its type.
     */
    @Nano
    public static void testDbObjectGetters() {
        DbObject inner = new DbObject.Builder().addLong("x", 9).build();
        DbObject o = new DbObject.Builder()
                .addDbValue("b", new DbBoolean(true))
                .addInt("i", -5)
                .addLong("big", 1L << 40)
                .addDbValue("d", new DbDouble(2.5))
                .addString("s", "text")
                .addDbValue("bs", new DbByteArray(new byte[] {1, 2}))
                .addArray("a", new DbArray.Builder().add(new DbLong(1)).build())
                .addObject("o", inner)
                .build();
        Assert.assertEquals(8, o.getFieldCount());
        Assert.assertTrue(o.getBoolean("b"));
        Assert.assertEquals(-5, o.getInt("i"));
        Assert.assertEquals(-5, o.getLong("i"));
        Assert.assertEquals(0, o.getInt("big"));
        Assert.assertTrue(o.has("i", DbObject.INT));
        Assert.assertFalse(o.has("big", DbObject.INT));
        Assert.assertTrue(o.has("big", DbObject.LONG));
        Assert.assertEquals(DbObject.LONG, o.getType("i"));
        Assert.assertEquals(2.5, o.getDouble("d"), 0.0);
        Assert.assertEquals(0.0, o.getDouble("i"), 0.0);
        Assert.assertEquals(0, o.getLong("d"));
        Assert.assertNull(o.getString("i"));
        Assert.assertFalse(o.getBoolean("s"));
        Assert.assertNull(o.getByteArray("s"));
        Assert.assertNull(o.getArray("o"));
        Assert.assertNull(o.getObject("a"));
        Assert.assertEquals('z', o.getType("none"));
        Assert.assertFalse(o.has("none", DbObject.LONG));
        Assert.assertFalse(o.has("s", DbObject.LONG));
        char[] types = {DbObject.BOOLEAN, DbObject.LONG, DbObject.LONG, DbObject.DOUBLE,
                DbObject.STRING, DbObject.BYTE_ARRAY, DbObject.ARRAY, DbObject.OBJECT};
        String[] names = {"b", "i", "big", "d", "s", "bs", "a", "o"};
        Class<?>[] classes = {DbBoolean.class, DbLong.class, DbLong.class, DbDouble.class,
                DbString.class, DbByteArray.class, DbArray.class, DbObject.class};
        for (int i = 0; i < names.length; i++) {
            Assert.assertEquals(names[i], types[i], o.getType(names[i]));
            DbValue v = o.getDbValue(names[i]);
            Assert.assertTrue(names[i], classes[i].isInstance(v));
            Assert.assertEquals(types[i], v.getType());
        }
        Assert.assertEquals(9, o.getLong(new String[] {"o", "x"}));
        Assert.assertEquals(0, o.getLong(new String[] {"a", "x"}));
        Assert.assertEquals(0, o.getLong(new String[] {"none", "x"}));
        Assert.assertTrue(o.has(new String[] {"o", "x"}, DbObject.INT));
        byte[] bs = o.getByteArray("bs");
        bs[0] = 7;
        Assert.assertArrayEquals(new byte[] {1, 2}, o.getByteArray("bs"));
    }

    /**
     * DbObject, the bytes: one object has one byte string, the fields in the order of their
     * names' unsigned bytes, so the order of the Builder's adds does not matter; a later add
     * of a name replaces the field; new DbObject(bytes) copies its argument and refuses other
     * bytes with BadFormatException, whose message starts with the condition's code,
     * "format-1" for format 1; getObject() is a view whose getBytes() has the header.
     */
    @Nano
    public static void testDbObjectBytes() {
        DbObject a = new DbObject.Builder().addLong("é", 1).addLong("b", 2)
                .addLong("B", 3).build();
        DbObject b = new DbObject.Builder().addLong("B", 0).addLong("b", 2)
                .addLong("é", 1).addLong("B", 3).build();
        Assert.assertArrayEquals(a.getBytes(), b.getBytes());
        Assert.assertEquals(3, b.getLong("B"));
        Assert.assertEquals(DbObject.HEADER, a.getBytes()[0]);

        byte[] bytes = a.getBytes();
        DbObject c = new DbObject(bytes);
        bytes[bytes.length - 1] = 9;
        Assert.assertEquals(1, c.getLong("é"));
        Assert.assertTrue(c.getBytes() != c.getBytes());

        assertThrows("null", IllegalArgumentException.class, () -> new DbObject(null));
        assertThrows("empty", BadFormatException.class, () -> new DbObject(new byte[0]));
        BadFormatException e = assertThrows("format 1", BadFormatException.class,
                () -> new DbObject(new byte[] {'b', 'e', 'r', 'g', 'o', 1, 0, 0}));
        Assert.assertTrue(e.getMessage(), e.getMessage().startsWith("format-1"));

        DbObject inner = new DbObject.Builder().addString("x", "y").build();
        DbObject outer = new DbObject.Builder().addObject("in", inner).addLong("n", 1).build();
        DbObject view = outer.getObject("in");
        Assert.assertArrayEquals(inner.getBytes(), view.getBytes());
        Assert.assertEquals(inner.getByteSize(), view.getByteSize());
        Assert.assertEquals(inner.getBytes().length - 1, inner.getByteSize());
        byte[] w = new byte[inner.getByteSize() + 2];
        Assert.assertEquals(1 + inner.getByteSize(), inner.write(w, 1));
    }

    /**
     * DbObject.Builder: each add refuses a null, empty, too long or lone-surrogate name, a
     * null value and a 32,768th field; build() refuses more than 16 levels; it may build
     * again. DbArray.Builder: add() refuses null; build() refuses more than 15 levels.
     */
    @Nano
    public static void testBuilders() {
        final DbObject.Builder b = new DbObject.Builder();
        for (String name : new String[] {null, "", "a".repeat(256), "a\ud800"}) {
            assertThrows("name " + name, IllegalArgumentException.class,
                    () -> b.addLong(name, 1));
            assertThrows("name " + name, IllegalArgumentException.class,
                    () -> b.addString(name, "x"));
        }
        assertThrows("null value", IllegalArgumentException.class,
                () -> b.addString("a", null));
        assertThrows("null value", IllegalArgumentException.class,
                () -> b.addObject("a", null));
        assertThrows("null value", IllegalArgumentException.class,
                () -> b.addArray("a", null));
        assertThrows("null value", IllegalArgumentException.class,
                () -> b.addDbValue("a", null));
        for (int i = 0; i < 32767; i++) {
            b.addInt("f" + i, i);
        }
        assertThrows("32,768th field", IllegalArgumentException.class,
                () -> b.addInt("x", 1));
        b.addInt("f0", 5);          // a replace, not a new field
        DbObject o1 = b.build();
        DbObject o2 = b.build();
        Assert.assertEquals(32767, o1.getFieldCount());
        Assert.assertArrayEquals(o1.getBytes(), o2.getBytes());
        Assert.assertEquals(5, o1.getInt("f0"));

        DbObject deep = new DbObject.Builder().build();
        for (int level = 2; level <= 16; level++) {
            deep = new DbObject.Builder().addObject("o", deep).build();
        }
        final DbObject sixteen = deep;
        assertThrows("17 levels", IllegalArgumentException.class,
                () -> new DbObject.Builder().addObject("o", sixteen).build());

        assertThrows("null element", IllegalArgumentException.class,
                () -> new DbArray.Builder().add(null));
        DbArray a = new DbArray.Builder().build();
        for (int level = 2; level <= 15; level++) {
            a = new DbArray.Builder().add(a).build();
        }
        final DbArray fifteen = a;
        assertThrows("16 levels of arrays", IllegalArgumentException.class,
                () -> new DbArray.Builder().add(fifteen).build());
        new DbObject.Builder().addArray("a", fifteen).build();
    }

    /**
     * DbObject.toDbObject(): a DbObject is returned as it is; an array at the top is in the
     * field "array", a primitive or a wrapper in "p"; null refused. toJavaObject(): a
     * primitive class or a wrapper reads "p", an array class "array", null if it is absent;
     * a class that is not a Data Object is refused with ObjectCreationException.
     */
    @Nano
    public static void testDataObjectConversions() {
        final DbObject o = new DbObject.Builder().addLong("x", 1).build();
        Assert.assertTrue(DbObject.toDbObject(o) == o);
        Assert.assertEquals(2, DbObject.toDbObject(new int[] {4, 5}).getArray("array")
                .getSize());
        Assert.assertEquals(7, DbObject.toDbObject(7).getLong("p"));
        Assert.assertEquals(7, DbObject.toDbObject(Integer.valueOf(7)).getLong("p"));
        assertThrows("null", IllegalArgumentException.class, () -> DbObject.toDbObject(null));
        assertThrows("not a Data Object", IllegalArgumentException.class,
                () -> DbObject.toDbObject(new NoConstructor(1)));

        Assert.assertEquals(7, (int) DbObject.toDbObject(7).toJavaObject(Integer.class));
        Assert.assertEquals(7, (int) DbObject.toDbObject(7).toJavaObject(int.class));
        Assert.assertArrayEquals(new int[] {4, 5}, DbObject.toDbObject(new int[] {4, 5})
                .toJavaObject(int[].class));
        Assert.assertNull(o.toJavaObject(Integer.class));
        Assert.assertNull(o.toJavaObject(long.class));
        Assert.assertNull(o.toJavaObject(int[].class));
        assertThrows("not a Data Object", ObjectCreationException.class,
                () -> o.toJavaObject(NoConstructor.class));
        ObjectCreationException e = assertThrows("constructor", ObjectCreationException.class,
                () -> o.toJavaObject(Throws.class));
        Assert.assertTrue(e.getCause() instanceof IllegalStateException);
    }

    /**
     * DbObject, "Strings": a String with a lone surrogate is refused with
     * IllegalArgumentException by toDbObject(), whose message names its place, the field and
     * an array element's index ("inner.names[3]"); by the Builder, in a value and in a name;
     * and by DbString.
     */
    @Nano
    public static void testLoneSurrogateRefusals() {
        Holder h = new Holder();
        h.inner = new Names();
        h.inner.names = new String[] {"a", "b", "c", "x\udc00"};
        IllegalArgumentException e = assertThrows("toDbObject", IllegalArgumentException.class,
                () -> DbObject.toDbObject(h));
        Assert.assertTrue(e.getMessage(), e.getMessage().contains("inner.names[3]"));
        assertThrows("Builder value", IllegalArgumentException.class,
                () -> new DbObject.Builder().addString("s", "a\ud800"));
        assertThrows("Builder name", IllegalArgumentException.class,
                () -> new DbObject.Builder().addLong("n\ud800", 1));
        assertThrows("DbString", IllegalArgumentException.class, () -> new DbString("\ud800"));
        new DbString("\ud83d\ude00");
    }

    /**
     * DbObject.Builder.addObject(): a nested object, also a view that getObject() gave, is
     * copied in at build(); DbArray.Builder.add() of a view likewise.
     */
    @Nano
    public static void testViewsCopiedIn() {
        DbObject inner = new DbObject.Builder().addString("x", "y").addLong("n", 7).build();
        DbObject outer = new DbObject.Builder().addObject("in", inner).addLong("z", 1).build();
        DbObject view = outer.getObject("in");
        DbObject again = new DbObject.Builder().addObject("v", view).build();
        Assert.assertEquals("y", again.getString(new String[] {"v", "x"}));
        Assert.assertEquals(7, again.getLong(new String[] {"v", "n"}));
        Assert.assertArrayEquals(inner.getBytes(), again.getObject("v").getBytes());
        DbArray a = new DbArray.Builder().add(view).add(outer).build();
        Iterator<DbValue> it = a.iterator();
        Assert.assertArrayEquals(inner.getBytes(), ((DbObject) it.next()).getBytes());
        Assert.assertArrayEquals(outer.getBytes(), ((DbObject) it.next()).getBytes());
    }

    /**
     * DbArray.toIntArray(), toLongArray() and toDoubleArray(): each element converted as a get
     * converts a value into a field of the type, best effort (bergdb 020-09, section 5.4): an
     * integer clamped, a double toward zero, a text parsed, a boolean 1 or 0, the rest 0.
     */
    @Nano
    public static void testDbArrayConversions() {
        DbArray a = new DbArray.Builder().add(new DbLong(1L << 40)).add(new DbLong(-(1L << 40)))
                .add(new DbDouble(-2.7)).add(new DbString(" 12 ")).add(new DbBoolean(true))
                .add(new DbByteArray(new byte[] {5})).add(new DbObject.Builder().build())
                .build();
        Assert.assertArrayEquals(new int[] {Integer.MAX_VALUE, Integer.MIN_VALUE, -2, 12, 1, 0,
                0}, a.toIntArray());
        Assert.assertArrayEquals(new long[] {1L << 40, -(1L << 40), -2, 12, 1, 0, 0},
                a.toLongArray());
        Assert.assertArrayEquals(new double[] {1L << 40, -(1L << 40), -2.7, 12, 1, 0, 0},
                a.toDoubleArray());
    }

    // ======== DbArray and the values ========

    /**
     * DbArray: getSize(), its elements in order by the iterator, which refuses remove() and
     * a next() past the end; toIntArray(), toLongArray() and toDoubleArray() give new arrays.
     */
    @Nano
    public static void testDbArray() {
        DbArray a = new DbArray.Builder().add(new DbLong(1)).add(new DbDouble(2.0))
                .add(new DbLong(3)).build();
        Assert.assertEquals(3, a.getSize());
        Assert.assertEquals(DbObject.ARRAY, a.getType());
        Iterator<DbValue> it = a.iterator();
        Assert.assertEquals(1, ((DbLong) it.next()).toLong());
        assertThrows("remove", UnsupportedOperationException.class, () -> it.remove());
        it.next();
        it.next();
        Assert.assertFalse(it.hasNext());
        assertThrows("past the end", NoSuchElementException.class, () -> it.next());
        Assert.assertArrayEquals(new long[] {1, 2, 3}, a.toLongArray());
        Assert.assertArrayEquals(new int[] {1, 2, 3}, a.toIntArray());
        Assert.assertArrayEquals(new double[] {1, 2, 3}, a.toDoubleArray());
        int[] ints = a.toIntArray();
        ints[0] = 9;
        Assert.assertArrayEquals(new int[] {1, 2, 3}, a.toIntArray());
    }

    /**
     * DbValue: write() writes getByteSize() bytes and returns offset + getByteSize(), and
     * throws IndexOutOfBoundsException if 'b' is too small; DbDouble stores every NaN as the
     * one NaN and keeps -0.0; DbLong takes the fewest bytes; DbString and DbByteArray refuse
     * null, DbString a lone surrogate; DbByteArray copies its bytes both ways.
     */
    @Nano
    public static void testValues() {
        DbValue[] values = {new DbBoolean(true), new DbLong(-1), new DbLong(1L << 40),
                new DbDouble(-0.0), new DbString("été"),
                new DbByteArray(new byte[300]), new DbArray.Builder().add(new DbLong(1)).build(),
                new DbObject.Builder().addLong("x", 1).build()};
        for (final DbValue v : values) {
            byte[] b = new byte[v.getByteSize() + 3];
            Assert.assertEquals(v.toString(), 3 + v.getByteSize(), v.write(b, 3));
            final byte[] small = new byte[v.getByteSize() - 1];
            assertThrows("too small " + v, IndexOutOfBoundsException.class,
                    () -> v.write(small, 0));
            final byte[] at = new byte[v.getByteSize()];
            assertThrows("offset " + v, IndexOutOfBoundsException.class,
                    () -> v.write(at, 1));
        }
        Assert.assertEquals(2, new DbLong(-1).getByteSize());
        Assert.assertEquals(9, new DbLong(1L << 40).getByteSize());

        DbObject nan = new DbObject.Builder().addDbValue("n",
                new DbDouble(Double.longBitsToDouble(0x7ff0000000000123L)))
                .addDbValue("z", new DbDouble(-0.0)).build();
        Assert.assertEquals(0x7ff8000000000000L, Double.doubleToRawLongBits(nan.getDouble("n")));
        Assert.assertEquals(0x8000000000000000L, Double.doubleToRawLongBits(nan.getDouble("z")));

        assertThrows("DbString(null)", IllegalArgumentException.class, () -> new DbString(null));
        assertThrows("DbString lone", IllegalArgumentException.class,
                () -> new DbString("a\ud800"));
        assertThrows("DbByteArray(null)", IllegalArgumentException.class,
                () -> new DbByteArray(null));
        byte[] in = {1, 2};
        DbByteArray ba = new DbByteArray(in);
        in[0] = 9;
        Assert.assertArrayEquals(new byte[] {1, 2}, ba.getByteArray());
        Assert.assertEquals("x", new DbString("x").toStringValue());
    }
}
