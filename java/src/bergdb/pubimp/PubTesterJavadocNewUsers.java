package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import bergdb.core.Db;
import bergdb.core.TestNodeSize;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.DataFormatException;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.DbArray;
import bergdb.pub.DbObject;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.DirectoryInUseException;
import bergdb.stream.MemoryStream;
import bergdb.stream.ReadBelowFirstPosException;

/**
 * The Pub API's Javadoc and messages against what new users' applications met (bergdb
 * 020-24-04, a catalogue larger than memory; 020-24-05, a document store; 020-24-08, a log
 * store where the file system misbehaves; 020-24-10, many small databases opened and closed).
 * Each test names the finding and the promise it shows.
 *
 * @author Frans Lundberg
 */
public class PubTesterJavadocNewUsers {

    // ======== Classes ========

    /** A document. */
    public static class Doc {
        public String title;
        public long n;

        public Doc() {}

        public Doc(String title, long n) {
            this.title = title;
            this.n = n;
        }
    }

    /** U5-3: tags as text, an older version of the class. */
    public static class TagsAsText {
        public String[] tags;
    }

    /** U5-3: a tag as an object. */
    public static class Tag {
        public String name;
    }

    /** U5-3: tags as objects, a newer version of the class. */
    public static class TagsAsObjects {
        public Tag[] tags;
    }

    /** U5-6: a public final field (V3). */
    public static class WithFinal {
        public final long created = 1;
        public long x;
    }

    /** U5-6: a superclass. */
    public static class Base {
        public long x;
    }

    /** U5-6: a field that hides a superclass's field of the same name (V8). */
    public static class Hiding extends Base {
        public long x;
    }

    /** U5-7: one version of a class. */
    public static class First {
        public char grade;
        public byte[] data;
        public boolean flag;
        public String text;
        public long n;
        public String chars;
    }

    /** U5-7: the same fields with other types. */
    public static class Second {
        public String grade;
        public String data;
        public int flag;
        public boolean text;
        public boolean n;
        public char[] chars;
    }

    /** U4-5: an indexed object. */
    public static class Item {
        public long price;

        public Item() {}

        public Item(long price) {
            this.price = price;
        }
    }

    // ======== Tests ========

    /**
     * U5-9 and U5-8 (bergdb 020-24-05): a put of an object at a key with another suffix than
     * ".obj", also ".OBJ", is refused with IllegalArgumentException ("Bad key"), from put(),
     * w() and rw(); the message names the key as the user wrote it and the object keys, and
     * does not call ".obj" obsolete, which the Javadoc documents. It named the key in its
     * internal form ("/dk/-x.OBJ").
     */
    @Nano
    public static void testObjectAtAnotherSuffixNamesTheKey() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            for (final String key : new String[] {"/k/x.OBJ", "/k/x.Obj", "/k/notes.txt"}) {
                List<IllegalArgumentException> es = new ArrayList<>();
                es.add(PubTesterJavadoc.assertThrows("put", IllegalArgumentException.class,
                        () -> c.put(key, new Doc("a", 1))));
                es.add(PubTesterJavadoc.assertThrows("w", IllegalArgumentException.class,
                        () -> c.w().put(key, new Doc("a", 1)).execute()));
                es.add(PubTesterJavadoc.assertThrows("rw", IllegalArgumentException.class,
                        () -> c.rw(env -> env.put(key, new Doc("a", 1)))));
                for (IllegalArgumentException e : es) {
                    String m = e.getMessage();
                    Assert.assertTrue(key + ": " + m, m.startsWith("Bad key"));
                    Assert.assertTrue(key + ": " + m, m.contains("'" + key + "'"));
                    Assert.assertTrue(key + ": " + m, m.contains("\".obj\""));
                    Assert.assertTrue(key + ": " + m, !m.contains("obsolete"));
                    Assert.assertTrue(key + ": " + m, !m.contains("/dk/"));
                }
                Assert.assertNull(c.get(key, byte[].class));
            }
            c.put("/k/x.obj", new Doc("a", 1));
            c.put("/k/x", new Doc("b", 2));
            Assert.assertEquals("a", c.get("/k/x.obj", Doc.class).title);
            Assert.assertEquals("b", c.get("/k/x", Doc.class).title);
        }
    }

    /**
     * U5-8 (bergdb 020-24-05): the suffixes are case-sensitive. A String at "/k/notes.TXT"
     * is read as Object.class as its bytes, at "/k/notes.txt" as a String; an object at
     * "/k/x.OBJ" is refused (testObjectAtAnotherSuffixNamesTheKey).
     */
    @Nano
    public static void testSuffixesAreCaseSensitive() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/k/notes.TXT", "hi");
            c.put("/k/notes.txt", "hi");
            Object upper = c.get("/k/notes.TXT", Object.class);
            Assert.assertTrue("" + upper, upper instanceof byte[]);
            Assert.assertTrue(Arrays.equals(new byte[] {'h', 'i'}, (byte[]) upper));
            Assert.assertEquals("hi", c.get("/k/notes.txt", Object.class));
            Assert.assertEquals("hi", c.get("/k/notes.TXT", String.class));
        }
    }

    /**
     * U5-9 (bergdb 020-24-05): a get as DbObject, or as a Data Object class, of a value that
     * is not a stored object throws ObjectCreationException whose message names the key in
     * a sentence; it ended with " ukey=/g/str".
     */
    @Nano
    public static void testGetOfANonObjectNamesTheKey() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/g/str", "some text");
            c.put("/g/bytes", new byte[] {1, 2, 3});
            for (String key : new String[] {"/g/str", "/g/bytes"}) {
                for (Class<?> type : new Class<?>[] {DbObject.class, Doc.class}) {
                    ObjectCreationException e = PubTesterJavadoc.assertThrows(key,
                            ObjectCreationException.class, () -> c.get(key, type));
                    String m = e.getMessage();
                    Assert.assertTrue(key + ": " + m, m.startsWith("The value at " + key
                            + " cannot be read as an object: "));
                    Assert.assertTrue(key + ": " + m, !m.contains("ukey="));
                }
            }
        }
    }

    /**
     * U5-9 (bergdb 020-24-05): a get as String of a stored object throws
     * DataFormatException, as before, and its message says that the value is an object, not
     * only that it is not well-formed UTF-8. A byte[] that is not UTF-8 keeps the message
     * of bergdb 021-06.
     */
    @Nano
    public static void testGetAsStringOfAnObject() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/g/n", 42);
            c.put("/g/doc", new Doc("a", 1));
            for (String key : new String[] {"/g/n", "/g/doc"}) {
                DataFormatException e = PubTesterJavadoc.assertThrows(key,
                        DataFormatException.class, () -> c.get(key, String.class));
                Assert.assertTrue(key + ": " + e.getMessage(), e.getMessage().startsWith(
                        "The value at " + key + " is an object, not a String"));
            }
            c.put("/g/b.bin", new byte[] {(byte) 0xff});
            DataFormatException e = PubTesterJavadoc.assertThrows("bin",
                    DataFormatException.class, () -> c.get("/g/b.bin", String.class));
            Assert.assertTrue(e.getMessage(), e.getMessage().startsWith(
                    "The value at /g/b.bin is not well-formed UTF-8"));
        }
    }

    /**
     * U5-3 (bergdb 020-24-05; 020-09, section 5.7): a get by another version's class may
     * give an array with null elements, an element that has no sensible conversion; a put
     * of the object back is refused, naming the element, until they are set.
     */
    @Nano
    public static void testGetMayGiveNullElementsThatAPutRefuses() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            TagsAsText text = new TagsAsText();
            text.tags = new String[] {"x", "y"};
            c.put("/m/a", text);
            final TagsAsObjects objects = c.get("/m/a", TagsAsObjects.class);
            Assert.assertEquals(2, objects.tags.length);
            Assert.assertNull(objects.tags[0]);
            Assert.assertNull(objects.tags[1]);
            IllegalArgumentException e = PubTesterJavadoc.assertThrows("put back",
                    IllegalArgumentException.class, () -> c.put("/m/a", objects));
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("tags[0]"));
            Assert.assertEquals("x", c.get("/m/a", TagsAsText.class).tags[0]);

            Tag t = new Tag();
            t.name = "x";
            TagsAsObjects o = new TagsAsObjects();
            o.tags = new Tag[] {t};
            c.put("/m/b", o);
            final TagsAsText back = c.get("/m/b", TagsAsText.class);
            Assert.assertEquals(1, back.tags.length);
            Assert.assertNull(back.tags[0]);
            PubTesterJavadoc.assertThrows("put back", IllegalArgumentException.class,
                    () -> c.put("/m/b", back));
            back.tags[0] = "x";
            c.put("/m/b", back);
            Assert.assertEquals("x", c.get("/m/b", TagsAsText.class).tags[0]);
        }
    }

    /**
     * U5-6 (bergdb 020-24-05; 020-09, V3 and V8): a public final field, and a field that
     * hides a superclass's field of the same name, make a class not a Data Object: a put
     * refuses it with IllegalArgumentException, a get with ObjectCreationException, also at
     * a key without a value.
     */
    @Nano
    public static void testFinalAndHidingFieldsAreRefused() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            IllegalArgumentException e = PubTesterJavadoc.assertThrows("final",
                    IllegalArgumentException.class, () -> c.put("/v/f", new WithFinal()));
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("'created' is final"));
            e = PubTesterJavadoc.assertThrows("hiding", IllegalArgumentException.class,
                    () -> c.put("/v/h", new Hiding()));
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("named 'x'"));
            PubTesterJavadoc.assertThrows("final", ObjectCreationException.class,
                    () -> c.get("/v/f", WithFinal.class));
            PubTesterJavadoc.assertThrows("hiding", ObjectCreationException.class,
                    () -> c.get("/v/h", Hiding.class));
            Assert.assertNull(c.get("/v/f", byte[].class));
            Assert.assertNull(c.get("/v/h", byte[].class));
        }
    }

    /**
     * U5-7 (bergdb 020-24-05; 020-09, sections 5.4 to 5.6): the conversions that the
     * package's "Objects" names. A char is stored as an integer, its code: into a String
     * it reads as its number, "65" for 'A', and a String into a char is read as a number,
     * "66" as 'B' and "B" as 0. Bytes into a String are decoded as UTF-8, a String into a
     * byte[] gives its UTF-8 bytes. A boolean into a number is 1 or 0, into a String "true"
     * or "false"; a number into a boolean is true if it is not 0; a String into a boolean is
     * true only for "true", in any case. A String into a char[] is null.
     */
    @Nano
    public static void testConversionsOfTheJavadoc() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            First f = new First();
            f.grade = 'A';
            f.data = new byte[] {104, 105, (byte) 0xff};
            f.flag = true;
            f.text = "yes";
            f.n = 7;
            f.chars = "ab";
            c.put("/c/1", f);
            Second s = c.get("/c/1", Second.class);
            Assert.assertEquals("65", s.grade);
            Assert.assertEquals("hi�", s.data);
            Assert.assertEquals(1, s.flag);
            Assert.assertEquals(false, s.text);
            Assert.assertEquals(true, s.n);
            Assert.assertNull(s.chars);
            First back = c.get("/c/1", First.class);
            Assert.assertEquals('A', back.grade);

            Second t = new Second();
            t.grade = "66";
            t.data = "hé";
            t.flag = 0;
            t.text = true;
            t.n = true;
            t.chars = new char[] {'a'};
            c.put("/c/2", t);
            First g = c.get("/c/2", First.class);
            Assert.assertEquals('B', g.grade);
            Assert.assertTrue(Arrays.equals("hé".getBytes(java.nio.charset.StandardCharsets.UTF_8),
                    g.data));
            Assert.assertEquals(false, g.flag);
            Assert.assertEquals("true", g.text);
            Assert.assertEquals(1, g.n);
            Assert.assertNull(g.chars);
            t.grade = "B";
            c.put("/c/3", t);
            Assert.assertEquals('\u0000', c.get("/c/3", First.class).grade);
            t.text = false;
            c.put("/c/4", t);
            Assert.assertEquals("false", c.get("/c/4", First.class).text);
            f.text = "TRUE";
            c.put("/c/5", f);
            Assert.assertEquals(true, c.get("/c/5", Second.class).text);
        }
    }

    /**
     * U5-10 (bergdb 020-24-05): DbObject.toString() gives "o", not the fields, and a DbArray
     * "a:" and its size; DbObject has no equals() of its own: two objects of equal bytes are
     * not equal(), and a Set holds both; getBytes() compared with Arrays.equals() compares
     * them.
     */
    @Nano
    public static void testDbObjectToStringAndEquals() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            c.put("/o/a", new Doc("a", 1));
            DbObject x = c.get("/o/a", DbObject.class);
            DbObject y = c.get("/o/a", DbObject.class);
            Assert.assertEquals("o", x.toString());
            Assert.assertTrue(!x.equals(y));
            Assert.assertTrue(Arrays.equals(x.getBytes(), y.getBytes()));
            Assert.assertEquals(Arrays.hashCode(x.getBytes()), Arrays.hashCode(y.getBytes()));
            Set<DbObject> set = new HashSet<>();
            set.add(x);
            set.add(y);
            Assert.assertEquals(2, set.size());
            c.put("/o/arr", new long[] {1, 2});
            DbArray arr = c.get("/o/arr", DbObject.class).getArray("array");
            Assert.assertEquals("a:2", arr.toString());
            Assert.assertEquals("a", x.getDbValue("title").toString());
            Assert.assertEquals("1", x.getDbValue("n").toString());
            Assert.assertEquals("b:3", new bergdb.pub.DbByteArray(new byte[3]).toString());
            Assert.assertEquals("d:2.5", new bergdb.pub.DbDouble(2.5).toString());
            Assert.assertEquals("true", new bergdb.pub.DbBoolean(true).toString());
        }
    }

    /**
     * U5-11 (bergdb 020-24-05): the versions of a key, newest first, by a walk: a get,
     * transactionInfo().time() t, then a get at t less one unit, until a get finds no value,
     * at the key's first put or at a delete; the delete's time is not given, so the walk
     * does not pass it, but a get at a lookup time before the delete does.
     */
    @Nano
    public static void testVersionsOfAKeyByAWalk() {
        try (final Database db = Factory.database().memory().start()) {
            final Connection c = db.connection();
            long t1 = c.put("/w/k", new Doc("v1", 1)).getTime().units();
            long t2 = c.put("/w/k", new Doc("v2", 2)).getTime().units();
            c.put("/w/other", new Doc("x", 0));
            long t3 = c.delete("/w/k").getTime().units();
            long t4 = c.put("/w/k", new Doc("v3", 3)).getTime().units();
            long t5 = c.put("/w/k", new Doc("v4", 4)).getTime().units();
            Connection h = db.newConnection();
            Assert.assertEquals("v4@" + t5 + " v3@" + t4, walk(h, "/w/k", Time.MAX));
            Assert.assertEquals("v2@" + t2 + " v1@" + t1, walk(h, "/w/k", Time.units(t3 - 1)));
        }
    }

    /** The versions of 'key' from the lookup time 'from' back: each title and its time. */
    private static String walk(Connection h, String key, Time from) {
        StringBuilder sb = new StringBuilder();
        Time at = from;
        while (true) {
            h.setLookupTime(at);
            Doc doc = h.get(key, Doc.class);
            if (doc == null) {
                return sb.toString();
            }
            Time t = h.transactionInfo().time();
            sb.append(sb.length() == 0 ? "" : " ").append(doc.title).append('@')
                    .append(t.units());
            at = Time.units(t.units() - 1);
        }
    }

    /**
     * U4-5 (bergdb 020-24-04): an iterator of a scan holds nothing to release, and has no
     * close(): many iterators of a primary scan and of an index scan, read in part and then
     * dropped or kept, do not hold reclaim back. Reclaim cuts past their lookup time, and a
     * kept one throws LookupTimeNotAvailableException when it reads again, before its end
     * (UsePrimaryBuilder, UseIndexBuilder).
     */
    @Nano
    public static void testDroppedIteratorsHoldNothing() {
        TestClock clock = new TestClock();
        Db db = TestNodeSize.builder(8).testSetup(new CutStream()).clock(clock)
                .startupDistance(2000).build();
        Database d = DatabaseImp.createAndStart(db);
        try {
            Connection c = d.connection();
            long ms = Duration.seconds(0.001).units();
            long time = Duration.seconds(1).units();
            clock.setTime(Time.units(time));
            d.indexBuilder("by-price").dir("/i/").type("long").field("price").start().join();
            for (int i = 0; i < 150; i++) {
                c.put("/i/" + (1000 + i), new Item(i));
            }
            d.setRetainDuration(Duration.seconds(1));
            Time scanTime = c.currentTime();
            List<Iterator<Kv<Item>>> kept = new ArrayList<>();
            for (int i = 0; i < 400; i++) {
                Iterator<Kv<Item>> it = i % 2 == 0
                        ? c.usePrimary(Item.class).dir("/i/").kvs().iterator()
                        : c.useIndex("by-price", Item.class).kvs().iterator();
                Assert.assertEquals(1000L, Long.parseLong(it.next().key().substring(3)));
                if (i < 2) {
                    kept.add(it);       // Others are dropped.
                }
            }
            int puts = 0;
            while (d.getFirstAvailableLookupTime().units() <= scanTime.units()) {
                Assert.assertTrue("no cut after " + puts + " puts", puts < 20000);
                time += 10 * ms;
                clock.setTime(Time.units(time));
                c.put("/other/" + (puts % 50) + ".txt", "v" + puts);
                puts++;
            }
            for (Iterator<Kv<Item>> it : kept) {
                final Iterator<Kv<Item>> fit = it;
                PubTesterJavadoc.assertThrows("kept", LookupTimeNotAvailableException.class,
                        () -> {
                            for (int i = 0; i < 149; i++) {
                                fit.next();
                            }
                        });
            }
        } finally {
            d.close();
        }
    }

    // ======== 020-24-08, a log store where the file system misbehaves ========

    /**
     * U8-2 (bergdb 020-24-08): a start whose read fails on the storage, here as the first
     * stream file was deleted, throws the storage's exception, a StreamIoException whose
     * cause is a ReadBelowFirstPosException, as DatabaseBuilder.start() says. It threw a
     * DbFailedException, "A read failed on the storage (the cause). The database takes no
     * more transactions or reads and must be restarted.": the index manager's first scan,
     * after the Db's start, failed the database that was starting.
     */
    @Nano
    public static void testStartWithTheFirstFileDeleted(TestEnvironment env) throws IOException {
        File dir = env.createTempDir();
        try (Database d = Factory.database().create(dir.getPath()).startupDistanceInMb(5)
                .start()) {
            Connection c = d.connection();
            for (int i = 0; i < 2000; i++) {      // 1500 showed it; 1000 did not.
                c.put(String.format("/log/%012d.bin", i), new byte[1000]);
            }
        }
        Assert.assertTrue("deleted", new File(dir, "00000000000000.bergdb").delete());
        for (int i = 0; i < 2; i++) {      // The second: the first closed what it opened.
            StreamIoException e = PubTesterJavadoc.assertThrows("start " + i,
                    StreamIoException.class,
                    () -> Factory.database().open(dir.getPath()).start());
            Assert.assertTrue(e.toString(), e.getCause() instanceof ReadBelowFirstPosException);
        }
    }

    /**
     * U8-2 (bergdb 020-24-08): a start during which the storage fails, as a write of the
     * start's own on a full disk, throws the storage's StreamIoException, as
     * DatabaseBuilder.start() says. It threw a DbFailedException, "Cannot call getOne(): the
     * database failed (the cause) and must be restarted.", which named a call that the
     * application did not make. Here a hook right after the Db's start fails a sync on a
     * stream whose appends fail, and the index manager's scan, the start's next read, meets
     * the failure ("Cannot call getMany()").
     */
    @Nano
    public static void testStartOnAFailedStorage() {
        final FailingStream s = new FailingStream();
        DatabaseImp.testHookAfterStart = db -> {
            s.failAppends = true;
            db.execute(db.trans().put("/a", "a0").build());
            try {
                db.sync(SyncLevel.ORDINARY);
                throw new AssertionError("synced");
            } catch (DbFailedException e) {
                // Expected: the storage failed, and the database with it.
            }
        };
        try {
            StreamIoException e = PubTesterJavadoc.assertThrows("start",
                    StreamIoException.class,
                    () -> ((DatabaseBuilderImp) Factory.database()).mainStream(s).start());
            Throwable root = e;
            while (root.getCause() != null) {
                root = root.getCause();
            }
            Assert.assertEquals(FailingStream.MESSAGE, root.getMessage());
        } finally {
            DatabaseImp.testHookAfterStart = null;
        }
        Assert.assertTrue("closed", s.closed);
    }

    /** A MemoryStream whose appends fail while failAppends is set, as on a full disk. */
    static final class FailingStream implements AppendOnlyStream {
        static final String MESSAGE = "FailingStream: no space left, as set";
        final MemoryStream inner = new MemoryStream();
        volatile boolean failAppends = false;
        volatile boolean closed = false;

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
            if (failAppends) {
                throw new IOException(MESSAGE);
            }
            inner.append(source, sourceOffset, length);
        }

        public void pretruncate(long position) throws IOException {
            inner.pretruncate(position);
        }

        public void close() throws IOException {
            inner.close();
            closed = true;
        }
    }

    /**
     * U8-11 (bergdb 020-24-08): create() of a path that is a regular file is refused with a
     * StreamIoException that names the path; it said "Not a directory", without the path.
     * The file is left as it was.
     */
    @Nano
    public static void testCreateOnAFileNamesThePath(TestEnvironment env) throws IOException {
        final File file = new File(env.createTempDir(), "file");
        Files.write(file.toPath(), new byte[] {1, 2, 3});
        StreamIoException e = PubTesterJavadoc.assertThrows("create", StreamIoException.class,
                () -> Factory.database().create(file.getPath()).start());
        Assert.assertTrue(e.getMessage(), e.getMessage().contains(file.getPath()));
        Assert.assertEquals(3L, file.length());
    }

    /**
     * U10-1 (bergdb 020-24-10; 021-20): a database's directory deleted right after stop(),
     * while the database still writes in the background, and a new database created at the
     * path. The start is refused as in use until the old database has closed, as stop()
     * says, and then taken; the old database writes nothing into the new directory. The
     * start threw StreamFormatException ("The meta block at 200000 names the last
     * transaction at ...") or was taken: the old database's close made its next stream files
     * by name in the new directory.
     */
    @Nano
    public static void testNewDatabaseWhereAStoppedOneWasDeleted(TestEnvironment env)
            throws Exception {
        File dir = new File(env.createTempDir(), "doc");
        Database old = Factory.database().create(dir.getPath()).start();
        try {
            for (int i = 0; i < 50; i++) {      // 1 MB, still in the write buffer.
                old.connection().put("/big" + i + ".bin", new byte[20_000]);
            }
            old.stop();
            deleteTree(dir);
            try (Database db = startRetried(dir)) {
                db.connection().put("/new.txt", "new");
                db.sync();
            }
        } finally {
            try {
                old.close();
            } catch (StreamIoException e) {
                // Expected when its close had a new file to make: the directory was gone.
            }
        }
        try (Database again = Factory.database().open(dir.getPath()).start()) {
            Assert.assertEquals("new", again.connection().get("/new.txt", String.class));
            Assert.assertFalse("old", again.connection().exists("/big0.bin"));
        }
    }

    /**
     * U10-1 (bergdb 020-24-10; 021-20): a database's directory deleted while the database
     * runs. A start of a new database at the path is refused as in use while the old one is
     * open, and the old one fails at its next stream file instead of making it in the
     * directory now at the path. Once it is closed, a new database at the path starts and
     * keeps its data. The start was taken, and the old database went on and wrote its next
     * files into the new directory: the new database's synced value was lost, and its next
     * start failed ("Bad size of file .../00000000000000.bergdb").
     */
    @Nano
    public static void testDirectoryDeletedWhileTheDatabaseRuns(TestEnvironment env)
            throws Exception {
        File dir = new File(env.createTempDir(), "doc");
        Database old = Factory.database().create(dir.getPath()).start();
        try {
            Connection c = old.connection();
            for (int i = 0; i < 50; i++) {
                c.put("/big" + i + ".bin", new byte[20_000]);
            }
            old.sync();
            deleteTree(dir);
            StreamIoException e = PubTesterJavadoc.assertThrows("start", StreamIoException.class,
                    () -> Factory.database().create(dir.getPath()).start());
            Assert.assertTrue(e.toString(), e.getCause() instanceof DirectoryInUseException);
            DbFailedException f = PubTesterJavadoc.assertThrows("the old database",
                    DbFailedException.class, () -> {
                        for (int i = 0; i < 500; i++) {     // Up to 10 MB: a new file.
                            c.put("/more" + i + ".bin", new byte[20_000]);
                            if (i % 50 == 49) {
                                old.sync();
                            }
                        }
                    });
            Assert.assertTrue(f.toString(), causes(f).contains("is no longer"));
        } finally {
            old.close();
        }
        try (Database db = Factory.database().create(dir.getPath()).start()) {
            db.connection().put("/new.txt", "new");
        }
        try (Database again = Factory.database().open(dir.getPath()).start()) {
            Assert.assertEquals("new", again.connection().get("/new.txt", String.class));
            Assert.assertFalse("old", again.connection().exists("/big0.bin"));
        }
    }

    /** A start of create(dir), again while it is refused as in use, for up to 10 s. */
    private static Database startRetried(File dir) throws InterruptedException {
        long end = System.nanoTime() + 10_000_000_000L;
        while (true) {
            try {
                return Factory.database().create(dir.getPath()).start();
            } catch (StreamIoException e) {
                if (!(e.getCause() instanceof DirectoryInUseException)
                        || System.nanoTime() > end) {
                    throw e;
                }
                Thread.sleep(5);
            }
        }
    }

    /** Deletes 'dir' and everything in it; again if a file was added meanwhile. */
    private static void deleteTree(File dir) throws IOException {
        for (int attempt = 0; ; attempt++) {
            try (java.util.stream.Stream<Path> paths = Files.walk(dir.toPath())) {
                for (Path p : paths.sorted(Comparator.reverseOrder()).toArray(Path[]::new)) {
                    Files.deleteIfExists(p);
                }
                return;
            } catch (java.nio.file.DirectoryNotEmptyException e) {
                if (attempt == 100) {
                    throw e;
                }
            }
        }
    }

    /** The messages of 'e' and its causes, as one text. */
    private static String causes(Throwable e) {
        StringBuilder sb = new StringBuilder();
        for (Throwable t = e; t != null; t = t.getCause()) {
            sb.append(t).append("; ");
        }
        return sb.toString();
    }

    /**
     * U10-3 (bergdb 020-24-10): a closed Database that the application still references
     * holds little heap: its write buffer, 10 MB, is released at the close, also after
     * stop(). It held it until the object was dropped: 11 MB for each, 331 MB for 30.
     */
    @Nano
    public static void testClosedDatabasesHoldLittleHeap(TestEnvironment env) throws Exception {
        File root = env.createTempDir();
        List<Database> kept = new ArrayList<Database>();
        long before = heapAfterGc();
        for (int i = 0; i < 10; i++) {
            DatabaseBuilder b = Factory.database();
            if (i % 3 == 2) {
                b.memory();
            } else {
                b.create(new File(root, "d" + i).getPath());
            }
            Database d = b.startupDistanceInMb(5).start();
            d.connection().put("/a.txt", "a");
            if (i % 2 == 0) {
                d.close();
            } else {
                d.stop();
            }
            kept.add(d);
        }
        for (Database d : kept) {
            try {
                d.close();      // Waits for the stopped ones; the others return.
            } catch (DbException e) {
                throw new AssertionError(e);
            }
        }
        long grown = heapAfterGc() - before;
        Assert.assertTrue("heap grew by " + grown / 1000 + " KB for " + kept.size()
                + " closed databases", grown < 30_000_000L);   // 110 MB before.
        kept.clear();
    }

    private static long heapAfterGc() throws InterruptedException {
        Runtime r = Runtime.getRuntime();
        for (int i = 0; i < 3; i++) {
            // Runtime.gc(), not System.gc(): on Android (ART) System.gc() starts no collection
            // unless finalization ran before it (bergdb 024-38, android-finding.md; 006-18-03).
            Runtime.getRuntime().gc();
            Thread.sleep(20);
        }
        return r.totalMemory() - r.freeMemory();
    }

    /**
     * U10-6 (bergdb 020-24-10): sync() after close() returns, from the Database and from a
     * Connection, as its Javadoc says when the transaction is durable: close() wrote and
     * forced it. Also after stop() once the close is done, and for a transaction that no
     * sync() preceded. It threw StreamIoException, "StorageManager has error: Storage is
     * closing.".
     */
    @Nano
    public static void testSyncAfterClose(TestEnvironment env) throws Exception {
        File root = env.createTempDir();
        for (int i = 0; i < 4; i++) {
            Database d = Factory.database().create(new File(root, "d" + i).getPath()).start();
            Connection c = d.connection();
            c.put("/a.txt", "a");
            if (i % 2 == 0) {
                d.sync();
            }
            if (i < 2) {
                d.close();
            } else {
                d.stop();
                d.close();      // Waits for the stop's close.
            }
            d.sync();
            c.sync();
            d.sync(SyncLevel.ORDINARY);
        }
    }
}
