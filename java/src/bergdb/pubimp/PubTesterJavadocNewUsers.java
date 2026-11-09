package bergdb.pubimp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import bergdb.core.Db;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.DataFormatException;
import bergdb.pub.Database;
import bergdb.pub.DbArray;
import bergdb.pub.DbObject;
import bergdb.pub.Duration;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.TestClock;
import bergdb.pub.Time;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.CutStream;

/**
 * The Pub API's Javadoc and messages against what two new users' applications met (bergdb
 * 020-24-04, a catalogue larger than memory; 020-24-05, a document store). Each test names
 * the finding and the promise it shows.
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
}
