package bergdb.pubimp;

import java.io.File;
import java.io.IOException;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Kv;

/**
 * Long keys through the Pub API (bergdb 021-16; 020-24-05, U5-1 and U5-2), since bergdb 024-24
 * at the limit L2: a key has at most 111 bytes as stored, its UTF-8 and a byte for each part,
 * so each '/' counts two (the package's Limits; 024-17). Until 024-24 a key's length had no
 * limit, and these tests put keys of 100,000 to 1,000,000 chars, and one 20,000 directories
 * deep: a key of about 90 KB or more made the next start throw StackOverflowError, a key of
 * 1,000,000 chars after one of 100,000 with the same start failed the database (021-16).
 * The Core's tests are in bergdb.core.DbTesterLongKeys.
 */
public class PubTesterLongKeys {

    /** Asserts that 'r' throws IllegalArgumentException for L2. */
    private static void refused(String what, Runnable r) {
        try {
            r.run();
        } catch (IllegalArgumentException e) {
            Assert.assertTrue(what + ": " + e.getMessage(),
                    e.getMessage().contains("more than 111 (bergdb 024-17, L2)"));
            return;
        }
        throw new AssertionError(what + ": not refused");
    }

    /**
     * U5-1 at L2: a key of 111 bytes ("/d/", 102 chars and ".txt": "/dd/-" in the ikey), a
     * key 34 directories deep (109 bytes), and one of 54 letters å (two bytes each, 110
     * bytes), put and closed; the database starts again, has the values, and lists the
     * directories. A key one byte longer, of each kind, is refused by put() and delete()
     * with IllegalArgumentException, and nothing is written.
     */
    @Nano
    public static void testLongAndDeepKeysStartAgain(TestEnvironment env) throws IOException {
        final String dir = new File(env.createTempDir(), "db").getPath();
        final String longKey = "/d/" + "k".repeat(102) + ".txt";
        final String deepDir = "/" + "a/".repeat(34);
        final String deepKey = deepDir + "k.txt";
        final String swedish = "/" + "\u00e5".repeat(54);
        final String[] over = {"/d/" + "k".repeat(103) + ".txt", "/" + "a/".repeat(35) + "k.txt",
                "/" + "\u00e5".repeat(55), deepDir + "k234.txt"};

        try (Database db = Factory.database().create(dir).start()) {
            Connection c = db.connection();
            c.put(longKey, "long");
            c.put(deepKey, "deep");
            c.put(swedish, "å");
            for (String k : over) {
                refused("a put at " + k, () -> c.put(k, "x"));
                refused("a delete at " + k, () -> c.delete(k));
                refused("a w() at " + k, () -> c.w().put(k, "x").execute());
                Assert.assertNull(c.get(k, String.class));
            }
        }

        try (Database db = Factory.database().open(dir).start()) {
            Connection c = db.connection();
            Assert.assertEquals("long", c.get(longKey, String.class));
            Assert.assertEquals("deep", c.get(deepKey, String.class));
            Assert.assertEquals("å", c.get(swedish, String.class));
            assertListed(c, "/d/", longKey);
            assertListed(c, deepDir, deepKey);
            c.put(deepDir + "k2.txt", "deep2");
            Assert.assertEquals("deep2", c.get(deepDir + "k2.txt", String.class));
        }
    }

    private static void assertListed(Connection c, String dir, String key) {
        int count = 0;
        for (Kv<String> kv : c.usePrimary(String.class).dir(dir).kvs()) {
            Assert.assertEquals("the key listed in a directory of " + dir.length() + " chars",
                    key, kv.key());
            count++;
        }
        Assert.assertEquals("the keys listed", 1, count);
    }

    /**
     * U5-2 at L2: a put at a key of 111 bytes after one of 59 with the same start; both
     * values are there, and a later call works. (Keys of 100,000 and 1,000,000 chars until
     * bergdb 024-24.)
     */
    @Nano
    public static void testLongKeyAfterItsStart() {
        final String first = "/d/" + "k".repeat(50) + ".txt";
        final String second = "/d/" + "k".repeat(102) + ".txt";
        try (Database db = Factory.database().memory().start()) {
            Connection c = db.connection();
            c.put(first, "first");
            c.put(second, "second");
            Assert.assertEquals("first", c.get(first, String.class));
            Assert.assertEquals("second", c.get(second, String.class));
            Assert.assertNull(c.get("/x.txt", String.class));
        }
    }
}
