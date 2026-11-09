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
 * Long keys through the Pub API (bergdb 021-16; 020-24-05, U5-1 and U5-2): a key's length
 * has no limit, and a key of about 90 KB or more made the next start throw
 * StackOverflowError, a key of 1,000,000 chars after one of 100,000 with the same start
 * failed the database. Each test runs with the thread's default stack, and failed before
 * 021-16. The Core's tests are in bergdb.core.DbTesterLongKeys.
 */
public class PubTesterLongKeys {

    /**
     * U5-1: a key of 200,007 chars and a key 20,000 directories deep (120,006 chars), put
     * and closed; the database starts again, has both values, and lists both directories.
     */
    @Nano
    public static void testLongAndDeepKeysStartAgain(TestEnvironment env) throws IOException {
        final String dir = new File(env.createTempDir(), "db").getPath();
        final String longKey = "/d/" + "k".repeat(200 * 1000) + ".txt";
        final String deepDir = "/" + "dir-x/".repeat(20 * 1000);
        final String deepKey = deepDir + "k.txt";

        try (Database db = Factory.database().create(dir).start()) {
            Connection c = db.connection();
            c.put(longKey, "long");
            c.put(deepKey, "deep");
        }

        try (Database db = Factory.database().open(dir).start()) {
            Connection c = db.connection();
            Assert.assertEquals("long", c.get(longKey, String.class));
            Assert.assertEquals("deep", c.get(deepKey, String.class));
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
     * U5-2: a put at a key of 1,000,000 chars after one of 100,000 with the same start threw
     * StackOverflowError and failed the database. Now both values are there, and a later
     * call works.
     */
    @Nano
    public static void testLongKeyAfterItsStart() {
        final String first = "/d/" + "k".repeat(100 * 1000) + ".txt";
        final String second = "/d/" + "k".repeat(1000 * 1000) + ".txt";
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
