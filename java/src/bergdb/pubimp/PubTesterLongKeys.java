package bergdb.pubimp;

import java.io.File;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import bergdb.core.Db;
import bergdb.dag.GetMany;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Kv;
import bergdb.pub.Limits;

/**
 * Long keys through the Pub API (bergdb 021-16; 020-24-05, U5-1 and U5-2), since bergdb 024-24
 * at the limit L2: a key has at most 111 bytes as stored, its UTF-8 and a byte for each part,
 * so each '/' counts two (the package's Limits; 024-17). Until 024-24 a key's length had no
 * limit, and these tests put keys of 100,000 to 1,000,000 chars, and one 20,000 directories
 * deep: a key of about 90 KB or more made the next start throw StackOverflowError, a key of
 * 1,000,000 chars after one of 100,000 with the same start failed the database (021-16).
 * The Core's tests are in bergdb.core.DbTesterLongKeys. Since bergdb 026-02 also the Pub
 * API's key check, Limits.keyBytes() and Limits.checkKey(), against what a put does.
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

    /** Limits' constants are Db's (bergdb 026-02): L6 is a key's limit. */
    @Nano
    public static void testLimitsConstants() {
        Assert.assertEquals(Db.MAX_OPERATIONS, Limits.MAX_OPERATIONS);
        Assert.assertEquals(Db.MAX_KEY_BYTES, Limits.MAX_KEY_BYTES);
        Assert.assertEquals(Db.MAX_TRANS_KEY_BYTES, Limits.MAX_TRANS_KEY_BYTES);
        Assert.assertEquals(Db.MAX_VALUE_BYTES, Limits.MAX_VALUE_BYTES);
        Assert.assertEquals(Db.MAX_TRANS_BYTES, Limits.MAX_TRANS_BYTES);
        Assert.assertEquals(Db.MAX_KEY_BYTES, Limits.MAX_LEVEL_BYTES);
        Assert.assertEquals(111, Limits.MAX_KEY_BYTES);
        Assert.assertEquals(21L, Limits.keyBytes("/customers/12345678"));    // the package's
    }

    /** Pieces of a random key: 1, 2, 3 and 4 bytes of UTF-8, U+0000, U+0001, key replace. */
    private static final String[] PIECES = {"a", "Z", "7", ".", "-", "_", " ", "\u00e5",
            "\u00f6", "\u03a9", "\u4e2d", "\u20ac", "\uD83D\uDE00", "\u0000", "\u0001",
            "${transactionTime}", "obj", "txt"};

    private static final String TIME = "${transactionTime}";

    /** The bytes of a key as stored by the rule in words: its UTF-8 and one for each '/'. */
    private static long ruleBytes(String key) {
        return key.getBytes(StandardCharsets.UTF_8).length + key.chars().filter(c -> c == '/')
                .count();
    }

    /**
     * Keys at 111 and 112 bytes as stored, of each kind: ASCII, many '/', two, three and
     * four bytes of UTF-8, U+0000, and "${transactionTime}".
     */
    private static List<String> boundaryKeys() {
        List<String> keys = new ArrayList<>();
        keys.add("/" + "k".repeat(109));
        keys.add("/" + "k".repeat(110));
        keys.add("/a".repeat(37));
        keys.add("/a".repeat(36) + "/ab");
        keys.add("/" + "\u00e5".repeat(54) + "k");
        keys.add("/" + "\u00e5".repeat(55));
        keys.add("/" + "\u4e2d".repeat(36) + "k");
        keys.add("/" + "\u4e2d".repeat(36) + "kk");
        keys.add("/" + "\uD83D\uDE00".repeat(27) + "k");
        keys.add("/" + "\uD83D\uDE00".repeat(27) + "kk");
        keys.add("/" + "\u0000".repeat(109));
        keys.add("/" + "\u0000".repeat(110));
        keys.add("/t/" + TIME + "/" + "k".repeat(86));                 // in a directory
        keys.add("/t/" + TIME + "/" + "k".repeat(87));
        keys.add("/t/" + "k".repeat(84) + TIME + ".txt");               // in the name
        keys.add("/t/" + "k".repeat(85) + TIME + ".txt");
        for (int i = 0; i < keys.size(); i++) {
            Assert.assertEquals(keys.get(i), 111 + i % 2, ruleBytes(keys.get(i)));
        }
        return keys;
    }

    /** Keys of a bad form, some of them over 111 bytes too. */
    private static List<String> badKeys() {
        List<String> keys = new ArrayList<>();
        for (String k : new String[] {null, "", "/", "a", "a/b", "//", "//a", "/a//b", "/a/",
                "/a/b/", "/a\uD800", "/\uDC00b", "/a/\uD83D", "\uD83D\uDE00/a", "/a/b//",
                "k".repeat(200), "/" + "k".repeat(200) + "/", "/" + "k".repeat(200) + "//k",
                "/" + "k".repeat(200) + "\uDC00"}) {
            keys.add(k);
        }
        return keys;
    }

    /**
     * A random key: of a bad form now and then; else its stored size near the limit (100
     * to 117 bytes) or anywhere up to 160, of random pieces, with few or many '/', and a
     * suffix sometimes.
     */
    private static String randomKey(Random r) {
        if (r.nextInt(12) == 0) {
            List<String> bad = badKeys();
            String k = bad.get(r.nextInt(bad.size()));
            if (k != null && r.nextBoolean()) {     // a bad form somewhere in a longer key
                k = "/" + "q".repeat(r.nextInt(120)) + k;
            }
            return k;
        }
        int target = r.nextInt(3) > 0 ? 100 + r.nextInt(18) : 2 + r.nextInt(159);
        double slash = r.nextInt(4) == 0 ? 0.6 : 0.08;
        StringBuilder b = new StringBuilder("/").append(PIECES[r.nextInt(PIECES.length)]);
        while (ruleBytes(b.toString()) < target) {
            if (r.nextDouble() < slash) {
                b.append('/');
            }
            b.append(PIECES[r.nextInt(PIECES.length)]);
        }
        if (r.nextInt(4) == 0) {
            b.append(r.nextBoolean() ? ".txt" : ".obj");
        }
        return b.toString();
    }

    /** The message of r's IllegalArgumentException, or null if it returns. */
    private static String refusal(Runnable r) {
        try {
            r.run();
            return null;
        } catch (IllegalArgumentException e) {
            return e.getMessage();
        }
    }

    /** Asserts that two messages, or nulls, are equal. */
    private static void assertMessage(String about, String expected, String actual) {
        if (!java.util.Objects.equals(expected, actual)) {
            throw new AssertionError(about + ", expected " + expected + ", got " + actual);
        }
    }

    /** The bkeys of the Core's latest state. */
    private static Set<ByteBuffer> coreKeys(Db core) {
        GetMany g = core.newGetMany();
        core.getMany(g);
        Set<ByteBuffer> keys = new HashSet<>();
        for (Kvt kv : g.result) {
            keys.add(ByteBuffer.wrap(bergdb.dag.Keys.toBytes(kv.key)));
        }
        return keys;
    }

    /**
     * bergdb 026-02, option A: for boundary keys, keys of a bad form and random keys, with key
     * replace off and on, Limits.checkKey() throws if and only if a put and a delete of a
     * memory database throw, with the same message; Limits.keyBytes() throws for a bad form
     * with that message, and else gives the bytes of the key that the put stored, read back
     * by a scan of the Core, and the rule's count (UTF-8 and one for each '/'). The one
     * other refusal of a put of a byte[] at a key, "${transactionTime}" in the directory of
     * an object key with key replace on (020-14, X1), is outside checkKey().
     */
    @Nano
    public static void testLimitsMatchPut() {
        Random r = new Random(2602);
        List<String> keys = new ArrayList<>(boundaryKeys());
        keys.addAll(badKeys());
        for (int i = 0; i < 600; i++) {
            keys.add(randomKey(r));
        }
        int[] counts = new int[4];      // taken, too long, bad form, X1
        for (boolean replace : new boolean[] {false, true}) {
            try (Database db = Factory.database().memory().start()) {
                Connection c = db.connection();
                c.setEnableKeyReplace(replace);
                Db core = ((DatabaseImp) db).getDb();
                Set<ByteBuffer> start = coreKeys(core);
                for (String key : keys) {
                    counts[checkKeyAsPut(c, core, start, key, replace)]++;
                }
            }
        }
        for (int count : counts) {
            Assert.assertTrue(java.util.Arrays.toString(counts), count > 20);
        }
    }

    /** Checks one key; returns 0 if taken, 1 if too long, 2 if of a bad form, 3 for X1. */
    private static int checkKeyAsPut(Connection c, Db core, Set<ByteBuffer> start,
            String key, boolean replace) {
        String about = "replace " + replace + ", key " + (key == null ? null
                : key.replace("\u0000", "\\0").replace("\u0001", "\\1")) + ": ";
        String check = refusal(() -> Limits.checkKey(key));
        long[] bytes = {-1};
        String form = refusal(() -> bytes[0] = Limits.keyBytes(key));
        assertMessage(about + "delete", check, refusal(() -> c.delete(key)));
        assertMessage(about + "w().delete", check, refusal(() -> c.w().delete(key).execute()));
        if (form != null) {
            assertMessage(about + "keyBytes", check, form);
        } else {
            Assert.assertEquals(about + "rule", ruleBytes(key), bytes[0]);
            Assert.assertEquals(about + "checkKey", bytes[0] > Limits.MAX_KEY_BYTES,
                    check != null);
            Assert.assertTrue(about + check, check == null
                    || check.contains("more than 111 (bergdb 024-17, L2)"));
        }

        boolean x1 = replace && check == null && Entries.isObjectKey(PubKeys.u2i(key))
                && key.substring(0, key.lastIndexOf('/')).contains(TIME);
        byte[] value = {7};
        String put = refusal(() -> c.put(key, value));
        if (x1) {
            Assert.assertTrue(about + put, put != null && put.contains("(bergdb 020-14, X1)"));
            return 3;
        }
        assertMessage(about + "put", check, put);
        if (put != null) {
            return form != null ? 2 : 1;
        }

        Set<ByteBuffer> stored = coreKeys(core);
        stored.removeAll(start);
        Assert.assertEquals(about + "stored", 1, stored.size());
        byte[] bkey = stored.iterator().next().array();
        Assert.assertEquals(about + "stored bytes", bytes[0], (long) bkey.length);
        Assert.assertEquals(about + "replaced", replace && key.contains(TIME),
                !java.util.Arrays.equals(bkey, bergdb.dag.Keys.toBytes(PubKeys.u2i(key))));
        core.execute(core.trans().delete(bergdb.dag.Keys.toSegments(bkey)).build());
        return 0;
    }
}
