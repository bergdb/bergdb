package bergdb.pubimp;

import java.util.Arrays;

import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Kv;

/**
 * The read side of BergDB's rule for strings (bergdb 021-04, 021-06): every string in a
 * stream is well-formed UTF-8, and a reader that meets bytes that are not never repairs
 * them. A key whose bkey is not an ikey's (written through the Core API, or by another
 * writer, such as the C clone, bergdb 012) has no String key: the Core reaches it by its
 * bkey, the Pub layer's scans leave it out, and no get by a String key names it.
 *
 * @author Frans Lundberg
 */
public class Utf8ReadTester {

    /** The bkey of an ikey, then the given bytes. */
    static byte[] bkey(String ikey, int... more) {
        byte[] start = Keys.toBytes(ikey);
        byte[] result = Arrays.copyOf(start, start.length + more.length);
        for (int i = 0; i < more.length; i++) {
            result[start.length + i] = (byte) more[i];
        }
        return result;
    }

    /**
     * CK1 and CK2 of bergdb 021-04: an ikey with ED A0 80 (U+D800 in WTF-8, which the C
     * clone takes) and one with EF BF BD (U+FFFD). Java read both as the String "/d/a"
     * U+FFFD, whose bkey is CK2's: CK1's value could not be got by its key, and a scan gave
     * two values with one key. Now they stay two keys: CK1 has no ikey, the Core reaches it
     * by its bkey, a scan of /d/ leaves it out, as it leaves out a key that is no ukey of
     * the directory ("/dd/-x/y"), and the String key gets CK2's value.
     */
    @Nano
    public static void testCk1AndCk2StayTwoKeys() {
        Database d = Factory.database().memory().start();
        try {
            Db db = ((DatabaseImp) d).getDb();
            byte[] ck1 = bkey("/dd/-a", 0xef, 0xa2, 0x82);
            byte[] ck2 = Keys.toBytes("/dd/-a�");
            byte[] noUkey = Keys.toBytes("/dd/-x/y");
            db.execute(db.trans().put(ck1, new byte[] {'1'}).put(ck2, new byte[] {'2'})
                    .put(noUkey, new byte[] {'3'}));
            Connection c = d.connection();
            c.w().put("/d/b", "b").put("/d/￾", "fffe").execute();

            Assert.assertEquals("1", new String(DbUtil.get(db, ck1)));
            Assert.assertEquals("2", new String(DbUtil.get(db, ck2)));
            Assert.assertNull(Keys.bkey2ikeyOrNull(ck1));
            Assert.assertEquals("2", c.get("/d/a�", String.class));
            Assert.assertTrue(c.exists("/d/a�"));

            Assert.assertEquals("/d/a�=2 /d/b=b /d/￾=fffe ",
                    kvs(c.usePrimary(String.class).dir("/d/").kvs()));
            Assert.assertEquals("/d/￾=fffe /d/b=b /d/a�=2 ",
                    kvs(c.usePrimary(String.class).dir("/d/").backward().kvs()));
            Assert.assertEquals("/d/b=b /d/￾=fffe ",
                    kvs(c.usePrimary(String.class).dir("/d/").startAt("a�")
                    .inclusive(false).kvs()));
            int n = 0;
            for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/d/").kvs()) {
                Assert.assertTrue(kv.key(), kv.key().startsWith("/d/"));
                n++;
            }
            Assert.assertEquals(3, n);
        } finally {
            d.stop();
        }
    }

    /**
     * A page of the scan (100 keys) that holds only bkeys without an ikey is not the end of
     * the directory: 150 of them, then a user's key, forward and backward.
     */
    @Nano
    public static void testScanPastKeysWithoutIkey() {
        Database d = Factory.database().memory().start();
        try {
            Db db = ((DatabaseImp) d).getDb();
            bergdb.core.Trans.Builder t = db.trans();
            for (int i = 0; i < 150; i++) {
                t.put(bkey("/dd/-k" + (1000 + i), 0xc2, 0x82), new byte[] {'x'});
            }
            db.execute(t);
            Connection c = d.connection();
            c.w().put("/d/a", "a").put("/d/z", "z").execute();
            Assert.assertEquals("/d/a=a /d/z=z ", kvs(c.usePrimary(String.class).dir("/d/").kvs()));
            Assert.assertEquals("/d/z=z /d/a=a ",
                    kvs(c.usePrimary(String.class).dir("/d/").backward().kvs()));
        } finally {
            d.stop();
        }
    }

    static <T> String kvs(Iterable<Kv<T>> kvs) {
        StringBuilder b = new StringBuilder();
        for (Kv<T> kv : kvs) {
            b.append(kv.key()).append('=').append(kv.value()).append(' ');
        }
        return b.toString();
    }
}
