package bergdb.pubimp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import bergdb.core.Db;
import bergdb.core.DbConstants;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DbObject;
import bergdb.pub.Factory;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.Kv;
import bergdb.pub.NoSuchIndexException;

/**
 * Db's Javadoc, "Keys and the layers above" (bergdb 020-22), checked against what the code
 * does, a promise at a time (bergdb 020-27): writes through the Core in a database of the
 * Pub API. The tests write through the Db under the running Database, as the other testers
 * do; for a user that Db is not API, and the Javadoc says to write while no Database runs.
 * The refusals of BergDB's keys are tested by PubTesterIndexJobs.testStartRefusesBadIndexData,
 * PubTesterIndex's F16-1 test, IndexDefinitionTester and DbTesterRestart; the keys of /d and
 * /- that are no Pub key's by PubTester.testTransactionInfoLeavesOutKeysWithNoUkey,
 * PubTesterIndex.testScanLeavesOutAKeyWithNoUkey and PubTesterPrimary.
 */
public class PubTesterCoreKeys {

    private static byte[] obj(long x, String y) {
        return new DbObject.Builder().addLong("x", x).addString("y", y).build().getBytes();
    }

    /** The keys of the scan of index 'name' at x. */
    private static List<String> scan(Connection c, String name, long x) {
        List<String> keys = new ArrayList<>();
        for (Kv<DbObject> kv : c.useIndex(name, DbObject.class).eq(x).kvs()) {
            Assert.assertEquals(kv.key(), x, kv.value().getLong("x"));
            keys.add(kv.key());
        }
        return keys;
    }

    private static void assertScan(String about, Connection c, long x, String... keys) {
        Assert.assertEquals(about + ", x = " + x, Arrays.asList(keys).toString(),
                scan(c, "byx", x).toString());
    }

    private static void corePut(Db core, String ikey, byte[] value) {
        core.execute(core.trans().put(Keys.toBytes(ikey), value).build());
    }

    private static void createIndex(Database d) {
        d.indexBuilder("byx").dir("/p/").type("long").field("x").start().join();
    }

    /**
     * A put through the Core at an object key of an indexed directory can leave the value
     * out of the index's scans: a put that changes the indexed field, and a put of a new
     * key, are left out, and a scan never gives a value that does not match its query; a
     * put that keeps the indexed field changes nothing in the index. The value is back in
     * the scans when the key is written again through the Pub API, a put of its own bytes
     * (as a DbObject or as a byte[]), or when the index is deleted and created again.
     */
    @Nano
    public static void testCorePutAtAnIndexedObjectKey() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            Db core = ((DatabaseImp) d).getDb();
            c.put("/p/a", new DbObject(obj(1, "a")));
            c.put("/p/b", new DbObject(obj(1, "b")));
            createIndex(d);
            assertScan("built", c, 1, "/p/a", "/p/b");

            corePut(core, "/dp/-a", obj(2, "a"));
            assertScan("a changed", c, 1, "/p/b");
            assertScan("a changed", c, 2);
            corePut(core, "/dp/-b", obj(1, "b2"));
            assertScan("b kept its x", c, 1, "/p/b");
            corePut(core, "/dp/-c", obj(1, "c"));
            assertScan("c new", c, 1, "/p/b");

            c.put("/p/a", c.get("/p/a", DbObject.class));
            assertScan("a put again as a DbObject", c, 2, "/p/a");
            corePut(core, "/dp/-a", obj(3, "a"));
            assertScan("a changed again", c, 3);
            c.put("/p/a", c.get("/p/a", byte[].class));
            assertScan("a put again as a byte[]", c, 3, "/p/a");

            corePut(core, "/dp/-a", obj(4, "a"));
            assertScan("before the index is made again", c, 4);
            d.deleteIndex("byx");
            createIndex(d);
            assertScan("made again", c, 1, "/p/b", "/p/c");
            assertScan("made again", c, 4, "/p/a");
        } finally {
            d.close();
        }
    }

    /**
     * A put through the Core of an object of format 1, of BergDB 2026.3 and before, at an
     * indexed object key (bergdb 020-23, Z2): the value has no entry, as no index of 2026.4
     * takes one (IndexDefinition.entryLevels; RwEnvironmentImp gives a previous value of
     * format 1 none), so the key's entry is stale and every scan leaves the key out, as it
     * leaves out a value that a Core put changed, whatever the scan's type. A scan as byte[],
     * whose conversion does not refuse it, returned its bytes as a match of a query that they
     * do not hold, and one as DbObject or Object threw ObjectCreationException. A get of it
     * as an object refuses it; a put through the Pub API brings the key back.
     */
    @Nano
    public static void testCorePutOfAFormat1ObjectAtAnIndexedObjectKey() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            Db core = ((DatabaseImp) d).getDb();
            c.put("/p/a", new DbObject(obj(1, "a")));
            c.put("/p/b", new DbObject(obj(1, "b")));
            createIndex(d);
            final byte[] format1 = {'b', 'e', 'r', 'g', 'o', 1, 0, 0};
            corePut(core, "/dp/-a", format1);
            for (Class<?> type : new Class<?>[] {byte[].class, DbObject.class, Object.class}) {
                List<String> keys = new ArrayList<>();
                for (Kv<?> kv : c.useIndex("byx", type).eq(1L).kvs()) {
                    keys.add(kv.key());
                }
                for (Kv<?> kv : c.useIndex("byx", type).backward().kvs()) {
                    keys.add(kv.key());
                }
                int n = 0;
                for (Object o : c.useIndex("byx", type).objects()) {
                    n++;
                }
                Assert.assertEquals("as " + type.getName(), "[/p/b, /p/b]", keys.toString());
                Assert.assertEquals("as " + type.getName(), 1, n);
            }
            try {
                c.get("/p/a", DbObject.class);
                throw new AssertionError("a get of an object of format 1 as a DbObject");
            } catch (bergdb.pub.ObjectCreationException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("format 1"));
            }
            Assert.assertArrayEquals(format1, c.get("/p/a", byte[].class));

            c.put("/p/a", new DbObject(obj(1, "a")));
            assertScan("a put through the Pub API", c, 1, "/p/a", "/p/b");
            c.put("/after", "x");
            Assert.assertEquals("x", c.get("/after", String.class));
        } finally {
            d.close();
        }
    }

    /** A delete through the Core at an indexed object key leaves an entry that scans skip. */
    @Nano
    public static void testCoreDeleteAtAnIndexedObjectKey() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            Db core = ((DatabaseImp) d).getDb();
            c.put("/p/a", new DbObject(obj(1, "a")));
            c.put("/p/b", new DbObject(obj(1, "b")));
            createIndex(d);
            core.execute(core.trans().delete(Keys.toBytes("/dp/-a")).build());
            assertScan("a deleted", c, 1, "/p/b");
            Assert.assertEquals("its entry stays", 2, entryCount(core));
        } finally {
            d.close();
        }
    }

    /** The number of KVs under the index entries' prefix. */
    private static int entryCount(Db core) {
        bergdb.dag.GetMany g = core.newGetMany();
        g.startKey = Keys.toSegments(DbConstants.INTERNAL_PREFIX + "dient/");
        g.stopCondition = new bergdb.dag.GetMany.Prefix(g.startKey);
        core.getMany(g);
        return g.result.size();
    }

    /**
     * Your keys, every key that does not start with the bytes 01 66, 01 2f or 01 25: the Pub
     * API never lists them, and its writes, its index builds and deletions never write them:
     * each keeps its value and the transaction that wrote it.
     */
    @Nano
    public static void testYourKeysNeverWritten() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            Db core = ((DatabaseImp) d).getDb();
            byte[][] keys = {{5, 6}, {0}, {(byte) 0xff}, Keys.toBytes("/k1"),
                    Keys.toBytes("/k/x"), Keys.toBytes("/p/a")};
            for (int i = 0; i < keys.length; i++) {
                Assert.assertFalse("free: " + i, keys[i][0] == 1 && (keys[i][1] == 0x66
                        || keys[i][1] == 0x2f || keys[i][1] == 0x25));
            }
            long[] tpos = new long[keys.length];
            GetData gd = core.newGetData();
            for (int i = 0; i < tpos.length; i++) {
                core.execute(core.trans().put(keys[i], new byte[] {(byte) i}).build());
                Assert.assertTrue(core.getOne(Long.MAX_VALUE, Keys.toSegments(keys[i]), gd)
                        != null);
                tpos[i] = gd.tpos;
            }

            c.put("/p/a", new DbObject(obj(1, "a")));
            c.put("/k1", "a value");
            c.put("/k/x", "a value");
            createIndex(d);
            c.put("/p/b", new DbObject(obj(2, "b")));
            c.rw(env -> env.put("/p/c", new DbObject(obj(3, "c"))));
            c.delete("/p/a");
            d.deleteIndex("byx");
            List<String> listed = new ArrayList<>();
            for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/").kvs()) {
                listed.add(kv.key());
            }
            for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir("/k/").kvs()) {
                listed.add(kv.key());
            }
            Assert.assertEquals("[/k1, /k/x]", listed.toString());

            for (int i = 0; i < tpos.length; i++) {
                byte[] v = core.getOne(Long.MAX_VALUE, Keys.toSegments(keys[i]), gd);
                Assert.assertArrayEquals("key " + i, new byte[] {(byte) i}, v);
                Assert.assertEquals("key " + i + ", its transaction", tpos[i], gd.tpos);
            }
        } finally {
            d.close();
        }
    }

    /**
     * A write of BergDB's keys through the Db under a running Database is seen only in part
     * until the next start: a definition deleted through the Core is gone for useIndex(),
     * which reads it from the stream, while the index manager, which reads the definitions
     * at a start, still has the index.
     */
    @Nano
    public static void testOnlineWriteOfADefinitionSeenInPart() {
        Database d = Factory.database().memory().start();
        try {
            Connection c = d.connection();
            Db core = ((DatabaseImp) d).getDb();
            c.put("/p/a", new DbObject(obj(1, "a")));
            createIndex(d);
            core.execute(core.trans().delete(Keys.toBytes(DbConstants.INTERNAL_PREFIX
                    + "didef/-byx")).build());
            try {
                scan(c, "byx", 1);
                throw new AssertionError("useIndex() found the deleted definition");
            } catch (NoSuchIndexException e) {
                // Expected.
            }
            try {
                createIndex(d);
                throw new AssertionError("the index manager has no index byx");
            } catch (IndexAlreadyExistsException e) {
                // Expected.
            }
        } finally {
            d.close();
        }
    }
}
