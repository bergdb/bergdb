package bergdb.core;

import java.util.Arrays;
import java.util.List;

import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/**
 * Long keys (bergdb 021-16). A key is a tree of key nodes with a level per segment of 7 bytes
 * (Keys.toSegments), and walks of that tree were recursions with a frame per level: with the
 * thread's default stack, a database with a key of about 90 KB or more did not start (the
 * start's check, Dag.visitMemoryNodes), and a put of a key of 1,000,000 bytes after one of
 * 100,000 with the same start failed the database (Dag.freshTreeBound); a StackOverflowError
 * each (020-24-05, U5-1 and U5-2). BergDB has no limit on a key's length. Each test runs with
 * the default stack, and failed with a StackOverflowError before 021-16.
 */
public class DbTesterLongKeys {

    private static final long LATEST = Long.MAX_VALUE;

    private static byte[] key(String start, int length) {
        byte[] key = new byte[length];
        Arrays.fill(key, (byte) 'k');
        byte[] s = start.getBytes(java.nio.charset.StandardCharsets.UTF_8);
        System.arraycopy(s, 0, key, 0, s.length);
        return key;
    }

    private static void assertValue(Db db, byte[] key, String value) {
        Assert.assertArrayEquals("the value of the key of " + key.length + " bytes",
                value.getBytes(java.nio.charset.StandardCharsets.UTF_8), DbUtil.get(db, key));
    }

    /** The keys of a scan of the whole database, forward or backward. */
    private static void assertScan(Db db, boolean forward, byte[]... keys) {
        GetMany g = db.newGetMany();
        g.lookupTime = LATEST;
        if (!forward) {
            g.setBackward();
        }
        g.stopCondition = new GetMany.DontStop();
        db.getMany(g);
        List<Kvt> result = g.result;
        Assert.assertEquals("the scan's KVs", keys.length, result.size());
        for (int i = 0; i < keys.length; i++) {
            Assert.assertTrue("the scan's key " + i,
                    Arrays.equals(Keys.toSegments(keys[i]), result.get(i).key));
        }
    }

    /**
     * U5-1: a key of 200,000 bytes and a short key, put, and the database started again from
     * its stream: the start's check (DbStarter.postStartupCheck) threw StackOverflowError;
     * now the values are there, the scans list both keys, and a put works.
     */
    @Nano
    public static void testLongKeyRestart() {
        final byte[] longKey = key("/d/", 200 * 1000);
        final byte[] shortKey = Keys.toBytes("/a");
        MemoryStream stream = new MemoryStream();
        Db db = Db.builder().testSetup(stream).start();
        try {
            db.execute(db.trans().put(longKey, "long".getBytes()).build());
            db.execute(db.trans().put(shortKey, "short".getBytes()).build());
            db.sync(SyncLevel.ORDINARY);
            db.checkNodes();
            stream = stream.copy();     // A closed stream takes no append.
        } finally {
            db.close();
        }

        Db db2 = Db.builder().testSetup(stream).start();
        try {
            assertValue(db2, longKey, "long");
            assertValue(db2, shortKey, "short");
            assertScan(db2, true, shortKey, longKey);
            assertScan(db2, false, longKey, shortKey);
            db2.checkNodes();
            byte[] longer = key("/d/", 210 * 1000);
            db2.execute(db2.trans().put(longer, "longer".getBytes()).build());
            assertValue(db2, longer, "longer");
            assertValue(db2, longKey, "long");
        } finally {
            db2.close();
        }
    }

    /**
     * U5-2: a put of a key of 1,000,000 bytes after a key of 100,000 bytes with the same
     * start threw StackOverflowError in Dag.dirtyNodeBound (the recursion of freshTreeBound,
     * a frame per segment of the new key's part), and the database failed. Now both values
     * are there, and the database goes on. The startup distance of 200 MB keeps the first
     * key's nodes in memory, dirty: at 50 MB the second put writes them, and the still-dirty
     * passes take seconds (Db.handleStillDirtyNodes, a pass a level of the first key; 021-16,
     * finding Q1), which is not what this test is about.
     */
    @Nano
    public static void testLongKeyAfterItsStart() {
        final byte[] first = key("/d/", 100 * 1000);
        final byte[] second = key("/d/", 1000 * 1000);
        Db db = Db.builder().testSetup().startupDistance(200 * 1000 * 1000).start();
        try {
            db.execute(db.trans().put(first, "first".getBytes()).build());
            db.execute(db.trans().put(second, "second".getBytes()).build());
            assertValue(db, first, "first");
            assertValue(db, second, "second");
            db.execute(db.trans().put("/x", "x").build());
            assertValue(db, Keys.toBytes("/x"), "x");
        } finally {
            db.close();
        }
    }
}
