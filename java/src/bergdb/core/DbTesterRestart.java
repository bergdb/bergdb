package bergdb.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;

import bergdb.common.StringUtil;
import bergdb.dag.KeyNode;
import bergdb.dag.Node;
import bergdb.dag.NodeVisitor;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.storage.RecoverableStream;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * Class that tests restarting Db from an in-memory stream.
 * Typically a short startupDistance is used and eviction is often disabled.
 * 
 * @author Frans Lundberg
 */
public class DbTesterRestart {

    @Nano
    public static void test0() {
        // Simple restart, Db with one single value.
        
        byte[] value;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).testId().start();
        clock.setTime(10);
        Trans trans = db.trans().put("admin1", "Sanna").build();
        db.execute(trans);
        db.sync(SyncLevel.ORDINARY);
        long tt = trans.tt;
        stream = stream.copy();
        
        db = null;
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        
        value = DbUtil.get(db2, Long.MAX_VALUE, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, tt-1, StringUtil.toBytes("admin1"));
        Assert.assertNull(value);
        
        value = DbUtil.get(db2, tt, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
    }
    

    @Nano
    public static void testRestartOfEmptyDatabase() {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).testId().start();
        clock.setTime(10);
        db.sync(SyncLevel.ORDINARY);
        
        long c1 = DbUtil.checksum(db);
        
        stream = stream.copy();
        
        db = null;
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        
        long c2 = DbUtil.checksum(db2);
        
        Assert.assertEquals(c1, c2);
    }
    
    @Nano
    public static void longerThanStartup() {
        // Stream is longer than startupDistance, single key, value updated many times.
        
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(2);
        Db db = Db.builder().testSetup(stream)
                .clock(clock).startupDistance(10*1000).start();
        byte[] bytes = new byte[1000];
        
        for (int i = 0; i < 20; i++) {
            clock.setTime(100 + i*10);
            bytes[0] = (byte) i;
            Trans trans = db.trans().put("k", bytes).build();
            db.execute(trans);
        }
        long sum1 = DbUtil.checksum(db);
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        Assert.assertNull(DbUtil.get(db2, 5, "k"));
        
        for (int i = 0; i < 20; i++) {
            long lookupTime = 100 + i*10 + 5;
            byte[] v = DbUtil.get(db2, lookupTime, "k");
            Assert.assertTrue(v != null);
            Assert.assertEquals(i, v[0]);
        }
        
        long sum2 = DbUtil.checksum(db2);
        Assert.assertEquals("checksum", sum1, sum2);
        
        db2.stop();
    }
    
    /**
     * Db should remember startupDistance after restart of initial state database.
     */
    @Nano
    private static void dbShouldRememberStartupDistance1() throws InterruptedException {
        final int startupDistance = 400 * 1000;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(startupDistance).start();
        Assert.assertEquals("before restart", startupDistance, db.getStartupDistance());
        db.sync(SyncLevel.ORDINARY);
        
        // Restart
        
        long streamLength = stream.getLength();
        Assert.assertTrue("" + streamLength, streamLength > RecoverableStream.META_BLOCK_SIZE);
        
        stream = stream.copy();
        Assert.assertTrue(stream.getLength() > RecoverableStream.META_BLOCK_SIZE);
        
        db = Db.builder().mainStream(stream).start();
        
        Assert.assertEquals("after restart", startupDistance, db.getStartupDistance());
    }
    
    /**
     * Db should remember startupDistance after one user transaction.
     */
    @Nano
    private static void dbShouldRememberStartupDistance2() throws InterruptedException {
        int startupDistance = 400 * 1000;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(startupDistance).start();
        db.execute(db.trans().put("key", "value"));
        Assert.assertEquals("before restart", startupDistance, db.getStartupDistance());
        db.sync(SyncLevel.STRONG);
        
        // Restart
        
        stream = stream.copy();
        db = Db.builder()
                .mainStream(stream)
                .clock(clock)
                .start();
        
        Assert.assertEquals("after restart", startupDistance, db.getStartupDistance());
    }
    
    /** Simplest possible delete-and-restart test. */
    @Nano private static void testDelete1() {
        AppendOnlyStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        
        clock.setTime(10);
        db.execute(db.trans().put("k1", "k1-value"));
        
        clock.setTime(20);
        db.execute(db.trans().delete("k1"));
        db.sync(SyncLevel.ORDINARY);
        
        //db.printGraph(System.out);
        //db.getStream().print(System.out);
        
        db = null;
        
        // Restart
        
        Db db2 = Db.builder().testSetup(s).start();        
        //db2.printGraph(System.out);
        
        byte[] v1 = DbUtil.get(db2, 15, "k1");
        Assert.assertArrayEquals(StringUtil.toBytes("k1-value"), v1);
        v1 = DbUtil.get(db2, 25, "k1");
        Assert.assertNull(v1);
    }
    
    /** Multiple deletes in a single transaction. */
    @Nano private static void testDelete2() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        
        clock.setTime(10);
        db.execute(db.trans().put("k1", "k1-value").put("k2", "k2-value"));
        
        clock.setTime(20);
        db.execute(db.trans().delete("k1").delete("k2").delete("kk").put("k3", "k3-value").build());
        
        long sum1 = DbUtil.checksum(db);
        db.sync(SyncLevel.ORDINARY);
        
        // Restart
        
        Db db2 = Db.builder().testSetup(s.copy()).start();        
        long sum2 = DbUtil.checksum(db2);
        
        Assert.assertEquals(sum1, sum2);
    }

    /**
     * Deletes of missing keys of 7 bytes or more (more than one key segment), then two
     * restarts. Regression test for a bug found 2026-10-12: the delete created
     * a key node for a missing segment, the rerun at startup did not, so node ids
     * differed after the first restart, and the second restart failed.
     */
    @Nano private static void testDeleteMissingLongKey() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();

        clock.setTime(10);
        db.execute(db.trans().put("/a", "a-value").put("/abcdefXX", "x-value"));

        clock.setTime(20);
        db.execute(db.trans().delete("/k/1000"));            // two segments, both missing

        clock.setTime(30);
        db.execute(db.trans().delete("/abcdefgh12345"));     // three segments, first exists

        clock.setTime(40);
        db.execute(db.trans().put("/b", "b-value"));
        long sum1 = DbUtil.checksum(db);
        db.sync(SyncLevel.STRONG);
        db.stop();

        // Restart, put, restart

        s = s.copy();
        db = Db.builder().testSetup(s).clock(clock).start();
        Assert.assertEquals("checksum after first restart", sum1, DbUtil.checksum(db));

        clock.setTime(50);
        db.execute(db.trans().put("/c", "c-value"));
        long sum2 = DbUtil.checksum(db);
        db.sync(SyncLevel.STRONG);
        db.stop();

        s = s.copy();
        db = Db.builder().testSetup(s).clock(clock).start();
        Assert.assertEquals("checksum after second restart", sum2, DbUtil.checksum(db));
        Assert.assertEquals("a-value", DbUtil.getString(db, "/a"));
        Assert.assertEquals("x-value", DbUtil.getString(db, "/abcdefXX"));
        Assert.assertEquals("c-value", DbUtil.getString(db, "/c"));
        Assert.assertNull(DbUtil.get(db, Long.MAX_VALUE, "/k/1000"));
        db.stop();
    }
    
    /**
     * One object per node after restarts with bounded startup (level 2): every node in D
     * is the node table's object for its id and is dirty, every dirty node in memory is
     * in D, and no id has two dirty objects. Regression test for bugs found 2026-10-12
     * (level 2): after a
     * restart, D could hold a copy of a node read from the stream while the Dag held
     * another object with the same id; and Db and NodeCollection had a node table each.
     */
    @Nano private static void testOneObjectPerNodeAfterRestarts() {
        Random rnd = new Random(1);
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).startupDistance(10 * 1000).start();
        long time = 10;
        int restarts = 0;
        
        for (int i = 0; i < 1000; i++) {
            clock.setTime(time += 10);
            Trans.Builder b = db.trans();
            Set<String> keys = new LinkedHashSet<String>();
            int ops = 1 + rnd.nextInt(3);
            while (keys.size() < ops) {
                keys.add("/k/" + rnd.nextInt(500));
            }
            for (String key : keys) {
                byte[] value = new byte[1 + rnd.nextInt(40)];
                rnd.nextBytes(value);
                b.put(key, value);
            }
            db.execute(b.build());
            
            if (i % 250 == 249) {
                db.sync(SyncLevel.STRONG);
                db.stop();
                s = s.copy();
                db = Db.builder().testSetup(s).clock(clock).start();
                restarts++;
            }
            
            if (restarts > 0 && i % 250 < 20) {
                String problems = identityViolations(db);
                Assert.assertTrue("transaction " + i + ": " + problems, problems == null);
            }
        }
        
        Assert.assertTrue("startup pos moved", db.internal().x().startupPos.get() 
                > RecoverableStream.META_BLOCK_SIZE);
    }
    
    /**
     * Checks one object per node: returns null if OK, else a description. See
     * testOneObjectPerNodeAfterRestarts().
     */
    static String identityViolations(Db db) {
        final Cache3 table = db.internal().cache();
        final Set<Node> inD = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        final StringBuilder problems = new StringBuilder();
        
        db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                inD.add(node);
                if (table.getNode(node.getId()) != node) {
                    problems.append("node " + node.getId() + " in D is not in the node table; ");
                }
                if (!node.isDirty()) {
                    problems.append("node " + node.getId() + " in D is not dirty; ");
                }
            }
        });
        
        final Map<Long, Node> dirtyById = new HashMap<Long, Node>();
        db.internal().dag().visitMemoryNodes(new NodeVisitor() {
            public void visit(TopNode node) { check(node); }
            public void visit(KeyNode node) { check(node); }
            public void visit(ValueNode node) {}
            
            private void check(Node node) {
                if (!node.isDirty()) {
                    return;
                }
                if (!inD.contains(node)) {
                    problems.append("dirty node " + node.getId() + " is not in D; ");
                }
                Node other = dirtyById.put(node.getId(), node);
                if (other != null && other != node) {
                    problems.append("two dirty objects for node " + node.getId() + "; ");
                }
            }
        });
        
        return problems.length() == 0 ? null : problems.toString();
    }
    
    /**
     * Level 2, restarts with bounded startup: puts, deletes, short and long keys, and
     * transactions with one to twenty keys; after each restart, every key is checked at
     * the latest time and at earlier times. See docs/levels.md.
     * Fails without DbStarter.canonicalNode()'s use of the stored position (a delete of
     * a key that does not exist). Larger: testLevel2RestartsKeepAllValuesF.
     */
    @Nano private static void testLevel2RestartsKeepAllValues() {
        checkAllValues(1, 30, 50, 200);
        checkAllValues(2, 8, 25, 200);
    }
    
    @Nano("f") private static void testLevel2RestartsKeepAllValuesF() {
        checkAllValues(1, 30, 50, 1000);
        checkAllValues(2, 8, 25, 1000);
    }
    
    private static void checkAllValues(long seed, int maxNodeSize, int restartEvery, int n) {
        Level2Run run = new Level2Run(seed, maxNodeSize, restartEvery);
        run.run(n);
        Assert.assertTrue(run.problem, run.problem == null);
    }
    
    /**
     * Level 2: the stream with restarts is the same, byte for byte, as without (T2 in
     * docs/sis-model.md). Fails without NodeCollection.resolvePointers().
     * Larger: testLevel2SameStreamWithRestartsF.
     */
    @Nano private static void testLevel2SameStreamWithRestarts() throws java.io.IOException {
        checkSameStream(2, 30, 20, 200);
    }
    
    @Nano("f") private static void testLevel2SameStreamWithRestartsF() throws java.io.IOException {
        checkSameStream(3, 30, 40, 600);
    }
    
    private static void checkSameStream(long seed, int maxNodeSize, int restartEvery, int n) 
            throws java.io.IOException {
        Level2Run a = new Level2Run(seed, maxNodeSize, 0);
        a.run(n);
        Level2Run b = new Level2Run(seed, maxNodeSize, restartEvery);
        b.run(n);
        Assert.assertTrue(b.problem, b.problem == null);
        
        long length = a.stream.getLength();
        Assert.assertEquals("stream length", length, b.stream.getLength());
        byte[] bytesA = new byte[(int) length];
        byte[] bytesB = new byte[(int) length];
        a.stream.read(0, bytesA, 0, (int) length);
        b.stream.read(0, bytesB, 0, (int) length);
        int first = -1;
        for (int i = 0; i < length && first < 0; i++) {
            if (bytesA[i] != bytesB[i]) {
                first = i;
            }
        }
        Assert.assertEquals("first byte that differs", -1, first);
    }
    
    /**
     * A random run with restarts every restartEvery transactions (0 for none), and with
     * lookups of every key after each restart (or at the same points, if lookupEvery).
     */
    static class Level2Run {
        final Random rnd;
        final Random lookupRnd;
        final int maxNodeSize;
        final int restartEvery;
        int lookupEvery;
        boolean doRestarts = true;
        final CoreTestClock clock = new CoreTestClock();
        final Map<String, TreeMap<Long, byte[]>> model = new HashMap<String, TreeMap<Long, byte[]>>();
        final List<Long> times = new ArrayList<Long>();
        MemoryStream stream = new MemoryStream();
        Db db;
        String problem;
        
        Level2Run(long seed, int maxNodeSize, int restartEvery) {
            this.rnd = new Random(seed);
            this.lookupRnd = new Random(seed + 1000);
            this.maxNodeSize = maxNodeSize;
            this.restartEvery = restartEvery;
            this.lookupEvery = restartEvery;
        }
        
        Db start() {
            DbBuilder b = Db.builder().testSetup(stream).clock(clock).startupDistance(2000);
            if (maxNodeSize == 8) b.maxNodeSize8();
            if (maxNodeSize == 30) b.maxNodeSize30();
            return b.start();
        }
        
        void run(int n) {
            db = start();
            long time = 10;
            
            for (int i = 0; i < n && problem == null; i++) {
                clock.setTime(time += 10);
                times.add(time);
                Trans.Builder b = db.trans();
                Set<String> keys = new LinkedHashSet<String>();
                int ops = rnd.nextInt(10) == 0 ? 1 + rnd.nextInt(20) : 1 + rnd.nextInt(3);
                while (keys.size() < ops) {
                    keys.add(rnd.nextBoolean() ? "/k/" + rnd.nextInt(300) : "/long/" + rnd.nextInt(300));
                }
                for (String key : keys) {
                    byte[] value = null;
                    if (rnd.nextInt(5) == 0) {
                        b.delete(key);
                    } else {
                        value = new byte[1 + rnd.nextInt(60)];
                        rnd.nextBytes(value);
                        b.put(key, value);
                    }
                    TreeMap<Long, byte[]> history = model.get(key);
                    if (history == null) {
                        model.put(key, history = new TreeMap<Long, byte[]>());
                    }
                    history.put(time, value);
                }
                db.execute(b.build());
                
                if (doRestarts && restartEvery > 0 && i % restartEvery == restartEvery - 1) {
                    db.sync(SyncLevel.STRONG);
                    db.stop();
                    stream = stream.copy();
                    try {
                        db = start();
                    } catch (RuntimeException e) {
                        problem = "restart after transaction " + i + ": " + e;
                        return;
                    }
                }
                
                if (lookupEvery > 0 && i % lookupEvery == lookupEvery - 1) {
                    check(i);
                }
            }
            
            db.sync(SyncLevel.STRONG);
        }
        
        /** Checks every key at the latest time and at ten earlier times. */
        void check(int i) {
            List<Long> lookupTimes = new ArrayList<Long>();
            lookupTimes.add(Long.MAX_VALUE);
            for (int j = 0; j < 10; j++) {
                lookupTimes.add(times.get(lookupRnd.nextInt(times.size())) 
                        + lookupRnd.nextInt(2) - 1);
            }
            
            for (Map.Entry<String, TreeMap<Long, byte[]>> e : model.entrySet()) {
                for (long t : lookupTimes) {
                    Map.Entry<Long, byte[]> expected = e.getValue().floorEntry(t);
                    byte[] expectedValue = expected == null ? null : expected.getValue();
                    byte[] value;
                    try {
                        value = DbUtil.get(db, t, e.getKey());
                    } catch (RuntimeException ex) {
                        problem = "after restart at " + i + ": get(" + e.getKey() + ", " + t 
                                + ") failed: " + ex;
                        return;
                    }
                    if (!java.util.Arrays.equals(expectedValue, value)) {
                        problem = "after restart at " + i + ": " + e.getKey() + " at time " + t
                                + ": expected " + (expectedValue == null ? "none" 
                                        : expectedValue.length + " bytes") 
                                + ", got " + (value == null ? "none" : value.length + " bytes");
                        return;
                    }
                }
            }
        }
    }
    
    /**
     * After a restart, the meta block knows the position of the last transaction, as
     * without the restart, so that the next meta block written is the same. Regression 
     * test for a bug found 2026-10-12 (level 2, step 3): it kept the position 
     * stored in the last meta block on disk, from before the transactions after it.
     */
    @Nano private static void testLastTransPosAfterRestart() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        long lastTpos = -1;
        for (int i = 0; i < 10; i++) {
            clock.setTime(10 + 10 * i);
            Trans t = db.trans().put("/k/" + i, "value").build();
            db.execute(t);
            lastTpos = t.tpos;
        }
        Assert.assertEquals("before restart", lastTpos, 
                db.internal().nodeStream().getMetaBlock().getLastTransSpos());
        db.sync(SyncLevel.STRONG);
        db.stop();
        
        db = Db.builder().testSetup(s.copy()).clock(clock).start();
        Assert.assertEquals("after restart", lastTpos, 
                db.internal().nodeStream().getMetaBlock().getLastTransSpos());
    }
}
