package bergdb.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.CutStream;
import bergdb.stream.MemoryStream;

/**
 * The merges at the delete through Db (bergdb 024-21; 024-11, section 6, T7): BU1 after every
 * transaction (Dag.checkFill), restarts in the middle of merge-heavy work and starts of a
 * stream cut at a record's end, whose reruns must make the same tree, node for node; and
 * readers at earlier times while the writer merges, with eviction.
 *
 * @author Frans Lundberg
 */
public class DbTesterMerge {

    private static String key(int i) {
        return "/m/" + String.format("%05d", i);
    }

    /** BU1 at the latest time of 'db' (Dag.checkFill), as a reader reads. */
    static Dag.Fill checkFill(Db db, String at) {
        long time = db.lookupTime(Long.MAX_VALUE);
        Dag.Fill f = db.internal().dag().checkFill(time, db.newGetData());
        Assert.assertTrue(at + ": " + f, f.error == null);
        return f;
    }

    /**
     * The key nodes reachable at the latest time, as text: each node's id and klongs in
     * the order a walk meets them, live or not, with its pointers' ids: two databases with
     * the same text have the same tree, node for node.
     */
    static String tree(Db db) {
        long time = db.lookupTime(Long.MAX_VALUE);
        GetData gd = db.newGetData();
        KeyNode root = db.internal().dag().getTopDs().findRoot(time, gd);
        StringBuilder sb = new StringBuilder();
        java.util.ArrayDeque<KeyNode> todo = new java.util.ArrayDeque<KeyNode>();
        java.util.Set<Long> seen = new java.util.HashSet<Long>();
        todo.push(root);
        while (!todo.isEmpty()) {
            KeyNode n = todo.pop();
            if (!seen.add(n.getId())) continue;
            sb.append(n.getId()).append(n.isSegmentLeaf() ? " L:" : " I:");
            int sz = n.getSize();
            long del = n.getDeleteBitmapAtTime(time, sz);
            TreeMap<Long, Integer> live = new TreeMap<Long, Integer>();
            for (int i = 0; i < sz; i++) {
                long k = n.getKlong(i);
                sb.append(' ').append(Long.toHexString(k));
                if (Klong.isKey(k) && !Klong.isDeleted(del, i)) live.put(Klong.getCompareValue(k), i);
            }
            sb.append('\n');
            for (int i : live.values()) {
                if (n.isSegmentLeaf() && Klong.getLength(n.getKlong(i)) < Klong.MAX_SIZE) continue;
                Node c = gd.followPointer(n, i);
                if (c instanceof KeyNode) todo.push((KeyNode) c);
            }
        }
        return sb.toString();
    }

    /** The workload: 'n' keys put, then all but every 'k'-th deleted in random order, 'per'
     *  keys a transaction, with an overwrite of a key of another segment tree in each. */
    private static List<TreeMap<String, String>> workload(int n, int k, int per, long seed) {
        List<TreeMap<String, String>> ts = new ArrayList<TreeMap<String, String>>();
        for (int i = 0; i < n; i += per) {
            TreeMap<String, String> t = new TreeMap<String, String>();
            for (int j = i; j < Math.min(n, i + per); j++) t.put(key(j), "v" + j);
            ts.add(t);
        }
        List<Integer> dels = new ArrayList<Integer>();
        for (int i = 0; i < n; i++) if (i % k != 0) dels.add(i);
        Collections.shuffle(dels, new Random(seed));
        for (int i = 0; i < dels.size(); i += per) {
            TreeMap<String, String> t = new TreeMap<String, String>();
            for (int j = i; j < Math.min(dels.size(), i + per); j++) t.put(key(dels.get(j)), null);
            t.put("/other/x", "o" + i);
            ts.add(t);
        }
        return ts;
    }

    private static Trans build(Db db, TreeMap<String, String> ops) {
        Trans.Builder b = db.trans();
        for (Map.Entry<String, String> e : ops.entrySet()) {
            if (e.getValue() == null) b.delete(e.getKey());
            else b.put(e.getKey(), e.getValue());
        }
        return b.build();
    }

    private static void checkValues(Db db, TreeMap<String, String> state, int n, String at) {
        for (int i = 0; i < n; i++) {
            String exp = state.get(key(i));
            String act = DbUtil.getString(db, key(i));
            if (exp == null ? act != null : !exp.equals(act)) {
                throw new AssertionError(at + ": " + key(i) + ", expected " + exp + ", got " + act);
            }
        }
    }

    /**
     * Restarts in the middle of merge-heavy work (T7): 1,200 keys at node size 8, then all
     * but every third deleted in random order, 40 a transaction; after every third
     * transaction a restart on a copy of the stream, at startup distances of 10 bytes and 10
     * MB, so that a start reruns little or every record. After each start: the values, BU1,
     * and the tree the same as before the restart, node for node (ids, klongs, pointers):
     * the rerun makes the same merges and the same nodes.
     */
    @Nano
    public static void testRestartsRerunTheMerges() {
        final long merges0 = Dag.statJoins;
        for (int sd : new int[] {10, 10 * 1000 * 1000}) {
            String at0 = "startup distance " + sd;
            MemoryStream ms = new MemoryStream();
            Db db = Db.builder().testSetup(ms).maxNodeSize8().startupDistance(sd).start();
            TreeMap<String, String> state = new TreeMap<String, String>();
            List<TreeMap<String, String>> ts = workload(1200, 3, 40, sd);
            for (int i = 0; i < ts.size(); i++) {
                String at = at0 + ", transaction " + i;
                Trans t = build(db, ts.get(i));
                db.execute(t);
                for (Map.Entry<String, String> e : ts.get(i).entrySet()) {
                    if (e.getValue() == null) state.remove(e.getKey());
                    else state.put(e.getKey(), e.getValue());
                }
                checkFill(db, at);
                if (i % 3 == 2) {
                    db.sync(t.lastPos, SyncLevel.ORDINARY);
                    String before = tree(db);
                    db.close();
                    ms = ms.copy();
                    db = Db.builder().testSetup(ms).maxNodeSize8().startupDistance(sd).start();
                    Assert.assertEquals(at + ": the tree after the restart", before, tree(db));
                    checkFill(db, at + ", restarted");
                    checkValues(db, state, 1200, at + ", restarted");
                }
            }
            checkValues(db, state, 1200, at0);
            db.close();
        }
        Assert.assertTrue("merges", Dag.statJoins > merges0);
    }

    /**
     * Option 2 of dead klongs through Db (bergdb 024-23): 400 keys at node sizes 14 and 30
     * (theta 3 and 7), then transactions of 40 overwrites of random keys, so that leaves and
     * inner nodes reach theta dead klongs and are compacted; after every third transaction a
     * restart on a copy of the stream, at startup distances of 10 bytes and 10 MB. After each
     * start: the values, BU1 and at most theta dead klongs a node (checkFill), and the tree the
     * same as before the restart, node for node: the rerun compacts the same nodes. With 10 MB
     * a start reruns every record, and its reruns compact (Dag.statCompactions).
     */
    @Nano
    public static void testRestartsRerunTheCompactions() {
        for (int b : new int[] {14, 30}) {
            for (int sd : new int[] {10, 10 * 1000 * 1000}) {
                String at0 = "node size " + b + ", startup distance " + sd;
                MemoryStream ms = new MemoryStream();
                Db db = builder(ms, b, sd).start();
                TreeMap<String, String> state = new TreeMap<String, String>();
                Random rnd = new Random(b + sd);
                final long compactions0 = Dag.statCompactions;
                long rerun = 0;             // compactions made by the starts' reruns
                for (int i = 0; i < 30; i++) {
                    String at = at0 + ", transaction " + i;
                    TreeMap<String, String> ops = new TreeMap<String, String>();
                    if (i == 0) {
                        for (int j = 0; j < 400; j++) ops.put(key(j), "v" + j);
                    } else {
                        for (int j = 0; j < 40; j++) ops.put(key(rnd.nextInt(400)), "w" + i + "." + j);
                    }
                    Trans t = build(db, ops);
                    db.execute(t);
                    state.putAll(ops);
                    checkFill(db, at);
                    if (i % 3 == 2) {
                        db.sync(t.lastPos, SyncLevel.ORDINARY);
                        String before = tree(db);
                        db.close();
                        ms = ms.copy();
                        final long c0 = Dag.statCompactions;
                        db = builder(ms, b, sd).start();
                        rerun += Dag.statCompactions - c0;
                        Assert.assertEquals(at + ": the tree after the restart", before, tree(db));
                        checkFill(db, at + ", restarted");
                        checkValues(db, state, 400, at + ", restarted");
                    }
                }
                checkValues(db, state, 400, at0);
                db.close();
                Assert.assertTrue(at0 + ": compactions", Dag.statCompactions > compactions0);
                if (sd > 1000) {
                    Assert.assertTrue(at0 + ": compactions of the reruns", rerun > 0);
                }
            }
        }
    }

    private static DbBuilder builder(MemoryStream ms, int b, int sd) {
        DbBuilder builder = Db.builder().testSetup(ms).startupDistance(sd);
        return b == 14 ? builder.maxNodeSize14() : builder.maxNodeSize30();
    }

    /**
     * Crashes (T7): the same work at node size 8 and a startup distance of 10 bytes, on a
     * CutStream; then for every second transaction of the deletes a copy of the stream cut
     * at that transaction's end and at a byte inside its record: a start gives the state
     * after the last whole transaction, its tree node for node, and BU1.
     */
    @Nano
    public static void testCrashCutsRerunTheMerges() {
        CutStream cs = new CutStream();
        Db db = Db.builder().testSetup(cs).maxNodeSize8().startupDistance(10).start();
        List<TreeMap<String, String>> ts = workload(600, 3, 30, 7);
        List<Long> ends = new ArrayList<Long>();
        List<String> trees = new ArrayList<String>();
        List<TreeMap<String, String>> states = new ArrayList<TreeMap<String, String>>();
        TreeMap<String, String> state = new TreeMap<String, String>();
        for (TreeMap<String, String> ops : ts) {
            Trans t = build(db, ops);
            db.execute(t);
            db.sync(t.lastPos, SyncLevel.ORDINARY);
            for (Map.Entry<String, String> e : ops.entrySet()) {
                if (e.getValue() == null) state.remove(e.getKey());
                else state.put(e.getKey(), e.getValue());
            }
            ends.add(db.getStreamLength());
            trees.add(tree(db));
            states.add(new TreeMap<String, String>(state));
        }
        db.close();
        int puts = 20;              // 600 keys, 30 a transaction
        for (int i = puts; i < ts.size(); i += 2) {
            for (int inside = 0; inside < 2; inside++) {
                long cut = inside == 0 ? ends.get(i) : ends.get(i) - 3;
                int last = inside == 0 ? i : i - 1;
                String at = "transaction " + i + (inside == 0 ? ", its end" : ", inside");
                CutStream c = cs.copy();
                c.truncate(cut);
                Db d = Db.builder().testSetup(c).maxNodeSize8().startupDistance(10).start();
                checkValues(d, states.get(last), 600, at);
                Assert.assertEquals(at + ": the tree", trees.get(last), tree(d));
                checkFill(d, at);
                d.close();
            }
        }
    }

    /**
     * Readers at earlier times while the writer merges (024-21, section 3.6): two threads
     * scan the database at random times of the transactions done, and get keys there, while
     * the writer deletes all but every third of 1,500 keys, at node size 8, with eviction
     * after every transaction (Eviction.Schedule.EVERY), so that readers load nodes through
     * handles that merged nodes share. Every answer is the model's at that time.
     */
    @Nano
    public static void testReadersAcrossMerges() throws InterruptedException {
        final Db db = Db.builder().testSetup().maxNodeSize8().startupDistance(1000)
                .evictionSchedule(Eviction.Schedule.EVERY, 1).start();
        final int n = 1500;
        final List<TreeMap<String, String>> ts = workload(n, 3, 50, 3);
        final List<Long> times = Collections.synchronizedList(new ArrayList<Long>());
        final List<TreeMap<String, String>> states =
                Collections.synchronizedList(new ArrayList<TreeMap<String, String>>());
        final AtomicReference<String> failure = new AtomicReference<String>();
        final boolean[] stop = new boolean[1];
        final long[] reads = new long[1];
        Thread[] readers = new Thread[2];
        for (int r = 0; r < readers.length; r++) {
            final Random rnd = new Random(r);
            readers[r] = new Thread(new Runnable() {
                public void run() {
                    try {
                        while (!stop[0] && failure.get() == null) {
                            int size = times.size();
                            if (size == 0) { Thread.yield(); continue; }
                            int i = rnd.nextInt(size);
                            long time = times.get(i);
                            TreeMap<String, String> st = states.get(i);
                            GetMany g = db.newGetMany();
                            g.lookupTime = time;
                            g.startKey = Keys.toSegments("/m/");
                            g.inclusive = true;
                            db.getMany(g);
                            List<String> got = new ArrayList<String>();
                            for (Kvt kvt : g.result) {
                                String k = Keys.toString(kvt.key);
                                if (k.startsWith("/m/")) got.add(k);
                            }
                            List<String> exp = new ArrayList<String>();
                            for (String k : st.keySet()) if (k.startsWith("/m/")) exp.add(k);
                            if (!exp.equals(got)) {
                                failure.compareAndSet(null, "scan at " + time + ": " + got.size()
                                        + " keys, expected " + exp.size());
                            }
                            int k = rnd.nextInt(n);
                            byte[] vb = DbUtil.get(db, time, key(k));
                            String v = vb == null ? null : bergdb.common.StringUtil.toString(vb);
                            String e = st.get(key(k));
                            if (e == null ? v != null : !e.equals(v)) {
                                failure.compareAndSet(null, "get " + key(k) + " at " + time
                                        + ": " + v + ", expected " + e);
                            }
                            synchronized (reads) { reads[0]++; }
                        }
                    } catch (Throwable e) {
                        failure.compareAndSet(null, "reader: " + e);
                    }
                }
            });
            readers[r].start();
        }
        try {
            TreeMap<String, String> state = new TreeMap<String, String>();
            for (TreeMap<String, String> ops : ts) {
                Trans t = build(db, ops);
                db.execute(t);
                for (Map.Entry<String, String> e : ops.entrySet()) {
                    if (e.getValue() == null) state.remove(e.getKey());
                    else state.put(e.getKey(), e.getValue());
                }
                states.add(new TreeMap<String, String>(state));
                times.add(t.tt);
                checkFill(db, "transaction " + times.size());
                Thread.yield();
            }
        } finally {
            stop[0] = true;
            for (Thread t : readers) {
                t.join(60_000);
                Assert.assertFalse("a reader thread did not end within 60 s", t.isAlive());
            }
            db.close();
        }
        Assert.assertTrue(String.valueOf(failure.get()), failure.get() == null);
        Assert.assertTrue("reads: " + reads[0], reads[0] > 0);
    }
}
