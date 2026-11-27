package bergdb.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Random;
import java.util.Set;

import bergdb.dag.Dag;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.PutData;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.DbException;
import bergdb.stream.MemoryStream;

/**
 * Db.checkDirtyNodes's counts against the key nodes that a transaction marks (bergdb 028-45;
 * 027-08, section 4.2): for each transaction the counts that Db's check computed, told to the
 * test hooks (Db.TestHooks.dirtyNodesCounted, with the walk asked for also where the estimate
 * fits, walkDirtyNodes), the cheap estimate and the walk, and after it the key nodes it
 * marked. The walk is Dag.dirtyNodeBound of the keys; a transaction with a key
 * transformation is counted after its key transformations, with the keys they gave (bergdb
 * 028-50; until then the estimate of the key as given, 028-45's fault, RB-005); a value
 * transformation counts as a put and a delete. Those three ways are what DagTester's bound
 * tests and the tree checker's C-T8 do not reach: they count each key as the put or the
 * delete it is (030-39, F7).
 */
public class DbTesterDirtyCount {

    /**
     * The key nodes that the transaction being executed marks, as Db marks them (Db.putKvs,
     * endOfOp, endOfTrans): the key nodes that the Dag follows, makes, appends to or reports
     * on the path of its change, if the transaction changes anything, less those it
     * replaces. Counted from Db's own listeners on x.putData, wrapped, as DagTester's
     * BoundCase counts them on a Dag; that is at least C-T8's count (markedKeyNodes in
     * lean/SIS/Tree/Bound.lean: the nodes on the access path of the change, and those it
     * makes), as every such node is followed or made by the writer and is not replaced.
     */
    private static final class Marks {
        final Set<Node> marked = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        final Set<Node> replaced = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        boolean changed = false;

        /** The user transaction that the test executes, and its count, -1 until executed. */
        Trans trans;
        long count = -1;

        /** Db's counts of 'trans' (Db.TestHooks.dirtyNodesCounted), and how many times. */
        Db.DirtyNodeCounts counts;
        int counted;

        /** Before 'trans' is executed. */
        void expect(Trans t) {
            trans = t;
            count = -1;
            counts = null;
            counted = 0;
            clear();
        }

        void clear() {
            marked.clear();
            replaced.clear();
            changed = false;
        }

        void install(Db db) {
            final PutData pd = db.internal().x().putData;
            final Dag.NodeChangeListener nc = pd.nodeChangeListener;
            final Dag.PointerListener pl = pd.pointerListener;
            pd.nodeChangeListener = new Dag.NodeChangeListener() {
                public void topNodeCreated(TopNode node) {
                    changed = true;
                    nc.topNodeCreated(node);
                }
                public void keyNodeCreated(KeyNode node) {
                    marked.add(node);
                    changed = true;
                    nc.keyNodeCreated(node);
                }
                public void valueNodeCreated(ValueNode node, long[] key) {
                    changed = true;
                    nc.valueNodeCreated(node, key);
                }
                public void keyNodeChanged(KeyNode node) {
                    marked.add(node);
                    changed = true;
                    nc.keyNodeChanged(node);
                }
                public void keyNodeReplaced(KeyNode node) {
                    replaced.add(node);
                    nc.keyNodeReplaced(node);
                }
                public void keyNodeOnPath(KeyNode node) {
                    marked.add(node);
                    nc.keyNodeOnPath(node);
                }
                public void topNodeReplaced(TopNode node) {
                    nc.topNodeReplaced(node);
                }
            };
            pd.pointerListener = new Dag.PointerListener() {
                public void superRootAccessed(TopNode superRoot) {
                    pl.superRootAccessed(superRoot);
                }
                public void pointerFollowed(Node pred, int i, Node result, int type) {
                    if (result instanceof KeyNode) marked.add(result);
                    pl.pointerFollowed(pred, i, result, type);
                }
            };
            Db.testHooks = new Db.TestHooks() {
                public void transExecuted(Db.ExecuteData x) {
                    // Reclaim's internal transactions, if any, run after the user's: each
                    // counts its own marks, and only the user's is kept.
                    if (x.trans == trans) {
                        long n = 0;
                        if (changed) {
                            for (Node node : marked) if (!replaced.contains(node)) n++;
                        }
                        count = n;
                    }
                    clear();
                }
                public void valueNodeCreated(ValueNode node, long[] key) {}
                public void nodeTouched(Node node) {}
                public void nodeReplaced(Node node) {}
                public void dirtyNodesCounted(Trans t, Db.DirtyNodeCounts c) {
                    if (t == trans) {
                        counts = c;
                        counted++;
                    }
                }
                public boolean walkDirtyNodes() {
                    return true;
                }
            };
        }
    }

    /** A transformation that gives the value v, null for a delete. */
    private static ValueTransformation give(final byte[] v) {
        return new ValueTransformation() {
            public byte[] transform(long transTime, byte[] in, byte[] previous) {
                return v;
            }
        };
    }

    /** A key transformation to 'key'; with 'withTime', the transaction's time after it. */
    private static KeyTransformation toKey(final String key, final boolean withTime) {
        return new KeyTransformation() {
            public void transform(Trans trans, int index) {
                long[] k = Keys.toSegments(withTime ? key + trans.tt : key);
                trans.kvs[index].setKey(k);
                trans.writeKeyHashes[index] = Keys.hash(k);
            }
        };
    }

    /** 'prefix' and letters after it, 'len' bytes in all. */
    private static String longKey(String prefix, int len) {
        final StringBuilder s = new StringBuilder(prefix);
        while (s.length() < len) s.append((char) ('a' + s.length() % 26));
        return s.toString();
    }
    
    /** The test's state of one database: the keys present, the counts of the two ways. */
    private static final class Run {
        final int b;
        final long seed;
        final Db db;
        final Marks marks = new Marks();
        final Set<String> live = new HashSet<String>();
        final Random r;
        int checked, fits, walks, refused, longKeys;
        int afterKt;            // counted after their key transformations (bergdb 028-50)
        int kt = 0;             // the key transformations' targets so far, for unique keys

        Run(int b, long seed) {
            this.b = b;
            this.seed = seed;
            this.r = new Random(seed);
            DbBuilder builder = Db.builder().testSetup(new MemoryStream());
            db = (b == 8 ? builder.maxNodeSize8() : builder.maxNodeSize30()).start();
            marks.install(db);
        }

        /** Key i of the database: one segment ("k00012") or two ("/p000/x00512"). */
        String key(int i) {
            return i % 2 == 0 ? String.format("k%05d", i)
                    : String.format("/p%03d/x%05d", i / 64, i);
        }

        /**
         * Executes t, whose keys after the transformations are 'present' and 'absent' (the
         * deletes), and checks the key nodes it marks against the counts of Db's check
         * (Db.TestHooks.dirtyNodesCounted): counted once, after the key transformations if it
         * has one (bergdb 028-50). A transaction that the check refuses marks nothing. 'what'
         * names it in a failure.
         */
        void check(String what, Trans t, Set<String> present, Set<String> absent) {
            boolean kt = false;
            for (Kv kv : t.kvs) kt |= kv.keyTransformation != null;
            marks.expect(t);
            final String at = "node size " + b + ", seed " + seed + ", transaction " + checked
                    + " (" + what + ", " + t.kvs.length + " operations): ";
            DbException refusal = null;
            try {
                db.execute(t);
            } catch (DbException e) {
                refusal = e;
            }
            if (refusal != null) {
                // Only by the walk (bergdb 005-31).
                Assert.assertTrue(at + refusal.getMessage(),
                        refusal.getMessage().contains("005-31"));
            }
            final Db.DirtyNodeCounts c = marks.counts;
            Assert.assertTrue(at + "counted once: " + marks.counted, marks.counted == 1);
            Assert.assertTrue(at + "counted after the key transformations: " + kt,
                    c.afterKeyTransformations == kt);
            Assert.assertTrue(at + "not walked", c.walked >= 0);
            final boolean fit = c.estimate <= c.maxNodes;
            if (refusal != null) {
                // Refused by the walk: nothing marked, nothing changed.
                Assert.assertTrue(at + "refused, the walk " + c.walked + " within "
                        + c.maxNodes, c.refused());
                Assert.assertTrue(at + "marks of a refused transaction", marks.count == -1);
                refused++;
                checked++;
                return;
            }
            Assert.assertTrue(at + "a walk of " + c.walked + " over " + c.maxNodes
                    + " was taken", !c.refused());
            Assert.assertTrue(at + "no count of the marks", marks.count >= 0);
            final long m = marks.count;
            Assert.assertTrue(at + m + " key nodes marked, more than the walk's count "
                    + c.walked + " (estimate " + c.estimate + ")", m <= c.walked);
            if (fit) {
                Assert.assertTrue(at + m + " key nodes marked, more than the estimate "
                        + c.estimate + ", which fits the limit " + c.maxNodes, m <= c.estimate);
                fits++;
            } else {
                walks++;
            }
            if (kt) {
                afterKt++;
            }
            live.removeAll(absent);
            live.addAll(present);
            checked++;
        }

        /** The keys of the database, loaded in transactions of plain puts. */
        void load(int n) {
            for (int i0 = 0; i0 < n; i0 += 400) {
                Trans.Builder tb = db.trans();
                Set<String> ps = new HashSet<String>();
                for (int i = i0; i < Math.min(n, i0 + 400); i++) {
                    tb.put(key(i), "v");
                    ps.add(key(i));
                }
                check("load", tb.build(), ps, new HashSet<String>());
            }
        }

        /**
         * A transaction of random operations, 'ops' of them on the keys 0 to n - 1: plain
         * puts and deletes, value transformations that give a value or null (a delete of a
         * present key, nothing on an absent one), key transformations to another key of the
         * database (a put, or with a transformation to null a delete) or to a new key of more
         * segments than the key as given.
         */
        void random(int n, int ops) {
            Trans.Builder tb = db.trans();
            Set<String> used = new HashSet<String>();
            Set<String> ps = new HashSet<String>(), ds = new HashSet<String>();
            for (int j = 0; j < ops; j++) {
                String k = key(r.nextInt(n));
                if (!used.add(k)) continue;
                final int kind = r.nextInt(8);
                switch (kind) {
                case 0:                                 // a plain put
                    tb.put(k, "p");
                    ps.add(k);
                    break;
                case 1:                                 // a plain delete
                    tb.delete(k);
                    ds.add(k);
                    break;
                case 2:                                 // a value transformation, a value
                    tb.put(Keys.toSegments(k), null, new byte[0], give(new byte[] {7}));
                    ps.add(k);
                    break;
                case 3:                                 // a transformation to null
                case 4:
                    tb.put(Keys.toSegments(k), null, new byte[0], give(null));
                    ds.add(k);
                    break;
                case 5:                                 // a key transformation to k
                case 6: {
                    // As given, a key of one segment that no other KV has.
                    final String given = String.format("q%04d", kt++ % 10000);
                    final boolean del = kind == 6 && r.nextBoolean();
                    tb.put(Keys.toSegments(given), toKey(k, false), new byte[] {1},
                            del ? give(null) : null);
                    (del ? ds : ps).add(k);
                    break;
                }
                default: {                              // to a longer new key
                    // A key of one segment as given, of up to 16 after the transformation
                    // (L2, 111 bytes), its last bytes the transaction's time.
                    final boolean del = r.nextInt(4) == 0;
                    tb.put(Keys.toSegments("z"),
                            toKey(longKey("/L" + (kt++) + "/", 20 + r.nextInt(80)), true),
                            new byte[] {2}, del ? give(null) : null);
                    longKeys++;
                    break;
                }
                }
            }
            check("random", tb.build(), ps, ds);
        }
    }

    /**
     * The counts of checkDirtyNodes against the key nodes marked, at node sizes 8 and 30 (bergdb
     * 028-45), with the record limit lowered to 4 MB so that a transaction of a few deletes
     * takes the walk: loads of plain puts; deletes by value transformations of most keys
     * under a few nodes, which join nodes; random transactions of plain puts and deletes,
     * value transformations to a value and to null on present and absent keys, and key
     * transformations to keys of the database and to longer new keys, each such transaction
     * counted after its key transformations (bergdb 028-50). Both ways of checkDirtyNodes are
     * reached: an estimate within the limit, and one over it that is walked.
     */
    @Nano
    public static void testCountsCoverMarkedKeyNodes() {
        final long savedLimit = StoredTrans.recordLimit;
        StoredTrans.recordLimit = 4 * 1000 * 1000;
        try {
            for (int b : new int[] {8, 30}) {
                final Run run = new Run(b, 28045 + b);
                try {
                    final int n = b == 8 ? 1200 : 6000;
                    // At the start, with the stream short and 'height' small: key
                    // transformations of a key of one segment to a new key of 15 or 16.
                    for (int cnt : new int[] {1, 1, 5, 50}) {
                        Trans.Builder tb = run.db.trans();
                        for (int q = 0; q < cnt; q++) {
                            tb.put(Keys.toSegments(String.format("g%04d", q)),
                                    toKey(longKey("/F" + (run.kt++) + "/", 100), true),
                                    new byte[] {3}, null);
                        }
                        run.longKeys += cnt;
                        run.check("long keys at the start", tb.build(), new HashSet<String>(),
                                new HashSet<String>());
                    }
                    run.load(n);

                    // Most keys of a range deleted by value transformations, in two
                    // transactions: two of three keys, then two of three of those left, so
                    // that nodes fall under m entries and are joined.
                    for (int rep = 0; rep < 2; rep++) {
                        final long joins0 = Dag.statJoins;
                        final int lo = run.r.nextInt(n - 12 * b);
                        for (int pass = 0; pass < 2; pass++) {
                            Trans.Builder tb = run.db.trans();
                            Set<String> ds = new HashSet<String>();
                            for (int i = lo; i < lo + 12 * b; i++) {
                                final String k = run.key(i);
                                if ((pass == 0 ? i % 3 != 0 : i % 9 != 0)
                                        && run.live.contains(k)) {
                                    tb.put(Keys.toSegments(k), null, new byte[0], give(null));
                                    ds.add(k);
                                }
                            }
                            // An absent key, which the transformation leaves absent.
                            tb.put(Keys.toSegments("absent"), null, new byte[0], give(null));
                            run.check("joins", tb.build(), new HashSet<String>(), ds);
                        }
                        // The keys left, one delete by a value transformation a transaction:
                        // a node under m entries joined with a sibling off the key's path.
                        for (int i = lo; i < lo + 12 * b; i++) {
                            final String k = run.key(i);
                            if (run.live.contains(k) && run.r.nextBoolean()) {
                                Trans.Builder tb = run.db.trans();
                                tb.put(Keys.toSegments(k), null, new byte[0], give(null));
                                Set<String> ds = new HashSet<String>();
                                ds.add(k);
                                run.check("one delete", tb.build(), new HashSet<String>(), ds);
                            }
                        }
                        Assert.assertTrue("node size " + b + ": joins", Dag.statJoins > joins0);
                    }
                    
                    for (int i = 0; i < 60; i++) {
                        final int ops = i % 3 == 0 ? 1 + run.r.nextInt(4)
                                : 1 + run.r.nextInt(i % 3 == 1 ? 30 : 300);
                        run.random(n, ops);
                    }
                    final String at = "node size " + b + ": ";
                    Assert.assertTrue(at + "estimates within the limit: " + run.fits, 
                            run.fits > 0);
                    Assert.assertTrue(at + "estimates over the limit, walked: " + run.walks, 
                            run.walks > 0);
                    Assert.assertTrue(at + "keys transformed to longer keys: " + run.longKeys, 
                            run.longKeys > 0);
                    Assert.assertTrue(at + "counted after key transformations: " + run.afterKt,
                            run.afterKt > 0);
                } finally {
                    Db.testHooks = null;
                    run.db.close();
                }
            }
        } finally {
            StoredTrans.recordLimit = savedLimit;
        }
    }
    
    /**
     * The database of 028-45's case at node size 8: a prefix of 105 bytes, 15 segments, and
     * 40 keys after each of its first 0 to 14 segments, "v00000" to "v00039" after the
     * prefix's first 7 lv bytes, so that each of the 15 segment trees on the prefix's path is
     * three levels high; a stream of 64 kB, 'height' 12. Returns the prefix.
     */
    private static String deepPrefix(Run run) {
        final String prefix = longKey("", 105);
        List<String> all = new ArrayList<String>();
        for (int lv = 0; lv <= 14; lv++) {
            for (int v = 0; v < 40; v++) {
                all.add(prefix.substring(0, 7 * lv) + String.format("v%05d", v));
            }
        }
        for (int i0 = 0; i0 < all.size(); i0 += 300) {
            Trans.Builder tb = run.db.trans();
            for (int i = i0; i < Math.min(all.size(), i0 + 300); i++) tb.put(all.get(i), "v");
            run.db.execute(tb.build());
        }
        return prefix;
    }

    /** The set of the keys given. */
    private static Set<String> keys(String... keys) {
        return new HashSet<String>(Arrays.asList(keys));
    }

    /**
     * A key transformed to a key of more segments, counted after its key transformation
     * (bergdb 028-50; until then 028-45's known fault, RB-005, which this test asserted). A
     * key of one segment transformed to one of 16, under a prefix whose 15 segment trees are
     * each three levels high (deepPrefix), marks 46 key nodes on its path (3 of each tree and
     * a new one), at node size 8. Until 028-50 the check counted it with the key as given:
     * 3 nodes a level of 'height' 12, and 3, 39 nodes, by the estimate and in the walk. Now
     * the count is of the key of 16 segments: the estimate, 579, which fits the default limit,
     * and the walk, each at least the marks (Run.check). Deterministic: no random choice.
     */
    @Nano
    public static void testKeyTransformationToDeeperKey() {
        final Run run = new Run(8, 0);
        try {
            final String prefix = deepPrefix(run);
            Trans.Builder tb = run.db.trans();
            tb.put(Keys.toSegments("g"), toKey(prefix + "zzzzz", false), new byte[] {3}, null);
            run.check("to a deeper key", tb.build(), keys(prefix + "zzzzz"), keys());
            final Db.DirtyNodeCounts c = run.marks.counts;
            final long m = run.marks.count;
            final long asGiven = (c.estimate - 3) / 16 + 3;     // one segment, not 16
            Assert.assertTrue("counted after the key transformation", c.afterKeyTransformations);
            Assert.assertTrue("the estimate fits: " + c.estimate, c.estimate <= c.maxNodes);
            Assert.assertTrue("028-45's case: " + m + " key nodes marked, more than the count of "
                    + "the key as given, " + asGiven, m > asGiven);
            Assert.assertTrue("at most the counts: " + m + ", the estimate " + c.estimate
                    + ", the walk " + c.walked, m <= c.estimate && m <= c.walked);
            Assert.assertTrue("the key", DbUtil.get(run.db, prefix + "zzzzz") != null);
        } finally {
            Db.testHooks = null;
            run.db.close();
        }
    }

    /**
     * The check after the key transformations refuses a transaction and lets one through
     * (bergdb 028-50): the database of deepPrefix, the record limit lowered to 11,150 bytes, so
     * that an action is admitted with 42 index nodes at node size 8 (10,400 bytes until bergdb
     * 031-06, which leaves an eighth of the limit to the step that the record may carry,
     * StoredTrans.actionDirtyLimit()). The put of "g" transformed to the key
     * of 16 segments (testKeyTransformationToDeeperKey) is refused, its estimate (579) and its
     * walk over 42; until 028-50 it was taken, counted 39 with the key as given. Its key as
     * written, its write hash and the time are given back, nothing is written, and the
     * database goes on. A put of a key of 16 segments as given, transformed to "h", of one, is
     * taken, its estimate within 42; until 028-50 it was refused, counted 579 with the key as
     * given. With the limit restored, the refused transaction run again is taken and marks
     * more key nodes than the lowered limit's record takes: it could not have been written in
     * one record there.
     */
    @Nano
    public static void testRefusedAfterKeyTransformations() {
        final long savedLimit = StoredTrans.recordLimit;
        final Run run = new Run(8, 0);
        try {
            final Db db = run.db;
            final String prefix = deepPrefix(run);
            final String deep = prefix + "zzzzz";
            final long[] g = Keys.toSegments("g");
            final Trans t = db.trans().put(g, toKey(deep, false), new byte[] {3}, null).build();
            final long hash = t.writeKeyHashes[0];
            final long length = db.getStreamLength();
            final long count = db.getTransactionCount();
            final long ttBefore = t.tt;
            StoredTrans.recordLimit = 11150;
            
            run.marks.expect(t);
            try {
                db.execute(t);
                throw new AssertionError("taken: a key transformation over the limit");
            } catch (DbException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("005-31")
                        && e.getMessage().contains("after its key transformations"));
            }
            final Db.DirtyNodeCounts c = run.marks.counts;
            final long asGiven = (c.estimate - 3) / 16 + 3;
            Assert.assertTrue("counted once, after the key transformation: " + run.marks.counted,
                    run.marks.counted == 1 && c.afterKeyTransformations);
            Assert.assertTrue("refused: the estimate " + c.estimate + ", the walk " + c.walked
                    + ", a record " + c.maxNodes, c.refused());
            Assert.assertTrue("the count of the key as given, " + asGiven + ", within "
                    + c.maxNodes + ", as until 028-50", asGiven <= c.maxNodes);
            Assert.assertTrue("the key as written, given back",
                    Arrays.equals(g, t.kvs[0].getKey()) && t.writeKeyHashes[0] == hash);
            Assert.assertTrue("nothing appended", length == db.getStreamLength());
            Assert.assertTrue("no transaction", count == db.getTransactionCount());
            Assert.assertTrue("t.tt given back", t.tt == ttBefore);
            Assert.assertTrue("not put", DbUtil.get(db, deep) == null);
            
            // A key of 16 segments as given, of one after its transformation: taken.
            final Trans t2 = db.trans().put(Keys.toSegments(prefix + "zzzzy"), toKey("h", false),
                    new byte[] {4}, null).build();
            run.check("to a shorter key", t2, keys("h"), keys());
            final Db.DirtyNodeCounts c2 = run.marks.counts;
            final long asGiven2 = (c2.estimate - 3) * 16 + 3;   // 16 segments, not one
            Assert.assertTrue("the estimate within the limit: " + c2.estimate + ", "
                    + c2.maxNodes, c2.estimate <= c2.maxNodes);
            Assert.assertTrue("the count of the key as given, " + asGiven2 + ", over "
                    + c2.maxNodes + ", as until 028-50", asGiven2 > c2.maxNodes);
            Assert.assertTrue("the key", DbUtil.get(db, "h") != null);
            
            // The refused transaction again, with the limit restored: taken, and its marks
            // more than the lowered limit's record takes.
            StoredTrans.recordLimit = savedLimit;
            run.check("again", t, keys(deep), keys());
            Assert.assertTrue("marks " + run.marks.count + ", more than " + c.maxNodes,
                    run.marks.count > c.maxNodes);
            Assert.assertTrue("the key", DbUtil.get(db, deep) != null);
        } finally {
            StoredTrans.recordLimit = savedLimit;
            Db.testHooks = null;
            run.db.close();
        }
    }
}
