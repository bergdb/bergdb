package bergdb.dag;

import bergdb.core.ActionRoomProbe;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Random;
import java.util.Set;

/**
 * bergdb 028-72: Java's count, Dag.dirtyNodeBound, on trees that the writer PE built, in
 * memory, at node sizes 8, 14 and 30: a key K of six segments whose every segment tree on its
 * path holds N other entries, built in transactions of 1,000 puts in random order, then
 * thinned by deletes of 60 % of them. For the delete of K, and for a transaction of 500
 * deletes, it prints the heights of K's segment trees, Java's count and the count a level
 * (the count over the sum of H + 2 over the segments, H a tree's height on the path), the
 * worst tree of the same heights (ActionRoomProbe's, every node of the path full), and the
 * key nodes that PE marked when the transaction ran (as DagTester's BoundCase counts them).
 */
public class RealTreeProbe {

    static final PointerFollower FOLLOW = new PointerFollower() {
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            final Node result = predecessor.getPointerNode(pointerIndex);
            if (result == null || !Pointer.isMem(result)) {
                throw new IllegalStateException("Not a memory pointer.");
            }
            op.pointerListener.pointerFollowed(predecessor, pointerIndex, result,
                    Pointer.TYPE_MEMORY);
            return result;
        }
    };

    static final class Case {
        final int b;
        final Dag dag;
        final PutData pd;
        final Set<Node> dirty = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        long t = 1;

        Case(int b) {
            this.b = b;
            dag = Dag.createEmpty(0, b, FOLLOW, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
            pd = dag.newPutData();
            pd.pointerFollower = FOLLOW;
            final Dag.PointerListener inner = pd.pointerListener;
            pd.pointerListener = new Dag.PointerListener() {
                public void pointerFollowed(Node pred, int i, Node result, int type) {
                    if (result instanceof KeyNode) dirty.add(result);
                    inner.pointerFollowed(pred, i, result, type);
                }
                public void superRootAccessed(TopNode s) {}
            };
            pd.nodeChangeListener = new Dag.NodeChangeListener() {
                public void topNodeCreated(TopNode node) {}
                public void keyNodeCreated(KeyNode node) { dirty.add(node); }
                public void valueNodeCreated(ValueNode node, long[] key) {}
                public void keyNodeChanged(KeyNode node) { dirty.add(node); }
                public void keyNodeReplaced(KeyNode node) { dirty.remove(node); }
                public void keyNodeOnPath(KeyNode node) { dirty.add(node); }
            };
        }

        GetData gd() {
            final GetData gd = dag.newGetData();
            gd.pointerFollower = FOLLOW;
            return gd;
        }

        /** One transaction: the KVs in key order, a delete with no value. */
        void tx(List<long[]> keys, boolean[] deletes) {
            final Integer[] order = new Integer[keys.size()];
            for (int i = 0; i < order.length; i++) order[i] = i;
            java.util.Arrays.sort(order, (x, y) -> Keys.compareArrays(keys.get(x), keys.get(y)));
            final long[][] k = new long[order.length][];
            final byte[][] v = new byte[order.length][];
            for (int i = 0; i < order.length; i++) {
                k[i] = keys.get(order[i]);
                v[i] = deletes[order[i]] ? null : new byte[] {(byte) t};
            }
            dirty.clear();
            pd.tt = t;
            dag.putKvs(k, v, pd);
            pd.clear();
            t++;
        }

        long bound(List<long[]> keys, boolean[] deletes) {
            return dag.dirtyNodeBound(t - 1, keys.toArray(new long[0][]), deletes, gd());
        }

        /** The key nodes on the path of 'key' in each of its segment trees. */
        int[] levels(long[] key) {
            final int[] levels = new int[key.length];
            final GetData gd = gd();
            final KlongWithPointer kwi = gd.kwi;
            KeyNode node = dag.getTopDs().findRoot(t - 1, gd);
            for (int i = 0; i < key.length; i++) {
                levels[i] = 1;
                while (!node.isSegmentLeaf()) {
                    node.searchLte(t - 1, key[i], kwi);
                    node = (KeyNode) gd.followPointer(node, kwi.pointerIndex);
                    levels[i]++;
                }
                if (i == key.length - 1) break;
                node.searchEq(t - 1, key[i], kwi);
                if (kwi.klong == Klong.NULL) throw new IllegalStateException("not found");
                node = (KeyNode) gd.followPointer(node, kwi.pointerIndex);
            }
            return levels;
        }
    }

    static final Random R = new Random(2807201);

    static byte[] bytes(int n) {
        final byte[] a = new byte[n];
        for (int i = 0; i < n; i++) a[i] = (byte) (0x21 + R.nextInt(0x5e));
        return a;
    }

    static void run(int b, int perTree, int deletes) {
        final Case c = new Case(b);
        final byte[] kBytes = bytes(38);                 // K: five full segments and one of 3
        final long[] kKey = Keys.toSegments(kBytes);
        final List<long[]> others = new ArrayList<long[]>();
        for (int i = 0; i < kKey.length - 1; i++) {
            for (int j = 0; j < perTree; j++) {
                final byte[] o = new byte[7 * i + 9];
                System.arraycopy(kBytes, 0, o, 0, 7 * i);
                System.arraycopy(bytes(9), 0, o, 7 * i, 9);
                others.add(Keys.toSegments(o));
            }
        }
        for (int j = 0; j < perTree; j++) {              // the last segment's tree: K's leaf
            final byte[] o = kBytes.clone();
            System.arraycopy(bytes(3), 0, o, 35, 3);
            others.add(Keys.toSegments(o));
        }
        others.add(kKey);
        final java.util.TreeSet<long[]> distinct = new java.util.TreeSet<long[]>(Keys::compareArrays);
        for (java.util.Iterator<long[]> it = others.iterator(); it.hasNext(); ) {
            if (!distinct.add(it.next())) it.remove();     // a random tail drawn twice
        }
        Collections.shuffle(others, R);
        for (int from = 0; from < others.size(); from += 1000) {
            final List<long[]> batch = others.subList(from, Math.min(others.size(), from + 1000));
            c.tx(batch, new boolean[batch.size()]);
        }
        report(c, "built", kKey, others, deletes);
        final List<long[]> live = new ArrayList<long[]>();
        final List<long[]> gone = new ArrayList<long[]>();
        for (long[] k : others) {
            if (k != kKey && R.nextInt(100) < 60) gone.add(k); else live.add(k);
        }
        for (int from = 0; from < gone.size(); from += 1000) {
            final List<long[]> batch = gone.subList(from, Math.min(gone.size(), from + 1000));
            final boolean[] d = new boolean[batch.size()];
            java.util.Arrays.fill(d, true);
            c.tx(batch, d);
        }
        report(c, "thinned", kKey, live, deletes);
    }

    static void report(Case c, String what, long[] kKey, List<long[]> live, int deletes) {
        final int[] levels = c.levels(kKey);
        long sumH2 = 0;
        for (int l : levels) sumH2 += (l - 1) + 2;
        final Dag.Fill fill = c.dag.checkFill(c.t - 1, c.gd());
        // One delete of K: Java's count, the worst tree of the same heights, the marks.
        final List<long[]> one = new ArrayList<long[]>();
        one.add(kKey);
        final long bound = c.bound(one, new boolean[] {true});
        ActionRoomProbe.levelsBySeg = levels;
        final long worst = ActionRoomProbe.count(c.b, 0, new long[][] {kKey}, new boolean[] {true});
        ActionRoomProbe.levelsBySeg = null;
        final long putBound = c.bound(one, new boolean[] {false});
        System.out.printf("B=%d %s: %,d live keys, %s; K's trees, key nodes on the path: %s%n",
                c.b, what, live.size(), fill.error == null ? "V1, V2, V4 hold" : fill.error,
                java.util.Arrays.toString(levels));
        // 500 deletes of live keys, K among them, at random.
        final List<long[]> dels = new ArrayList<long[]>();
        dels.add(kKey);
        final List<long[]> pool = new ArrayList<long[]>(live);
        Collections.shuffle(pool, R);
        for (long[] k : pool) {
            if (dels.size() == deletes) break;
            if (k != kKey) dels.add(k);
        }
        final boolean[] d = new boolean[dels.size()];
        java.util.Arrays.fill(d, true);
        final long many = c.bound(dels, d);
        long manyH2 = 0;
        for (long[] k : dels) {
            for (int l : c.levels(k)) manyH2 += (l - 1) + 2;
        }
        // The marks are counted for the 500 deletes, K among them; the one delete of K is
        // counted, not run.
        c.tx(dels, d);
        final int marked = c.dirty.size();
        System.out.printf("  one delete of K: Java %,d (%.2f a level), the worst tree of the "
                + "same heights %,d (%.2f a level); one put of K: Java %,d (%.2f a level)%n",
                bound, bound / (double) sumH2, worst, worst / (double) sumH2, putBound,
                putBound / (double) sumH2);
        System.out.printf("  %d deletes at random, K among them: Java %,d (%.2f a level), key "
                + "nodes marked %,d (Java's count %.1f times them)%n", dels.size(), many,
                many / (double) manyH2, marked, many / (double) Math.max(1, marked));
        // Put back what was deleted, so that the next report sees the same keys.
        c.tx(dels, new boolean[dels.size()]);
    }

    public static void main(String[] args) {
        run(8, 30000, 500);
        run(14, 30000, 500);
        run(30, 30000, 500);
        System.out.println("END");
    }
}
