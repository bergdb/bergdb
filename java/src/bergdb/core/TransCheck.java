package bergdb.core;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.WeakHashMap;

import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.KlongWithPointer;
import bergdb.dag.Node;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;

/**
 * Java's own check of the writer's contract (bergdb 030-09, section 3; the contract is
 * 030-04, section 3.2, in Lean lean/contract/Contract/Statement.lean), test-only: on with the
 * system property transcheck=1, off by default; the unit tests and the f-tests run with it
 * (before-commit.sh, unit.sh, f.sh). Db calls it at the start and at the end of each
 * transaction's puts (Db.putKvs), under the write lock, and tells it the key nodes the
 * transaction made, changed, replaced and took back (Dag.NodeChangeListener). It checks what
 * can be checked on those nodes and their neighbours, without a read of the stream: a pointer
 * to a node that is not in memory ends the check there. Nothing is changed.
 *
 * <p>Two walks from the space root, through the live klongs, at the transaction's time tt and
 * at tt - 1, visit the nodes on the paths of the transaction's keys and every node made,
 * changed or replaced that they reach from such a node.</p>
 *
 * <ol>
 * <li><b>Clause 1, the invariants</b>, on each node the walk at tt visits: at most M klongs;
 * W1 to W4 (the first klong is a time klong and the times increase; a bitmap deletes only
 * key klongs before it, holds the bits of the bitmap before it, and deletes every earlier
 * klong of a compare value it deletes); every key klong has a pointer; a live klong, unless it
 * is the space root and a segment leaf; the key order (every live compare value below the
 * range's end, in a segment leaf at or above its start). On every live child, in memory, of
 * a node made or changed: its kind (an inner node's child a key node; a segment leaf's child a
 * key node with a live klong for a long segment, a value for any other) and the key order in
 * it. No node is reached twice (beyond the contract: TREE, 030-06, finding 3).</li>
 * <li><b>Clause 2, the contents</b>: each key of the transaction has its new value at tt, or
 * none if deleted; every other key of a segment leaf made, changed or replaced has the same
 * value at tt - 1 and at tt.</li>
 * <li><b>Clause 3, the frame</b>, on each node it has seen before (after an earlier
 * transaction): the node keeps its klongs, and the klongs added after them start with a time
 * klong of tt; a node replaced keeps them all. A node made or changed is dirty (in D), unless
 * replaced or taken back. Beyond the contract (030-06, finding 4): every time klong of a node
 * made is of tt.</li>
 * <li><b>The search</b>: in each node made or changed, KeyNode.searchEq of each live compare
 * value at tt finds the klong that the contract's live klongs name (Contract/Tree.lean,
 * live).</li>
 * </ol>
 *
 * <p>Not local, so not checked here: that a node not in D is unchanged, the key order and the
 * kinds beyond the nodes visited, the levels, and the contents beyond the leaves touched. The
 * traces check them (lean/contract/check.sh). A failure throws an AssertionError, which fails
 * the transaction's database (Db.fail) and so the test.</p>
 */
final class TransCheck {
    /** On with the system property transcheck=1 (bergdb 030-09); off by default. */
    static final boolean ON = "1".equals(System.getProperty("transcheck"));

    private static final long NONE = Long.MAX_VALUE;     // no end of a range
    private static final Object UNKNOWN = new Object();  // a read met a node not in memory

    private static long transactions, visited, made, unreached, reads, keys, faultsFound;
    private static String firstFailure;

    /** True while TransCheckTester makes a fault on purpose: its failure is counted apart. */
    static volatile boolean faultTest = false;

    static {
        if (ON) {
            Runtime.getRuntime().addShutdownHook(new Thread() {
                public void run() {
                    System.out.println(summary());
                }
            });
        }
    }

    /** One line: what was checked in this process. */
    static synchronized String summary() {
        return "TRANSCHECK: " + transactions + " transactions, " + visited + " nodes visited, "
                + made + " made, " + unreached + " made or changed and not reached, " + keys
                + " keys of the transactions, " + reads + " reads, " + faultsFound
                + " faults made on purpose found; "
                + (firstFailure == null ? "no failure" : "first failure: " + firstFailure);
    }

    private final int maxNodeSize;
    /** Each node seen after a transaction: its size and the hash of its klongs then. */
    private final WeakHashMap<KeyNode, long[]> seen = new WeakHashMap<KeyNode, long[]>();
    private final IdentityHashMap<KeyNode, Boolean> madeNodes = new IdentityHashMap<KeyNode, Boolean>();
    private final IdentityHashMap<KeyNode, Boolean> changed = new IdentityHashMap<KeyNode, Boolean>();
    private final IdentityHashMap<KeyNode, Boolean> replaced = new IdentityHashMap<KeyNode, Boolean>();
    private final IdentityHashMap<KeyNode, Boolean> takenBack = new IdentityHashMap<KeyNode, Boolean>();
    private final KlongWithPointer kwi = new KlongWithPointer();
    private KeyNode rootBefore;
    private long tt;

    TransCheck(int maxNodeSize) {
        this.maxNodeSize = maxNodeSize;
    }

    void made(KeyNode x) {
        madeNodes.put(x, Boolean.TRUE);
    }

    void changed(KeyNode x) {
        changed.put(x, Boolean.TRUE);
    }

    void replaced(KeyNode x) {
        replaced.put(x, Boolean.TRUE);
    }

    void takenBack(KeyNode x) {
        takenBack.put(x, Boolean.TRUE);
    }

    /** Before the puts of the transaction at time tt; superRoot, the super root then. */
    void begin(TopNode superRoot, long tt) {
        madeNodes.clear();
        changed.clear();
        replaced.clear();
        takenBack.clear();
        this.tt = tt;
        rootBefore = rootOf(superRoot);
    }

    /**
     * After the puts of the transaction, with its KVs in the order the Dag got them; superRoot,
     * the super root now. Throws AssertionError on a failure.
     */
    void end(TopNode superRoot, Kv[] kvs) {
        try {
            check(superRoot, kvs);
        } catch (AssertionError e) {
            synchronized (TransCheck.class) {
                if (faultTest) {
                    faultsFound++;
                } else if (firstFailure == null) {
                    firstFailure = e.getMessage();
                }
            }
            throw e;
        }
    }

    private void check(TopNode superRoot, Kv[] kvs) {
        KeyNode rootAfter = rootOf(superRoot);
        long[][] txKeys = new long[kvs.length][];
        for (int i = 0; i < kvs.length; i++) txKeys[i] = kvs[i].getKey();

        Walk after = new Walk(tt, true, txKeys);
        if (rootAfter != null) after.walk(rootAfter, all(kvs.length));
        Walk before = new Walk(tt - 1, false, txKeys);
        if (rootBefore != null) before.walk(rootBefore, all(kvs.length));

        // Clause 2: the transaction's keys, and the other keys of the leaves it touched.
        HashMap<KeyOf, Boolean> isTxKey = new HashMap<KeyOf, Boolean>();
        for (int i = 0; i < kvs.length; i++) {
            isTxKey.put(new KeyOf(txKeys[i]), Boolean.TRUE);
            if (rootAfter == null) continue;
            Object r = get(rootAfter, tt, txKeys[i]);
            if (r == UNKNOWN) continue;
            byte[] v = kvs[i].getValue();
            if (v == null ? r != null : !(r instanceof ValueNode
                    && Arrays.equals(((ValueNode) r).getValue(), v))) {
                fail("the key " + Arrays.toString(txKeys[i]) + " of the transaction has "
                        + (r == null ? "no value" : "another value") + " after it");
            }
        }
        if (rootAfter != null) compare(before.contents, rootAfter, tt, isTxKey, "is lost or changed");
        if (rootBefore != null) compare(after.contents, rootBefore, tt - 1, isTxKey, "is new or changed");

        // Clause 3: the frame, on every node seen before; D.
        for (KeyNode x : after.visited.keySet()) frame(x);
        for (KeyNode x : before.visited.keySet()) frame(x);
        for (KeyNode x : changed.keySet()) frame(x);
        for (KeyNode x : replaced.keySet()) {
            if (takenBack.containsKey(x)) continue;
            frame(x);
            long[] s = seen.get(x);
            if (s != null && x.size != s[0]) fail(name(x) + " was replaced, and has klongs added");
        }
        long count = 0;
        for (KeyNode x : madeNodes.keySet()) {
            if (takenBack.containsKey(x) || replaced.containsKey(x)) continue;
            count++;
            if (!x.isDirty()) fail(name(x) + " was made, and is not dirty (not in D)");
            for (int i = 0; i < x.size; i++) {
                long k = x.klongs[i];
                if (Klong.getIntType(k) == Klong.INT_TYPE_TIME && Klong.getTime(k) != tt) {
                    fail(name(x) + " was made, with a time klong of " + Klong.getTime(k) + ", not " + tt);
                }
            }
        }
        long notReached = 0;
        for (KeyNode x : changed.keySet()) {
            if (takenBack.containsKey(x) || replaced.containsKey(x)) continue;
            if (!x.isDirty()) fail(name(x) + " was changed, and is not dirty (not in D)");
            if (!after.visited.containsKey(x)) notReached++;
        }
        for (KeyNode x : madeNodes.keySet()) {
            if (takenBack.containsKey(x) || replaced.containsKey(x)) continue;
            if (!after.visited.containsKey(x) && !changed.containsKey(x)) notReached++;
        }

        // The snapshots for the next transaction.
        for (KeyNode x : after.visited.keySet()) snapshot(x);
        for (KeyNode x : changed.keySet()) snapshot(x);
        for (KeyNode x : madeNodes.keySet()) snapshot(x);
        synchronized (TransCheck.class) {
            transactions++;
            visited += after.visited.size() + before.visited.size();
            made += count;
            unreached += notReached;
            keys += kvs.length;
            reads += kvs.length + before.contents.size() + after.contents.size();
        }
    }

    /** Every key of 'contents' but the transaction's has the same value at time t. */
    private void compare(Map<KeyOf, Object> contents, KeyNode root, long t,
            Map<KeyOf, Boolean> isTxKey, String what) {
        for (Map.Entry<KeyOf, Object> e : contents.entrySet()) {
            if (isTxKey.containsKey(e.getKey())) continue;
            Object v = e.getValue();
            if (v == UNKNOWN) continue;
            Object r = get(root, t, e.getKey().key);
            if (r == UNKNOWN) continue;
            if (!(r instanceof ValueNode) || !Arrays.equals(((ValueNode) r).getValue(),
                    ((ValueNode) v).getValue())) {
                fail("the key " + e.getKey() + ", not of the transaction, " + what);
            }
        }
    }

    /** The frame of node x if it was seen before. */
    private void frame(KeyNode x) {
        long[] s = seen.get(x);
        if (s == null) return;
        int n = (int) s[0];
        if (x.size < n) fail(name(x) + " lost klongs: " + x.size + " now, " + n + " before");
        if (hash(x, n) != s[1]) fail(name(x) + " has a klong changed");
        if (x.size > n) {
            long k = x.klongs[n];
            if (Klong.getIntType(k) != Klong.INT_TYPE_TIME || Klong.getTime(k) != tt) {
                fail(name(x) + " got klongs that do not start with a time klong of " + tt);
            }
            if (!x.isDirty() && !replaced.containsKey(x)) {
                fail(name(x) + " got klongs and is not dirty (not in D)");
            }
        }
    }

    private void snapshot(KeyNode x) {
        if (takenBack.containsKey(x)) return;
        seen.put(x, new long[] {x.size, hash(x, x.size)});
    }

    private static long hash(KeyNode x, int n) {
        long h = 0xcbf29ce484222325L;
        long[] ks = x.klongs;
        for (int i = 0; i < n; i++) {
            h ^= ks[i];
            h *= 0x100000001b3L;
        }
        return h;
    }

    private static KeyNode rootOf(TopNode superRoot) {
        if (superRoot == null) return null;
        Node n = superRoot.getPointerNode(0);
        return n instanceof KeyNode ? (KeyNode) n : null;
    }

    private static String name(KeyNode x) {
        return "key node " + x.getId();
    }

    private static void fail(String what) {
        throw new AssertionError("transcheck (bergdb 030-09): " + what);
    }

    private static int[] all(int n) {
        int[] r = new int[n];
        for (int i = 0; i < n; i++) r[i] = i;
        return r;
    }

    /**
     * Java's get of key at time t from the space root, in memory only (KeyNode.searchLte in an
     * inner node, searchEq in a segment leaf, as Dag.getOne): the value node, null if the key has
     * none, or UNKNOWN if a pointer leads out of memory.
     */
    private Object get(KeyNode root, long t, long[] key) {
        KeyNode x = root;
        int d = 0;
        for (int guard = 0; guard < 100000; guard++) {
            if (x.isSegmentLeaf()) {
                x.searchEq(t, key[d], kwi);
                if (kwi.klong == Klong.NULL) return null;
                Node y = kwi.node;
                if (y == null) return UNKNOWN;
                if (d == key.length - 1) return y instanceof ValueNode ? y : UNKNOWN;
                if (!(y instanceof KeyNode)) return UNKNOWN;
                x = (KeyNode) y;
                d++;
            } else {
                x.searchLte(t, key[d], kwi);
                if (kwi.klong == Klong.NULL) return null;
                if (!(kwi.node instanceof KeyNode)) return UNKNOWN;
                x = (KeyNode) kwi.node;
            }
        }
        fail("a get of " + Arrays.toString(key) + " does not end");
        return null;
    }

    /** The live klongs of x at time t: their compare values and indexes, by compare value. */
    private static int live(KeyNode x, long t, long[] cvs, int[] idx) {
        int sz = x.size;
        long[] ks = x.klongs;
        int end = sz;
        long bitmap = Klong.DELETE_NONE_BITMAP;
        for (int i = 0; i < sz; i++) {
            long k = ks[i];
            int type = Klong.getIntType(k);
            if (type == Klong.INT_TYPE_TIME && Klong.getTime(k) > t) {
                end = i;
                break;
            }
            if (type == Klong.INT_TYPE_DELETE_BITMAP) bitmap = k;
        }
        int n = 0;
        for (int i = 0; i < end; i++) {
            long k = ks[i];
            if (Klong.getIntType(k) != Klong.INT_TYPE_KEY || Klong.isDeleted(bitmap, i)) continue;
            long c = Klong.getCompareValue(k);
            int j = 0;
            while (j < n && cvs[j] < c) j++;
            if (j < n && cvs[j] == c) {
                idx[j] = i;
            } else {
                System.arraycopy(cvs, j, cvs, j + 1, n - j);
                System.arraycopy(idx, j, idx, j + 1, n - j);
                cvs[j] = c;
                idx[j] = i;
                n++;
            }
        }
        return n;
    }

    /** A segment of 7 bytes: the key goes on in the next segment's tree. */
    private static boolean isLong(long cv) {
        return Klong.getLength(cv) == 7;
    }

    /** W1 to W4, at most M klongs, a pointer for every key klong. */
    private void nodeCheck(KeyNode x) {
        int sz = x.size;
        long[] ks = x.klongs;
        if (sz > maxNodeSize) fail(name(x) + " has " + sz + " klongs, more than " + maxNodeSize);
        long time = -1;
        long before = Klong.DELETE_NONE_BITMAP;
        for (int i = 0; i < sz; i++) {
            long k = ks[i];
            switch (Klong.getIntType(k)) {
            case Klong.INT_TYPE_TIME:
                if (Klong.getTime(k) <= time) fail(name(x) + ": W1, the times do not increase");
                time = Klong.getTime(k);
                break;
            case Klong.INT_TYPE_KEY:
                if (i == 0) fail(name(x) + ": W1, the first klong is not a time klong");
                if (x.getPointee(i) == null && !Spos.isValid(x.getPointerPos(i))) {
                    fail(name(x) + ": key klong " + i + " has no pointer");
                }
                break;
            case Klong.INT_TYPE_DELETE_BITMAP:
                if (i == 0) fail(name(x) + ": W1, the first klong is not a time klong");
                for (int j = 0; j < 62; j++) {
                    boolean del = Klong.isDeleted(k, j);
                    if (Klong.isDeleted(before, j) && !del) {
                        fail(name(x) + ": W3, bitmap " + i + " drops bit " + j);
                    }
                    if (!del) continue;
                    if (j >= i || Klong.getIntType(ks[j]) != Klong.INT_TYPE_KEY) {
                        fail(name(x) + ": W2, bitmap " + i + " deletes klong " + j);
                    }
                    long c = Klong.getCompareValue(ks[j]);
                    for (int j2 = 0; j2 < j; j2++) {
                        if (Klong.getIntType(ks[j2]) == Klong.INT_TYPE_KEY
                                && Klong.getCompareValue(ks[j2]) == c && !Klong.isDeleted(k, j2)) {
                            fail(name(x) + ": W4, bitmap " + i + " deletes klong " + j + " but not "
                                    + j2 + " of the same compare value");
                        }
                    }
                }
                before = k;
                break;
            default:
                fail(name(x) + ": a klong of no type at " + i);
            }
        }
    }

    /** A key as a map's key. */
    private static final class KeyOf {
        final long[] key;
        final int hash;

        KeyOf(long[] key) {
            this.key = key;
            this.hash = Arrays.hashCode(key);
        }

        public int hashCode() {
            return hash;
        }

        public boolean equals(Object o) {
            return o instanceof KeyOf && Arrays.equals(key, ((KeyOf) o).key);
        }

        public String toString() {
            return Arrays.toString(key);
        }
    }

    /** The segments of a key up to segment d, c: a chain to the first. */
    private static final class Prefix {
        final Prefix up;
        final long c;
        final int d;

        Prefix(Prefix up, long c, int d) {
            this.up = up;
            this.c = c;
            this.d = d;
        }

        long[] key() {
            long[] key = new long[d + 1];
            for (Prefix p = this; p != null; p = p.up) key[p.d] = p.c;
            return key;
        }
    }

    /** One walk at time t through the live klongs. */
    private final class Walk {
        final long t;
        final boolean check;
        final long[][] txKeys;
        final IdentityHashMap<KeyNode, Boolean> visited = new IdentityHashMap<KeyNode, Boolean>();
        /** The keys of the segment leaves made, changed or replaced: key, value or UNKNOWN. */
        final HashMap<KeyOf, Object> contents = new HashMap<KeyOf, Object>();
        /** The nodes to visit; a walk keeps no Java stack, as keys may have thousands of
         *  segments and a test runs the writer with a small stack (DbTesterLongKeys). */
        final ArrayDeque<Object[]> todo = new ArrayDeque<Object[]>();

        Walk(long t, boolean check, long[][] txKeys) {
            this.t = t;
            this.check = check;
            this.txKeys = txKeys;
        }

        boolean interesting(KeyNode x) {
            return madeNodes.containsKey(x) || changed.containsKey(x) || replaced.containsKey(x);
        }

        /** The walk from the space root; ks, the transaction's keys. */
        void walk(KeyNode root, int[] ks) {
            todo.push(new Object[] {root, new long[] {0, 0, NONE}, Boolean.TRUE, ks, null});
            while (!todo.isEmpty()) {
                Object[] a = todo.pop();
                long[] r = (long[]) a[1];
                visit((KeyNode) a[0], (int) r[0], r[1], r[2], a[2] == Boolean.TRUE, (int[]) a[3],
                        (Prefix) a[4]);
            }
        }

        /** Key node x to visit, at segment depth d with the range [lo, hi). */
        void later(KeyNode x, int d, long lo, long hi, int[] ks, Prefix prefix) {
            todo.push(new Object[] {x, new long[] {d, lo, hi}, Boolean.FALSE, ks, prefix});
        }

        /**
         * Visits key node x of segment depth d with the range [lo, hi) of compare values; ks,
         * the transaction's keys whose path goes through it; prefix, the segments before d.
         */
        void visit(KeyNode x, int d, long lo, long hi, boolean spaceRoot, int[] ks, Prefix prefix) {
            if (visited.put(x, Boolean.TRUE) != null) {
                if (check) fail(name(x) + " is reached twice at " + t + " (TREE)");
                return;
            }
            long[] cvs = new long[x.size];
            int[] idx = new int[x.size];
            int n = live(x, t, cvs, idx);
            boolean leaf = x.isSegmentLeaf();
            boolean mine = interesting(x);
            if (check) {
                nodeCheck(x);
                if (n == 0 && !(spaceRoot && leaf)) fail(name(x) + " has no live klong at " + t);
                for (int j = 0; j < n; j++) {
                    if (cvs[j] >= hi || (leaf && cvs[j] < lo)) {
                        fail(name(x) + ": the key order, compare value " + cvs[j] + " not in ["
                                + lo + ", " + (hi == NONE ? "-" : "" + hi) + ")");
                    }
                    if (mine) {
                        x.searchEq(t, cvs[j], kwi);
                        if (kwi.klong == Klong.NULL || kwi.pointerIndex != idx[j]) {
                            fail(name(x) + ": searchEq of " + cvs[j] + " finds klong "
                                    + kwi.pointerIndex + ", the live klong is " + idx[j]);
                        }
                    }
                }
            }
            for (int j = 0; j < n; j++) {
                long c = cvs[j];
                long next = j + 1 < n ? cvs[j + 1] : hi;
                Node y = x.getPointerNode(idx[j]);
                if (leaf) {
                    if (isLong(c)) {
                        if (check && mine && y != null) kidCheck(y, true, 0, NONE);
                        int[] sub = through(ks, d, c, c + 1, true);
                        if (y instanceof KeyNode && (sub.length > 0 || interesting((KeyNode) y))) {
                            later((KeyNode) y, d + 1, 0, NONE, sub, new Prefix(prefix, c, d));
                        }
                    } else {
                        if (check && mine && y != null && !(y instanceof ValueNode)) {
                            fail(name(x) + ": the live klong " + c + " of a segment leaf names no value");
                        }
                        if (mine) {
                            long[] key = new Prefix(prefix, c, d).key();
                            contents.put(new KeyOf(key), y instanceof ValueNode ? y : UNKNOWN);
                        }
                    }
                } else {
                    long clo = Math.max(lo, c);
                    if (check && mine && y != null) kidCheck(y, false, clo, next);
                    int[] sub = through(ks, d, j == 0 ? Long.MIN_VALUE : c, next, false);
                    if (y instanceof KeyNode && (sub.length > 0 || interesting((KeyNode) y))) {
                        later((KeyNode) y, d, clo, next, sub, prefix);
                    }
                }
            }
        }

        /** A live child y of a node made or changed: its kind, a live klong, the key order. */
        void kidCheck(Node y, boolean nextSegment, long lo, long hi) {
            if (!(y instanceof KeyNode)) fail("a live klong of an inner node, or of a long segment, "
                    + "names no key node at " + t);
            KeyNode k = (KeyNode) y;
            long[] cvs = new long[k.size];
            int[] idx = new int[k.size];
            int n = live(k, t, cvs, idx);
            if (n == 0) fail(name(k) + ", a live child, has no live klong at " + t);
            if (nextSegment) return;
            for (int j = 0; j < n; j++) {
                if (cvs[j] >= hi || (k.isSegmentLeaf() && cvs[j] < lo)) {
                    fail(name(k) + ": the key order, compare value " + cvs[j] + " not in its "
                            + "parent's range [" + lo + ", " + (hi == NONE ? "-" : "" + hi) + ")");
                }
            }
        }

        /**
         * The keys of ks whose segment d is in [from, to) (from = Long.MIN_VALUE: below 'to'),
         * and, if more, that have a segment after d.
         */
        int[] through(int[] ks, int d, long from, long to, boolean more) {
            int m = 0;
            int[] r = new int[ks.length];
            for (int i : ks) {
                long[] key = txKeys[i];
                if (d >= key.length || (more && d + 1 >= key.length)) continue;
                if ((from == Long.MIN_VALUE || key[d] >= from) && key[d] < to) r[m++] = i;
            }
            return Arrays.copyOf(r, m);
        }
    }
}
