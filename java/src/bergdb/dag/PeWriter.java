package bergdb.dag;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;

import bergdb.common.Bug;
import bergdb.pub.util.DbException;

/**
 * <p>The writer: PE, "plan, then emit" (bergdb 026-25; the design 026-23, section 1.2; the
 * trial 026-24; the proof 030-21). A transaction's operations, one a key in key order, change
 * the key tree in two steps. Plan: one walk over the tree from the space root decides, on lists
 * only, what each node that an operation touches holds after the transaction (a virtual node,
 * VN), and what is written for it. Emit: each decided node is written once, bottom-up: nothing,
 * klongs appended to it, or new nodes. No node is made and then taken back, none is written
 * twice. Record format 8 (StoredTrans.RECORD_FORMAT): a start's rerun gives a record's KVs to
 * this writer as one batch and makes the same nodes with the same ids.</p>
 *
 * <p>The program is that of lean/contract's Contract/PeWriter.lean (Contract.PE.peTx), rule
 * for rule, which bergdb 030-21 proves to meet the writer's contract (030-04); each method
 * names the definition it restates. The tree checker of the level scripts runs a copy of it,
 * lean/SIS/Tree/Pe.lean, against Java's traces, node for node with the ids (treecheck). The
 * differences of form from PeWriter.lean, none of which changes a node:</p>
 * <ul>
 * <li>A node of the tree is named by the pointer that reaches it (Tgt: a node and the index of
 * its klong), not by an id: an entry is unchanged in a node if it is the node's own live
 * klong of that compare value. A new node and a value are named by their objects.</li>
 * <li>The height of a node is known from its planned children, not from a level: a segment
 * leaf is at height 0, an inner node one above its children.</li>
 * <li>The walk over the segments is a loop with a stack of frames (Frame), not a recursion: a
 * key has a segment tree per 7 bytes, and a key of 57,344 bytes has 8,193 (bergdb 021-16,
 * 024-17's L3). Within a segment tree the recursions are bounded by its height.</li>
 * <li>A delete that deletes makes a delete node, with an id, for the record
 * (ValueNode.createDelete), where PeWriter.lean makes nothing; a delete of a key with no value
 * is a noop and makes nothing. Java has no level bounds G and H, and every key that
 * Keys.toSegments makes is one the tree can hold, so nothing is refused.</li>
 * </ul>
 *
 * <p>The ids: Db gives a node its id when it is reported made (Dag.NodeChangeListener), so the
 * order of the reports is that of PeWriter.lean's fresh ids: a value when its operation is
 * applied at its segment leaf, the key nodes of a segment tree below a leaf when that tree is
 * emitted, before the leaf's later operations, the nodes of the space root's tree when it is
 * emitted, bottom-up and left to right, and the top node last (TopDs.newSuperRoot).</p>
 *
 * <p>The listeners: a node made is reported made, then changed; a node that gets klongs,
 * changed; a node of the tree before that is not reachable after the transaction (replaced by
 * new nodes, joined, emptied, or collapsed) replaced; a node that keeps its klongs but has a
 * node written below it, on the path (keyNodeOnPath), so that Db makes it dirty as the Lean
 * model's step 3 marks it. The plan follows pointers without telling pd's pointer listener.</p>
 */
final class PeWriter {

    private static final int SAME = -2;
    private static final int APPEND = -1;
    // A decision k >= 1: k new nodes ("parts k").

    /** The most nodes of a path within one segment tree: deeper is a cycle of a damaged stream. */
    private static final int MAX_DEPTH = 1000;

    private final Dag dag;
    private final PutData pd;
    private final long tt;
    private final long[][] keys;
    private final byte[][] values;
    private final int maxNodeSize, m, c, h, theta, cap;
    private final boolean merges;

    PeWriter(Dag dag, long[][] keys, byte[][] values, PutData pd) {
        this.dag = dag;
        this.pd = pd;
        this.tt = pd.tt;
        this.keys = keys;
        this.values = values;
        final int b = dag.getMaxNodeSize();
        this.maxNodeSize = b;
        this.m = Dag.minFill(b);
        this.c = Dag.mergeCap(b);
        this.h = Dag.splitAbove(b);
        this.theta = Dag.theta(b);
        this.cap = Dag.cutSize(b);
        this.merges = m >= 2;
    }

    // ======== The planned tree ========

    /**
     * What an entry names (PeWriter.lean's ids): the node or value that pointer 'idx' of the
     * node 'src' names (an old pointer, copied as it is), or the object 'node' (a node or value
     * made, or the space root).
     */
    static final class Tgt {
        final KeyNode src;
        final int idx;
        final Node node;

        Tgt(KeyNode src, int idx) {
            this.src = src;
            this.idx = idx;
            this.node = null;
        }

        Tgt(Node node) {
            this.src = null;
            this.idx = -1;
            this.node = node;
        }
    }

    /** An entry of a planned node: a compare value and its child, a Tgt (VN.old) or a VN. */
    static final class Ent {
        final long cv;
        final Object ch;

        Ent(long cv, Object ch) {
            this.cv = cv;
            this.ch = ch;
        }
    }

    /** An entry of a final list F: a compare value and what it names, null for a node made. */
    static final class FEnt {
        final long cv;
        final Tgt t;

        FEnt(long cv, Tgt t) {
            this.cv = cv;
            this.t = t;
        }
    }

    /**
     * A planned key node (PeWriter.lean's VN.node): its base, the node of the tree before (null:
     * a new node) and the pointer that reached it; its segment g and height h; whether it is a
     * joined list; its entries, each child before its cut; its final list F; its decision.
     */
    static final class VN {
        final KeyNode base;
        final Tgt from;
        final int g, h;
        final boolean join;
        final ArrayList<Ent> es;
        final ArrayList<FEnt> f;
        final int dec;
        /** Set by emit: it or a node below it was written. */
        boolean wrote;
        /** A segment leaf: a node of a segment tree below it was written (its LeafFrame). */
        boolean subWrote;
        /** Its decision is one new node because its base would hold more than theta dead
         *  klongs (option 2's compaction, bergdb 024-23): for the counts only. */
        boolean compact;

        VN(KeyNode base, Tgt from, int g, int h, boolean join, ArrayList<Ent> es,
                ArrayList<FEnt> f, int dec) {
            this.base = base;
            this.from = from;
            this.g = g;
            this.h = h;
            this.join = join;
            this.es = es;
            this.f = f;
            this.dec = dec;
        }

        int size() {
            return f.size();
        }

        boolean changed() {
            return dec != SAME;
        }
    }

    // ======== The transaction (PeWriter.lean's peTx) ========

    /** Runs the transaction: plan from the space root, settle it, emit, a new top node if the
     *  space root changed. */
    void run() {
        Dag.statTransactions++;
        final KeyNode root = dag.getTopDs().findRoot(tt, pd);      // marks the super root and it
        if (root == null) {
            throw new DbException("Found no root node at t=" + tt + ", cannot continue put.");
        }
        final Tgt rootTgt = new Tgt(root);
        final VN v = (VN) runFrames(new TreeFrame(rootTgt, 0, 0, keys.length, true));
        final Object rv = settleRoot(v, 0, true);
        if (rv == null) {
            throw new Bug("PE at " + tt + ": the space root settled to nothing.");
        }
        final List<FEnt> e = emit(rv);
        if (e.size() != 1) {
            throw new Bug("PE at " + tt + ": the space root emitted " + e.size() + " nodes.");
        }
        final Tgt t = e.get(0).t;
        if (t.node == root) {
            return;
        }
        final KeyNode newRoot = t.node != null ? (KeyNode) t.node : follow(t);
        dag.getTopDs().newSuperRoot(tt, newRoot, pd.accessData, pd.pointerCreatedListener,
                pd.nodeChangeListener);
    }

    // ======== Plan: the walk with a stack of frames ========

    /** A step of the walk: a planTree, a plan of an inner node, or a segment leaf's groups. */
    private abstract static class Frame {
        Object result;

        /** The next frame to run, or null when this one is done, with its result set. */
        abstract Frame step(Object childResult);
    }

    /** Runs a frame and the frames it calls, to its result. */
    private static Object runFrames(Frame first) {
        final ArrayDeque<Frame> stack = new ArrayDeque<Frame>();
        stack.push(first);
        Object res = null;
        while (true) {
            final Frame f = stack.peek();
            final Frame call = f.step(res);
            if (call != null) {
                stack.push(call);
                res = null;
            } else {
                stack.pop();
                res = f.result;
                if (stack.isEmpty()) {
                    return res;
                }
            }
        }
    }

    /**
     * planTree: the tree of segment g with the operations [lo, hi), from its root (null: no tree
     * yet): planned, its root settled, emitted; its result is its new root, or null if it is
     * empty. For the space root ('space'), only planned: its result is the VN.
     */
    private final class TreeFrame extends Frame {
        final Tgt root;
        final int g, lo, hi;
        final boolean space;
        boolean called;

        TreeFrame(Tgt root, int g, int lo, int hi, boolean space) {
            this.root = root;
            this.g = g;
            this.lo = lo;
            this.hi = hi;
            this.space = space;
        }

        Frame step(Object r) {
            if (!called) {
                called = true;
                if (root != null) {
                    final KeyNode x = root.node != null ? (KeyNode) root.node : follow(root);
                    return planFrame(x, root, g, lo, hi, 0);
                }
                return new LeafFrame(null, null, g, lo, hi, new ArrayList<Ent>());
            }
            final VN v = (VN) r;
            if (space) {
                result = v;
                return null;
            }
            final Object s = settleRoot(v, g, false);
            if (s == null) {
                result = null;
                return null;
            }
            final List<FEnt> e = emit(s);
            if (e.size() != 1) {
                throw new Bug("PE at " + tt + ": a segment root emitted " + e.size() + " nodes.");
            }
            result = new Sub(e.get(0).t, s instanceof VN && ((VN) s).wrote);
            return null;
        }
    }

    /** A segment tree's new root, and whether a node of it was written. */
    private static final class Sub {
        final Tgt root;
        final boolean wrote;

        Sub(Tgt root, boolean wrote) {
            this.root = root;
            this.wrote = wrote;
        }
    }

    /** plan(x, ops): the frame of key node x, reached by 'from'. */
    private Frame planFrame(KeyNode x, Tgt from, int g, int lo, int hi, int depth) {
        if (depth > MAX_DEPTH) {
            throw pd.pointerFollower.cycle("A descent of the writer passed " + MAX_DEPTH
                    + " key nodes in one segment tree at key node " + x.getId()
                    + ": the pointers make a cycle.");
        }
        if (x.isSegmentLeaf()) {
            return new LeafFrame(x, from, g, lo, hi, liveEntries(x));
        }
        return new NodeFrame(x, from, g, lo, hi, depth);
    }

    /**
     * plan of an inner node x (PeWriter.lean's plan, planKids): its operations divided among its
     * children by its live list (route), each child with operations planned one height down,
     * then rebalance, then mkNode.
     */
    private final class NodeFrame extends Frame {
        final KeyNode x;
        final Tgt from;
        final int g, depth;
        final Live lv;
        final int[] start;          // the first operation of each child; start[n] = hi
        final ArrayList<Ent> kids = new ArrayList<Ent>();
        int j = 0;
        int hk = -1;                // the children's height, from a planned child
        boolean waiting;

        NodeFrame(KeyNode x, Tgt from, int g, int lo, int hi, int depth) {
            this.x = x;
            this.from = from;
            this.g = g;
            this.depth = depth;
            this.lv = live(x);
            if (lv.n == 0) {
                throw new DbException("Key node " + x.getId() + ", not a segment leaf, has no "
                        + "live klong at time " + tt + ": corrupt data.");
            }
            this.start = route(lv, g, lo, hi);
        }

        Frame step(Object r) {
            if (waiting) {
                waiting = false;
                final VN v = (VN) r;
                hk = v.h;
                kids.add(new Ent(lv.cv[j], v));
                j++;
            }
            while (j < lv.n) {
                if (start[j] == start[j + 1]) {
                    kids.add(new Ent(lv.cv[j], new Tgt(x, lv.idx[j])));
                    j++;
                    continue;
                }
                final Tgt t = new Tgt(x, lv.idx[j]);
                waiting = true;
                return planFrame(follow(t), t, g, start[j], start[j + 1], depth + 1);
            }
            if (hk < 0) {
                throw new Bug("PE at " + tt + ": inner key node " + x.getId()
                        + " planned no child.");
            }
            final ArrayList<Ent> es2 = rebalance(g, hk, kids);
            result = mkNode(x, from, g, hk + 1, false, es2);
            return null;
        }
    }

    /**
     * A segment leaf's entries with the operations applied (PeWriter.lean's applyGroups), by
     * compare value: a put of a key that ends here sets a new value, a delete removes the entry,
     * and the operations of keys with more segments go to the next segment's tree (a
     * TreeFrame), whose new root, or none, is the entry. Then mkNode. 'x' null: a new tree's
     * leaf.
     */
    private final class LeafFrame extends Frame {
        final KeyNode x;
        final Tgt from;
        final int g, hi;
        final ArrayList<Ent> es;
        int pos;
        long pendingCv;
        boolean waiting;
        boolean subWrote;

        LeafFrame(KeyNode x, Tgt from, int g, int lo, int hi, ArrayList<Ent> es) {
            this.x = x;
            this.from = from;
            this.g = g;
            this.pos = lo;
            this.hi = hi;
            this.es = es;
        }

        Frame step(Object r) {
            if (waiting) {
                waiting = false;
                if (r != null) {
                    setEntry(es, pendingCv, ((Sub) r).root);
                    subWrote |= ((Sub) r).wrote;
                } else {
                    removeEntry(es, pendingCv);
                }
            }
            while (pos < hi) {
                final long cv = keys[pos][g];
                int end = pos;
                while (end < hi && keys[end][g] == cv) {
                    end++;
                }
                int subLo = end;
                for (int i = pos; i < end; i++) {
                    if (keys[i].length != g + 1) {
                        subLo = Math.min(subLo, i);
                        continue;
                    }
                    if (values[i] != null) {
                        final ValueNode vn = new ValueNode(values[i]);
                        pd.nodeChangeListener.valueNodeCreated(vn, keys[i]);
                        setEntry(es, cv, new Tgt(vn));
                    } else if (find(es, cv) >= 0) {
                        pd.nodeChangeListener.valueNodeCreated(ValueNode.createDelete(), keys[i]);
                        removeEntry(es, cv);
                    }
                }
                if (subLo < end) {
                    final int at = find(es, cv);
                    final Tgt old = at < 0 ? null : (Tgt) es.get(at).ch;
                    pendingCv = cv;
                    waiting = true;
                    final int subHi = end;
                    pos = end;
                    return new TreeFrame(old, g + 1, firstLong(subLo, subHi, g), subHi, false);
                }
                pos = end;
            }
            final VN v = mkNode(x, from, g, 0, false, es);
            v.subWrote = subWrote;
            result = v;
            return null;
        }
    }

    /** The first operation of [lo, hi) whose key goes on after segment g (sorted: a key that
     *  ends at g comes before one that goes on, Keys.compareArrays). */
    private int firstLong(int lo, int hi, int g) {
        for (int i = lo; i < hi; i++) {
            if (keys[i].length != g + 1) {
                return i;
            }
        }
        return hi;
    }

    // ======== Lists ========

    /** The live klongs of a key node, in compare order: compare values and klong indexes. */
    static final class Live {
        final long[] cv;
        final int[] idx;
        int n;

        Live(int size) {
            cv = new long[size];
            idx = new int[size];
        }
    }

    /**
     * Contract's live: for each compare value with a key klong that the last bitmap does not
     * delete, the last such klong; in increasing order of the compare values.
     */
    static Live live(KeyNode node) {
        final int sz = node.size;
        final long[] ks = node.klongs;
        final long del = lastBitmap(ks, sz);
        final Live lv = new Live(sz);
        for (int i = 0; i < sz; i++) {
            final long k = ks[i];
            if (Klong.getIntType(k) != Klong.INT_TYPE_KEY || Klong.isDeleted(del, i)) {
                continue;
            }
            final long cv = Klong.getCompareValue(k);
            int j = 0;
            while (j < lv.n && lv.cv[j] < cv) {
                j++;
            }
            if (j < lv.n && lv.cv[j] == cv) {
                lv.idx[j] = i;
                continue;
            }
            System.arraycopy(lv.cv, j, lv.cv, j + 1, lv.n - j);
            System.arraycopy(lv.idx, j, lv.idx, j + 1, lv.n - j);
            lv.cv[j] = cv;
            lv.idx[j] = i;
            lv.n++;
        }
        return lv;
    }

    /** The last bitmap of the klongs, none set if there is none. */
    private static long lastBitmap(long[] ks, int sz) {
        long del = Klong.DELETE_NONE_BITMAP;
        for (int i = 0; i < sz; i++) {
            if (Klong.getIntType(ks[i]) == Klong.INT_TYPE_DELETE_BITMAP) {
                del = ks[i];
            }
        }
        return del;
    }

    /** A segment leaf's live list, each child an old pointer. */
    private static ArrayList<Ent> liveEntries(KeyNode x) {
        final Live lv = live(x);
        final ArrayList<Ent> es = new ArrayList<Ent>(lv.n + 4);
        for (int j = 0; j < lv.n; j++) {
            es.add(new Ent(lv.cv[j], new Tgt(x, lv.idx[j])));
        }
        return es;
    }

    /** The index of the entry of compare value cv, or -1. */
    private static int find(List<Ent> es, long cv) {
        for (int i = 0; i < es.size(); i++) {
            if (es.get(i).cv == cv) {
                return i;
            }
        }
        return -1;
    }

    /** setEntry: the entry of compare value cv set, in compare order. */
    private static void setEntry(ArrayList<Ent> es, long cv, Object ch) {
        int i = 0;
        while (i < es.size() && es.get(i).cv < cv) {
            i++;
        }
        if (i < es.size() && es.get(i).cv == cv) {
            es.set(i, new Ent(cv, ch));
        } else {
            es.add(i, new Ent(cv, ch));
        }
    }

    /** removeEntry. */
    private static void removeEntry(ArrayList<Ent> es, long cv) {
        final int i = find(es, cv);
        if (i >= 0) {
            es.remove(i);
        }
    }

    /**
     * route: the first operation of each child of the live list lv, by segment g of the keys
     * of [lo, hi), which are in key order: the first child every operation below the second
     * compare value, each other child those from its compare value to the next one's.
     */
    private int[] route(Live lv, int g, int lo, int hi) {
        final int[] start = new int[lv.n + 1];
        start[0] = lo;
        int i = lo;
        for (int j = 1; j < lv.n; j++) {
            while (i < hi && keys[i][g] < lv.cv[j]) {
                i++;
            }
            start[j] = i;
        }
        start[lv.n] = hi;
        return start;
    }

    /** partSizes: the sizes of k parts of n entries, as even as possible, the larger ones
     *  first (ceilFirst, a joined list) or last. */
    static int[] partSizes(int n, int k, boolean ceilFirst) {
        final int b = n / k;
        final int e = n % k;
        final int[] s = new int[k];
        for (int j = 0; j < k; j++) {
            s[j] = ceilFirst ? (j < e ? b + 1 : b) : (k - e <= j ? b + 1 : b);
        }
        return s;
    }

    /** nParts: the parts of a list of n entries made new, of at most cap entries. */
    static int nParts(int cap, int n) {
        final int cp = Math.max(cap, 1);
        return n <= cp ? 1 : (n + cp - 1) / cp;
    }

    /** cutParts: one if n is at most h, else at least two of at most cap entries. */
    private int cutParts(int n) {
        return n <= h ? 1 : Math.max(2, nParts(cap, n));
    }

    // ======== The decision (PeWriter.lean's ents, decideNode, mkNode) ========

    /** ents: the entries a parent gets for its child (cv, ch): one, or one for each part. */
    private static void ents(long cv, Object ch, ArrayList<FEnt> out) {
        if (ch instanceof Tgt) {
            out.add(new FEnt(cv, (Tgt) ch));
            return;
        }
        final VN v = (VN) ch;
        if (v.dec >= 2) {
            final int[] sizes = partSizes(v.f.size(), v.dec, v.join);
            out.add(new FEnt(cv, null));
            int off = sizes[0];
            for (int j = 1; j < sizes.length; j++) {
                out.add(new FEnt(sizes[j] == 0 ? 0 : v.f.get(off).cv, null));
                off += sizes[j];
            }
        } else if (v.dec >= 1 || v.base == null) {
            out.add(new FEnt(cv, null));
        } else {
            out.add(new FEnt(cv, v.from));
        }
    }

    /** mkNode: a virtual node from its entries (an inner node's first entry gets the empty
     *  key): its final list and its decision. */
    private VN mkNode(KeyNode base, Tgt from, int g, int ht, boolean join, ArrayList<Ent> es0) {
        final ArrayList<Ent> es = es0;
        if (ht != 0 && !es.isEmpty() && es.get(0).cv != 0) {
            es.set(0, new Ent(0, es.get(0).ch));
        }
        final ArrayList<FEnt> f = new ArrayList<FEnt>(es.size() + 2);
        for (Ent e : es) {
            ents(e.cv, e.ch, f);
        }
        if (ht != 0 && !f.isEmpty() && f.get(0).cv != 0) {
            f.set(0, new FEnt(0, f.get(0).t));
        }
        compacted = false;
        final VN v = new VN(base, from, g, ht, join, es, f, decide(base, join, f));
        v.compact = compacted;
        return v;
    }

    /** The entry e of F is the live klong of its compare value in 'base' (lb its live list). */
    private static boolean kept(KeyNode base, Live lb, FEnt e) {
        if (e.t == null || e.t.src != base) {
            return false;
        }
        for (int j = 0; j < lb.n; j++) {
            if (lb.cv[j] == e.cv) {
                return lb.idx[j] == e.t.idx;
            }
        }
        return false;
    }

    /** F holds a compare value. */
    private static boolean hasCv(List<FEnt> f, long cv) {
        for (FEnt e : f) {
            if (e.cv == cv) {
                return true;
            }
        }
        return false;
    }

    /** Set by decide(): its decision was by the dead klongs (VN.compact). */
    private boolean compacted;

    /** decideNode: same (F is the base's live list), append, or k new nodes. */
    private int decide(KeyNode base, boolean join, ArrayList<FEnt> f) {
        final int n = f.size();
        if (base == null) {
            return join ? nParts(c, n) : cutParts(n);
        }
        final Live lb = live(base);
        if (n == lb.n) {
            boolean same = true;
            for (int j = 0; j < n && same; j++) {
                same = f.get(j).cv == lb.cv[j] && kept(base, lb, f.get(j));
            }
            if (same) {
                return SAME;
            }
        }
        // The klongs that emit appends (appendKsO): a time klong, a bitmap if a compare value
        // left, and a key klong for each entry new or repointed.
        boolean removed = false;
        for (int j = 0; j < lb.n && !removed; j++) {
            removed = !hasCv(f, lb.cv[j]);
        }
        int added = 0;
        for (FEnt e : f) {
            if (!kept(base, lb, e)) {
                added++;
            }
        }
        final int extra = (removed ? 2 : 1) + added;
        if (base.size + extra <= maxNodeSize) {
            if (theta != 0 && deadAfter(base, lb, f, removed, added) > theta) {
                compacted = true;
                return n + 1 <= maxNodeSize ? 1 : cutParts(n);
            }
            return APPEND;
        }
        return cutParts(n);
    }

    /** The dead klongs of the base with emit's klongs appended (deadOver's count). */
    private static int deadAfter(KeyNode base, Live lb, List<FEnt> f, boolean removed,
            int added) {
        final int sz = base.size;
        final long[] ks = new long[sz + (removed ? 2 : 1) + added];
        System.arraycopy(base.klongs, 0, ks, 0, sz);
        int k = sz;
        ks[k++] = Klong.createTime(Klong.MAX_TIME);
        if (removed) {
            ks[k++] = emitBits(base, lb, f);
        }
        for (FEnt e : f) {
            if (!kept(base, lb, e)) {
                ks[k++] = Klong.compareValueToKeyKlong(e.cv);
            }
        }
        return deadCount(ks, k);
    }

    /** emitBits: the last bitmap and the bits of every key klong of the compare values that
     *  F leaves out. */
    private static long emitBits(KeyNode base, Live lb, List<FEnt> f) {
        final int sz = base.size;
        final long[] ks = base.klongs;
        long del = lastBitmap(ks, sz);
        for (int j = 0; j < lb.n; j++) {
            if (hasCv(f, lb.cv[j])) {
                continue;
            }
            for (int i = 0; i < sz; i++) {
                if (Klong.getIntType(ks[i]) == Klong.INT_TYPE_KEY
                        && Klong.getCompareValue(ks[i]) == lb.cv[j]) {
                    del = Klong.delete(del, i);
                }
            }
        }
        return del;
    }

    /** Contract's deadCount: the key klongs deleted by the last bitmap, or followed by a later
     *  key klong of the same compare value; each once. */
    static int deadCount(long[] ks, int sz) {
        final long del = lastBitmap(ks, sz);
        int dead = 0;
        A: for (int i = 0; i < sz; i++) {
            if (Klong.getIntType(ks[i]) != Klong.INT_TYPE_KEY) {
                continue;
            }
            if (Klong.isDeleted(del, i)) {
                dead++;
                continue;
            }
            final long cv = Klong.getCompareValue(ks[i]);
            for (int j = i + 1; j < sz; j++) {
                if (Klong.getIntType(ks[j]) == Klong.INT_TYPE_KEY
                        && Klong.getCompareValue(ks[j]) == cv) {
                    dead++;
                    continue A;
                }
            }
        }
        return dead;
    }

    // ======== Rebalance (PeWriter.lean's openEs, cntOf, findSmall, joinAt, rebalance) ========

    /** The entries of a child for a join: an untouched node opened, each of its live klongs an
     *  untouched child; a planned node's entries. The opened node is replaced. */
    private ArrayList<Ent> openEs(Object ch) {
        if (ch instanceof VN) {
            final VN v = (VN) ch;
            if (v.base != null) {
                replaced(v.base);
            }
            return new ArrayList<Ent>(v.es);
        }
        final KeyNode y = follow((Tgt) ch);
        replaced(y);
        final Live lv = live(y);
        final ArrayList<Ent> es = new ArrayList<Ent>(lv.n);
        for (int j = 0; j < lv.n; j++) {
            es.add(new Ent(lv.cv[j], new Tgt(y, lv.idx[j])));
        }
        return es;
    }

    /** The live count of a child, for M1. */
    private int cntOf(Object ch) {
        if (ch instanceof VN) {
            return ((VN) ch).size();
        }
        return live(follow((Tgt) ch)).n;
    }

    /** The first changed child with fewer than m entries, or -1. */
    private int findSmall(List<Ent> es) {
        for (int i = 0; i < es.size(); i++) {
            final Object ch = es.get(i).ch;
            if (ch instanceof VN && ((VN) ch).changed() && ((VN) ch).size() < m) {
                return i;
            }
        }
        return -1;
    }

    /** joinAt: the small child at ix with a neighbour by M1, the joined list of two inner
     *  nodes rebalanced one level down; at the children's height ht. */
    private ArrayList<Ent> joinAt(int g, int ht, ArrayList<Ent> es, int ix) {
        final VN x = (VN) es.get(ix).ch;
        boolean useLeft = false;
        if (ix > 0) {
            if (ix + 1 >= es.size()) {
                useLeft = true;
            } else {
                useLeft = cntOf(es.get(ix - 1).ch) + x.size() <= c;
            }
        }
        final int il = useLeft ? ix - 1 : ix;
        if (il + 1 >= es.size()) {
            throw new Bug("PE at " + tt + ": a join without a right neighbour.");
        }
        final Ent l = es.get(il);
        final Ent r = es.get(il + 1);
        final ArrayList<Ent> j = openEs(l.ch);
        final ArrayList<Ent> esR = openEs(r.ch);
        if (ht != 0 && !esR.isEmpty()) {
            esR.set(0, new Ent(r.cv, esR.get(0).ch));
        }
        j.addAll(esR);
        final ArrayList<Ent> j2 = ht == 0 ? j : rebalance(g, ht - 1, j);
        final VN v = mkNode(null, null, g, ht, true, j2);
        Dag.statJoins++;
        final ArrayList<Ent> out = new ArrayList<Ent>(es.size() - 1);
        for (int i = 0; i < il; i++) {
            out.add(es.get(i));
        }
        out.add(new Ent(l.cv, v));
        for (int i = il + 2; i < es.size(); i++) {
            out.add(es.get(i));
        }
        return out;
    }

    /** rebalance: the children of an inner node, at height ht: an empty child is dropped; while
     *  a changed child holds fewer than m entries and has a neighbour, it is joined with one. */
    private ArrayList<Ent> rebalance(int g, int ht, ArrayList<Ent> es0) {
        ArrayList<Ent> es = new ArrayList<Ent>(es0.size());
        for (Ent e : es0) {
            if (e.ch instanceof VN && ((VN) e.ch).f.isEmpty()) {
                dropped((VN) e.ch);
                continue;
            }
            es.add(e);
        }
        if (!merges) {
            return es;
        }
        for (int round = es.size() + 1; round > 0; round--) {
            if (es.size() < 2) {
                break;
            }
            final int ix = findSmall(es);
            if (ix < 0) {
                break;
            }
            es = joinAt(g, ht, es, ix);
        }
        return es;
    }

    // ======== Settle a root (PeWriter.lean's settleRoot) ========

    /**
     * A root settled alone: null, nothing left (not for the space root, which becomes an empty
     * segment leaf); an inner root with one entry gives way to its child; a root of two parts
     * or more gets a new root above it.
     */
    private Object settleRoot(Object v0, int g, boolean space) {
        Object v = v0;
        while (true) {
            if (v instanceof Tgt) {
                final Tgt t = (Tgt) v;
                final KeyNode y = t.node != null ? (KeyNode) t.node : follow(t);
                final Live lv = live(y);
                if (lv.n == 1 && !y.isSegmentLeaf()) {
                    replaced(y);
                    Dag.statCollapses++;
                    v = new Tgt(y, lv.idx[0]);
                    continue;
                }
                return v;
            }
            final VN n = (VN) v;
            if (n.f.isEmpty()) {
                if (!space) {
                    dropped(n);
                    return null;
                }
                if (n.h == 0) {
                    return v;
                }
                dropped(n);
                return mkNode(null, null, g, 0, false, new ArrayList<Ent>());
            }
            if (n.h != 0 && n.f.size() == 1) {
                if (n.es.size() != 1) {
                    throw new Bug("PE at " + tt + ": a root of one entry from "
                            + n.es.size() + " children.");
                }
                if (n.base != null) {
                    replaced(n.base);
                }
                Dag.statCollapses++;
                v = n.es.get(0).ch;
                continue;
            }
            if (n.dec >= 2) {
                final ArrayList<Ent> one = new ArrayList<Ent>(1);
                one.add(new Ent(0, n));
                Dag.statNewRoots++;
                v = mkNode(null, null, g, n.h + 1, false, one);
                continue;
            }
            return v;
        }
    }

    // ======== Emit (PeWriter.lean's emit, emitKids, newParts) ========

    /**
     * emit: the planned subtree written, children first, each node by its decision: kept,
     * klongs appended, or its final list cut into new nodes. Gives the entries its parent gets,
     * the first with compare value 0 (the parent puts its own).
     */
    private List<FEnt> emit(Object ch) {
        if (ch instanceof Tgt) {
            final ArrayList<FEnt> one = new ArrayList<FEnt>(1);
            one.add(new FEnt(0, (Tgt) ch));
            return one;
        }
        final VN v = (VN) ch;
        final ArrayList<FEnt> f = new ArrayList<FEnt>(v.f.size());
        boolean wroteBelow = false;
        for (Ent e : v.es) {
            final List<FEnt> sub = emit(e.ch);
            if (e.ch instanceof VN && ((VN) e.ch).wrote) {
                wroteBelow = true;
            }
            for (int i = 0; i < sub.size(); i++) {
                f.add(i == 0 ? new FEnt(e.cv, sub.get(0).t) : sub.get(i));
            }
        }
        if (v.h != 0 && !f.isEmpty() && f.get(0).cv != 0) {
            f.set(0, new FEnt(0, f.get(0).t));
        }
        final ArrayList<FEnt> out = new ArrayList<FEnt>(1);
        if (v.dec == SAME) {
            v.wrote = wroteBelow || v.subWrote;
            if (v.wrote) {
                pd.nodeChangeListener.keyNodeOnPath(v.base);
            }
            out.add(new FEnt(0, v.from));
            return out;
        }
        v.wrote = true;
        if (v.dec == APPEND) {
            append(v.base, f);
            Dag.statAppends++;
            out.add(new FEnt(0, v.from));
            return out;
        }
        if (v.base != null) {
            if (v.compact) {
                Dag.statCompactions++;
            } else if (v.dec == 1) {
                Dag.statReplaces++;
            } else {
                Dag.statCuts++;
            }
        }
        final int[] sizes = partSizes(f.size(), v.dec, v.join);
        int off = 0;
        for (int s : sizes) {
            final KeyNode nn = new KeyNode(v.h == 0);
            pd.nodeChangeListener.keyNodeCreated(nn);
            nn.addToEnd(Klong.createTime(tt), null, Spos.NULL);
            for (int i = off; i < off + s; i++) {
                final FEnt e = f.get(i);
                addEntry(nn, v.h != 0 && i == off ? 0 : e.cv, e.t);
            }
            pd.nodeChangeListener.keyNodeChanged(nn);
            out.add(new FEnt(s == 0 ? 0 : f.get(off).cv, new Tgt(nn)));
            off += s;
        }
        if (v.base != null) {
            replaced(v.base);
        }
        return out;
    }

    /** emitKs: the klongs that make the base hold F: a time klong, a bitmap if a compare
     *  value left, and a key klong for each entry new or repointed. */
    private void append(KeyNode base, List<FEnt> f) {
        final Live lb = live(base);
        boolean removed = false;
        for (int j = 0; j < lb.n && !removed; j++) {
            removed = !hasCv(f, lb.cv[j]);
        }
        if (removed) {
            base.addDeleteKlong(tt, emitBits(base, lb, f));
        }
        for (FEnt e : f) {
            if (!kept(base, lb, e)) {
                addEntry(base, e.cv, e.t);
            }
        }
        pd.nodeChangeListener.keyNodeChanged(base);
    }

    /** A key klong of compare value cv added to 'dest', naming what t names. */
    private void addEntry(KeyNode dest, long cv, Tgt t) {
        final long klong = Klong.compareValueToKeyKlong(cv);
        final int i;
        if (t.node != null) {
            dest.addKlong(tt, klong, t.node, pd.accessData);
            i = dest.size - 1;
        } else {
            i = dest.addKlongCopyPointer(tt, klong, t.src, t.idx);
        }
        final Node pointee = dest.getPointerNode(i);
        if (pointee != null) {
            pd.pointerCreatedListener.pointerCreated(dest, i, pointee);
        }
    }

    // ======== Helpers ========

    /** The key node that t names, followed as the writer reads, without telling pd's pointer
     *  listener (nothing is marked by the plan). */
    private KeyNode follow(Tgt t) {
        if (t.node != null) {
            return (KeyNode) t.node;
        }
        final Dag.PointerListener listener = pd.pointerListener;
        pd.pointerListener = Dag.DO_NOTHING_POINTER_LISTENER;
        final Node n;
        try {
            n = pd.followPointer(t.src, t.idx);
        } finally {
            pd.pointerListener = listener;
        }
        if (!(n instanceof KeyNode)) {
            throw new DbException("Pointer " + t.idx + " of key node " + t.src.getId()
                    + " names " + (n == null ? "nothing" : "a value") + " where a key node is"
                    + " expected, at time " + tt + ": corrupt data.");
        }
        return (KeyNode) n;
    }

    /** A node of the tree before that is not reachable after the transaction. */
    private void replaced(KeyNode node) {
        pd.nodeChangeListener.keyNodeReplaced(node);
    }

    /** A planned node left out, empty: its base, if any, is not reachable after. */
    private void dropped(VN v) {
        Dag.statDropped++;
        if (v.base != null) {
            replaced(v.base);
        }
    }
}
