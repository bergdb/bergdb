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
        // Always true since node sizes below 8 are refused (Dag.MIN_NODE_SIZE, bergdb 028-38);
        // kept as the Lean model's Cfg.merges (PeWriter.lean), which this class follows.
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
        /** The base's live list (null: no base; or not made yet, for a sparse node: lb()). */
        Live lb;
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
        /**
         * An inner node kept as it was, decided without its lists (NodeFrame's short way): es
         * holds its planned children only, f is null, and its final list is its base's live
         * list (entries() makes es whole when a join or a settle needs it).
         */
        boolean sparse;
        /**
         * A segment leaf kept or appended to, decided by counts (LeafFrame's short way): es and
         * f are null, its changes over its base's live list are 'changes' (an entry set, or
         * REMOVED), and its final list has nFinal entries.
         */
        ArrayList<Ent> changes;
        int nFinal;
        /** An inner node appended to, decided by counts (NodeFrame.appendedByCounts): es holds
         *  its children planned only (sparse), f is null, its final list has nFinal entries. */
        boolean counted;

        VN(KeyNode base, Live lb, Tgt from, int g, int h, boolean join, ArrayList<Ent> es,
                ArrayList<FEnt> f, int dec) {
            this.base = base;
            this.lb = lb;
            this.from = from;
            this.g = g;
            this.h = h;
            this.join = join;
            this.es = es;
            this.f = f;
            this.dec = dec;
        }

        int size() {
            return f != null ? f.size() : changes != null || counted ? nFinal : lb().n;
        }

        /** Its final list is empty (VN.isEmpty). A sparse node kept as it was had a child
         *  planned, so it is not; its live list is not made for this. */
        boolean isEmpty() {
            return !(sparse && dec == SAME) && size() == 0;
        }

        /** The base's live list, made when first needed. */
        Live lb() {
            if (lb == null && base != null) {
                lb = live(base);
            }
            return lb;
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
        if (!pd.forcePePlan && keys.length <= SHORT_OPS && shortWay(root)) {
            Dag.statShort++;
            return;
        }
        final Tgt rootTgt = new Tgt(root);
        final VN v = (VN) runFrames(new TreeFrame(rootTgt, 0, 0, keys.length, true));
        final Object rv = settleRoot(v, 0, true);
        if (rv == null) {
            throw new Bug("PE at " + tt + ": the space root settled to nothing.");
        }
        final Object e = emit(rv);
        if (!(e instanceof Tgt)) {
            throw new Bug("PE at " + tt + ": the space root emitted more than one node.");
        }
        final Tgt t = (Tgt) e;
        if (t.node == root) {
            return;
        }
        final KeyNode newRoot = t.node != null ? (KeyNode) t.node : follow(t);
        dag.getTopDs().newSuperRoot(tt, newRoot, pd.accessData, pd.pointerCreatedListener,
                pd.nodeChangeListener);
    }

    /** One report in the short way: its segment tree, depth, and last operation that wrote. */
    private static final class ShortMark {
        final KeyNode node;
        final int segment, depth;
        int lastOp;

        ShortMark(KeyNode node, int lastOp, int segment, int depth) {
            this.node = node;
            this.lastOp = lastOp;
            this.segment = segment;
            this.depth = depth;
        }
    }

    private static void shortMark(ArrayList<ShortMark> order, KeyNode node, int op,
            int segment, int depth) {
        for (ShortMark mark : order) {
            if (mark.node == node) {
                mark.lastOp = op;
                return;
            }
        }
        order.add(new ShortMark(node, op, segment, depth));
    }

    // ======== The short way of a small transaction ========
    //
    // A transaction of at most SHORT_OPS operations whose every segment leaf that it changes is
    // appended to, keeps a live klong and, but a segment root, at least m (a decision of
    // decideNode by counts, as LeafFrame's short way), and that makes no segment tree, keeps
    // every other node of its paths as it was: an inner node whose children planned are kept,
    // not empty and not joined, and whose first live klong is the empty key, is same (as
    // NodeFrame's short way), and a root of two live klongs or more, or a segment leaf, is not
    // settled away. So PE's plan writes exactly the klongs appended, and the values and delete
    // nodes in key order, as here, with no frame and no list: the operations are found as a
    // get finds a key, decided, and then written. Anything else: nothing is changed, and the
    // plan runs. The tree checker compares both ways with the model on every traced
    // transaction.
    //

    /** At most this many operations take the short way. */
    private static final int SHORT_OPS = 8;

    /**
     * The short way (see above): true if taken, the transaction done; false if not, nothing
     * changed or reported.
     */
    private boolean shortWay(KeyNode root) {
        final int n = keys.length;
        final KeyNode[] leafOf = new KeyNode[n];        // null: a noop
        final boolean[] rootLeaf = new boolean[n];      // its leaf is a root of its tree
        final java.util.ArrayList<KeyNode> path = new java.util.ArrayList<KeyNode>();
        final int[] pathEnd = new int[n];               // op i's nodes: path[pathEnd[i-1], pathEnd[i])
        final KlongWithPointer kwi = pd.kwi;
        final boolean[] liveOp = new boolean[n];        // its compare value live in its leaf
        for (int i = 0; i < n; i++) {
            final long[] key = keys[i];
            KeyNode node = root;
            for (int g = 0; ; g++) {
                boolean segRoot = true;
                int depth = 0;
                while (!node.isSegmentLeaf()) {
                    final int idx = innerChild(node, key[g], segRoot);
                    if (idx < 0 || ++depth > MAX_DEPTH) {
                        return false;
                    }
                    path.add(node);
                    node = follow(new Tgt(node, idx));
                    segRoot = false;
                }
                if (g == key.length - 1) {
                    leafOf[i] = node;
                    rootLeaf[i] = segRoot;
                    break;
                }
                node.searchEq(Long.MAX_VALUE, key[g], kwi);
                if (kwi.klong == Klong.NULL) {
                    if (values[i] != null) {
                        return false;               // a new segment tree
                    }
                    break;                          // a delete of a key not there: a noop
                }
                path.add(node);
                node = follow(new Tgt(node, kwi.pointerIndex));
            }
            pathEnd[i] = path.size();
        }
        // The leaves, each once: a leaf's operations need not be consecutive in key order (a
        // segment leaf holds keys before and after the keys of a segment tree below it).
        final KeyNode[] leaves = new KeyNode[n];
        int nl = 0;
        for (int i = 0; i < n; i++) {
            if (leafOf[i] != null && indexOf(leaves, nl, leafOf[i]) < 0) {
                leaves[nl++] = leafOf[i];
            }
        }
        for (int l = 0; l < nl; l++) {
            if (!shortLeaf(leaves[l], leafOf, rootLeaf, liveOp)) {
                return false;
            }
        }
        // Written: the values and delete nodes in key order, then each leaf's klongs.
        final Tgt[] made = new Tgt[n];
        for (int k = 0; k < n; k++) {
            if (leafOf[k] == null) {
                continue;
            }
            if (values[k] != null) {
                final ValueNode vn = new ValueNode(values[k]);
                pd.nodeChangeListener.valueNodeCreated(vn, keys[k]);
                made[k] = new Tgt(vn);
            } else if (liveOp[k]) {
                pd.nodeChangeListener.valueNodeCreated(ValueNode.createDelete(), keys[k]);
            } else {
                leafOf[k] = null;                   // a noop
            }
        }
        // Emit reports a segment tree after the trees below its leaves, then its own nodes
        // in post-order. A node follows the last operation through it and its deeper nodes.
        // Keep only paths that wrote; a missing delete supplies no mark.
        if (n == 1) {
            // One operation: the order below is its path from the leaf up (each mark of
            // segment g and depth q, the q-th node of the path; sorted by segment, then
            // depth, both decreasing, it is the path reversed), with no list to sort.
            if (leafOf[0] != null) {
                final ArrayList<Ent> ch = new ArrayList<Ent>(1);
                ch.add(new Ent(keys[0][keys[0].length - 1], made[0] != null ? made[0] : REMOVED));
                appendChanges(leafOf[0], null, ch);
                Dag.statAppends++;
                for (int q = pathEnd[0] - 1; q >= 0; q--) {
                    pd.nodeChangeListener.keyNodeOnPath(path.get(q));
                }
            }
            return true;
        }
        final ArrayList<ShortMark> order = new ArrayList<ShortMark>();
        for (int k = 0; k < n; k++) {
            if (leafOf[k] == null) continue;
            final int start = k == 0 ? 0 : pathEnd[k - 1];
            int g = 0;
            for (int q = start; q < pathEnd[k]; q++) {
                final KeyNode x = path.get(q);
                shortMark(order, x, k, g, q - start);
                if (x.isSegmentLeaf()) g++;
            }
            shortMark(order, leafOf[k], k, g, pathEnd[k] - start);
        }
        order.sort((a, b) -> {
            // A tree is named by the segments before it: sibling trees in key order,
            // a descendant tree before its ancestor tree (the space root's tree last).
            for (int g = 0; g < Math.min(a.segment, b.segment); g++) {
                int cmp = Long.compareUnsigned(keys[a.lastOp][g], keys[b.lastOp][g]);
                if (cmp != 0) return cmp;
            }
            if (a.segment != b.segment) return Integer.compare(b.segment, a.segment);
            int cmp = Integer.compare(a.lastOp, b.lastOp);
            return cmp != 0 ? cmp : Integer.compare(b.depth, a.depth);
        });
        for (ShortMark mark : order) {
            final KeyNode x = mark.node;
            ArrayList<Ent> ch = null;                   // made for a leaf only
            for (int k = 0; k < n; k++) {
                if (leafOf[k] == x) {
                    if (ch == null) {
                        ch = new ArrayList<Ent>(2);
                    }
                    ch.add(new Ent(keys[k][keys[k].length - 1], made[k] != null ? made[k] : REMOVED));
                }
            }
            if (ch != null) {
                appendChanges(x, null, ch);
                Dag.statAppends++;
            } else {
                pd.nodeChangeListener.keyNodeOnPath(mark.node);
            }
        }
        return true;
    }

    /** The index of x in a[0, n), or -1. */
    private static int indexOf(KeyNode[] a, int n, KeyNode x) {
        for (int i = 0; i < n; i++) {
            if (a[i] == x) {
                return i;
            }
        }
        return -1;
    }

    /**
     * The short way's decision of segment leaf 'leaf', with the operations k whose leafOf[k] is
     * it: appended to (or kept), with a live klong left and, but a root of its tree, at least
     * m if changed, as decideNode decides by counts; false if not. Sets liveOp[k] for them.
     *
     * <p>By counts over the leaf's live list, without the list (bergdb 028-19): a leaf without
     * room for its puts' klongs and one more is full whatever the counts (the size test below,
     * extra being at least 1 + added), so it is found before the live klongs are read; else
     * liveInto's pass gives the counts and the live compare values, in live()'s work arrays.</p>
     */
    private boolean shortLeaf(KeyNode leaf, KeyNode[] leafOf, boolean[] rootLeaf, boolean[] liveOp) {
        final int e = leafOf.length;
        int puts = 0;
        for (int k = 0; k < e; k++) {
            if (leafOf[k] == leaf && values[k] != null) {
                puts++;
            }
        }
        final int sz = leaf.size;
        if (puts > 0 && sz + 1 + puts > maxNodeSize) {
            return false;
        }
        final long[][] work = liveWork(sz);
        final long[] wcv = work[0];
        final long nk = liveInto(leaf.klongs, sz, wcv, null);
        final int n0 = (int) nk;
        final int keyKlongs = (int) (nk >>> 32);
        boolean isRoot = false;
        int nf = n0;
        int removed = 0;
        int added = 0;
        int repointed = 0;
        for (int k = 0; k < e; k++) {
            if (leafOf[k] != leaf) {
                continue;
            }
            isRoot = rootLeaf[k];
            final long cv = keys[k][keys[k].length - 1];
            final boolean in = java.util.Arrays.binarySearch(wcv, sz - n0, sz, cv) >= 0;
            if (values[k] != null) {
                added++;
                if (in) {
                    repointed++;
                } else {
                    nf++;
                }
            } else if (in) {
                removed++;
                nf--;
            }
            liveOp[k] = in;
        }
        if (added + removed == 0) {
            return true;
        }
        final int extra = (removed > 0 ? 2 : 1) + added;
        final int dead = (keyKlongs - n0) + removed + repointed;
        return !(nf < 1 || (!isRoot && merges && nf < m) || sz + extra > maxNodeSize
                || (theta != 0 && dead > theta));
    }

    /**
     * The child of an inner node for compare value cv, as route finds it: the latest live klong
     * of the greatest compare value at or below cv. -1 if the node's first live klong is not the
     * empty key, or, for a root of its segment tree ('segRoot'), if it has fewer than two live
     * klongs (settleRoot would collapse it): the short way is not taken.
     */
    private static int innerChild(KeyNode x, long cv, boolean segRoot) {
        final int sz = x.size;
        final long[] ks = x.klongs;
        long del = Klong.DELETE_NONE_BITMAP;
        boolean haveDel = false;
        boolean empty = false;
        long bestCv = -1;
        int best = -1;
        boolean other = false;              // a live compare value other than the empty key's
        for (int i = sz - 1; i >= 0; i--) { // from the end, as live()
            final long k = ks[i];
            final int type = Klong.getIntType(k);
            if (type == Klong.INT_TYPE_DELETE_BITMAP) {
                if (!haveDel) {
                    del = k;
                    haveDel = true;
                }
                continue;
            }
            if (type != Klong.INT_TYPE_KEY || Klong.isDeleted(del, i)) {
                continue;
            }
            final long c = Klong.getCompareValue(k);
            if (c == 0) {
                empty = true;
            } else {
                other = true;
            }
            if (c <= cv && c > bestCv) {    // the latest klong of the best compare value
                bestCv = c;
                best = i;
            }
        }
        if (!empty || (segRoot && !other)) {
            return -1;
        }
        return best;
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
                return new LeafFrame(null, null, null, g, lo, hi);
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
            final Object e = emit(s);
            if (!(e instanceof Tgt)) {
                throw new Bug("PE at " + tt + ": a segment root emitted more than one node.");
            }
            result = new Sub((Tgt) e, s instanceof VN && ((VN) s).wrote);
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
            return new LeafFrame(x, from, live(x), g, lo, hi);
        }
        return new NodeFrame(x, from, g, lo, hi, depth);
    }

    /** At most this many operations an inner node routes by searches, not by its live list
     *  (16 until bergdb 028-19, when the list was an object of its own). */
    private static final int SEARCH_ROUTE = 4;

    /**
     * plan of an inner node x (PeWriter.lean's plan, planKids): its operations divided among its
     * children by its live list (route), each child with operations planned one height down,
     * then rebalance, then mkNode.
     *
     * <p>The children of a few operations are found by searches (KeyNode.searchLte at the
     * latest time: the live klong of the greatest compare value at or below the operation's,
     * which is route's child when the first live klong is the empty key); of more, by route
     * over the live compare values of liveInto's pass, in live()'s work arrays (bergdb
     * 028-19). Neither makes the live list, which is made only if the node is not kept as it
     * was, or appended to by counts.</p>
     */
    private final class NodeFrame extends Frame {
        final KeyNode x;
        final Tgt from;
        final int g, depth;
        Live lv;
        // The children with operations, in order: their compare values, klong indexes, and
        // first operations (cStart[nc] = hi).
        long[] cCv;
        int[] cIdx;
        int[] cStart;
        int nc;
        boolean emptyKeyFirst;
        final ArrayList<Ent> planned = new ArrayList<Ent>(2);     // the children planned
        int j = 0;
        int hk = -1;                // the children's height, from a planned child
        boolean waiting;

        NodeFrame(KeyNode x, Tgt from, int g, int lo, int hi, int depth) {
            this.x = x;
            this.from = from;
            this.g = g;
            this.depth = depth;
            if (hi - lo > SEARCH_ROUTE || !routeBySearch(lo, hi)) {
                nc = 0;
                emptyKeyFirst = false;
                routeByLive(lo, hi);
            }
        }

        /**
         * The children of the operations by a scan of the node (as KeyNode.searchLte at the
         * latest time for each, in one pass): for each operation, the live klong of the greatest
         * compare value at or below its, the latest of that compare value; and whether the
         * smallest live compare value is the empty key's. False if one finds none.
         */
        private boolean routeBySearch(int lo, int hi) {
            final int sz = x.size;
            final long[] ks = x.klongs;
            final int k = hi - lo;
            final long[] bestCv = cCv = new long[k];
            final int[] bestIdx = cIdx = new int[k];
            java.util.Arrays.fill(bestIdx, -1);
            long del = Klong.DELETE_NONE_BITMAP;
            boolean haveDel = false;
            for (int i = sz - 1; i >= 0; i--) {     // from the end, as live()
                final long klong = ks[i];
                final int type = Klong.getIntType(klong);
                if (type == Klong.INT_TYPE_DELETE_BITMAP) {
                    if (!haveDel) {
                        del = klong;
                        haveDel = true;
                    }
                    continue;
                }
                if (type != Klong.INT_TYPE_KEY || Klong.isDeleted(del, i)) {
                    continue;
                }
                final long cv = Klong.getCompareValue(klong);
                if (cv == 0) {
                    emptyKeyFirst = true;
                }
                // The operations are in increasing order of segment g: those at or above cv are
                // the last ones.
                for (int o = k - 1; o >= 0 && cv <= keys[lo + o][g]; o--) {
                    if (bestIdx[o] < 0 || cv > bestCv[o]) {
                        bestCv[o] = cv;
                        bestIdx[o] = i;
                    }
                }
            }
            if (!emptyKeyFirst) {
                return false;
            }
            cStart = new int[k + 1];
            for (int o = 0; o < k; o++) {          // compacted in place: nc <= o
                if (bestIdx[o] < 0) {
                    return false;
                }
                if (nc == 0 || cIdx[nc - 1] != bestIdx[o]) {
                    cCv[nc] = bestCv[o];
                    cIdx[nc] = bestIdx[o];
                    cStart[nc] = lo + o;
                    nc++;
                }
            }
            cStart[nc] = hi;
            return true;
        }

        /**
         * The children of the operations by the live list (PeWriter.lean's route: by segment g
         * of the keys of [lo, hi), which are in key order, the first child every operation
         * below the second compare value, each other child those from its compare value to the
         * next one's), the list read by liveInto's pass into the work arrays, not made; the
         * children with operations kept, in order.
         */
        private void routeByLive(int lo, int hi) {
            final int sz = x.size;
            final long[][] work = liveWork(sz);
            final long[] wcv = work[0];
            final long[] widx = work[1];
            final int n = (int) liveInto(x.klongs, sz, wcv, widx);
            if (n == 0) {
                throw new DbException("Key node " + x.getId() + ", not a segment leaf, has no "
                        + "live klong at time " + tt + ": corrupt data.");
            }
            final int b = sz - n;
            emptyKeyFirst = wcv[b] == 0;
            final int most = Math.min(n, hi - lo);
            cCv = new long[most];
            cIdx = new int[most];
            cStart = new int[most + 1];
            nc = 0;
            int i = lo;
            for (int j = 0; j < n && i < hi; j++) {
                int e = hi;
                if (j + 1 < n) {
                    final long next = wcv[b + j + 1];
                    e = i;
                    while (e < hi && keys[e][g] < next) {
                        e++;
                    }
                }
                if (e > i) {
                    cCv[nc] = wcv[b + j];
                    cIdx[nc] = (int) widx[b + j];
                    cStart[nc] = i;
                    nc++;
                    cStart[nc] = e;
                    i = e;
                }
            }
        }

        Frame step(Object r) {
            if (waiting) {
                waiting = false;
                final VN v = (VN) r;
                hk = v.h;
                planned.add(new Ent(cCv[j], v));
                j++;
            }
            if (j < nc) {
                final Tgt t = new Tgt(x, cIdx[j]);
                waiting = true;
                return planFrame(follow(t), t, g, cStart[j], cStart[j + 1], depth + 1);
            }
            if (hk < 0) {
                throw new Bug("PE at " + tt + ": inner key node " + x.getId()
                        + " planned no child.");
            }
            // The short way: every child planned keeps its base, is not empty, and is not one
            // that rebalance joins; and the list starts with the empty key. Then the final list
            // is the live list, and the decision same, as mkNode would find.
            boolean keep = emptyKeyFirst;
            for (int i = 0; i < planned.size() && keep; i++) {
                final VN v = (VN) planned.get(i).ch;
                keep = v.dec < 1 && !v.isEmpty() && !(merges && v.changed() && v.size() < m);
            }
            if (keep) {
                final VN v = new VN(x, lv, from, g, hk + 1, false, planned, null, SAME);
                v.sparse = true;
                result = v;
                return null;
            }
            final VN a = appendedByCounts();
            if (a != null) {
                result = a;
                return null;
            }
            if (lv == null) {
                lv = live(x);
            }
            final ArrayList<Ent> es2 = rebalance(g, hk, entries(x, lv, planned));
            result = mkNode(x, lv, from, g, hk + 1, false, es2);
            return null;
        }

        /**
         * The node appended to, decided by counts (as LeafFrame's short way), or null: when no
         * child planned is empty or joined, and the list starts with the empty key, rebalance
         * changes nothing, and the final list is the live list with each child planned that is
         * not kept replaced by its entries (ents: its new nodes); decideNode's counts follow.
         * Its klongs are written by emit (appendPlanned). The counts of the live list are those
         * of liveInto's pass when the list was not made (routeBySearch), without making it: the
         * node's VN makes it if a join or a settle needs it (VN.lb()), bergdb 028-19.
         */
        private VN appendedByCounts() {
            if (!emptyKeyFirst) {
                return null;
            }
            int grown = 0;
            int added = 0;
            int repointed = 0;
            for (Ent e : planned) {
                final VN v = (VN) e.ch;
                if (v.isEmpty() || (merges && v.changed() && v.size() < m)) {
                    return null;
                }
                if (v.dec >= 1) {
                    final int k = v.dec >= 2 ? v.dec : 1;
                    added += k;
                    repointed++;
                    grown += k - 1;
                }
            }
            final int extra = 1 + added;
            final int sz = x.size;
            if (sz + extra > maxNodeSize) {
                return null;
            }
            final int n0;
            final int keyKlongs;
            if (lv != null) {
                n0 = lv.n;
                keyKlongs = lv.keys;
            } else {
                final long nk = liveInto(x.klongs, sz, liveWork(sz)[0], null);
                n0 = (int) nk;
                keyKlongs = (int) (nk >>> 32);
            }
            final int dead = (keyKlongs - n0) + repointed;
            if (theta != 0 && dead > theta) {
                return null;
            }
            final int nf = n0 + grown;
            final VN v = new VN(x, lv, from, g, hk + 1, false, planned, null, APPEND);
            v.sparse = true;
            v.nFinal = nf;
            v.counted = true;
            return v;
        }
    }

    /**
     * A segment leaf's entries with the operations applied (PeWriter.lean's applyGroups), by
     * compare value: a put of a key that ends here sets a new value, a delete removes the entry,
     * and the operations of keys with more segments go to the next segment's tree (a
     * TreeFrame), whose new root, or none, is the entry. Then the decision. 'x' null: a new
     * tree's leaf.
     *
     * <p>The entries are kept as changes over the leaf's live list ('ch', in increasing order
     * of compare value: an entry set, or REMOVED), so that a leaf kept or appended to is decided
     * by counts, as decideNode decides it, without its lists (the short way); a leaf cut or
     * replaced, or a new tree's, gets its whole list, merged, and mkNode.</p>
     */
    private final class LeafFrame extends Frame {
        final KeyNode x;
        final Tgt from;
        final Live lv;
        final int g, hi;
        final ArrayList<Ent> ch = new ArrayList<Ent>(4);
        int pos;
        long pendingCv;
        boolean waiting;
        boolean subWrote;

        LeafFrame(KeyNode x, Tgt from, Live lv, int g, int lo, int hi) {
            this.x = x;
            this.from = from;
            this.lv = lv;
            this.g = g;
            this.pos = lo;
            this.hi = hi;
        }

        Frame step(Object r) {
            if (waiting) {
                waiting = false;
                if (r != null) {
                    setChange(x, lv, ch, pendingCv, ((Sub) r).root);
                    subWrote |= ((Sub) r).wrote;
                } else if (current(x, lv, ch, pendingCv) != null) {
                    setChange(x, lv, ch, pendingCv, REMOVED);
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
                        setChange(x, lv, ch, cv, new Tgt(vn));
                    } else if (current(x, lv, ch, cv) != null) {
                        pd.nodeChangeListener.valueNodeCreated(ValueNode.createDelete(), keys[i]);
                        setChange(x, lv, ch, cv, REMOVED);
                    }
                }
                if (subLo < end) {
                    final Tgt old = current(x, lv, ch, cv);
                    pendingCv = cv;
                    waiting = true;
                    final int subHi = end;
                    pos = end;
                    return new TreeFrame(old, g + 1, firstLong(subLo, subHi, g), subHi, false);
                }
                pos = end;
            }
            result = leafNode();
            return null;
        }

        /** The leaf's planned node: by counts if kept or appended to, else by its list. */
        private VN leafNode() {
            if (x != null) {
                int n = lv.n;
                int removed = 0;
                int added = 0;
                int repointed = 0;
                for (Ent e : ch) {
                    final boolean inLive = inLive(lv, e.cv);
                    if (e.ch == REMOVED) {
                        n--;
                        removed++;
                    } else {
                        added++;
                        if (inLive) {
                            repointed++;
                        } else {
                            n++;
                        }
                    }
                }
                // decideNode with the counts: same, or append if it fits and leaves at most
                // theta dead klongs (as decide()).
                final boolean same = ch.isEmpty();
                final int extra = (removed > 0 ? 2 : 1) + added;
                final int dead = (lv.keys - lv.n) + removed + repointed;
                if (same || (x.size + extra <= maxNodeSize && !(theta != 0 && dead > theta))) {
                    final VN v = new VN(x, lv, from, g, 0, false, null, null, same ? SAME : APPEND);
                    v.changes = ch;
                    v.nFinal = n;
                    v.subWrote = subWrote;
                    return v;
                }
            }
            final VN v = mkNode(x, lv, from, g, 0, false, merged(x, lv, ch));
            v.subWrote = subWrote;
            return v;
        }
    }

    /** A removed entry among a leaf's changes. */
    private static final Object REMOVED = new Object();

    /** The entry of compare value cv of a leaf with changes ch over its live list lv (x null:
     *  a new tree's leaf, no list), or null. */
    private static Tgt current(KeyNode x, Live lv, List<Ent> ch, long cv) {
        final int k = findSorted(ch, cv);
        if (k >= 0) {
            final Object c = ch.get(k).ch;
            return c == REMOVED ? null : (Tgt) c;
        }
        if (lv == null) {
            return null;
        }
        final int j = java.util.Arrays.binarySearch(lv.cv, 0, lv.n, cv);
        return j < 0 ? null : new Tgt(x, lv.idx[j]);
    }

    /** Sets the change of compare value cv to c, a Tgt or REMOVED; a Tgt that is the live
     *  list's own entry leaves no change. */
    private static void setChange(KeyNode x, Live lv, ArrayList<Ent> ch, long cv, Object c) {
        int j = lv == null ? -1 : java.util.Arrays.binarySearch(lv.cv, 0, lv.n, cv);
        final boolean original = c instanceof Tgt && j >= 0 && ((Tgt) c).src == x
                && ((Tgt) c).idx == lv.idx[j];
        final boolean absent = c == REMOVED && j < 0;
        final int k = findSorted(ch, cv);
        if (original || absent) {
            if (k >= 0) {
                ch.remove(k);
            }
            return;
        }
        if (k >= 0) {
            ch.set(k, new Ent(cv, c));
            return;
        }
        ch.add(-k - 1, new Ent(cv, c));
    }

    /** The index of cv in a list in increasing order of compare values, or -(insertion
     *  point) - 1, as Arrays.binarySearch. */
    private static int findSorted(List<Ent> ch, long cv) {
        int lo = 0;
        int hi = ch.size() - 1;
        while (lo <= hi) {
            final int mid = (lo + hi) >>> 1;
            final long c = ch.get(mid).cv;
            if (c < cv) {
                lo = mid + 1;
            } else if (c > cv) {
                hi = mid - 1;
            } else {
                return mid;
            }
        }
        return -(lo + 1);
    }

    /** A leaf's whole list: its live list with the changes ch, each child an old pointer or
     *  a node made. */
    private static ArrayList<Ent> merged(KeyNode x, Live lv, List<Ent> ch) {
        final int n0 = lv == null ? 0 : lv.n;
        final ArrayList<Ent> es = new ArrayList<Ent>(n0 + ch.size());
        int k = 0;
        for (int j = 0; j < n0; j++) {
            final long cv = lv.cv[j];
            while (k < ch.size() && ch.get(k).cv < cv) {
                final Ent e = ch.get(k++);
                if (e.ch != REMOVED) {
                    es.add(e);
                }
            }
            if (k < ch.size() && ch.get(k).cv == cv) {
                final Ent e = ch.get(k++);
                if (e.ch != REMOVED) {
                    es.add(e);
                }
                continue;
            }
            es.add(new Ent(cv, new Tgt(x, lv.idx[j])));
        }
        while (k < ch.size()) {
            final Ent e = ch.get(k++);
            if (e.ch != REMOVED) {
                es.add(e);
            }
        }
        return es;
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

    /**
     * The live klongs of a key node, in compare order: compare values and klong indexes; and
     * the number of its key klongs.
     */
    static final class Live {
        final long[] cv;
        final int[] idx;
        int n;
        int keys;

        Live(long[] cv, int[] idx, int n, int keys) {
            this.cv = cv;
            this.idx = idx;
            this.n = n;
            this.keys = keys;
        }
    }

    /** live()'s work arrays (a node has at most Dag.MAX_NODE_SIZE klongs, but a damaged one). */
    private static final ThreadLocal<long[][]> LIVE_WORK = new ThreadLocal<long[][]>();

    /** This thread's work arrays for liveInto, of at least sz entries each. */
    private static long[][] liveWork(int sz) {
        long[][] work = LIVE_WORK.get();
        if (work == null || work[0].length < sz) {
            work = new long[][] {new long[Math.max(sz, 64)], new long[Math.max(sz, 64)]};
            LIVE_WORK.set(work);
        }
        return work;
    }

    /**
     * Contract's live: for each compare value with a key klong that the last bitmap does not
     * delete, the last such klong; in increasing order of the compare values.
     */
    static Live live(KeyNode node) {
        final int sz = node.size;
        final long[][] work = liveWork(sz);
        final long[] wcv = work[0];
        final long[] widx = work[1];
        final long nk = liveInto(node.klongs, sz, wcv, widx);
        final int n = (int) nk;
        final long[] cv = java.util.Arrays.copyOfRange(wcv, sz - n, sz);
        final int[] idx = new int[n];
        for (int j = 0; j < n; j++) {
            idx[j] = (int) widx[sz - n + j];
        }
        return new Live(cv, idx, n, (int) (nk >>> 32));
    }

    /**
     * live()'s pass over klongs ks[0, sz): the live compare values, in increasing order, into
     * wcv[sz - n, sz), and their klong indexes into widx (if not null) at the same places;
     * returns n, the number of live compare values, in the low 32 bits and the number of key
     * klongs in the high 32.
     */
    private static long liveInto(long[] ks, int sz, long[] wcv, long[] widx) {
        // One pass from the end: a key klong after the last bitmap is not deleted by it, and
        // the first klong of a compare value met is its latest. The list is made at the end of
        // the work arrays, [b, sz), in increasing order (met from the end, the klongs of a node
        // mostly come in decreasing order, each at the front).
        int n = 0;
        int keys = 0;
        long del = Klong.DELETE_NONE_BITMAP;
        boolean haveDel = false;
        for (int i = sz - 1; i >= 0; i--) {
            final long k = ks[i];
            final int type = Klong.getIntType(k);
            if (type == Klong.INT_TYPE_DELETE_BITMAP) {
                if (!haveDel) {
                    del = k;
                    haveDel = true;
                }
                continue;
            }
            if (type != Klong.INT_TYPE_KEY) {
                continue;
            }
            keys++;
            if (Klong.isDeleted(del, i)) {
                continue;
            }
            final long cv = Klong.getCompareValue(k);
            final int b = sz - n;
            int j = b;
            while (j < sz && wcv[j] < cv) {
                j++;
            }
            if (j < sz && wcv[j] == cv) {
                continue;                       // an earlier klong of it: shadowed
            }
            System.arraycopy(wcv, b, wcv, b - 1, j - b);
            wcv[j - 1] = cv;
            if (widx != null) {
                System.arraycopy(widx, b, widx, b - 1, j - b);
                widx[j - 1] = i;
            }
            n++;
        }
        return ((long) keys << 32) | n;
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

    /** An inner node's entries: its live list, the children planned in their places (by
     *  compare value), the others old pointers. */
    private static ArrayList<Ent> entries(KeyNode x, Live lv, List<Ent> planned) {
        final ArrayList<Ent> es = new ArrayList<Ent>(lv.n);
        int k = 0;
        for (int j = 0; j < lv.n; j++) {
            if (k < planned.size() && planned.get(k).cv == lv.cv[j]) {
                es.add(planned.get(k++));
            } else {
                es.add(new Ent(lv.cv[j], new Tgt(x, lv.idx[j])));
            }
        }
        return es;
    }

    /** A planned node's entries, made whole for a sparse one or a leaf by counts. */
    private static ArrayList<Ent> entries(VN v) {
        return v.sparse ? entries(v.base, v.lb(), v.es)
                : v.changes != null ? merged(v.base, v.lb, v.changes) : v.es;
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
    private VN mkNode(KeyNode base, Live lb, Tgt from, int g, int ht, boolean join,
            ArrayList<Ent> es0) {
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
        final VN v = new VN(base, lb, from, g, ht, join, es, f, decide(base, lb, join, f));
        v.compact = compacted;
        return v;
    }

    /** The entry e of F is the live klong of its compare value in 'base' (lb its live list). */
    private static boolean kept(KeyNode base, Live lb, FEnt e) {
        if (e.t == null || e.t.src != base) {
            return false;
        }
        final int j = java.util.Arrays.binarySearch(lb.cv, 0, lb.n, e.cv);
        return j >= 0 && lb.idx[j] == e.t.idx;
    }

    /**
     * The compare values of lb that F leaves out (removedCvs), in increasing order: both lists
     * are in increasing order of their compare values.
     */
    private static long[] removedCvs(Live lb, List<FEnt> f) {
        long[] r = null;
        int nr = 0;
        int k = 0;
        for (int j = 0; j < lb.n; j++) {
            final long cv = lb.cv[j];
            while (k < f.size() && f.get(k).cv < cv) {
                k++;
            }
            if (k < f.size() && f.get(k).cv == cv) {
                continue;
            }
            if (r == null) {
                r = new long[lb.n - j];
            }
            r[nr++] = cv;
        }
        return r == null ? NONE : java.util.Arrays.copyOf(r, nr);
    }

    private static final long[] NONE = new long[0];

    /** The entry e of F has a compare value that lb has (a repointed entry, not a new one). */
    private static boolean inLive(Live lb, long cv) {
        return java.util.Arrays.binarySearch(lb.cv, 0, lb.n, cv) >= 0;
    }

    /** Set by decide(): its decision was by the dead klongs (VN.compact). */
    private boolean compacted;

    /** decideNode: same (F is the base's live list), append, or k new nodes. */
    private int decide(KeyNode base, Live lb, boolean join, ArrayList<FEnt> f) {
        final int n = f.size();
        if (base == null) {
            return join ? nParts(c, n) : cutParts(n);
        }
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
        final long[] removed = removedCvs(lb, f);
        int added = 0;
        int repointed = 0;
        for (FEnt e : f) {
            if (!kept(base, lb, e)) {
                added++;
                if (inLive(lb, e.cv)) {
                    repointed++;
                }
            }
        }
        final int extra = (removed.length > 0 ? 2 : 1) + added;
        if (base.size + extra <= maxNodeSize) {
            // deadOver: the dead klongs of the base with them, the key klongs that are not live
            // now and the live ones that the bitmap deletes or a klong added shadows (an added
            // klong is live: F has one entry a compare value).
            final int dead = (lb.keys - lb.n) + removed.length + repointed;
            if (theta != 0 && dead > theta) {
                compacted = true;
                return n + 1 <= maxNodeSize ? 1 : cutParts(n);
            }
            return APPEND;
        }
        return cutParts(n);
    }

    /** emitBits: the last bitmap and the bits of every key klong of the compare values that
     *  F leaves out ('removed', in increasing order). */
    private static long emitBits(KeyNode base, long[] removed) {
        final int sz = base.size;
        final long[] ks = base.klongs;
        long del = lastBitmap(ks, sz);
        for (int i = 0; i < sz; i++) {
            if (Klong.getIntType(ks[i]) == Klong.INT_TYPE_KEY
                    && java.util.Arrays.binarySearch(removed, Klong.getCompareValue(ks[i])) >= 0) {
                del = Klong.delete(del, i);
            }
        }
        return del;
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
            return new ArrayList<Ent>(entries(v));
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
        final VN v = mkNode(null, null, null, g, ht, true, j2);
        Dag.statJoins++;
        Dag.statJoinsByHeight[Math.min(ht, Dag.statJoinsByHeight.length - 1)]++;
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
            if (e.ch instanceof VN && ((VN) e.ch).isEmpty()) {
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
            if (n.isEmpty()) {
                if (!space) {
                    dropped(n);
                    return null;
                }
                if (n.h == 0) {
                    return v;
                }
                dropped(n);
                return mkNode(null, null, null, g, 0, false, new ArrayList<Ent>());
            }
            if (n.h != 0 && n.size() == 1) {
                final ArrayList<Ent> es = entries(n);
                if (es.size() != 1) {
                    throw new Bug("PE at " + tt + ": a root of one entry from "
                            + es.size() + " children.");
                }
                if (n.base != null) {
                    replaced(n.base);
                }
                Dag.statCollapses++;
                v = es.get(0).ch;
                continue;
            }
            if (n.dec >= 2) {
                final ArrayList<Ent> one = new ArrayList<Ent>(1);
                one.add(new Ent(0, n));
                Dag.statNewRoots++;
                v = mkNode(null, null, null, g, n.h + 1, false, one);
                continue;
            }
            return v;
        }
    }

    // ======== Emit (PeWriter.lean's emit, emitKids, newParts) ========

    /**
     * emit: the planned subtree written, children first, each node by its decision: kept,
     * klongs appended, or its final list cut into new nodes. Gives the entries its parent gets:
     * one, what it names (a Tgt); or, for a cut into two nodes or more, their entries (Parts),
     * the first's compare value 0 (the parent puts its own).
     */
    private Object emit(Object ch) {
        if (ch instanceof Tgt) {
            return ch;
        }
        final VN v = (VN) ch;
        if (v.dec == SAME) {
            // Kept: its children planned emitted, its list not made (it is the base's).
            boolean wroteBelow = false;
            if (v.es != null) {
                for (Ent e : v.es) {
                    if (e.ch instanceof VN) {
                        emit(e.ch);
                        wroteBelow |= ((VN) e.ch).wrote;
                    }
                }
            }
            v.wrote = wroteBelow || v.subWrote;
            if (v.wrote) {
                pd.nodeChangeListener.keyNodeOnPath(v.base);
            }
            return v.from;
        }
        v.wrote = true;
        if (v.counted) {
            appendPlanned(v);
            Dag.statAppends++;
            return v.from;
        }
        if (v.dec == APPEND && v.changes != null) {
            appendChanges(v.base, v.lb, v.changes);
            Dag.statAppends++;
            return v.from;
        }
        final List<FEnt> f;
        if (v.h == 0) {
            f = v.f;            // a segment leaf's entries are old pointers or nodes made
        } else {
            final ArrayList<FEnt> fi = new ArrayList<FEnt>(v.f.size());
            for (Ent e : v.es) {
                final Object sub = emit(e.ch);
                if (sub instanceof Tgt) {
                    fi.add(new FEnt(e.cv, (Tgt) sub));
                    continue;
                }
                final List<FEnt> parts = ((Parts) sub).es;
                for (int i = 0; i < parts.size(); i++) {
                    fi.add(i == 0 ? new FEnt(e.cv, parts.get(0).t) : parts.get(i));
                }
            }
            if (!fi.isEmpty() && fi.get(0).cv != 0) {
                fi.set(0, new FEnt(0, fi.get(0).t));
            }
            f = fi;
        }
        if (v.dec == APPEND) {
            append(v.base, v.lb, f);
            Dag.statAppends++;
            return v.from;
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
        final ArrayList<FEnt> out = sizes.length > 1 ? new ArrayList<FEnt>(sizes.length) : null;
        Tgt one = null;
        int off = 0;
        for (int s : sizes) {
            // The node filled first, then reported made (its id, and its bytes counted with
            // what it holds, Residents.added), then its pointers, then changed.
            final KeyNode nn = new KeyNode(v.h == 0);
            nn.addToEnd(Klong.createTime(tt), null, Spos.NULL);
            for (int i = off; i < off + s; i++) {
                final FEnt e = f.get(i);
                addEntry(nn, v.h != 0 && i == off ? 0 : e.cv, e.t, false);
            }
            pd.nodeChangeListener.keyNodeCreated(nn);
            for (int i = 1; i < nn.size; i++) {
                reportPointer(nn, i);
            }
            pd.nodeChangeListener.keyNodeChanged(nn);
            if (out != null) {
                out.add(new FEnt(s == 0 ? 0 : f.get(off).cv, new Tgt(nn)));
            } else {
                one = new Tgt(nn);
            }
            off += s;
        }
        if (v.base != null) {
            replaced(v.base);
        }
        return out != null ? new Parts(out) : one;
    }

    /** The new nodes of a list cut into two or more, as emit gives them to the parent. */
    private static final class Parts {
        final ArrayList<FEnt> es;

        Parts(ArrayList<FEnt> es) {
            this.es = es;
        }
    }

    /** emitKs: the klongs that make the base hold F: a time klong, a bitmap if a compare
     *  value left, and a key klong for each entry new or repointed. */
    private void append(KeyNode base, Live lb, List<FEnt> f) {
        final long[] removed = removedCvs(lb, f);
        if (removed.length > 0) {
            base.addDeleteKlong(tt, emitBits(base, removed));
        }
        for (FEnt e : f) {
            if (!kept(base, lb, e)) {
                addEntry(base, e.cv, e.t, true);
            }
        }
        pd.nodeChangeListener.keyNodeChanged(base);
    }

    /**
     * emitKs for an inner node by counts (appendedByCounts): its children planned emitted, in
     * order; a key klong for each entry of a child that is not kept (its new nodes, the first
     * with the child's compare value), in increasing order of compare value (F's order); no
     * bitmap, as no compare value leaves.
     */
    private void appendPlanned(VN v) {
        for (Ent e : v.es) {
            final VN c = (VN) e.ch;
            final Object sub = emit(c);
            if (c.dec < 1) {
                continue;                       // kept: its entry is the live one
            }
            if (sub instanceof Tgt) {
                addEntry(v.base, e.cv, (Tgt) sub, true);
                continue;
            }
            final List<FEnt> parts = ((Parts) sub).es;
            for (int i = 0; i < parts.size(); i++) {
                addEntry(v.base, i == 0 ? e.cv : parts.get(i).cv, parts.get(i).t, true);
            }
        }
        pd.nodeChangeListener.keyNodeChanged(v.base);
    }

    /** emitKs for a leaf by counts: the bitmap of the entries removed, then a key klong for
     *  each entry set, in increasing order of compare value (F's order). */
    private void appendChanges(KeyNode base, Live lb, List<Ent> ch) {
        int nr = 0;
        for (Ent e : ch) {
            if (e.ch == REMOVED) {
                nr++;
            }
        }
        if (nr > 0) {
            final long[] removed = new long[nr];
            int k = 0;
            for (Ent e : ch) {
                if (e.ch == REMOVED) {
                    removed[k++] = e.cv;
                }
            }
            base.addDeleteKlong(tt, emitBits(base, removed));
        }
        for (Ent e : ch) {
            if (e.ch != REMOVED) {
                addEntry(base, e.cv, (Tgt) e.ch, true);
            }
        }
        pd.nodeChangeListener.keyNodeChanged(base);
    }

    /** A key klong of compare value cv added to 'dest', naming what t names; its pointer
     *  reported if 'report'. */
    private void addEntry(KeyNode dest, long cv, Tgt t, boolean report) {
        final long klong = Klong.compareValueToKeyKlong(cv);
        final int i;
        if (t.node != null) {
            dest.addKlong(tt, klong, t.node, pd.accessData);
            i = dest.size - 1;
        } else {
            i = dest.addKlongCopyPointer(tt, klong, t.src, t.idx);
        }
        if (report) {
            reportPointer(dest, i);
        }
    }

    /** Pointer i of 'node' made: reported if it names a node or a value in memory. */
    private void reportPointer(KeyNode node, int i) {
        final Node pointee = node.getPointerNode(i);
        if (pointee != null) {
            pd.pointerCreatedListener.pointerCreated(node, i, pointee);
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
