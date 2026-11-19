package bergdb.dag;

import java.util.*;

import bergdb.common.StringUtil;

/**
 * A2A3Check for the Dag since 2026-10-16 (WP D1 of F1-008-11; until record format 8,
 * Dag.handleFullNode; since then PE, bergdb 026-25; Db's marking): also checks the net
 * effect (no node with a klong at tt is unreachable at tt) and compares Db's marking (the marks of operations that change something, minus the nodes
 * the transaction replaced; Db.endOfOp, Db.endOfTrans) with the Lean model's marked set.
 * Written for F1-008-10, 2026-10-15, on its prototype; part of the Java tier of the Level 2
 * conformance checks (bergdb 011-11).
 *
 * Checks the SIS model's assumptions A2, A3 and A5 on the Java Dag, transaction by
 * transaction, all in memory (as DagFuzz).
 *
 * After each transaction T(i) at time tt, with R(t) the nodes reachable at time t
 * (super root at t, its root key node, live klongs at t, recursively):
 *   A3: every node created by T(i) is in R(tt).
 *   A2: every node that got a klong in T(i) is in R(tt).
 *   A5: every node in R(tt) is in R(tt of T(i-1)) or created by T(i).
 *   marked-dead: index nodes that Db would mark (followed, created, changed, super
 *       root accessed) that are not in R(tt).
 *   A6', no adoption, the weaker form (bergdb item 001, WP A4, 2026-10-16): every index
 *       node in R(tt) that a node x in R(tt) points to, live or dead, without being x's
 *       live child at tt, is reachable at tt from x (below x).
 *   TREE, one current parent (the same WP): every node in R(tt) but the super root is
 *       the live child at tt of exactly one node in R(tt).
 *   A-COPY (bergdb item 001, WPs E2 and E3, 2026-10-17; bergdb 001-08, 5.10):
 *       every pointer of a new entry (a key klong at tt, any key klong of a node the
 *       transaction created, a new top node's root and skip pointers) to a node the
 *       transaction did not create names a node of the writer's paths, or a child, live
 *       or dead, of one at tt of T(i-1). The paths: the nodes in R(tt of T(i-1)) with a
 *       node below them, themselves included, that the transaction changed or that is
 *       not in R(tt).
 *   TREE, A6' and A-COPY are assumptions of the model (SIS/Phys.lean, EvictRunOK;
 *   bergdb 001-08, 5.5), which level2.sh requires (bergdb 005-04). A6, the
 *   stronger form that item 001's plan assumed (no such index node at all), is not
 *   assumed: its failures, adoptions below the old parent, are counted for information.
 *   Java makes them where a transaction splits in place a segment root that it made
 *   (bergdb 005-04). -DdebugA6=1 prints each adoption and each A-COPY failure.
 *
 * Properties: maxnode (8), keys (200), n (300), ops (max ops per transaction, 4),
 * exact=1 (exactly ops ops), del (percent deletes, 0), long=1 (two segments for half
 * the keys), unsorted=1 (until record format 8: the ops in their random order; since then the
 * Dag gets a transaction as one batch in key order, bergdb 026-25), seeds (10), debugA6=1.
 *
 * shape=long (bergdb 024-09, step A1) takes the keys from UnlinkFuzz's long shape instead
 * (longShapeKey: 'keys' distinct keys of 1 to 5 segments that share prefixes; long is then
 * not used): many small segment trees that come and go. Until record format 8 a transaction
 * made a segment root, split it in place and emptied it again; that is where a klong to a
 * node taken back was left (fault 12 of bergdb 023-08, review C), which A-COPY counts as a
 * failure: the node is not made by the transaction, once taken back, nor on the writer's
 * paths.
 */
public class A2A3Check2 {
    static final int MAX_NODE = Integer.getInteger("maxnode", 8);
    static final int KEYS = Integer.getInteger("keys", 200);
    static final int N = Integer.getInteger("n", 300);
    static final int OPS = Integer.getInteger("ops", 4);
    static final boolean EXACT = "1".equals(System.getProperty("exact"));
    static final int DEL = Integer.getInteger("del", 0);
    static final boolean LONG = "1".equals(System.getProperty("long"));
    static final boolean UNSORTED = "1".equals(System.getProperty("unsorted"));
    static final int SEEDS = Integer.getInteger("seeds", 10);
    static final boolean SHAPE_LONG = "long".equals(System.getProperty("shape"));

    /**
     * Key i of UnlinkFuzz's long shape (the rule of UnlinkFuzz.key; TraceExport's long=2
     * uses it too): keys of one, three and five segments, the longer ones under seven
     * shared prefixes.
     */
    public static String longShapeKey(int i) {
        int a = i % 7, b = (i / 7) % 5;
        switch (i % 3) {
        case 0: return "/k/" + i;
        case 1: return "/long/prefix" + a + "/x" + b + "/" + i;
        default: return "/long/prefix" + a + "/y" + i + "/tail/more/" + b;
        }
    }

    static final PointerFollower FOLLOWER = new PointerFollower() {
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node result = predecessor.getPointerNode(pointerIndex);
            if (!Pointer.isMem(result)) {
                throw new IllegalStateException("stream pointer");
            }
            op.pointerListener.pointerFollowed(predecessor, pointerIndex, result, Pointer.TYPE_MEMORY);
            return result;
        }
    };

    static Set<Node> idSet() {
        return Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
    }

    // Totals over all seeds.
    static long trans, transA2, transA3, transA5, transDead;
    static long created, createdKey, createdTop, createdValue, notCurrentCreated, notCurrentCreatedValue;
    static long changed, changedNotCurrent, preexistingChangedNotCurrent;
    static long marked, markedDead, markedDeadPreexisting, resurrected, takenBack, joins;
    // Net effect: nodes with a klong at tt that are not current (the model's A2); the step-3
    // set of Db (marks of ops that change something, minus replaced nodes)
    // compared with the model's marked set.
    static long netChangedNotCurrent, transNetA2, step3, modelMarked, step3NotModel, modelNotStep3,
            transMarkDiff;
    // A6' and TREE (bergdb item 001, WP A4): nodes and transactions that fail them; and
    // the adoptions below the old parent, which A6' allows and A6 does not (bergdb 005-04).
    static long adoptedNotBelow, transA6w, multiParent, transTree;
    static long adoptedBelow, transBelow;
    // A-COPY (bergdb item 001, WPs E2 and E3): new pointers, and those that fail it.
    static long newPointers, aCopyFailed, transACopy, aCopyByChild;

    /** The live children of a key node at time t: for each compare value, the last
     *  key klong with time <= t that is not deleted at t. */
    static List<Node> liveChildren(KeyNode k, long t) {
        int sz = k.size;
        long del = k.getDeleteBitmapAtTime(t, sz);
        LinkedHashMap<Long, Integer> last = new LinkedHashMap<Long, Integer>();
        for (int i = 0; i < sz; i++) {
            long klong = k.klongs[i];
            if (Klong.isTime(klong)) {
                if (Klong.getTime(klong) > t) break;
                continue;
            }
            if (Klong.getType(klong) != Klong.TYPE_KEY) continue;
            if (Klong.isDeleted(del, i)) continue;
            last.put(Klong.getCompareValue(klong), i);
        }
        List<Node> result = new ArrayList<Node>();
        for (int i : last.values()) {
            Node child = k.getPointerNode(i);
            if (child == null) throw new IllegalStateException("no memory pointer");
            result.add(child);
        }
        return result;
    }

    static Set<Node> reachable(Dag dag, long t) {
        Set<Node> r = idSet();
        GetData gd = dag.newGetData();
        gd.pointerFollower = FOLLOWER;
        TopNode top = dag.getTopDs().findSuperRootAtTime(t, gd);
        if (top == null) return r;
        r.add(top);
        Deque<Node> stack = new ArrayDeque<Node>();
        stack.push(top.getPointerNode(0));
        while (!stack.isEmpty()) {
            Node x = stack.pop();
            if (!r.add(x)) continue;
            if (x instanceof KeyNode) {
                for (Node c : liveChildren((KeyNode) x, t)) stack.push(c);
            }
        }
        return r;
    }

    /** The children of a node, live or dead: the nodes its key klongs point to, or a top
     *  node's root pointer and skip pointers. */
    static Set<Node> allChildren(Node x) {
        Set<Node> result = idSet();
        if (x instanceof KeyNode) {
            KeyNode k = (KeyNode) x;
            for (int i = 0; i < k.size; i++) {
                if (Klong.getType(k.klongs[i]) != Klong.TYPE_KEY) continue;
                Node child = k.getPointerNode(i);
                if (child == null) throw new IllegalStateException("no memory pointer");
                result.add(child);
            }
        } else if (x instanceof TopNode) {
            TopNode t = (TopNode) x;
            result.add(t.getPointerNode(0));
            for (int oi = 1; oi < t.getSize(); oi++) {
                Node older = t.getPointerNode(oi);
                if (older != null) result.add(older);
            }
        }
        return result;
    }

    /** The live children of an index node at time t (a top node: its root pointer). */
    static Set<Node> liveSet(Node x, long t) {
        Set<Node> result = idSet();
        if (x instanceof KeyNode) result.addAll(liveChildren((KeyNode) x, t));
        else if (x instanceof TopNode) result.add(((TopNode) x).getPointerNode(0));
        return result;
    }

    /** A6: the index nodes in 'now' that a node in 'now' points to, live or dead, without
     *  being its live child at t. With 'notBelow', only those that are not reachable from
     *  that node at t either (A6', the weaker form). */
    static Set<Node> adoptedNodes(Set<Node> now, long t, boolean notBelow, long seed, int i) {
        Set<Node> result = idSet();
        for (Node x : now) {
            if (!x.isIndexNode()) continue;
            Set<Node> live = liveSet(x, t);
            Set<Node> below = null;
            for (Node y : allChildren(x)) {
                if (y.isIndexNode() && !live.contains(y) && now.contains(y)) {
                    if (notBelow) {
                        if (below == null) below = below(x, t);
                        if (below.contains(y)) continue;
                    }
                    result.add(y);
                    if (DEBUG_A6 && !notBelow) {
                        if (below == null) below = below(x, t);
                        System.out.println("A6 seed " + seed + " T" + i + ": " + describe(x, t)
                                + " has a dead pointer to " + describe(y, t) + ", reachable at t"
                                + (below.contains(y) ? ", below it" : ", NOT below it"));
                    }
                }
            }
        }
        return result;
    }

    /** The nodes reachable from x at time t through live pointers, x excluded. */
    static Set<Node> below(Node x, long t) {
        Set<Node> r = idSet();
        Deque<Node> stack = new ArrayDeque<Node>(liveSet(x, t));
        while (!stack.isEmpty()) {
            Node y = stack.pop();
            if (!r.add(y)) continue;
            stack.addAll(liveSet(y, t));
        }
        return r;
    }

    /** The children of a node as of time t: the nodes its key klongs up to t point to,
     *  or a top node's root pointer and skip pointers. */
    static Set<Node> childrenAt(Node x, long t) {
        Set<Node> result = idSet();
        if (x instanceof KeyNode) {
            KeyNode k = (KeyNode) x;
            for (int i = 0; i < k.size; i++) {
                long klong = k.klongs[i];
                if (Klong.isTime(klong)) {
                    if (Klong.getTime(klong) > t) break;
                    continue;
                }
                if (Klong.getType(klong) != Klong.TYPE_KEY) continue;
                Node child = k.getPointerNode(i);
                if (child == null) throw new IllegalStateException("no memory pointer");
                result.add(child);
            }
        } else if (x instanceof TopNode) {
            TopNode tn = (TopNode) x;
            result.add(tn.getPointerNode(0));
            for (int oi = 1; oi < tn.getSize(); oi++) {
                Node older = tn.getPointerNode(oi);
                if (older != null) result.add(older);
            }
        }
        return result;
    }

    /** The pointers of the entries that x got at time tt: its key klongs after a time
     *  klong of tt, or all its key klongs if the transaction created it; a new top
     *  node's root pointer and skip pointers. */
    static List<Node> entryPointers(Node x, long tt, boolean createdNow) {
        List<Node> result = new ArrayList<Node>();
        if (x instanceof KeyNode) {
            KeyNode k = (KeyNode) x;
            long time = -1;
            for (int i = 0; i < k.size; i++) {
                long klong = k.klongs[i];
                if (Klong.isTime(klong)) {
                    time = Klong.getTime(klong);
                    continue;
                }
                if (Klong.getType(klong) != Klong.TYPE_KEY) continue;
                if (createdNow || time == tt) {
                    Node child = k.getPointerNode(i);
                    if (child == null) throw new IllegalStateException("no memory pointer");
                    result.add(child);
                }
            }
        } else if (x instanceof TopNode && createdNow) {
            TopNode tn = (TopNode) x;
            result.add(tn.getPointerNode(0));
            for (int oi = 1; oi < tn.getSize(); oi++) {
                Node older = tn.getPointerNode(oi);
                if (older != null) result.add(older);
            }
        }
        return result;
    }

    /** The writer's paths: the nodes in 'before' (R at t) with a touched node below them
     *  at t, themselves included. */
    static Set<Node> writerPaths(Set<Node> before, long t, Set<Node> touched) {
        Set<Node> result = idSet();
        for (Node x : before) {
            if (touched.contains(x)) {
                result.add(x);
                continue;
            }
            for (Node y : below(x, t)) {
                if (touched.contains(y)) {
                    result.add(x);
                    break;
                }
            }
        }
        return result;
    }

    static String describe(Node x, long t) {
        if (x instanceof TopNode) return "top node " + ((TopNode) x).topNodeId;
        KeyNode k = (KeyNode) x;
        return "key node " + System.identityHashCode(k) + (k.isSegmentLeaf() ? " (segment leaf" : " (internal")
                + ", first time " + k.getFirstTime() + (k.getFirstTime() == t ? ", new" : "") + ")";
    }

    static final boolean DEBUG_A6 = "1".equals(System.getProperty("debugA6"));

    /** TREE: the nodes in 'now', the super root aside, that are the live child at t of no
     *  node or of several nodes in 'now'. */
    static Set<Node> notOneParent(Set<Node> now, Node superRoot, long t) {
        IdentityHashMap<Node, Integer> parents = new IdentityHashMap<Node, Integer>();
        for (Node x : now) {
            for (Node y : liveSet(x, t)) {
                Integer p = parents.get(y);
                parents.put(y, p == null ? 1 : p + 1);
            }
        }
        Set<Node> result = idSet();
        for (Node y : now) {
            if (y == superRoot) continue;       // The root's child: the root is not modelled here.
            Integer p = parents.get(y);
            if (p == null || p != 1) result.add(y);
        }
        return result;
    }

    static boolean hasKlongAt(KeyNode k, long t) {
        for (int i = k.size - 1; i >= 0; i--) {
            if (Klong.isTime(k.klongs[i])) return Klong.getTime(k.klongs[i]) == t;
        }
        return false;
    }

    /** The model's marked set: index nodes reachable at t with a changed node reachable
     *  from them at t (themselves included). */
    static Set<Node> modelMarked(Dag dag, long t, Set<Node> changed) {
        Set<Node> result = idSet();
        GetData gd = dag.newGetData();
        gd.pointerFollower = FOLLOWER;
        TopNode top = dag.getTopDs().findSuperRootAtTime(t, gd);
        if (top == null) return result;
        boolean below = mark(top.getPointerNode(0), t, changed, result, idSet());
        if (below || changed.contains(top)) result.add(top);
        return result;
    }

    static boolean mark(Node x, long t, Set<Node> changed, Set<Node> result, Set<Node> seen) {
        boolean any = changed.contains(x);
        if (x instanceof KeyNode) {
            for (Node c : liveChildren((KeyNode) x, t)) {
                if (mark(c, t, changed, result, seen)) any = true;
            }
            if (any) result.add(x);
        }
        return any;
    }

    static void runSeed(long seed) {
        Random rnd = new Random(seed);
        Dag dag = Dag.createEmpty(0, MAX_NODE, FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        final PutData pd = dag.newPutData();
        pd.pointerFollower = FOLLOWER;

        final Set<Node> cr = idSet(), ch = idSet(), mk = idSet(), crValue = idSet();
        final Set<Node> rp = idSet(), javaMarked = idSet();
        final List<Node> opMarks = new ArrayList<Node>();
        final boolean[] opChanged = new boolean[1];
        pd.nodeChangeListener = new Dag.NodeChangeListener() {
            public void topNodeCreated(TopNode node) { cr.add(node); opMarks.add(node); opChanged[0] = true; }
            public void keyNodeCreated(KeyNode node) { cr.add(node); opMarks.add(node); opChanged[0] = true; }
            public void valueNodeCreated(ValueNode node, long[] key) {
                if (!node.isDelete()) crValue.add(node);
                opChanged[0] = true;
            }
            public void keyNodeChanged(KeyNode node) { ch.add(node); opMarks.add(node); opChanged[0] = true; }
            public void keyNodeReplaced(KeyNode node) { rp.add(node); }
            public void topNodeReplaced(TopNode node) { rp.add(node); }
            public void keyNodeOnPath(KeyNode node) { mk.add(node); opMarks.add(node); }
        };
        final Dag.PointerListener inner = pd.pointerListener;
        pd.pointerListener = new Dag.PointerListener() {
            public void superRootAccessed(TopNode superRoot) {
                inner.superRootAccessed(superRoot);
                mk.add(superRoot);
                opMarks.add(superRoot);
            }
            public void pointerFollowed(Node pred, int idx, Node result, int type) {
                inner.pointerFollowed(pred, idx, result, type);
                if (result != null && result.isIndexNode()) { mk.add(result); opMarks.add(result); }
            }
        };

        Set<Node> prev = reachable(dag, 0);
        for (int i = 1; i <= N; i++) {
            long tt = 10 * i;
            pd.tt = tt;
            int ops = EXACT ? OPS : 1 + rnd.nextInt(OPS);
            TreeMap<long[], String> sorted = new TreeMap<long[], String>(new Comparator<long[]>() {
                public int compare(long[] a, long[] b) { return Keys.compareArrays(a, b); }
            });
            List<long[]> order = new ArrayList<long[]>();
            while (sorted.size() < ops) {
                String key = SHAPE_LONG ? longShapeKey(rnd.nextInt(KEYS)) : LONG && rnd.nextBoolean()
                        ? "/long/" + rnd.nextInt(KEYS) + "/" + rnd.nextInt(4)
                        : "/k/" + rnd.nextInt(KEYS);
                long[] seg = Keys.toSegments(key);
                if (sorted.containsKey(seg)) continue;
                String value = rnd.nextInt(100) < DEL ? null : "v" + tt + key;
                sorted.put(seg, value);
                order.add(seg);
            }
            if (!UNSORTED) {
                order = new ArrayList<long[]>(sorted.keySet());
            }
            cr.clear(); ch.clear(); mk.clear(); crValue.clear(); rp.clear(); javaMarked.clear();
            // Since record format 8 the Dag gets the transaction as one batch in key order, as
            // Db gives it, whatever 'order' is (Dag.putKvs; bergdb 026-25).
            long[][] keys = sorted.keySet().toArray(new long[0][]);
            byte[][] values = new byte[keys.length][];
            for (int k = 0; k < keys.length; k++) {
                String value = sorted.get(keys[k]);
                values[k] = value == null ? null : StringUtil.toBytes(value);
            }
            opMarks.clear();
            opChanged[0] = false;
            long joins0 = Dag.statJoins;
            dag.putKvs(keys, values, pd);
            joins += Dag.statJoins - joins0;
            pd.clearFast();
            if (opChanged[0]) javaMarked.addAll(opMarks);
            pd.clear();
            // Until record format 8 a node made by the transaction and taken back in it (bergdb
            // 023-05, P1; Dag.takeBack) was reported as made and as replaced: it was left out
            // of the net effect. The writer of format 8 makes no such node.
            for (Node x : rp) {
                if (cr.contains(x)) {
                    takenBack++;
                }
            }

            Set<Node> now = reachable(dag, tt);
            Set<Node> prevAgain = reachable(dag, tt - 10);
            if (!prevAgain.equals(prev)) {
                throw new IllegalStateException("seed " + seed + " T" + i + ": the past changed");
            }
            trans++;
            boolean a2 = false, a3 = false, a5 = false, dead = false;
            for (Node x : cr) {
                created++;
                if (x instanceof KeyNode) createdKey++; else createdTop++;
                if (!now.contains(x)) { notCurrentCreated++; a3 = true; }
            }
            for (Node x : crValue) {
                createdValue++;
                if (!now.contains(x)) { notCurrentCreatedValue++; a3 = true; }
            }
            for (Node x : ch) {
                changed++;
                if (!now.contains(x)) {
                    changedNotCurrent++;
                    a2 = true;
                    if (!cr.contains(x)) preexistingChangedNotCurrent++;
                }
            }
            Set<Node> all = idSet();
            all.addAll(mk); all.addAll(cr); all.addAll(ch);
            for (Node x : all) {
                marked++;
                if (!now.contains(x)) {
                    markedDead++;
                    dead = true;
                    if (!cr.contains(x)) markedDeadPreexisting++;
                }
            }
            for (Node x : now) {
                if (!prev.contains(x) && !cr.contains(x) && !crValue.contains(x)) {
                    resurrected++;
                    a5 = true;
                }
            }
            // Net effect: klongs at tt only in current nodes; marking as the model's.
            Set<Node> netChanged = idSet();
            for (Node x : cr) netChanged.add(x);
            for (Node x : crValue) netChanged.add(x);
            for (Node x : ch) if (hasKlongAt((KeyNode) x, tt)) netChanged.add(x);
            boolean netA2 = false;
            for (Node x : netChanged) {
                if (!now.contains(x)) { netChangedNotCurrent++; netA2 = true; }
            }
            if (netA2) transNetA2++;
            Set<Node> s3 = idSet();
            for (Node x : javaMarked) if (!rp.contains(x)) s3.add(x);
            Set<Node> mm = modelMarked(dag, tt, netChanged);
            step3 += s3.size();
            modelMarked += mm.size();
            boolean diff = false;
            for (Node x : s3) if (!mm.contains(x)) { step3NotModel++; diff = true; }
            for (Node x : mm) if (!s3.contains(x)) { modelNotStep3++; diff = true; }
            if (diff) transMarkDiff++;
            // A6' and TREE (bergdb item 001, WP A4), and A6's adoptions below the old parent.
            GetData gdTop = dag.newGetData();
            gdTop.pointerFollower = FOLLOWER;
            TopNode superRoot = dag.getTopDs().findSuperRootAtTime(tt, gdTop);
            Set<Node> ad = adoptedNodes(now, tt, false, seed, i);
            Set<Node> adNotBelow = adoptedNodes(now, tt, true, seed, i);
            Set<Node> np = notOneParent(now, superRoot, tt);
            adoptedNotBelow += adNotBelow.size();
            if (!adNotBelow.isEmpty()) transA6w++;
            Set<Node> adBelow = idSet();
            for (Node y : ad) if (!adNotBelow.contains(y)) adBelow.add(y);
            adoptedBelow += adBelow.size();
            if (!adBelow.isEmpty()) transBelow++;
            multiParent += np.size();
            if (!np.isEmpty()) transTree++;
            // A-COPY (bergdb item 001, WPs E2 and E3).
            Set<Node> touched = idSet();
            for (Node x : ch) if (prev.contains(x) && hasKlongAt((KeyNode) x, tt)) touched.add(x);
            for (Node x : prev) if (!now.contains(x)) touched.add(x);
            Set<Node> paths = writerPaths(prev, tt - 10, touched);
            Set<Node> pathChildren = idSet();
            for (Node z : paths) pathChildren.addAll(childrenAt(z, tt - 10));
            Set<Node> withEntries = idSet();
            withEntries.addAll(cr);
            withEntries.addAll(ch);
            boolean aCopy = false;
            for (Node x : withEntries) {
                for (Node y : entryPointers(x, tt, cr.contains(x))) {
                    if (cr.contains(y) || crValue.contains(y)) continue;
                    newPointers++;
                    if (paths.contains(y)) continue;
                    if (pathChildren.contains(y)) {
                        aCopyByChild++;
                        continue;
                    }
                    aCopyFailed++;
                    aCopy = true;
                    if (DEBUG_A6) {
                        System.out.println("A-COPY seed " + seed + " T" + i + ": " + describe(x, tt)
                                + " points to " + (y instanceof ValueNode ? "a value node" : describe(y, tt))
                                + ", not on the writer's paths nor a child of one");
                    }
                }
            }
            if (aCopy) transACopy++;
            if (a2) transA2++;
            if (a3) transA3++;
            if (a5) transA5++;
            if (dead) transDead++;
            prev = now;
        }
    }

    public static void main(String[] args) {
        long first = args.length > 0 ? Long.parseLong(args[0]) : 1;
        for (long s = first; s < first + SEEDS; s++) {
            runSeed(s);
        }
        System.out.println("maxnode=" + MAX_NODE + " keys=" + KEYS + " n=" + N + " ops="
                + (EXACT ? "" : "1..") + OPS + " del=" + DEL + "% long=" + LONG
                + " sorted=" + !UNSORTED + " seeds=" + SEEDS + (SHAPE_LONG ? " shape=long" : ""));
        System.out.println("  transactions " + trans + ": with a changed node not current at the end "
                + transA2 + " (A2 is the NET line below), violating A3 " + transA3 + ", A5 " + transA5
                + "; with marked nodes not current at the end " + transDead);
        System.out.println("  created index nodes " + created + " (key " + createdKey + ", top "
                + createdTop + "), not current at the end " + notCurrentCreated
                + "; created value nodes " + createdValue + ", not current " + notCurrentCreatedValue);
        System.out.println("  made and replaced in a transaction (taken back until record format 8, "
                + "bergdb 023-05; none since, 026-25) " + takenBack);
        System.out.println("  joins (merges) of the writer " + joins);
        System.out.println("  changed key nodes " + changed + ", not current at the end "
                + changedNotCurrent + " (pre-existing " + preexistingChangedNotCurrent + ")");
        System.out.println("  marked index nodes (followed, created, changed) " + marked
                + ", not current at the end " + markedDead + " (pre-existing "
                + markedDeadPreexisting + "); resurrected " + resurrected);
        System.out.println("  NET (A2): nodes with a klong at tt not current " + netChangedNotCurrent
                + " (transactions " + transNetA2 + ")");
        System.out.println("  MARKING: Db's step-3 nodes " + step3 + ", model marked " + modelMarked
                + ", in step 3 only " + step3NotModel + ", in model only " + modelNotStep3
                + " (transactions with a difference " + transMarkDiff + ")");
        System.out.println("  A6' (no adoption, an assumption of the model): adopted index nodes not below"
                + " the old parent " + adoptedNotBelow + " (transactions " + transA6w + "); below it,"
                + " which A6' allows and A6, not assumed, does not (bergdb 005-04), " + adoptedBelow
                + " (transactions " + transBelow + ")");
        System.out.println("  TREE (one current parent, an assumption of the model): nodes without exactly"
                + " one " + multiParent + " (transactions " + transTree + ")");
        System.out.println("  A-COPY (an assumption of the model: a new pointer names a node of the writer's"
                + " paths or a child of one): new pointers " + newPointers + " (to a child, not a node,"
                + " of the paths " + aCopyByChild + "), failing " + aCopyFailed + " (transactions "
                + transACopy + ")");
    }
}
