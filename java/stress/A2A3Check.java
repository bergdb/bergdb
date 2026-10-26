package bergdb.dag;

import java.util.*;

import bergdb.common.StringUtil;

/**
 * Checks the SIS model's assumptions A2, A3 and A5 on the Java Dag, transaction by
 * transaction, all in memory (as DagFuzz). Written for F1-008-10, 2026-10-15; part of the
 * Java tier of the Level 2 conformance checks (bergdb 011-11, 8.3).
 *
 * After each transaction T(i) at time tt, with R(t) the nodes reachable at time t
 * (super root at t, its root key node, live klongs at t, recursively):
 *   A3: every node created by T(i) is in R(tt).
 *   A2: every node that got a klong in T(i) is in R(tt).
 *   A5: every node in R(tt) is in R(tt of T(i-1)) or created by T(i).
 *   marked-dead: index nodes that Db would mark (followed, created, changed, super
 *       root accessed) that are not in R(tt).
 *
 * Properties: maxnode (8), keys (200), n (300), ops (max ops per transaction, 4),
 * exact=1 (exactly ops ops), del (percent deletes, 0), long=1 (two segments for half
 * the keys), unsorted=1 (do not sort the ops), seeds (10).
 */
public class A2A3Check {
    static final int MAX_NODE = Integer.getInteger("maxnode", 8);
    static final int KEYS = Integer.getInteger("keys", 200);
    static final int N = Integer.getInteger("n", 300);
    static final int OPS = Integer.getInteger("ops", 4);
    static final boolean EXACT = "1".equals(System.getProperty("exact"));
    static final int DEL = Integer.getInteger("del", 0);
    static final boolean LONG = "1".equals(System.getProperty("long"));
    static final boolean UNSORTED = "1".equals(System.getProperty("unsorted"));
    static final int SEEDS = Integer.getInteger("seeds", 10);

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
    static long marked, markedDead, markedDeadPreexisting, resurrected;

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

    static void runSeed(long seed) {
        Random rnd = new Random(seed);
        Dag dag = Dag.createEmpty(0, MAX_NODE, FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        final PutData pd = dag.newPutData();
        pd.pointerFollower = FOLLOWER;

        final Set<Node> cr = idSet(), ch = idSet(), mk = idSet(), crValue = idSet();
        pd.nodeChangeListener = new Dag.NodeChangeListener() {
            public void topNodeCreated(TopNode node) { cr.add(node); }
            public void keyNodeCreated(KeyNode node) { cr.add(node); }
            public void valueNodeCreated(ValueNode node, long[] key) {
                if (!node.isDelete()) crValue.add(node);
            }
            public void keyNodeChanged(KeyNode node) { ch.add(node); }
        };
        final Dag.PointerListener inner = pd.pointerListener;
        pd.pointerListener = new Dag.PointerListener() {
            public void superRootAccessed(TopNode superRoot) {
                inner.superRootAccessed(superRoot);
                mk.add(superRoot);
            }
            public void pointerFollowed(Node pred, int idx, Node result, int type) {
                inner.pointerFollowed(pred, idx, result, type);
                if (result != null && result.isIndexNode()) mk.add(result);
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
                String key = LONG && rnd.nextBoolean()
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
            cr.clear(); ch.clear(); mk.clear(); crValue.clear();
            for (long[] seg : order) {
                String value = sorted.get(seg);
                dag.putKv(seg, value == null ? null : StringUtil.toBytes(value), pd);
                pd.clearFast();
            }
            pd.clear();

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
                + " sorted=" + !UNSORTED + " seeds=" + SEEDS);
        System.out.println("  transactions " + trans + ": violating A2 " + transA2 + ", A3 " + transA3
                + ", A5 " + transA5 + "; with marked nodes not current at the end " + transDead);
        System.out.println("  created index nodes " + created + " (key " + createdKey + ", top "
                + createdTop + "), not current at the end " + notCurrentCreated
                + "; created value nodes " + createdValue + ", not current " + notCurrentCreatedValue);
        System.out.println("  changed key nodes " + changed + ", not current at the end "
                + changedNotCurrent + " (pre-existing " + preexistingChangedNotCurrent + ")");
        System.out.println("  marked index nodes (followed, created, changed) " + marked
                + ", not current at the end " + markedDead + " (pre-existing "
                + markedDeadPreexisting + "); resurrected " + resurrected);
    }
}
