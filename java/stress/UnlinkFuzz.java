package bergdb.dag;

import java.util.*;

import bergdb.common.StringUtil;

/**
 * A randomized test of the upward unlink at a delete (bergdb 023-05, P1, P4), on the Dag alone, all
 * in memory, as DagFuzz: random transactions of puts and deletes, keys sorted in each
 * transaction as Db sorts them. After each transaction it checks, against a model of every
 * key's history:
 *
 *   gets of every key at every time;
 *   scans at every time: forward and backward, of every key, and from random start keys,
 *       inclusive and not, with a limit, at most 'scans' of them a time;
 *   the tree at the latest time: every key node reachable then has a live klong, but the
 *       space root when it is a segment leaf and the leaves the climb kept because a node
 *       above was made by the transaction (Dag.statKeptNew); every inner node's smallest live
 *       klong is the empty key (023-04, LE-b; 023-05, P4); every live key of a segment leaf is
 *       in the range its parents' klongs give it, at or after the klong that leads to it and
 *       before the next one, as every reader assumes; and the keys reachable are the model's
 *       live keys.
 *
 * Key shapes (keys=N distinct keys, shape=): "fifo" puts keys in increasing order and deletes
 * the oldest, a window of about N/4 live keys; "random" puts and deletes at random; "long"
 * as random with keys of 1 to 3 segments sharing prefixes. del=P percent deletes (random,
 * long). Stops at the first error.
 *
 * Usage: java -ea -cp build/bergdb.jar:build/stress bergdb.dag.UnlinkFuzz firstSeed rounds
 * Properties: maxnode (8), keys (60), n (150), ops (6), del (40), shape (random), scans (6).
 */
public class UnlinkFuzz {
    static final int MAX_NODE = Integer.getInteger("maxnode", 8);
    static final int KEYS = Integer.getInteger("keys", 60);
    static final int N = Integer.getInteger("n", 150);
    static final int OPS = Integer.getInteger("ops", 6);
    static final int DEL = Integer.getInteger("del", 40);
    static final int SCANS = Integer.getInteger("scans", 6);
    static final String SHAPE = System.getProperty("shape", "random");

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

    static final Comparator<String> BYTES = new Comparator<String>() {
        public int compare(String a, String b) {
            return Keys.compareArrays(Keys.toSegments(a), Keys.toSegments(b));
        }
    };

    final long seed;
    final Random rnd;
    final Dag dag;
    final TreeMap<String, TreeMap<Long, String>> model = new TreeMap<String, TreeMap<Long, String>>(BYTES);
    final List<String> log = new ArrayList<String>();
    int fifoNext = 0, fifoFirst = 0;
    long keptBefore;

    UnlinkFuzz(long seed) {
        this.seed = seed;
        this.rnd = new Random(seed);
        this.dag = Dag.createEmpty(0, MAX_NODE, FOLLOWER, Dag.DO_NOTHING_POINTER_CREATED_LISTENER);
        this.keptBefore = Dag.statKeptNew;
    }

    String key(int i) {
        if (SHAPE.equals("long")) {
            int a = i % 7, b = (i / 7) % 5;
            switch (i % 3) {
            case 0: return "/k/" + i;
            case 1: return "/long/prefix" + a + "/x" + b + "/" + i;
            default: return "/long/prefix" + a + "/y" + i + "/tail/more/" + b;
            }
        }
        return "/k/" + i;
    }

    /** Returns null if OK, else a description of the first error. */
    String run() {
        PutData pd = dag.newPutData();
        pd.pointerFollower = FOLLOWER;
        GetData gd = dag.newGetData();
        gd.pointerFollower = FOLLOWER;

        for (int i = 1; i <= N; i++) {
            long tt = 10 * i;
            pd.tt = tt;
            int ops = 1 + rnd.nextInt(OPS);
            TreeMap<String, String> trans = new TreeMap<String, String>(BYTES);
            if (SHAPE.equals("fifo")) {
                int window = Math.max(2, KEYS / 4);
                for (int k = 0; k < ops; k++) {
                    if (fifoNext - fifoFirst >= window || (fifoNext > fifoFirst && rnd.nextInt(3) == 0)) {
                        trans.put(key(fifoFirst++), null);
                    }
                    trans.put(key(fifoNext++), "v" + tt);
                }
            } else {
                while (trans.size() < ops) {
                    String key = key(rnd.nextInt(KEYS));
                    trans.put(key, rnd.nextInt(100) < DEL ? null : "v" + tt + key);
                }
            }
            StringBuilder sb = new StringBuilder("T" + i + " t=" + tt + ":");
            for (Map.Entry<String, String> e : trans.entrySet()) {
                String value = e.getValue();
                dag.putKv(Keys.toSegments(e.getKey()), value == null ? null : StringUtil.toBytes(value), pd);
                pd.clearFast();
                TreeMap<Long, String> m = model.get(e.getKey());
                if (m == null) {
                    m = new TreeMap<Long, String>();
                    model.put(e.getKey(), m);
                }
                m.put(tt, value);
                sb.append(value == null ? " del " : " put ").append(e.getKey());
            }
            pd.clear();
            log.add(sb.toString());

            String err = checkGets(tt, gd);
            if (err == null) err = checkScans(tt);
            if (err == null) err = checkTree(tt);
            if (err != null) return "after T" + i + ": " + err;
        }
        return null;
    }

    String valueAt(String key, long t) {
        Map.Entry<Long, String> e = model.get(key).floorEntry(t);
        return e == null ? null : e.getValue();
    }

    String checkGets(long tt, GetData gd) {
        for (String key : model.keySet()) {
            for (long t = 0; t <= tt; t += 10) {
                String expected = valueAt(key, t);
                byte[] got = dag.getOne(t, Keys.toSegments(key), gd);
                String actual = got == null ? null : StringUtil.toString(got);
                if (expected == null ? actual != null : !expected.equals(actual)) {
                    return "get " + key + " at " + t + ": expected " + expected + ", got " + actual;
                }
            }
        }
        return null;
    }

    List<String> scan(long t, String start, boolean inclusive, boolean forward, int limit) {
        GetMany g = dag.newGetMany();
        g.gd.pointerFollower = FOLLOWER;
        g.lookupTime = t;
        g.actualLookupTime = t;
        g.startKey = start == null ? null : Keys.toSegments(start);
        g.inclusive = inclusive;
        g.forward = forward;
        if (limit > 0) g.stopCondition = new GetMany.GetN(limit);
        dag.getMany(g);
        List<String> r = new ArrayList<String>();
        for (Kvt kvt : g.result) {
            r.add(Keys.toString(kvt.key) + "=" + StringUtil.toString(kvt.value));
        }
        return r;
    }

    List<String> expectedScan(long t, String start, boolean inclusive, boolean forward, int limit) {
        List<String> r = new ArrayList<String>();
        NavigableMap<String, TreeMap<Long, String>> m = model;
        if (start != null) {
            m = forward ? model.tailMap(start, inclusive) : model.headMap(start, inclusive);
        }
        if (!forward) m = m.descendingMap();
        for (String key : m.keySet()) {
            String v = valueAt(key, t);
            if (v == null) continue;
            r.add(key + "=" + v);
            if (limit > 0 && r.size() == limit) break;
        }
        return r;
    }

    String checkScans(long tt) {
        for (long t = 0; t <= tt; t += 10) {
            for (int s = -2; s < SCANS; s++) {
                boolean forward = s == -2 || (s >= 0 && rnd.nextBoolean());
                String start = s < 0 ? null : (rnd.nextInt(4) == 0 ? "/k/" + rnd.nextInt(KEYS) + "x"
                        : key(rnd.nextInt(Math.max(KEYS, fifoNext + 1))));
                boolean inclusive = rnd.nextBoolean();
                int limit = s < 0 ? 0 : rnd.nextInt(4);
                List<String> got = scan(t, start, inclusive, forward, limit);
                List<String> exp = expectedScan(t, start, inclusive, forward, limit);
                if (!got.equals(exp)) {
                    return "scan at " + t + " from " + start + (inclusive ? " incl" : " excl")
                            + (forward ? " forward" : " backward") + " limit " + limit
                            + ": expected " + exp + ", got " + got;
                }
            }
        }
        return null;
    }

    /** The structure at the latest time, tt. */
    String checkTree(long tt) {
        GetData gd = dag.newGetData();
        gd.pointerFollower = FOLLOWER;
        KeyNode root = dag.getTopDs().findRoot(tt, gd);
        int[] liveKeys = new int[1];
        long kept = Dag.statKeptNew - keptBefore;
        String err = walk(root, tt, -1, Long.MAX_VALUE, true, liveKeys,
                new int[] {(int) Math.min(1000, kept)});
        if (err != null) return err;
        int expected = 0;
        for (String key : model.keySet()) if (valueAt(key, tt) != null) expected++;
        if (expected != liveKeys[0]) return "live keys reachable " + liveKeys[0] + ", model " + expected;
        return null;
    }

    /**
     * Walks the live klongs below 'node' at t. Every key of its segment tree below it is in
     * [lo, hi): lo is the compare value of the klong that leads to it, hi the next one's.
     */
    String walk(KeyNode node, long t, long lo, long hi, boolean isSpaceRoot, int[] liveKeys,
            int[] emptyAllowed) {
        int sz = node.getSize();
        long del = node.getDeleteBitmapAtTime(t, sz);
        TreeMap<Long, Integer> live = new TreeMap<Long, Integer>();
        for (int i = 0; i < sz; i++) {
            long k = node.getKlong(i);
            if (Klong.isTime(k) && Klong.getTime(k) > t) break;
            if (!Klong.isKey(k) || Klong.isDeleted(del, i)) continue;
            live.put(Klong.getCompareValue(k), i);     // the latest of a compare value wins
        }
        if (live.isEmpty()) {
            if (isSpaceRoot && node.isSegmentLeaf()) return null;
            if (node.isSegmentLeaf() && emptyAllowed[0] > 0) {
                emptyAllowed[0]--;
                return null;
            }
            return "reachable key node " + System.identityHashCode(node) + (node.isSegmentLeaf()
                    ? " (segment leaf)" : " (inner)") + " has no live klong";
        }
        if (!node.isSegmentLeaf()) {
            long smallest = live.firstKey();
            if (smallest != 0) {
                return "inner node " + System.identityHashCode(node) + ": smallest live klong "
                        + smallest + ", not the empty key";
            }
        }
        for (Map.Entry<Long, Integer> e : live.entrySet()) {
            int i = e.getValue();
            long k = node.getKlong(i);
            long cv = e.getKey();
            Node child = node.getPointerNode(i);
            if (node.isSegmentLeaf()) {
                if (cv < lo || cv >= hi) {
                    return "segment leaf " + System.identityHashCode(node) + ": live key " + cv
                            + " outside its range [" + lo + ", " + hi + ")";
                }
                if (Klong.getLength(k) < Klong.MAX_SIZE) {
                    liveKeys[0]++;
                    continue;
                }
                String err = walk((KeyNode) child, t, -1, Long.MAX_VALUE, false, liveKeys,
                        emptyAllowed);
                if (err != null) return err;
            } else {
                Long next = live.higherKey(cv);
                long childHi = next == null ? hi : Math.min(hi, next);
                String err = walk((KeyNode) child, t, Math.max(lo, cv), childHi, false, liveKeys,
                        emptyAllowed);
                if (err != null) return err;
            }
        }
        return null;
    }

    public static void main(String[] args) {
        long first = Long.parseLong(args[0]);
        int rounds = Integer.parseInt(args[1]);
        int fails = 0;
        long unlinked0 = Dag.statUnlinked, relabels0 = Dag.statRelabels;
        for (long seed = first; seed < first + rounds; seed++) {
            UnlinkFuzz f = new UnlinkFuzz(seed);
            String error;
            try {
                error = f.run();
            } catch (Throwable e) {
                error = "exception after " + f.log.size() + " transactions: " + e;
                if (!"1".equals(System.getProperty("quiet"))) e.printStackTrace(System.out);
            }
            if (error != null) {
                fails++;
                System.out.println("FAIL seed=" + seed + " maxnode=" + MAX_NODE + " keys=" + KEYS
                        + " shape=" + SHAPE + ": " + error);
                if (!"1".equals(System.getProperty("quiet"))) {
                    for (String s : f.log) System.out.println("  " + s);
                }
                break;
            }
        }
        System.out.println("unlinked " + (Dag.statUnlinked - unlinked0) + ", climbs " + Dag.statClimbs
                + ", empty keys pointed to the next child " + (Dag.statRelabels - relabels0)
                + ", kept for A3 " + Dag.statKeptNew + ", new roots "
                + Dag.statNewRoots + ", collapses " + Dag.statCollapses);
        System.out.println("Done: " + rounds + " rounds, " + fails + " failures.");
    }
}
