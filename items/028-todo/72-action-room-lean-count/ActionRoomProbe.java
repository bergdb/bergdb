package bergdb.core;

import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.Pointer;
import bergdb.dag.PointerFollower;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

/**
 * bergdb 028-72: Java's count, Dag.dirtyNodeBound, the walk that Db.checkDirtyNodes compares
 * with StoredTrans.actionDirtyLimit() (7/8 of the record limit), on the worst shape of tree
 * for a transaction within L1 to L5: every segment tree on the keys' paths H + 1 key nodes
 * high, every node of the paths full (B klongs, so no room), no dead klongs, the paths apart
 * below the space root's tree as far as full nodes allow. The tree is made of key nodes
 * directly, in memory: only the paths exist, the other klongs of a node are KEY klongs that
 * point nowhere and that no search of the walk picks. No record is written; the count is
 * the number Db's admission compares, at the release's record limit, and with
 * Db.dirtyNodeBytes() and StoredTrans.TOP_BYTES, the bytes.
 *
 * Usage: java -Xss1g -Xmx4g -cp CLASSES:java/build/bergdb.jar bergdb.core.ActionRoomProbe
 * [fill] [B:H ...] (fill: the klongs of every node of the paths, default B; B:H, the node
 * sizes and heights, default 8:61 14:38 30:22 30:21 62:16, 024-17, 5.2's H of a stream of
 * under 2^63 bytes). The run script is run.sh; its output is in out/.
 */
public class ActionRoomProbe {

    static final PointerFollower FOLLOW = new PointerFollower() {
        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            final Node result = predecessor.getPointerNode(pointerIndex);
            if (result == null) {
                throw new IllegalStateException("A pointer to nothing was followed.");
            }
            op.pointerListener.pointerFollowed(predecessor, pointerIndex, result,
                    Pointer.TYPE_MEMORY);
            return result;
        }
    };

    static int fillArg = -1;
    static long nodesMade;

    /** If not null, the levels of the tree of segment i, levelsBySeg[i] (RealTreeProbe). */
    public static int[] levelsBySeg = null;

    /** The klongs of each node of the paths at node size b. */
    static int fill(int b) {
        return fillArg > 0 ? Math.min(fillArg, b) : b;
    }

    /**
     * A segment tree of 'levels' levels of key nodes for the sorted values vals[from, to),
     * each pointing to targets[i] (the root of the next segment's tree, or nothing where a
     * key ends): an inner node holds a KEY klong for each of at most b - 1 groups, a leaf a
     * KEY klong for each value; each node is filled to fill(b) klongs with KEY klongs above
     * its values, which no search of a key routed to it picks.
     */
    static KeyNode tree(long[] vals, Node[] targets, int from, int to, int levels, int b) {
        final boolean leaf = levels == 1;
        final KeyNode node = new KeyNode(leaf);
        nodesMade++;
        final int n = to - from;
        if (leaf) {
            if (n > b - 1) {
                throw new IllegalStateException(n + " values in one leaf at node size " + b);
            }
            for (int i = from; i < to; i++) {
                node.addKlong(0, Klong.compareValueToKeyKlong(vals[i]), targets[i], Spos.NULL);
            }
        } else {
            final int g = Math.min(n, b - 1);
            for (int j = 0; j < g; j++) {
                final int lo = from + (int) ((long) n * j / g);
                final int hi = from + (int) ((long) n * (j + 1) / g);
                final KeyNode child = tree(vals, targets, lo, hi, levels - 1, b);
                node.addKlong(0, Klong.compareValueToKeyKlong(vals[lo]), child, Spos.NULL);
            }
        }
        long cv = vals[to - 1];
        while (node.size < fill(b)) {
            cv += 8;
            node.addKlong(0, Klong.compareValueToKeyKlong(cv), null, Spos.NULL);
        }
        return node;
    }

    /** The tree of segment 'seg' for keys that share their first seg segments, and below. */
    static KeyNode trie(List<long[]> keys, int seg, int levels, int b) {
        final TreeMap<Long, List<long[]>> by = new TreeMap<Long, List<long[]>>();
        for (long[] k : keys) {
            List<long[]> l = by.get(k[seg]);
            if (l == null) {
                l = new ArrayList<long[]>();
                by.put(k[seg], l);
            }
            l.add(k);
        }
        final long[] vals = new long[by.size()];
        final Node[] targets = new Node[by.size()];
        int i = 0;
        for (Map.Entry<Long, List<long[]>> e : by.entrySet()) {
            vals[i] = e.getKey();
            final List<long[]> sub = new ArrayList<long[]>();
            boolean ends = false;
            for (long[] k : e.getValue()) {
                if (k.length == seg + 1) {
                    ends = true;
                } else {
                    sub.add(k);
                }
            }
            if (ends && !sub.isEmpty()) {
                throw new IllegalStateException("A key ends where another goes on.");
            }
            targets[i] = sub.isEmpty() ? null : trie(sub, seg + 1, levels, b);
            i++;
        }
        final int lv = levelsBySeg == null ? levels : levelsBySeg[Math.min(seg, levelsBySeg.length - 1)];
        return tree(vals, targets, 0, vals.length, lv, b);
    }

    /** Java's count of the operations (keys[i], deletes[i]) on the worst tree of their keys. */
    public static long count(int b, int h, long[][] keys, boolean[] deletes) {
        final List<long[]> distinct = new ArrayList<long[]>();
        final TreeMap<String, Boolean> seen = new TreeMap<String, Boolean>();
        for (long[] k : keys) {
            if (seen.put(java.util.Arrays.toString(k), Boolean.TRUE) == null) {
                distinct.add(k);
            }
        }
        nodesMade = 0;
        final KeyNode root = trie(distinct, 0, h + 1, b);
        final TopNode top = new TopNode(0, root, Spos.NULL, 0, Spos.NULL);
        final Dag dag = new Dag(top, b);
        final GetData gd = dag.newGetData();
        gd.pointerFollower = FOLLOW;
        return dag.dirtyNodeBound(1, keys, deletes, gd);
    }

    static final Random R = new Random(28072);

    /** A key of 'bytes' bytes of printable characters, at random. */
    static long[] key(int bytes) {
        final byte[] k = new byte[bytes];
        for (int i = 0; i < bytes; i++) {
            k[i] = (byte) (0x21 + R.nextInt(0x5e));
        }
        return Keys.toSegments(k);
    }

    static long segments(long[][] keys) {
        long s = 0;
        for (long[] k : keys) {
            s += k.length;
        }
        return s;
    }

    /** The count with q of 024-17 and the Lean's, c (H + 2) S + 14 n. */
    static long withQ(int c, int h, long s, long n) {
        return c * (h + 2L) * s + 14L * n;
    }

    /** The Lean's nodesALevel (SIS/Tree/Bound.lean, since 028-21). */
    static int leanC(int b) {
        final int q = Math.max(2, Math.min(b / 2, Math.min(b - Dag.splitAbove(b),
                b - Dag.mergeCap(b))) - 3);
        return 8 + (3 * q + 4) / (q - 1) + (q <= 2 ? 1 : 0);
    }

    /** 024-17's count with q a level (5.2a): 14, 9, 8 and 8. */
    static int c2417(int b) {
        return b == 8 ? 14 : b == 14 ? 9 : 8;
    }

    static long nodeBytes(int b) {
        return 32 + 16L * (b + 1) + 16;            // Db.dirtyNodeBytes()
    }

    static long maxNodes(int b) {
        return (StoredTrans.actionDirtyLimit() - StoredTrans.TOP_BYTES) / nodeBytes(b);
    }

    static String pct(long nodes, int b) {
        final double bytes = nodes * (double) nodeBytes(b) + StoredTrans.TOP_BYTES;
        return String.format("%.1f %%", 100.0 * bytes / StoredTrans.actionDirtyLimit());
    }

    static void line(String what, int b, int h, long[][] keys, boolean[] deletes, long ops) {
        final long t0 = System.nanoTime();
        final long n = count(b, h, keys, deletes);
        final long ms = (System.nanoTime() - t0) / 1000000;
        final long s = segments(keys) / (keys.length / ops);   // the value-transformation
                                                               // case walks each key twice
        final double perLevel = (n - 0.0) / (s * (h + 2.0));
        System.out.printf("B=%d H=%d %-34s n=%d S=%d: Java %,d (%.2f a level, %s of 7/8)"
                + "; 024-17 %,d (%s); Lean %,d (%s); nodes made %,d, %d ms%n",
                b, h, what, ops, s, n, perLevel, pct(n, b),
                withQ(c2417(b), h, s, ops), pct(withQ(c2417(b), h, s, ops), b),
                withQ(leanC(b), h, s, ops), pct(withQ(leanC(b), h, s, ops), b),
                nodesMade, ms);
    }

    static long[][] keysOf(int[] lengths) {
        final long[][] keys = new long[lengths.length][];
        for (int i = 0; i < lengths.length; i++) {
            keys[i] = key(lengths[i]);
        }
        return keys;
    }

    static boolean[] all(int n, boolean v) {
        final boolean[] a = new boolean[n];
        java.util.Arrays.fill(a, v);
        return a;
    }

    static int[] repeat(int n, int bytes) {
        final int[] a = new int[n];
        java.util.Arrays.fill(a, bytes);
        return a;
    }

    /** 500 keys whose bytes are multiples of 7 and sum to L3, 57,344: 8,692 segments. */
    static int[] ownKeys() {
        final int[] a = new int[500];
        for (int i = 0; i < 500; i++) {
            a[i] = i < 192 ? 119 : 112;            // 192 x 17 + 308 x 16 = 8,192 full segments
        }
        return a;
    }

    static void sizes(int b, int h) {
        System.out.printf("%nNode size %d, H %d, q %d, the Lean's c %d, 024-17's c %d; "
                + "7/8 = %,d bytes, %,d nodes of %d bytes%n", b, h,
                Math.max(2, Math.min(b / 2, Math.min(b - Dag.splitAbove(b), b - Dag.mergeCap(b))) - 3),
                leanC(b), c2417(b), StoredTrans.actionDirtyLimit(), maxNodes(b), nodeBytes(b));
        for (int bytes : new int[] {6, 7, 105, 112, 1022}) {
            final long[][] k = keysOf(new int[] {bytes});
            line("one delete of " + bytes + " B", b, h, k, all(1, true), 1);
            line("one put of " + bytes + " B (it exists)", b, h, k, all(1, false), 1);
        }
        long[][] k = keysOf(new int[] {57344});
        line("one delete of 57,344 B", b, h, k, all(1, true), 1);
        k = keysOf(repeat(500, 105));
        line("500 deletes of 105 B (user keys)", b, h, k, all(500, true), 500);
        k = keysOf(ownKeys());
        line("500 deletes, 119/112 B, L3", b, h, k, all(500, true), 500);
        line("500 puts, 119/112 B, L3", b, h, k, all(500, false), 500);
        final long[][] k2 = new long[1000][];
        final boolean[] d2 = new boolean[1000];
        for (int i = 0; i < 500; i++) {
            k2[2 * i] = k[i];
            k2[2 * i + 1] = k[i];
            d2[2 * i + 1] = true;
        }
        line("500 value transformations, L3", b, h, k2, d2, 500);
        final int[] one = repeat(500, 7);
        one[499] = 57344 - 499 * 7;
        k = keysOf(one);
        line("499 deletes of 7 B, 1 of 53,851 B", b, h, k, all(500, true), 500);

        // Keys that share their first 14 segments: the paths meet, and the count is less.
        final long[][] shared = new long[500][];
        final long[] prefix = key(98);
        for (int i = 0; i < 500; i++) {
            final long[] tail = key(7);
            shared[i] = new long[16];
            System.arraycopy(prefix, 0, shared[i], 0, 14);
            System.arraycopy(tail, 0, shared[i], 14, 2);
        }
        line("500 deletes of 105 B, 14 segments shared", b, h, shared, all(500, true), 500);

        // 031-06, section 3's mixed record: the action, 500 deletes at L3, and a step of 401
        // puts of 2,060 segments (400 of 28 bytes, 5 segments, and one of 413, 60 segments),
        // walked together as recordDirtyFits() walks them, against dirtyLimit() (15/16).
        mixed(b, h, 413, "60");
        mixed(b, h, 1022, "147, a key at O1 (b)'s cap");
        mixed(b, h, 57344, "8,193, an own key at L3, O1 (a)");
    }

    /** The mixed record, the step's last KV of 'last' bytes. */
    static void mixed(int b, int h, int last, String about) {
        final long[][] action = keysOf(ownKeys());
        final int[] stepBytes = repeat(401, 28);
        stepBytes[400] = last;
        final long[][] step = keysOf(stepBytes);
        final long[][] rec = new long[action.length + step.length][];
        final boolean[] recDel = new boolean[rec.length];
        for (int i = 0; i < action.length; i++) {
            rec[i] = action[i];
            recDel[i] = true;
        }
        System.arraycopy(step, 0, rec, action.length, step.length);
        final long n = count(b, h, rec, recDel);
        final long dirtyBytes = n * nodeBytes(b) + StoredTrans.TOP_BYTES;
        final long own = 42300000L;          // 031-06, section 3: the record's own bytes
        System.out.printf("B=%d H=%d mixed record (500 deletes at L3, a step of 400 puts of 5 "
                + "segments and one of %s): Java %,d nodes, %,d bytes, %.1f %% of 15/16 (%,d); "
                + "with %,d own bytes %.1f %% of the record limit%n", b, h, about, n, dirtyBytes,
                100.0 * dirtyBytes / StoredTrans.dirtyLimit(), StoredTrans.dirtyLimit(), own,
                100.0 * (dirtyBytes + own) / StoredTrans.recordLimit);
    }

    public static void main(String[] args) throws Exception {
        int a = 0;
        if (args.length > a && !args[a].contains(":")) {
            fillArg = Integer.parseInt(args[a++]);
        }
        final List<int[]> runs = new ArrayList<int[]>();
        for (; a < args.length; a++) {
            final String[] bh = args[a].split(":");
            runs.add(new int[] {Integer.parseInt(bh[0]), Integer.parseInt(bh[1])});
        }
        if (runs.isEmpty()) {
            runs.add(new int[] {8, 61});
            runs.add(new int[] {14, 38});
            runs.add(new int[] {30, 22});
            runs.add(new int[] {30, 21});
            runs.add(new int[] {62, 16});
        }
        System.out.println("bergdb 028-72, ActionRoomProbe: record limit "
                + StoredTrans.recordLimit + ", actionDirtyLimit " + StoredTrans.actionDirtyLimit()
                + ", TOP_BYTES " + StoredTrans.TOP_BYTES + ", fill "
                + (fillArg > 0 ? fillArg : "B"));
        final Thread t = new Thread(null, new Runnable() {
            public void run() {
                for (int[] bh : runs) {
                    sizes(bh[0], bh[1]);
                }
            }
        }, "probe", 1L << 30);
        t.start();
        t.join();
        System.out.println("END");
    }
}
