import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.Random;

/**
 * 005-08: real HashMaps, 256 of them as in Cache3, filled with node ids
 * of several patterns, with the old and the new map index; counts the tree nodes and the
 * longest bin in the final state (reflection; run with
 * --add-opens java.base/java.util=ALL-UNNAMED), and an exact simulation of the bins that
 * needs no reflection (as Cache3.testBinsStaySmall does), to check that they agree.
 */
public class BinSim {
    interface Index { int of(long id); }

    static final Index OLD = new Index() {
        public int of(long v) {
            long t = (v >>> 0) ^ (v >>> 8) ^ (v >>> 16) ^ (v >>> 24) ^ (v >>> 32) ^ (v >>> 40)
                    ^ (v >>> 48) ^ (v >>> 56);
            return (int) ((t & Long.MAX_VALUE) % 256);
        }
    };

    static final Index NEW = new Index() {
        public int of(long id) {
            return (int) ((id * 0x9E3779B97F4A7C15L) >>> 56);
        }
    };

    /** Bursts: 'perTrans' consecutive odd ids from start+1, then the start moves by 'gap'. */
    static long[] bursts(long start, int n, int perTrans, long gap) {
        long[] ids = new long[n];
        long p = start;
        int j = 0;
        while (j < n) {
            long v = p % 2 == 0 ? p + 1 : p + 2;
            for (int k = 0; k < perTrans && j < n; k++) {
                ids[j++] = v;
                v += 2;
            }
            p += gap;
        }
        return ids;
    }

    static long[] randomOdd(long seed, int n, long range) {
        Random r = new Random(seed);
        long[] ids = new long[n];
        for (int j = 0; j < n; j++) ids[j] = ((r.nextLong() & Long.MAX_VALUE) % range) | 1;
        return ids;
    }

    /** Final state of real HashMaps: {tree nodes, longest bin, entries}. */
    static long[] real(long[] ids, Index index) throws Exception {
        @SuppressWarnings("unchecked")
        HashMap<Long, Object>[] maps = new HashMap[256];
        for (int i = 0; i < 256; i++) maps[i] = new HashMap<Long, Object>();
        Object v = new Object();
        for (long id : ids) maps[index.of(id)].put(id, v);
        Field tf = HashMap.class.getDeclaredField("table");
        tf.setAccessible(true);
        Class<?> nodeClass = Class.forName("java.util.HashMap$Node");
        Field nextF = nodeClass.getDeclaredField("next");
        nextF.setAccessible(true);
        long trees = 0, longest = 0, entries = 0;
        for (HashMap<Long, Object> m : maps) {
            Object[] tab = (Object[]) tf.get(m);
            if (tab == null) continue;
            for (Object e : tab) {
                long len = 0;
                for (Object x = e; x != null; x = nextF.get(x)) {
                    len++;
                    entries++;
                    if (x.getClass().getName().equals("java.util.HashMap$TreeNode")) trees++;
                }
                longest = Math.max(longest, len);
            }
        }
        return new long[] {trees, longest, entries};
    }

    /**
     * The simulation: inserts the ids in order into 256 simulated HashMaps (capacity 16,
     * doubled when the size passes 0.75 of it; the bin is the low bits of h ^ h >>> 16, h
     * the Long's hash) and returns {the inserts into a bin that already held 8 or more at a
     * capacity of 64 or more (HashMap makes the bin a tree then), the largest bin met}.
     */
    static long[] sim(long[] ids, Index index) {
        int[] size = new int[256];
        int[] cap = new int[256];
        int[][] bins = new int[256][];
        long[][] members = new long[256][];
        for (int m = 0; m < 256; m++) {
            cap[m] = 16;
            bins[m] = new int[16];
            members[m] = new long[16];
        }
        long treeify = 0, largest = 0;
        for (long id : ids) {
            int m = index.of(id);
            int h = Long.valueOf(id).hashCode();
            h ^= h >>> 16;
            int b = h & (cap[m] - 1);
            if (bins[m][b] >= 8 && cap[m] >= 64) treeify++;
            bins[m][b]++;
            largest = Math.max(largest, bins[m][b]);
            if (size[m] == members[m].length) members[m] = java.util.Arrays.copyOf(members[m], 2 * size[m]);
            members[m][size[m]++] = id;
            if (size[m] > cap[m] * 3 / 4) {
                cap[m] *= 2;
                bins[m] = new int[cap[m]];
                for (int j = 0; j < size[m]; j++) {
                    int hh = Long.valueOf(members[m][j]).hashCode();
                    hh ^= hh >>> 16;
                    int bb = hh & (cap[m] - 1);
                    bins[m][bb]++;
                    largest = Math.max(largest, bins[m][bb]);
                }
            }
        }
        return new long[] {treeify, largest};
    }

    static void row(String name, long[] ids) throws Exception {
        long[] ro = real(ids, OLD), rn = real(ids, NEW);
        long[] so = sim(ids, OLD), sn = sim(ids, NEW);
        System.out.printf("%-34s n=%8d | old: trees %8d (%.2f/id) longest %3d, sim treeify %8d largest %3d"
                + " | new: trees %6d longest %2d, sim treeify %4d largest %2d%n",
                name, ids.length, ro[0], ro[0] / (double) ids.length, ro[1], so[0], so[1],
                rn[0], rn[1], sn[0], sn[1]);
    }

    public static void main(String[] args) throws Exception {
        int n = args.length > 0 ? Integer.parseInt(args[0]) : 1100000;
        row("dense odd from 1", bursts(0, n, Integer.MAX_VALUE, 0));
        for (long start : new long[] {0, (1L << 31) - 5000, (1L << 32) + 77, (1L << 40) + 12345, 5L << 44}) {
            for (int[] kg : new int[][] {{110, 3400}, {110, 5000}, {110, 9000}, {4, 150}, {1, 64},
                    {12, 800}, {1000, 30000}, {50, 24000}}) {
                row("bursts " + kg[0] + "/" + kg[1] + " from " + start, bursts(start, n, kg[0], kg[1]));
            }
        }
        row("random odd < 2^40", randomOdd(1, n, 1L << 40));
        row("random odd < 2^26", randomOdd(2, n, 1L << 26));
    }
}
