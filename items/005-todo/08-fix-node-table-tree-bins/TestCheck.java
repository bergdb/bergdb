import java.util.Arrays;

/** 005-08: the numbers of Cache3.testBinsStaySmall with the old and the new index. */
public class TestCheck {
    static final int MAP_BITS = 8;

    static int newIndex(long id) {
        return (int) ((id * 0x9E3779B97F4A7C15L) >>> (64 - MAP_BITS));
    }

    static int oldIndex(long v) {
        long temp = (v >>> 0) ^ (v >>> 8) ^ (v >>> 16) ^ (v >>> 24) ^ (v >>> 32) ^ (v >>> 40)
                ^ (v >>> 48) ^ (v >>> 56);
        return (int) ((temp & Long.MAX_VALUE) % 256);
    }

    static long nextVpos(long vpos) {
        return vpos % 2 == 0 ? vpos + 1 : vpos + 2;
    }

    static int bin(long id, int capacity) {
        int h = Long.hashCode(id);
        return (h ^ (h >>> 16)) & (capacity - 1);
    }

    public static void main(String[] args) {
        long[][] cases = {{0, 110, 5000}, {(1L << 32) + 77, 4, 150}, {(1L << 40) + 12345, 1000, 30000}};
        int n = 1000 * 1000;
        for (boolean old : new boolean[] {true, false}) {
            for (long[] c : cases) {
                int[] size = new int[1 << MAP_BITS];
                long[][] ids = new long[1 << MAP_BITS][16];
                int[][] bins = new int[1 << MAP_BITS][16];
                long trees = 0;
                int largest = 0;
                int count = 0;
                long t0 = System.nanoTime();
                for (long pos = c[0]; count < n; pos += c[2]) {
                    long id = nextVpos(pos);
                    for (int k = 0; k < c[1] && count < n; k++, count++, id += 2) {
                        int m = old ? oldIndex(id) : newIndex(id);
                        int[] b = bins[m];
                        int i = bin(id, b.length);
                        if (b[i] >= 8 && b.length >= 64) trees++;
                        largest = Math.max(largest, ++b[i]);
                        if (size[m] == ids[m].length) ids[m] = Arrays.copyOf(ids[m], 2 * size[m]);
                        ids[m][size[m]++] = id;
                        if (size[m] > b.length / 4 * 3) {
                            b = bins[m] = new int[2 * b.length];
                            for (int j = 0; j < size[m]; j++) b[bin(ids[m][j], b.length)]++;
                        }
                    }
                }
                int minSize = Integer.MAX_VALUE, maxSize = 0;
                for (int s : size) { minSize = Math.min(minSize, s); maxSize = Math.max(maxSize, s); }
                System.out.printf("%s case %s: puts into a bin of 8: %d (%.1f%%), largest %d, map sizes %d..%d, %.0f ms%n",
                        old ? "old" : "new", Arrays.toString(c), trees, 100.0 * trees / n, largest,
                        minSize, maxSize, (System.nanoTime() - t0) / 1e6);
            }
        }
    }
}
