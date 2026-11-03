package bergdb.core;

import java.util.SplittableRandom;

/**
 * bergdb 005-79, step 2, "shown, not assumed": Part A's integer expressions against the
 * double expressions they replace, on the edges and on random values spread over the bit
 * lengths below each bound, and the first differences above the bounds.
 *
 *   spacing    (long) (0.25 * r)        r / Reclaim.ITERATION_DIVISOR    r below 2^53
 *   watermark  (long) (b * 0.75)        Eviction.lowOf(b)                b below 2^53 / 3
 *   fraction   (long) (0.25 * g)        Reclaim.fractionOf(g, 16384)     g below 2^53
 *
 * Compile against the clone's jar and run with this class before the jar on -cp:
 *   javac --release 17 -cp java/build/bergdb.jar -d OUT Equiv.java
 *   java -cp OUT:java/build/bergdb.jar bergdb.core.Equiv [N]    (N random values, 10^8)
 */
public class Equiv {
    static final long B53 = 1L << 53;

    interface Pair {
        long oldValue(long x);
        long newValue(long x);
    }

    static final Pair SPACING = new Pair() {
        public long oldValue(long r) { return (long) (0.25 * r); }
        public long newValue(long r) { return r / Reclaim.ITERATION_DIVISOR; }
    };

    static final Pair WATERMARK = new Pair() {
        public long oldValue(long b) { return (long) (b * 0.75); }
        public long newValue(long b) { return Eviction.lowOf(b); }
    };

    static final Pair FRACTION = new Pair() {
        public long oldValue(long g) { return (long) (0.25 * g); }
        public long newValue(long g) {
            return Reclaim.fractionOf(g, Reclaim.DEFAULT_INTERNAL_FRACTION);
        }
    };

    public static void main(String[] args) {
        long n = args.length > 0 ? Long.parseLong(args[0]) : 100000000L;
        if (Reclaim.DEFAULT_INTERNAL_FRACTION != 16384 || Reclaim.ITERATION_DIVISOR != 4) {
            throw new AssertionError("unexpected constants");
        }
        boolean ok = true;
        ok &= run("spacing", SPACING, 0, B53, n);
        ok &= run("watermark", WATERMARK, 1, B53 / 3, n);
        ok &= run("fraction", FRACTION, 0, B53, n);
        System.out.println(ok ? "EQUIV OK: no difference below the bounds"
                : "EQUIV FAILED: a difference below a bound");
        System.exit(ok ? 0 : 1);
    }

    /** Checks [lo, bound) and prints the first differences from bound on. */
    static boolean run(String name, Pair p, long lo, long bound, long n) {
        long t0 = System.nanoTime();
        long checked = 0, diffs = 0;
        long[] edges = {lo, lo + 1, lo + 2, lo + 3, lo + 4, 5, 7, 8, 0xFFFF, 0x10000,
                1L << 31, 1L << 47, B53 / 3 - 1, B53 / 3, B53 - 4, B53 - 3, B53 - 2, B53 - 1};
        for (long x : edges) {
            if (x >= lo && x < bound) {
                checked++;
                if (p.oldValue(x) != p.newValue(x)) {
                    diffs++;
                    System.out.println(name + " DIFFERS at edge " + x);
                }
            }
        }
        // Every value of the last 2^20 below the bound, and of the first 2^20 from lo.
        for (long x = Math.max(lo, bound - (1 << 20)); x < bound; x++) {
            checked++;
            if (p.oldValue(x) != p.newValue(x)) {
                diffs++;
                if (diffs < 10) System.out.println(name + " DIFFERS at " + x);
            }
        }
        for (long x = lo; x < lo + (1 << 20) && x < bound; x++) {
            checked++;
            if (p.oldValue(x) != p.newValue(x)) {
                diffs++;
                if (diffs < 10) System.out.println(name + " DIFFERS at " + x);
            }
        }
        // Random values below the bound, the bit length uniform from 1 to the bound's.
        SplittableRandom r = new SplittableRandom(79);
        int bits = 64 - Long.numberOfLeadingZeros(bound - 1);
        for (long i = 0; i < n; i++) {
            long x = r.nextLong() >>> (64 - 1 - r.nextInt(bits));
            if (x < lo || x >= bound) continue;
            checked++;
            if (p.oldValue(x) != p.newValue(x)) {
                diffs++;
                if (diffs < 10) System.out.println(name + " DIFFERS at " + x);
            }
        }
        System.out.printf("%-9s below %d: %d values checked, %d differences (%.1f s)%n",
                name, bound, checked, diffs, (System.nanoTime() - t0) / 1e9);

        // Above the bound: the first differences, scanning up from it.
        StringBuilder sb = new StringBuilder();
        int found = 0;
        for (long x = bound; x < bound + (1 << 24) && found < 5; x++) {
            long o = p.oldValue(x), v = p.newValue(x);
            if (o != v) {
                found++;
                sb.append(String.format("%n    x = %d = bound + %d: double %d, integer %d", x,
                        x - bound, o, v));
            }
        }
        // And how often they differ at random above the bound, up to 2^62.
        long above = 0, aboveDiffs = 0;
        for (long i = 0; i < Math.min(n, 10000000L); i++) {
            long x = bound + (r.nextLong() >>> (64 - 1 - r.nextInt(62)));
            if (x < bound || x >= (1L << 62)) continue;
            above++;
            if (p.oldValue(x) != p.newValue(x)) aboveDiffs++;
        }
        System.out.println("  above the bound, the first differences:" + (found == 0
                ? " none in 2^24 values" : sb.toString()));
        System.out.printf("  above the bound, random values to 2^62: %d of %d differ%n",
                aboveDiffs, above);
        return diffs == 0;
    }
}
