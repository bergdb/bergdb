import java.util.Arrays;
import java.util.HashMap;

/**
 * TableBench, for bergdb item 009-02, decision T1: the table from node id to
 * handle. It fills a table with n handles, ids in a scattered order (odd
 * numbers, as Spos.nextVpos makes them), and times every put; a put that
 * resizes a map is timed by itself. Then, with "mem", the heap bytes per
 * entry, handles included.
 *
 * Tables: maps256 (256 HashMaps, as Cache3 today), maps4096 (4,096
 * HashMaps), intr4096 (4,096 small tables chained through the handle's next
 * field, each doubled at a load of 0.75, as Frans's MyLongMap of 2017 but
 * growing), handles (the handles alone, in an array: the cost of a handle).
 * The map of an id is Cache3.mapIndex's (Fibonacci hashing).
 *
 * Usage: java TableBench.java TABLE N [mem]
 */
public class TableBench {
    /** A handle of the size 009-02 proposes: 8 + 8 + 4 + 4 bytes and an 8-byte header, 32. */
    static final class H {
        final long id;
        volatile Object obj;
        long writtenPos;
        int state;
        H(long id) { this.id = id; }
    }

    /** The same handle with the intrusive table's next field. */
    static final class HN {
        final long id;
        volatile Object obj;
        long writtenPos;
        int state;
        HN next;
        HN(long id) { this.id = id; }
    }

    static int mapIndex(long id, int bits) {
        return (int) ((id * 0x9E3779B97F4A7C15L) >>> (64 - bits));
    }

    /** One of 4,096 intrusive tables: bins of chained handles, doubled at 0.75. */
    static final class Intr {
        HN[] bins = new HN[16];
        int size;

        /** Puts h; returns the nanoseconds of the resize it did, or 0. */
        long put(HN h) {
            long t = 0;
            if (size + 1 > bins.length * 3 / 4) {
                long t0 = System.nanoTime();
                HN[] old = bins;
                HN[] nb = new HN[old.length * 2];
                int mask = nb.length - 1;
                for (HN e : old) {
                    while (e != null) {
                        HN next = e.next;
                        int b = bin(e.id) & mask;
                        e.next = nb[b];
                        nb[b] = e;
                        e = next;
                    }
                }
                bins = nb;
                t = System.nanoTime() - t0;
            }
            int b = bin(h.id) & (bins.length - 1);
            h.next = bins[b];
            bins[b] = h;
            size++;
            return t;
        }

        static int bin(long id) {
            int x = Long.hashCode(id);
            return x ^ (x >>> 16);
        }
    }

    static long id(long k, long mask) {
        return 2 * ((k * 0x9E3779B1L) & mask) + 1;
    }

    static long used() {
        Runtime r = Runtime.getRuntime();
        for (int i = 0; i < 4; i++) {
            System.gc();
            try { Thread.sleep(200); } catch (InterruptedException e) { }
        }
        return r.totalMemory() - r.freeMemory();
    }

    public static void main(String[] args) {
        String table = args[0];
        int n = Integer.parseInt(args[1]);
        boolean mem = args.length > 2 && args[2].equals("mem");
        long mask = Long.highestOneBit(n - 1) * 2 - 1;      // n <= mask + 1, a bijection
        int bits = table.equals("maps256") ? 8 : 12;
        int maps = 1 << bits;

        long before = mem ? used() : 0;
        long[] resizeNs = new long[maps * 24];
        int[] resizeLevel = new int[maps * 24];
        int resizes = 0;
        long maxPut = 0, over1ms = 0, over10ms = 0;
        Object keep;
        long t0 = System.nanoTime();

        if (table.equals("handles")) {
            H[] hs = new H[n];
            for (int k = 0; k < n; k++) hs[k] = new H(id(k, mask));
            keep = hs;
        } else if (table.equals("intr4096")) {
            Intr[] ts = new Intr[maps];
            for (int i = 0; i < maps; i++) ts[i] = new Intr();
            for (int k = 0; k < n; k++) {
                long id = id(k, mask);
                Intr t = ts[mapIndex(id, bits)];
                long p0 = System.nanoTime();
                long r = t.put(new HN(id));
                long p = System.nanoTime() - p0;
                if (r > 0) {
                    resizeNs[resizes] = p;
                    resizeLevel[resizes++] = Integer.numberOfTrailingZeros(t.bins.length);
                }
                if (p > maxPut) maxPut = p;
                if (p > 1_000_000) over1ms++;
                if (p > 10_000_000) over10ms++;
            }
            keep = ts;
        } else {
            @SuppressWarnings("unchecked")
            HashMap<Long, H>[] ms = new HashMap[maps];
            for (int i = 0; i < maps; i++) ms[i] = new HashMap<Long, H>();
            int[] counts = new int[maps];
            for (int k = 0; k < n; k++) {
                long id = id(k, mask);
                int i = mapIndex(id, bits);
                long p0 = System.nanoTime();
                ms[i].put(id, new H(id));
                long p = System.nanoTime() - p0;
                int c = ++counts[i];
                // HashMap doubles when its size passes 0.75 of its capacity: at 13, 25, 49, ...
                if (c > 13 && (c - 1) % 12 == 0 && Integer.bitCount((c - 1) / 12) == 1) {
                    resizeNs[resizes] = p;
                    resizeLevel[resizes++] = 32 - Integer.numberOfLeadingZeros((c - 1) / 12) + 4;
                }
                if (p > maxPut) maxPut = p;
                if (p > 1_000_000) over1ms++;
                if (p > 10_000_000) over10ms++;
            }
            keep = ms;
        }
        long fill = System.nanoTime() - t0;

        StringBuilder sb = new StringBuilder();
        sb.append(String.format("%s n=%d fill=%.1fs maxPut=%.3fms puts>1ms=%d puts>10ms=%d",
                table, n, fill / 1e9, maxPut / 1e6, over1ms, over10ms));
        // The two largest resize levels: the capacity after the resize, the count, the
        // median and the largest time of such a resize.
        int top = 0;
        for (int i = 0; i < resizes; i++) top = Math.max(top, resizeLevel[i]);
        for (int level = top; level > top - 2 && level > 4; level--) {
            long[] xs = new long[resizes];
            int c = 0;
            for (int i = 0; i < resizes; i++) if (resizeLevel[i] == level) xs[c++] = resizeNs[i];
            if (c == 0) continue;
            long[] ys = Arrays.copyOf(xs, c);
            Arrays.sort(ys);
            sb.append(String.format(" | resize to 2^%d: %d, median %.3fms, max %.3fms",
                    level, c, ys[c / 2] / 1e6, ys[c - 1] / 1e6));
        }
        if (mem) {
            long after = used();
            sb.append(String.format(" | heap %.1f bytes/entry", (after - before) / (double) n));
        }
        System.out.println(sb);
        if (keep.hashCode() == 42) System.out.println();     // keeps 'keep' live
    }
}
