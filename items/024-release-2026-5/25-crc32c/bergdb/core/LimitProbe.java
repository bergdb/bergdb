package bergdb.core;

import java.io.File;
import java.util.Random;

import bergdb.dag.Keys;
import bergdb.stream.FileStream;

/**
 * Probe of bergdb 024-17, section 4: the cost of a put and a delete against the batch size
 * (operations a transaction), on a database of n keys in a directory. Not product code.
 *
 * Usage: java -Xmx12g -cp probe:build/bergdb.jar bergdb.core.LimitProbe DIR N [sizes]
 *
 * Keys "k" + 11 digits (12 bytes), values of 8 bytes. Load: keys 0..n-1 in order, 1,000 a
 * transaction. Then for each batch size b and each mode (seq: b consecutive keys from a
 * random start; rand: b uniform random keys), updates of existing keys, then deletes of
 * existing keys. Per row: transactions, operations, ns an operation (the build and the
 * execute), stream bytes an operation, the largest and the median execute in ms, the
 * largest stream growth of one execute (its record and meta blocks), the got-dirty nodes
 * of the largest transaction, dirtyNodeBound of the first transaction of the row, and the
 * heap a built transaction holds (after a GC, first transaction of the row).
 */
public class LimitProbe {

    static Db db;
    static int n;
    static boolean[] deleted;
    static int liveCount;
    static final Random r = new Random(17);

    static String key(int i) {
        return String.format("k%011d", i);
    }

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        n = Integer.parseInt(args[1]);
        int[] sizes = {1, 10, 100, 1000, 10000, 100000};
        if (args.length > 2) {
            String[] s = args[2].split(",");
            sizes = new int[s.length];
            for (int i = 0; i < s.length; i++) sizes[i] = Integer.parseInt(s[i]);
        }
        deleteDir(dir);
        dir.mkdirs();
        DbBuilder db0 = Db.builder().stream("main", new FileStream(dir, false)).noEvict();
        if (System.getProperty("sd") != null) {
            db0.startupDistance(Integer.parseInt(System.getProperty("sd")));
        }
        db = db0.start();
        deleted = new boolean[n];
        liveCount = n;

        long t0 = System.nanoTime();
        byte[] v = new byte[8];
        for (int i = 0; i < n; i += 1000) {
            Trans.Builder b = db.trans();
            for (int j = i; j < Math.min(n, i + 1000); j++) b.put(key(j), v);
            db.execute(b.build());
        }
        System.out.printf("# loaded %d keys in %.1f s, stream %d bytes, sd %d%n", n,
                (System.nanoTime() - t0) / 1e9, db.getStreamLength(),
                db.getStartupDistance());
        // Warm up the JIT and the take's pace: 200,000 random updates in tx of 100.
        run(false, false, 100, 2000, false);

        System.out.println("op     mode b       txs   ops      ns/op   B/op    maxms   p50ms"
                + "  maxrecB     dirtyMax  bound     heapB      dirty/op");
        for (int b : sizes) {
            int txs = Math.max(3, Math.min(20000, 200000 / b));
            run(false, false, b, txs, true);
            run(false, true, b, txs, true);
        }
        for (int b : sizes) {
            int budget = b >= 100000 ? b : Math.max(3 * b, 20000);
            if (2L * budget > liveCount / 2) break;
            int txs = budget / b;
            run(true, false, b, txs, true);
            run(true, true, b, txs, true);
        }
        db.close();
        deleteDir(dir);
    }

    /** Picks the keys of one transaction: b distinct live keys. */
    static int[] pick(int b, boolean seq) {
        int[] ks = new int[b];
        if (seq) {
            int start = r.nextInt(n);
            int c = 0;
            for (int i = start; c < b; i = (i + 1) % n) {
                if (!deleted[i]) ks[c++] = i;
            }
        } else {
            java.util.HashSet<Integer> seen = new java.util.HashSet<>();
            int c = 0;
            while (c < b) {
                int i = r.nextInt(n);
                if (!deleted[i] && seen.add(i)) ks[c++] = i;
            }
        }
        return ks;
    }

    static void run(boolean delete, boolean seq, int b, int txs, boolean print) {
        byte[] v = new byte[8];
        long[] times = new long[txs];
        long totalNs = 0, maxRec = 0, dirtyMax = -1, bound = -1, heap = -1, dirtySum = 0;
        long s0 = db.getStreamLength();
        for (int t = 0; t < txs; t++) {
            int[] ks = pick(b, seq);
            long base = (t == 0 && print) ? used() : 0;
            long a = System.nanoTime();
            Trans.Builder tb = db.trans();
            for (int i : ks) {
                if (delete) tb.delete(key(i));
                else { v[0] = (byte) t; tb.put(key(i), v); }
            }
            Trans tr = tb.build();
            long built = System.nanoTime();
            if (t == 0 && print) {
                // Outside the timing: the heap of the built transaction, and the bound.
                heap = used() - base;
                long[][] segs = new long[b][];
                boolean[] dels = new boolean[b];
                for (int i = 0; i < b; i++) {
                    segs[i] = Keys.toSegments(Keys.toBytes(key(ks[i])));
                    dels[i] = delete;
                }
                try {
                    bound = db.internal().dag().dirtyNodeBound(db.currentTime(), segs, dels,
                            db.newGetData());
                } catch (Exception e) {
                    bound = -2;
                }
                a = System.nanoTime() - (built - a);
                built = System.nanoTime();
            }
            long before = db.getStreamLength();
            long e0 = System.nanoTime();
            db.execute(tr);
            long e1 = System.nanoTime();
            long rec = db.getStreamLength() - before;
            maxRec = Math.max(maxRec, rec);
            Db.ExecuteData x = db.internal().x();
            if (x.transInfo != null) {
                dirtyMax = Math.max(dirtyMax, x.transInfo.gotDirtyNodes.size());
                dirtySum += x.transInfo.gotDirtyNodes.size();
            }
            times[t] = e1 - e0;
            totalNs += (built - a) + (e1 - e0);
            if (delete) {
                for (int i : ks) { deleted[i] = true; }
                liveCount -= b;
            }
        }
        long bytes = db.getStreamLength() - s0;
        java.util.Arrays.sort(times);
        long ops = (long) txs * b;
        if (print) {
            System.out.printf("%-6s %-4s %-7d %-5d %-8d %-7d %-7d %-7.2f %-6.2f %-11d %-9d %-9d %-10d %.3f%n",
                    delete ? "delete" : "put", seq ? "seq" : "rand", b, txs, ops,
                    totalNs / ops, bytes / ops, times[txs - 1] / 1e6, times[txs / 2] / 1e6,
                    maxRec, dirtyMax, bound, heap, (double) dirtySum / ops);
        }
    }

    /** Used heap after a GC. */
    static long used() {
        Runtime rt = Runtime.getRuntime();
        System.gc();
        return rt.totalMemory() - rt.freeMemory();
    }

    static void deleteDir(File d) {
        File[] fs = d.listFiles();
        if (fs != null) for (File f : fs) { if (f.isDirectory()) deleteDir(f); else f.delete(); }
        d.delete();
    }
}
