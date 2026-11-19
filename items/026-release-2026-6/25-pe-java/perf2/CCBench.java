package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.Locale;
import java.util.Random;

import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.stream.FileStream;

/**
 * The cost of the commit check (bergdb 030-20, section 5): one JVM, one database, the commit
 * time of transactions of several sizes and kinds. Run it twice per configuration, with and
 * without -Dtranscheck=1 (TransCheck, bergdb 030-09, section 3), and compare; run.sh does that
 * in ABBA order. Not part of the build: compiled against build/bergdb.jar by run.sh.
 *
 * <p>The database: a FileStream on disk, no eviction (as Perf.java, so the check sees every
 * node), the simulated clock of Perf.java. Loaded with cc.n base keys (4-byte keys 2i, values
 * of cc.valsize bytes) in transactions of 500 puts (the most a transaction may have, 024-17). Then, for each transaction size of
 * cc.tsizes and each kind, a warm-up of cc.warm operations and a measured phase of cc.ops
 * operations (puts or deletes; the transactions are ops / tsize):</p>
 *
 * <ul>
 * <li>update: new values of random base keys;</li>
 * <li>insert: new keys 2i + 1, random, between the base keys;</li>
 * <li>delete: the keys the insert phase added, random, until as many are gone as it added;</li>
 * <li>mixed: half updates of base keys, a quarter inserts, a quarter deletes of inserted keys.</li>
 * </ul>
 *
 * <p>Measured: the wall time of each Db.execute (an append commit: it returns when the record
 * is in the stream's buffer, as Perf's append latency), its median and 99th percentile, the
 * operations per second over the phase. A sample of keys is read back at the end. Prints
 * one line per phase ("RESULT ..."), with the epoch milliseconds of its start and end (to cut
 * a JFR recording to one phase).</p>
 *
 * <p>Parameters (-Dcc.NAME): n (1000000), valsize (100), tsizes (1,10,100,500), kinds
 * (update,insert,delete,mixed), ops (200000), warm (40000), dir (the data directory; emptied),
 * seed (1).</p>
 */
public class CCBench {
    final int n = Integer.getInteger("cc.n", 1000000);
    final int valsize = Math.max(8, Integer.getInteger("cc.valsize", 100));
    final int[] tsizes = ints(System.getProperty("cc.tsizes", "1,10,100,500"));
    final String[] kinds = System.getProperty("cc.kinds", "update,insert,delete,mixed").split(",");
    final int ops = Integer.getInteger("cc.ops", 200000);
    final int warm = Integer.getInteger("cc.warm", 40000);
    final File dir = new File(System.getProperty("cc.dir", "build/cc-data"));
    final long seed = Long.getLong("cc.seed", 1);

    final CoreTestClock clock = new CoreTestClock();
    long time = 1000L * 1000 * 1000;
    Db db;
    final Random rnd;
    int[] version;            // base key i (key 2i): its version
    int[] oddVersion;         // inserted key 2i + 1: its version, 0 if absent
    int[] present;            // the inserted keys present, in no order
    int[] posOf;              // the index in present of inserted key i, -1 if absent
    int presentCount;

    CCBench() {
        rnd = new Random(seed);
    }

    static int[] ints(String s) {
        String[] p = s.split(",");
        int[] r = new int[p.length];
        for (int i = 0; i < p.length; i++) r[i] = Integer.parseInt(p[i].trim());
        return r;
    }

    byte[] value(int key, int v) {
        byte[] b = new byte[valsize];
        Perf.wr(b, 0, key);
        Perf.wr(b, 4, v);
        for (int i = 8; i < valsize; i++) b[i] = (byte) (key + v + i);
        return b;
    }

    long execute(Trans.Builder b) {
        time += 1000;
        clock.setTime(time);
        Trans t = b.build();
        long s = System.nanoTime();
        db.execute(t);
        return System.nanoTime() - s;
    }

    void open() throws IOException {
        if (dir.exists()) {
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) f.delete();
        }
        dir.mkdirs();
        DbBuilder b = Db.builder();
        b.stream("main", new FileStream(dir));
        b.clock(clock).noEvict().testId();
        db = b.build();
        db.start();
    }

    void load() {
        long t0 = System.nanoTime();
        int[] perm = new int[n];
        for (int i = 0; i < n; i++) perm[i] = i;
        Random r = new Random(seed + 1);
        for (int i = n - 1; i > 0; i--) {
            int j = r.nextInt(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        version = new int[n];
        oddVersion = new int[n];
        present = new int[n];
        posOf = new int[n];
        Arrays.fill(posOf, -1);
        long sum = 0;
        for (int i = 0; i < n; i += 500) {
            Trans.Builder b = db.trans();
            for (int j = i; j < Math.min(n, i + 500); j++) {
                int k = perm[j];
                version[k] = 1;
                b.put(KeyFactory.binaryIntKey(2 * k), value(2 * k, 1));
            }
            sum += execute(b);
        }
        double sec = 1e-9 * (System.nanoTime() - t0);
        System.out.printf(Locale.ROOT, "LOAD n=%d %.2f s, execute %.2f s, %.0f puts/s, heap used %.0f MB%n",
                n, sec, 1e-9 * sum, n / sec, usedMb());
    }

    static double usedMb() {
        Runtime rt = Runtime.getRuntime();
        return (rt.totalMemory() - rt.freeMemory()) / 1e6;
    }

    void addPresent(int i) {
        posOf[i] = presentCount;
        present[presentCount++] = i;
    }

    void removePresent(int i) {
        int p = posOf[i];
        int last = present[--presentCount];
        present[p] = last;
        posOf[last] = p;
        posOf[i] = -1;
    }

    /** One transaction of tsize operations of the kind; returns its execute time. */
    long transaction(String kind, int tsize, boolean[] mark, int[] used) {
        Trans.Builder b = db.trans();
        int u = 0;
        for (int j = 0; j < tsize; j++) {
            int op;     // 0 update, 1 insert, 2 delete
            if (kind.equals("update")) op = 0;
            else if (kind.equals("insert")) op = 1;
            else if (kind.equals("delete")) op = 2;
            else {
                int x = rnd.nextInt(4);
                op = x < 2 ? 0 : x == 2 ? 1 : 2;
            }
            if (op == 2 && presentCount - u <= 0) op = 1;
            if (op == 0) {
                int i;
                do { i = rnd.nextInt(n); } while (mark[2 * i]);
                mark[2 * i] = true; used[u++] = 2 * i;
                version[i]++;
                b.put(KeyFactory.binaryIntKey(2 * i), value(2 * i, version[i]));
            } else if (op == 1) {
                int i;
                do { i = rnd.nextInt(n); } while (posOf[i] >= 0 || mark[2 * i + 1]);
                mark[2 * i + 1] = true; used[u++] = 2 * i + 1;
                oddVersion[i]++;
                b.put(KeyFactory.binaryIntKey(2 * i + 1), value(2 * i + 1, oddVersion[i]));
                addPresent(i);
            } else {
                int i;
                do { i = present[rnd.nextInt(presentCount)]; } while (mark[2 * i + 1]);
                mark[2 * i + 1] = true; used[u++] = 2 * i + 1;
                b.delete(KeyFactory.binaryIntKey(2 * i + 1));
                removePresent(i);
            }
        }
        for (int q = 0; q < u; q++) mark[used[q]] = false;
        return execute(b);
    }

    void phase(String kind, int tsize, boolean[] mark, int[] used) {
        int wtx = Math.max(1, warm / tsize);
        for (int i = 0; i < wtx; i++) transaction(kind, tsize, mark, used);
        int tx = Math.max(1, ops / tsize);
        long[] lat = new long[tx];
        long startMs = System.currentTimeMillis();
        long t0 = System.nanoTime();
        for (int i = 0; i < tx; i++) lat[i] = transaction(kind, tsize, mark, used);
        long wall = System.nanoTime() - t0;
        long endMs = System.currentTimeMillis();
        long sum = 0;
        for (long l : lat) sum += l;
        Arrays.sort(lat);
        System.out.printf(Locale.ROOT,
                "RESULT kind=%s tsize=%d tx=%d ops=%d wall_s=%.3f exec_s=%.3f ops_per_s=%.0f "
                + "tx_med_us=%.2f tx_mean_us=%.2f tx_p99_us=%.2f op_mean_us=%.3f present=%d "
                + "heap_mb=%.0f start_ms=%d end_ms=%d%n",
                kind, tsize, tx, (long) tx * tsize, 1e-9 * wall, 1e-9 * sum,
                (double) tx * tsize / (1e-9 * wall), lat[tx / 2] / 1e3, sum / 1e3 / tx,
                lat[Math.min(tx - 1, (int) (tx * 0.99))] / 1e3, sum / 1e3 / ((double) tx * tsize),
                presentCount, usedMb(), startMs, endMs);
    }

    /** Reads back a sample of keys at the latest time and checks them. */
    void check() {
        Random r = new Random(seed + 2);
        GetData gd = db.newGetData();
        int bad = 0;
        for (int q = 0; q < 20000; q++) {
            int i = r.nextInt(n);
            byte[] v = db.getOne(time, Keys.toSegments(KeyFactory.binaryIntKey(2 * i)), gd);
            if (v == null || !Arrays.equals(v, value(2 * i, version[i]))) bad++;
            byte[] w = db.getOne(time, Keys.toSegments(KeyFactory.binaryIntKey(2 * i + 1)), gd);
            byte[] want = posOf[i] >= 0 ? value(2 * i + 1, oddVersion[i]) : null;
            if (want == null ? w != null : !Arrays.equals(w, want)) bad++;
        }
        System.out.println("CHECK 40000 reads, " + bad + " wrong");
        if (bad > 0) throw new RuntimeException("CHECK failed: " + bad + " wrong values");
    }

    void run() throws IOException {
        System.out.println("CCBench transcheck=" + TransCheck.ON + " n=" + n + " valsize=" + valsize
                + " tsizes=" + Arrays.toString(tsizes) + " kinds=" + Arrays.toString(kinds)
                + " ops=" + ops + " warm=" + warm);
        open();
        try {
            load();
            int maxT = 0;
            for (int t : tsizes) maxT = Math.max(maxT, t);
            boolean[] mark = new boolean[2 * n];
            int[] used = new int[maxT];
            for (int tsize : tsizes) {
                for (String kind : kinds) phase(kind, tsize, mark, used);
            }
            check();
            System.out.printf(Locale.ROOT, "STREAM %.0f MB%n", db.getStreamLength() / 1e6);
        } finally {
            db.close();
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) f.delete();
            dir.delete();
        }
    }

    public static void main(String[] args) throws IOException {
        new CCBench().run();
        System.out.println("CCBENCH DONE");
    }
}
