package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Locale;
import java.util.Random;

import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * Java's side of the benchmarks of bergdb 012-15: the workloads of cbench.c (C's side) through
 * Java's Db, with the same keys, values, clock and id, so that both write the same bytes. One
 * thread, as C has one caller; phase "get4t" adds Java's getOne with four threads, which C does
 * not do. Compiled against the cross harness's classes (test/cross/java-build.sh) by
 * bench/bench.sh; run without -ea.
 *
 * Usage: java -cp build/java/classes:build/bench/java bergdb.core.JBench run DIR [NAME=VALUE ...]
 *        ... JBench start DIR [keys=N] [budget=BYTES]
 * The modes, phases and output: cbench.c's comment.
 */
public class JBench {
    static final long SEC = bergdb.pub.util.Clock.UNITS_PER_SEC;
    static final int TX = 1000;
    static final int SCAN = 10000;

    final String[] args;
    final CoreTestClock clock = new CoreTestClock();
    long time = SEC;
    Random updRnd;
    Db db;

    JBench(String[] args) {
        this.args = args;
    }

    long param(String name, long def) {
        for (int i = 2; i < args.length; i++) {
            if (args[i].startsWith(name + "=")) return Long.parseLong(args[i].substring(name.length() + 1));
        }
        return def;
    }

    static byte[] key24(int k) {
        byte[] b = new byte[24];
        System.arraycopy("/scale/key/".getBytes(StandardCharsets.US_ASCII), 0, b, 0, 11);
        long v = k;
        for (int i = 23; i >= 11; i--) { b[i] = (byte) ('0' + v % 10); v /= 10; }
        return b;
    }

    static byte[] value8(int k, int version) {
        byte[] v = new byte[8];
        for (int i = 0; i < 4; i++) v[i] = (byte) (k >>> (24 - 8 * i));
        v[4] = (byte) version;
        return v;
    }

    static int valueKey(byte[] v) {
        return ((v[0] & 0xff) << 24) | ((v[1] & 0xff) << 16) | ((v[2] & 0xff) << 8) | (v[3] & 0xff);
    }

    static void result(String phase, long ops, double sec, String extra) {
        System.out.println(String.format(Locale.ROOT, "RESULT phase=%s ops=%d sec=%.6f per_sec=%.1f%s%s", phase, ops,
                sec, sec > 0 ? ops / sec : 0.0, extra.isEmpty() ? "" : " ", extra));
        System.out.flush();
    }

    static long heapUsed() {
        for (int i = 0; i < 3; i++) System.gc();
        return Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
    }

    void printMem(String at, long keys, long heap0) {
        long heap = heapUsed();
        System.out.println(String.format(Locale.ROOT, "MEM at=%s keys=%d heap=%d heap_delta=%d per_key=%.1f stream=%d",
                at, keys, heap, heap - heap0, keys > 0 ? (double) (heap - heap0) / keys : 0.0, db.getStreamLength()));
        System.out.flush();
    }

    Db open(File dir, int sd, long budget) throws IOException {
        DbBuilder b = Db.builder().mainStream(new FileStream(dir)).clock(clock).testId()
                .maxNodeSize30().startupDistance(sd);
        if (budget > 0) b.cacheSizeIndicator(budget);
        else b.noEvict();
        Db d = b.build();
        d.start();
        return d;
    }

    void putTrans(int[] ord, int off, int keys, int count, int version) {
        Trans.Builder tb = db.trans();
        for (int j = 0; j < count; j++) {
            int k = ord != null ? ord[off + j] : updRnd.nextInt(keys);
            tb.put(key24(k), value8(k, version));
        }
        time += SEC / 10000;
        clock.setTime(time);
        db.execute(tb.build());
    }

    void gets(String phase, int keys, long n, int rounds, long lookup, int version) {
        GetData gd = db.newGetData();
        for (int r = 0; r < rounds; r++) {
            Random rnd = new Random(3 + r);
            long found = 0, bad = 0;
            long a = System.nanoTime();
            for (long i = 0; i < n; i++) {
                int k = rnd.nextInt(keys);
                byte[] v = db.getOne(lookup, Keys.toSegments(key24(k)), gd);
                if (v != null && v.length == 8) {
                    found++;
                    if (valueKey(v) != k || (version >= 0 && v[4] != version)) bad++;
                }
            }
            double sec = (System.nanoTime() - a) / 1e9;
            result(phase, n, sec, "round=" + r + " found=" + found + " bad=" + bad);
            if (bad != 0) throw new IllegalStateException(phase + ": " + bad + " wrong values");
        }
    }

    /** getOne latest with several threads, each n / threads gets: Java's, not C's. */
    void getsThreaded(final int keys, long n, int rounds, final int threads) throws InterruptedException {
        for (int r = 0; r < rounds; r++) {
            final long each = n / threads;
            final long[] found = new long[threads];
            Thread[] ts = new Thread[threads];
            final int round = r;
            for (int t = 0; t < threads; t++) {
                final int tt = t;
                ts[t] = new Thread() {
                    public void run() {
                        GetData gd = db.newGetData();
                        Random rnd = new Random(100 + 10 * round + tt);
                        long f = 0;
                        for (long i = 0; i < each; i++) {
                            int k = rnd.nextInt(keys);
                            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(key24(k)), gd);
                            if (v != null && v.length == 8 && valueKey(v) == k) f++;
                        }
                        found[tt] = f;
                    }
                };
            }
            long a = System.nanoTime();
            for (Thread t : ts) t.start();
            for (Thread t : ts) t.join();
            double sec = (System.nanoTime() - a) / 1e9;
            long f = 0;
            for (long x : found) f += x;
            result("get" + threads + "t", each * threads, sec, "round=" + r + " found=" + f + " threads=" + threads);
        }
    }

    void scans(int keys, long n, int rounds) {
        for (int r = 0; r < rounds; r++) {
            Random rnd = new Random(5 + r);
            long total = 0;
            long a = System.nanoTime();
            for (long i = 0; i < n; i++) {
                int k = rnd.nextInt(keys);
                GetMany g = db.newGetMany();
                g.lookupTime = Long.MAX_VALUE;
                g.startKey = Keys.toSegments(key24(k));
                g.inclusive = true;
                g.stopCondition = new GetMany.GetN(SCAN);
                db.getMany(g);
                total += g.result.size();
            }
            double sec = (System.nanoTime() - a) / 1e9;
            result("many", total, sec, "round=" + r + " scans=" + n);
        }
    }

    void run() throws Exception {
        File dir = new File(args[1]);
        int keys = (int) param("keys", 1000000);
        long upd = param("upd", 0), single = param("single", 0), syncs = param("syncs", 0),
                syncb = param("syncb", 0), getsN = param("gets", 0), scansN = param("scans", 0),
                low = param("low", 0), threads = param("threads", 4);
        int rounds = (int) param("rounds", 3), sd = (int) param("sd", 50000000);
        System.out.println("RUN lang=java keys=" + keys + " upd=" + upd + " single=" + single + " syncs=" + syncs
                + " syncb=" + syncb + " gets=" + getsN + " scans=" + scansN + " low=" + low + " rounds=" + rounds
                + " sd=" + sd + " threads=" + threads);
        long heap0 = heapUsed();
        clock.setTime(time);
        long a = System.nanoTime();
        db = open(dir, sd, 0);
        result("create", 1, (System.nanoTime() - a) / 1e9, "");

        int[] ord = new int[keys];
        for (int i = 0; i < keys; i++) ord[i] = i;
        Random rnd = new Random(1);
        for (int i = keys - 1; i > 0; i--) { int j = rnd.nextInt(i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        long len0 = db.getStreamLength();
        a = System.nanoTime();
        long trans = 0;
        for (int i = 0; i < keys; i += TX) {
            int e = Math.min(keys, i + TX);
            putTrans(ord, i, keys, e - i, 0);
            trans++;
        }
        double sec = (System.nanoTime() - a) / 1e9;
        ord = null;
        long len1 = db.getStreamLength();
        result("load", keys, sec, String.format(Locale.ROOT, "trans=%d trans_per_sec=%.1f bytes=%d bytes_per_put=%.2f stream=%d",
                trans, trans / sec, len1 - len0, (double) (len1 - len0) / keys, len1));
        long tLoad = time;
        printMem("load", keys, heap0);

        updRnd = new Random(2);
        if (upd > 0) {
            len0 = len1;
            a = System.nanoTime();
            trans = 0;
            for (long i = 0; i < upd; i += TX) {
                long e = Math.min(upd, i + TX);
                putTrans(null, 0, keys, (int) (e - i), 1);
                trans++;
            }
            sec = (System.nanoTime() - a) / 1e9;
            len1 = db.getStreamLength();
            result("batch", upd, sec, String.format(Locale.ROOT, "trans=%d trans_per_sec=%.1f bytes=%d bytes_per_put=%.2f stream=%d",
                    trans, trans / sec, len1 - len0, (double) (len1 - len0) / upd, len1));
        }
        if (single > 0) {
            len0 = len1;
            a = System.nanoTime();
            for (long i = 0; i < single; i++) putTrans(null, 0, keys, 1, 2);
            sec = (System.nanoTime() - a) / 1e9;
            len1 = db.getStreamLength();
            result("single", single, sec, String.format(Locale.ROOT, "trans=%d bytes=%d bytes_per_put=%.2f stream=%d",
                    single, len1 - len0, (double) (len1 - len0) / single, len1));
        }
        if (param("firstsync", 0) > 0) {
            a = System.nanoTime();
            db.sync(SyncLevel.ORDINARY);
            result("firstsync", 1, (System.nanoTime() - a) / 1e9, "");
        }
        if (syncs > 0) {
            len0 = len1;
            a = System.nanoTime();
            for (long i = 0; i < syncs; i++) {
                putTrans(null, 0, keys, 1, 3);
                db.sync(SyncLevel.ORDINARY);
            }
            sec = (System.nanoTime() - a) / 1e9;
            len1 = db.getStreamLength();
            result("syncone", syncs, sec, String.format(Locale.ROOT, "trans=%d bytes=%d bytes_per_put=%.2f stream=%d",
                    syncs, len1 - len0, (double) (len1 - len0) / syncs, len1));
        }
        if (syncb > 0) {
            len0 = len1;
            a = System.nanoTime();
            for (long i = 0; i < syncb; i++) {
                putTrans(null, 0, keys, TX, 4);
                db.sync(SyncLevel.ORDINARY);
            }
            sec = (System.nanoTime() - a) / 1e9;
            len1 = db.getStreamLength();
            result("syncbatch", syncb, sec, String.format(Locale.ROOT, "trans=%d puts=%d bytes=%d bytes_per_put=%.2f stream=%d",
                    syncb, syncb * TX, len1 - len0, (double) (len1 - len0) / (syncb * TX), len1));
        }
        printMem("writes", keys, heap0);

        if (getsN > 0) {
            gets("get", keys, getsN, rounds, Long.MAX_VALUE, -1);
            gets("hist", keys, getsN, rounds, tLoad, 0);
            if (threads > 1) getsThreaded(keys, getsN, rounds, (int) threads);
        }
        if (scansN > 0) scans(keys, scansN, rounds);

        a = System.nanoTime();
        db.close();
        result("close", 1, (System.nanoTime() - a) / 1e9, "stream=" + len1);
        db = null;

        if (low > 0) {
            heap0 = heapUsed();
            a = System.nanoTime();
            db = open(dir, sd, low);
            result("lowopen", 1, (System.nanoTime() - a) / 1e9, "budget=" + low);
            printMem("lowopen", keys, heap0);
            gets("lowget", keys, getsN, rounds, Long.MAX_VALUE, -1);
            printMem("lowget", keys, heap0);
            db.close();
        }
        System.out.println("DONE lang=java");
    }

    void start() throws Exception {
        File dir = new File(args[1]);
        int keys = (int) param("keys", 10000000);
        clock.setTime(1000000L * SEC);
        long heap0 = heapUsed();
        long a = System.nanoTime();
        long budget = param("budget", 0);
        DbBuilder b = Db.builder().mainStream(new FileStream(dir)).clock(clock);
        if (budget > 0) b.cacheSizeIndicator(budget);
        else b.noEvict();
        db = b.build();
        StartInfo si = db.start();
        double sec = (System.nanoTime() - a) / 1e9;
        long len = db.getStreamLength();
        result("start", 1, sec, "trans=" + si.transCount + " start_pos=" + si.startPos + " stream=" + len
                + " section=" + (len - si.startPos) + " sd=" + db.getStartupDistance());
        printMem("start", 0, heap0);
        Random rnd = new Random(7);
        GetData gd = db.newGetData();
        long found = 0;
        for (int i = 0; i < 2000; i++) {
            int k = rnd.nextInt(keys);
            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(key24(k)), gd);
            if (v != null && v.length == 8 && valueKey(v) == k) found++;
        }
        System.out.println("CHECK found=" + found + " of 2000");
        db.close();
        if (found != 2000) System.exit(1);
    }

    public static void main(String[] args) throws Exception {
        JBench b = new JBench(args);
        if (args.length >= 2 && args[0].equals("run")) b.run();
        else if (args.length >= 2 && args[0].equals("start")) b.start();
        else {
            System.err.println("usage: JBench run DIR [NAME=VALUE ...] | start DIR [keys=N]");
            System.exit(2);
        }
        System.exit(0);
    }
}
