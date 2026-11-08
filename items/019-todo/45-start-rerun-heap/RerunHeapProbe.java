package bergdb.core;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.util.*;

import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * Probe of bergdb 019-45: the live heap of a running database and of its start, against the
 * startup distance and the cache budget. ScaleBench's settings (bergdb 004-02: key24 keys,
 * 8-byte values, transactions of 1,000 puts, maxNodeSize30, testId, the BUDGET schedule) on a
 * FileStream in DIR, so that the stream is not on the heap.
 *
 * <p>Phase load: KEYS puts in a random order, then UPDATES transactions of 1,000 random
 * updates; every 50 transactions a full GC and the live heap; at the end the live heap, the
 * resident bytes and the pinned bytes (D, the record, the super root; Residents.bytesOf).
 * Phase start: a new Db on the same stream, while a sampler thread runs a full GC every 25
 * ms and records the live heap by the start's phase (the innermost DbStarter method on the
 * main thread's stack, or Db.readTransactions); with -Dhisto, a class histogram (jcmd) at
 * the first sample in the rerun, in linkD and in postStartupCheck. Then the live heap and
 * the counts after the start, after 2, 4 and 6 s idle, after 2,000 gets and after one
 * transaction. Phase startplain: the start without the sampler, for a start in a small heap
 * (-Xmx). Phase all: load, then start.
 *
 * <p>Usage, from java/ after build.sh (bergdb.core, so compile it into its own directory):
 * <pre>
 *   javac --release 17 -cp build/classes -d /tmp/p RerunHeapProbe.java
 *   java -Xmx8g -cp /tmp/p:build/classes bergdb.core.RerunHeapProbe DIR KEYS UPDATES SD_MB BUDGET_MB [all|load|start|startplain]
 * </pre>
 * DIR must not hold a database for load and all. Live bytes are above the live heap at the
 * probe's start (about 1 MB).
 */
public class RerunHeapProbe {
    static final byte[] PREFIX = "/scale/key/".getBytes(StandardCharsets.US_ASCII);

    static byte[] key(int k) {
        byte[] b = new byte[24];
        System.arraycopy(PREFIX, 0, b, 0, PREFIX.length);
        long v = k;
        for (int i = 23; i >= PREFIX.length; i--) { b[i] = (byte) ('0' + v % 10); v /= 10; }
        return b;
    }

    static byte[] value(int k, int version) {
        byte[] b = new byte[8];
        b[0] = (byte) (k >>> 24); b[1] = (byte) (k >>> 16); b[2] = (byte) (k >>> 8); b[3] = (byte) k;
        b[4] = (byte) (version >>> 8); b[5] = (byte) version;
        return b;
    }

    static long live() {
        System.gc(); System.gc();
        Runtime r = Runtime.getRuntime();
        return r.totalMemory() - r.freeMemory();
    }

    static void histo(String ph) {
        try {
            Process pr = new ProcessBuilder("jcmd", Long.toString(ProcessHandle.current().pid()), "GC.class_histogram").redirectErrorStream(true).start();
            java.io.BufferedReader rd = new java.io.BufferedReader(new java.io.InputStreamReader(pr.getInputStream()));
            System.out.println("histogram at " + ph + ":");
            String line; int n = 0;
            while ((line = rd.readLine()) != null) { if (n++ < 22) System.out.println("  " + line); else if (line.contains("Total")) System.out.println("  " + line); }
            pr.waitFor();
        } catch (Exception e) { System.out.println("histo: " + e); }
    }

    static String mb(long b) { return String.format(Locale.ROOT, "%.1f", b / 1e6); }

    /** Resident bytes, pinned bytes (D, the record, the super root) and D's object count. */
    static long[] counts(Db db) {
        synchronized (db.internal().getWriteLock()) {
            Cache3 c = db.internal().cache();
            bergdb.dag.TopNode sr = db.internal().dag().getTopDs().getSuperRoot();
            long pinned = 0, dirty = 0;
            for (Node n : c.nodes()) {
                if (Residents.isPinned(n, sr)) { pinned += Residents.bytesOf(n); if (n.isDirty()) dirty++; }
            }
            return new long[] {c.residents().bytes(), pinned, dirty, c.residents().objects()};
        }
    }

    static Db open(File dir, int sdMb, int budgetMb, TestClockHolder ck) throws java.io.IOException {
        DbBuilder b = Db.builder().mainStream(new FileStream(dir)).clock(ck.clock).testId().maxNodeSize30()
                .startupDistance(sdMb * 1000000);
        if (budgetMb > 0) b.cacheSizeIndicator(budgetMb * 1000000L).evictionSchedule(Eviction.Schedule.BUDGET, 1);
        else b.noEvict();
        Db db = b.build();
        db.start();
        return db;
    }

    static final class TestClockHolder { final CoreTestClock clock = new CoreTestClock(); }

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        int keys = Integer.parseInt(args[1]);
        int updates = Integer.parseInt(args[2]);
        int sd = Integer.parseInt(args[3]);
        int budget = Integer.parseInt(args[4]);
        String phase = args.length > 5 ? args[5] : "all";
        TestClockHolder ck = new TestClockHolder();
        long time = 1000000000000L;
        long base = live();
        System.out.println("probe: keys " + keys + ", updates " + updates + " transactions, sd " + sd
                + " MB, budget " + budget + " MB, max heap " + mb(Runtime.getRuntime().maxMemory()) + " MB; base live " + mb(base) + " MB");
        if (!phase.startsWith("start")) {
            ck.clock.setTime(time);
            Db db = open(dir, sd, budget, ck);
            Random r = new Random(1);
            int[] order = new int[keys];
            for (int i = 0; i < keys; i++) order[i] = i;
            for (int i = keys - 1; i > 0; i--) { int j = r.nextInt(i + 1); int t = order[i]; order[i] = order[j]; order[j] = t; }
            long maxLive = 0; long[] atMax = null; int tx = 0;
            int total = (keys + 999) / 1000 + updates;
            for (int t = 0; t < total; t++) {
                Trans.Builder tb = db.trans();
                if (t * 1000 < keys) {
                    for (int j = t * 1000; j < Math.min(keys, t * 1000 + 1000); j++) tb.put(key(order[j]), value(order[j], 0));
                } else {
                    for (int j = 0; j < 1000; j++) { int k = r.nextInt(keys); tb.put(key(k), value(k, t)); }
                }
                time += 100000; ck.clock.setTime(time);
                db.execute(tb.build());
                tx++;
                if (tx % 50 == 0 || t == total - 1) {
                    long l = live() - base;
                    if (l > maxLive) { maxLive = l; atMax = counts(db); }
                }
            }
            db.sync(SyncLevel.ORDINARY);
            long l = live() - base;
            long[] c = counts(db);
            System.out.println("running: live at the end " + mb(l) + " MB (resident " + mb(c[0]) + ", pinned " + mb(c[1])
                    + " MB, " + c[2] + " dirty); max live " + mb(maxLive) + " MB (resident " + mb(atMax[0]) + ", pinned "
                    + mb(atMax[1]) + "); stream " + mb(db.internal().nodeStream().getNextPos()) + " MB");
            db.close();
            Properties p = new Properties();
            p.setProperty("time", Long.toString(time));
            try (java.io.FileOutputStream fo = new java.io.FileOutputStream(new File(dir, "probe.properties"))) { p.store(fo, null); }
        }
        if (phase.equals("load")) return;
        Properties p = new Properties();
        try (java.io.FileInputStream fi = new java.io.FileInputStream(new File(dir, "probe.properties"))) { p.load(fi); }
        TestClockHolder ck2 = new TestClockHolder();
        ck2.clock.setTime(Long.parseLong(p.getProperty("time")));
        // The start, with a sampler: a full GC every 25 ms, the live bytes and the main thread's phase.
        final Thread main = Thread.currentThread();
        final long[] peak = {0};
        final String[] peakAt = {""};
        final TreeMap<String, Long> byPhase = new TreeMap<>();
        final boolean[] done = {false};
        final long base2 = live();
        Thread sampler = new Thread(() -> {
            while (!done[0]) {
                long l = live() - base2;
                String ph = "?";
                for (StackTraceElement e : main.getStackTrace()) {
                    String m = e.getMethodName();
                    if ((e.getClassName().endsWith("DbStarter") && !m.equals("start") && !m.equals("startup") && !m.equals("doOrdinaryStartup")) || m.equals("readTransactions")) { ph = e.getClassName().replaceAll(".*\\.", "") + "." + m; break; }
                }
                synchronized (byPhase) {
                    if (!byPhase.containsKey(ph) && System.getProperty("histo") != null
                            && (ph.endsWith("rerunTransaction") || ph.endsWith("linkD") || ph.endsWith("checkThatValueNodesHaveSpos"))) {
                        histo(ph);
                    }
                    byPhase.merge(ph, l, Math::max);
                }
                if (l > peak[0]) { peak[0] = l; peakAt[0] = ph; }
                try { Thread.sleep(25); } catch (InterruptedException e) { return; }
            }
        });
        sampler.setDaemon(true);
        if (!phase.equals("startplain")) sampler.start();
        long t0 = System.nanoTime();
        Db db = open(dir, sd, budget, ck2);
        long startMs = (System.nanoTime() - t0) / 1000000;
        done[0] = true;
        if (sampler.isAlive()) sampler.join();
        long l = live() - base2;
        long[] c = counts(db);
        System.out.println("start: " + startMs + " ms; peak live " + mb(peak[0]) + " MB in " + peakAt[0]
                + "; after the start " + mb(l) + " MB (resident " + mb(c[0]) + ", pinned " + mb(c[1]) + " MB, " + c[2]
                + " dirty); section " + mb(db.internal().nodeStream().getNextPos() - db.internal().getStartupPosForEvict()) + " MB");
        System.out.println("  max live by phase: " + byPhase);
        for (int i = 1; i <= 3; i++) {
            Thread.sleep(2000);
            long[] ci = counts(db);
            System.out.println("idle " + (2 * i) + " s: live " + mb(live() - base2) + " MB, resident " + mb(ci[0]) + ", pinned " + mb(ci[1]) + "; " + db.internal().eviction().stats());
        }
        Random rr = new Random(5);
        for (int i = 0; i < 2000; i++) { int k = rr.nextInt(keys); db.getOne(Long.MAX_VALUE, Keys.toSegments(key(k)), db.newGetData()); }
        Thread.sleep(2000);
        long[] cr = counts(db);
        System.out.println("after 2,000 gets and 2 s: live " + mb(live() - base2) + " MB, resident " + mb(cr[0]) + ", pinned " + mb(cr[1]) + "; " + db.internal().eviction().stats());
        db.execute(db.trans().put(key(1), value(1, 9999)).build());
        Thread.sleep(2000);
        cr = counts(db);
        System.out.println("after a transaction and 2 s: live " + mb(live() - base2) + " MB, resident " + mb(cr[0]) + ", pinned " + mb(cr[1]) + "; " + db.internal().eviction().stats());
        db.close();
    }
}
