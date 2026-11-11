package bergdb.core;

import java.io.*;
import java.nio.file.*;
import java.util.*;

import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * The probe of bergdb 024-07 (the last touch of a reclaim iteration), written 2026-11-11.
 * PF1's (024-03) fill and log commands, with the same database, keys, values, clock and
 * transactions, so that its numbers compare with 024-03's, section 7; and with what PF1
 * did not have: reclaim's statistics (Reclaim.Stats) for each iteration, the commit that
 * ran an iteration's last step apart from the commit that wrote the largest record, and the
 * distance from the startup pos to the stream's end.
 *
 * Commands (java -cp classes:JAR bergdb.core.T7 CMD key=value...):
 *   fill   a new database in dir: n keys "/k/%010d" (order=asc|random), valsize bytes, batch
 *          KVs a transaction.
 *   log    start on dir; maxdrive transactions, each lbatch new keys after every key so far
 *          and, with fifo=1, deletes of the lbatch oldest (keys in time order).
 *   drive  start on dir; maxdrive transactions of lbatch overwrites of random keys below n,
 *          and, with tail=T, T new keys after every key so far in each (keys put beyond the
 *          scan's end beside a random drive).
 * Settings: retain (s of the test clock, default 1), dt (time units a transaction, 10000),
 * sd (startup distance), stats=1 (Reclaim.Stats), touchcount=1 (its TouchCounter: an
 * identity map of every node a touch visits, so not for timing), limit=BYTES
 * (StoredTrans.recordLimit, for the stall at a small size), report=N.
 * The test clock's time is kept in dir/../NAME.time between JVMs.
 */
public class T7 {
    static final long SEC = Clock.UNITS_PER_SEC;
    final Map<String, String> p = new HashMap<String, String>();
    int i(String k, int d) { return p.containsKey(k) ? Integer.parseInt(p.get(k)) : d; }
    long l(String k, long d) { return p.containsKey(k) ? Long.parseLong(p.get(k)) : d; }
    String s(String k, String d) { return p.containsKey(k) ? p.get(k) : d; }

    File dir;
    File timeFile;
    CoreTestClock clock;
    long time = 10 * SEC;
    Db db;
    long dt;
    Reclaim.Stats stats;
    final long t0 = System.nanoTime();
    long txCount, maxRecord, maxExecNs, bigRecords, recBytes;
    long maxRecordNs, maxRecordTx, maxExecTx;
    long[] execSample = new long[1 << 20];
    int execN;
    // reclaim's internal records, from Reclaim.Stats
    long stepRecs, stepBytes, maxStepRecord, maxLag;

    static void out(String s) {
        System.out.println(s);
        System.out.flush();
    }

    String el() { return String.format("[%.1fs]", (System.nanoTime() - t0) / 1e9); }

    static String key(long i) { return String.format("/k/%010d", i); }

    static byte[] value(int size, long tag) {
        byte[] v = new byte[size];
        for (int j = 0; j < size; j++) v[j] = (byte) ('a' + (tag + j) % 26);
        for (int j = 0; j < 8 && j < size; j++) v[j] = (byte) (tag >>> (8 * j));
        return v;
    }

    void open(boolean fresh) throws IOException {
        dir = new File(s("dir", "data"));
        timeFile = new File(dir.getParentFile(), dir.getName() + ".time");
        if (fresh) {
            rm(dir);
            dir.mkdirs();
        } else if (timeFile.exists()) {
            time = Long.parseLong(new String(Files.readAllBytes(timeFile.toPath())).trim()) + SEC;
        }
        dt = l("dt", 10000);
        if (p.containsKey("limit")) StoredTrans.recordLimit = l("limit", 0);
        clock = new CoreTestClock();
        clock.setTime(time);
        DbBuilder b = Db.builder().mainStream(new FileStream(dir)).clock(clock);
        if (p.containsKey("sd")) b.startupDistance(i("sd", 50000000));
        long t = System.nanoTime();
        db = b.start();
        long ms = (System.nanoTime() - t) / 1000000;
        long retain = l("retain", 1) * SEC;
        if (retain > 0) db.setRetainDuration(retain);
        if (i("stats", 1) == 1) {
            synchronized (db.internal().getWriteLock()) {
                stats = db.internal().reclaim().enableStats();
                stats.countTouch = i("touchcount", 0) == 1;
            }
        }
        out(el() + " START ms=" + ms + " len=" + db.getStreamLength() + " fap="
                + db.getFirstAvailablePos() + " fresh=" + fresh + " recordLimit="
                + StoredTrans.recordLimit);
    }

    void close() throws IOException {
        long t = System.nanoTime();
        db.sync(SyncLevel.ORDINARY);
        db.close();
        Files.write(timeFile.toPath(), Long.toString(time).getBytes());
        out(el() + " CLOSE ms=" + (System.nanoTime() - t) / 1000000);
    }

    long kept() { return db.getStreamLength() - db.getFirstAvailablePos(); }

    long lag() { return db.getStreamLength() - db.internal().getStartupPosForEvict(); }

    void resetTx() {
        txCount = maxRecord = maxExecNs = bigRecords = recBytes = 0;
        maxRecordNs = maxRecordTx = maxExecTx = 0;
        stepRecs = stepBytes = maxStepRecord = maxLag = 0;
        execN = 0;
    }

    /** One user transaction; reports the commit in which a reclaim iteration ended. */
    Trans exec(Trans.Builder b) {
        time += dt;
        clock.setTime(time);
        Trans t = b.build();
        long iters = db.getReclaimIterationCount();
        long sr = stats == null ? 0 : stats.step.records, sb = stats == null ? 0 : stats.step.bytes;
        long a = System.nanoTime();
        db.execute(t);
        long ns = System.nanoTime() - a;
        txCount++;
        long rec = t.nextPos - t.tpos;
        recBytes += rec;
        if (rec > maxRecord) {
            maxRecord = rec;
            maxRecordNs = ns;
            maxRecordTx = txCount;
        }
        if (rec > 1000000) {
            bigRecords++;
            out(String.format("%s BIGREC tx=%d userRecord=%d commitMs=%.1f", el(), txCount, rec,
                    ns / 1e6));
        }
        if (ns > maxExecNs) {
            maxExecNs = ns;
            maxExecTx = txCount;
        }
        if (execN < execSample.length) execSample[execN++] = ns;
        maxLag = Math.max(maxLag, lag());
        long thisStep = 0;
        if (stats != null) {
            long dr = stats.step.records - sr;
            thisStep = stats.step.bytes - sb;
            stepRecs += dr;
            stepBytes += thisStep;
            maxStepRecord = Math.max(maxStepRecord, thisStep);
        }
        if (db.getReclaimIterationCount() != iters) {
            StringBuilder sbd = new StringBuilder();
            sbd.append(String.format("%s ITEREND tx=%d commitMs=%.1f userRecord=%d stepRecord=%d "
                    + "lag=%d resident=%d", el(), txCount, ns / 1e6, rec, thisStep, lag(),
                    db.internal().cacheStats().residentBytes));
            if (stats != null && !stats.iterations.isEmpty()) {
                Reclaim.Stats.Iteration it = stats.iterations.get(stats.iterations.size() - 1);
                sbd.append(String.format(" | steps=%d kvs=%d values=%d dirtiedNodes=%d "
                        + "dirtiedBytes=%d maxStepDirtied=%d maxStepNodes=%d loads=%d",
                        it.steps, it.kvs, it.values, it.dirtiedNodes, it.dirtiedBytes,
                        it.maxStepDirtied, it.maxStepNodes, it.loads));
                if (stats.countTouch) {
                    sbd.append(String.format(" touch: visited=%d dirtied=%d old=%d minimal=%d",
                            it.touch.visited, it.touch.dirtied, it.touch.old, it.touch.minimal));
                }
            }
            out(sbd.toString());
        }
        return t;
    }

    String txLine() {
        long[] s = Arrays.copyOf(execSample, execN);
        Arrays.sort(s);
        long p50 = s.length == 0 ? 0 : s[s.length / 2];
        long p999 = s.length == 0 ? 0 : s[(int) Math.min(s.length - 1, (long) (s.length * 0.999))];
        return String.format("tx=%d bytes/tx=%d maxRec=%d recs>1MB=%d exec p50=%dus p99.9=%dus "
                + "max=%dms", txCount, txCount == 0 ? 0 : recBytes / txCount, maxRecord, bigRecords,
                p50 / 1000, p999 / 1000, maxExecNs / 1000000);
    }

    String txLine2() {
        return String.format("maxRecTx=%d maxRecCommitMs=%.1f maxExecTx=%d stepRecs=%d "
                + "stepBytes/rec=%d maxStepRecord=%d maxLag=%d", maxRecordTx, maxRecordNs / 1e6,
                maxExecTx, stepRecs, stepRecs == 0 ? 0 : stepBytes / stepRecs, maxStepRecord, maxLag);
    }

    String state(String label) {
        return String.format("%s len=%d kept=%d iters=%d fap=%d lag=%d", label,
                db.getStreamLength(), kept(), db.getReclaimIterationCount(),
                db.getFirstAvailablePos(), lag());
    }

    /** Counts the KVs of a scan from "/k/"; stops after max. */
    String scanTimed(String label, final long max) {
        GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments("/k/");
        g.inclusive = true;
        final long[] c = new long[1];
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) { return ++c[0] >= max ? STOP : CONTINUE; }
            public void eod() {}
        };
        long a = System.nanoTime();
        db.getMany(g);
        long ns = System.nanoTime() - a;
        return String.format("%s keys=%d ms=%.1f", label, c[0], ns / 1e6);
    }

    void fill() throws IOException {
        int n = i("n", 1000000), vs = i("valsize", 100), batch = i("batch", 100);
        open(true);
        int[] o = new int[n];
        for (int k = 0; k < n; k++) o[k] = k;
        if (s("order", "asc").equals("random")) {
            Random r = new Random(l("seed", 1));
            for (int k = o.length - 1; k > 0; k--) {
                int j = r.nextInt(k + 1);
                int t = o[k]; o[k] = o[j]; o[j] = t;
            }
        }
        resetTx();
        long a = System.nanoTime();
        for (int k = 0; k < o.length; ) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < batch && k < o.length; j++, k++) b.put(key(o[k]), value(vs, o[k]));
            exec(b);
        }
        long ns = System.nanoTime() - a;
        out(String.format("%s FILL n=%d valsize=%d batch=%d order=%s puts/s=%.0f s=%.1f", el(),
                o.length, vs, batch, s("order", "asc"), o.length / (ns / 1e9), ns / 1e9));
        out(el() + " FILL " + txLine());
        out(el() + " FILL " + txLine2());
        out(el() + " FILL " + state("state"));
        close();
    }

    void log() throws IOException {
        int n = i("n", 1000000), lb = i("lbatch", 100), vs = i("valsize", 100);
        int maxDrive = i("maxdrive", 100000), report = i("report", 5000);
        boolean fifo = i("fifo", 1) == 1;
        long next = l("next", n), oldest = l("oldest", 0);
        open(false);
        out(el() + " LOG before " + state("state"));
        resetTx();
        long iters0 = db.getReclaimIterationCount();
        long a = System.nanoTime();
        for (int k = 1; k <= maxDrive; k++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < lb; j++, next++) b.put(key(next), value(vs, next));
            if (fifo) for (int j = 0; j < lb; j++, oldest++) b.delete(key(oldest));
            exec(b);
            if (k % report == 0) out(String.format("%s log tx=%d %s %s", el(), k, state(""),
                    txLine()));
        }
        long ns = System.nanoTime() - a;
        out(String.format("%s LOG done tx=%d iters=%d s=%.1f tx/s=%.0f", el(), maxDrive,
                db.getReclaimIterationCount() - iters0, ns / 1e9, maxDrive / (ns / 1e9)));
        out(el() + " LOG " + txLine());
        out(el() + " LOG " + txLine2());
        out(el() + " LOG " + state("state"));
        out(el() + " LOG " + scanTimed("head1000", 1000));
        if (i("scan", 0) == 1) out(el() + " LOG " + scanTimed("all", Long.MAX_VALUE));
        close();
    }

    void drive() throws IOException {
        int n = i("n", 1000000), lb = i("lbatch", 100), vs = i("valsize", 100);
        int maxDrive = i("maxdrive", 100000), report = i("report", 5000), tail = i("tail", 0);
        long next = l("next", n);
        open(false);
        out(el() + " DRIVE before " + state("state"));
        resetTx();
        Random r = new Random(11);
        long iters0 = db.getReclaimIterationCount();
        long a = System.nanoTime();
        for (int k = 1; k <= maxDrive; k++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < lb; j++) {
                int x = r.nextInt(n);
                b.put(key(x), value(vs, x + k));
            }
            for (int j = 0; j < tail; j++, next++) b.put(key(next), value(vs, next));
            exec(b);
            if (k % report == 0) out(String.format("%s drive tx=%d %s %s", el(), k, state(""),
                    txLine()));
        }
        long ns = System.nanoTime() - a;
        out(String.format("%s DRIVE done tx=%d iters=%d s=%.1f tx/s=%.0f", el(), maxDrive,
                db.getReclaimIterationCount() - iters0, ns / 1e9, maxDrive / (ns / 1e9)));
        out(el() + " DRIVE " + txLine());
        out(el() + " DRIVE " + txLine2());
        out(el() + " DRIVE " + state("state"));
        close();
    }

    static void rm(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) rm(c);
        f.delete();
    }

    public static void main(String[] args) throws Exception {
        T7 x = new T7();
        for (int k = 1; k < args.length; k++) {
            int eq = args[k].indexOf('=');
            x.p.put(args[k].substring(0, eq), args[k].substring(eq + 1));
        }
        out("T7 " + String.join(" ", args) + " cp=" + System.getProperty("java.class.path"));
        switch (args[0]) {
        case "fill": x.fill(); break;
        case "log": x.log(); break;
        case "drive": x.drive(); break;
        default: throw new IllegalArgumentException(args[0]);
        }
        out(x.el() + " DONE");
        System.exit(0);
    }
}
