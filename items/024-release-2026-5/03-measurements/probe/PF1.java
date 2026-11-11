package bergdb.core;

import java.io.*;
import java.nio.file.*;
import java.util.*;

import bergdb.dag.GetData;
import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Klong;
import bergdb.dag.Kvt;
import bergdb.dag.Node;
import bergdb.dag.OpData;
import bergdb.dag.PointerFollower;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.DummyStream;
import bergdb.stream.FileStream;

/**
 * PF1's probe (bergdb 024-03), written 2026-11-11: release 2026.4 (and 2026.3 where the API
 * allows) at 1M to 10M keys on a FileStream with the default settings (startup distance 50
 * MB, cache indicator 200 MB), a test clock (dt units a transaction) and a retain duration.
 * Compiled apart against each release's jar, as 023-10's probe; the Count follower is
 * CleanupRule's (023-03).
 *
 * Commands (java -cp classes:JAR bergdb.core.PF1 CMD key=value...):
 *   fill    a new database in dir: n keys "/k/%010d" (order=random|asc), valsize bytes,
 *           batch KVs a transaction; then warm gets and a scan. keep=K: only keys i % K == 0.
 *   cold    start on dir; gets (cold, then warm), a scan.
 *   massdel start on dir; delete keys i < frac*n (ascending, batch), scans, then a drive.
 *   sparse  start on dir; delete all keys but i % keep == 0; measures; then a drive.
 *   start   start on dir; a scan of the head and the rest; nodes.
 *   mem     MEM (bergdb.dev.props.Mem's method) at n KVs, DummyStream, empty values.
 * The test clock's time is kept in dir/../NAME.time between JVMs.
 */
public class PF1 {
    static final long SEC = Clock.UNITS_PER_SEC;
    final Map<String, String> p = new HashMap<String, String>();
    int i(String k, int d) { return p.containsKey(k) ? Integer.parseInt(p.get(k)) : d; }
    long l(String k, long d) { return p.containsKey(k) ? Long.parseLong(p.get(k)) : d; }
    double d(String k, double d) { return p.containsKey(k) ? Double.parseDouble(p.get(k)) : d; }
    String s(String k, String d) { return p.containsKey(k) ? p.get(k) : d; }

    File dir;
    File timeFile;
    CoreTestClock clock;
    long time = 10 * SEC;
    Db db;
    long dt;
    final long t0 = System.nanoTime();
    // per-phase transaction stats
    long txCount, maxRecord, maxExecNs, bigRecords, recBytes;
    long[] execSample = new long[1 << 20];
    int execN;

    static void out(String s) {
        System.out.println(s);
        System.out.flush();
    }

    String el() { return String.format("[%.1fs]", (System.nanoTime() - t0) / 1e9); }

    static String key(int i) { return String.format("/k/%010d", i); }

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
        clock = new CoreTestClock();
        clock.setTime(time);
        DbBuilder b = Db.builder().mainStream(new FileStream(dir)).clock(clock);
        if (p.containsKey("sd")) b.startupDistance(i("sd", 50000000));
        long t = System.nanoTime();
        db = b.start();
        long ms = (System.nanoTime() - t) / 1000000;
        long retain = l("retain", 1) * SEC;
        if (retain > 0) db.setRetainDuration(retain);
        out(el() + " START ms=" + ms + " len=" + db.getStreamLength() + " fap="
                + db.getFirstAvailablePos() + " files=" + fileBytes() + " fresh=" + fresh);
    }

    void saveTime() throws IOException {
        Files.write(timeFile.toPath(), Long.toString(time).getBytes());
    }

    void close() throws IOException {
        long t = System.nanoTime();
        db.sync(SyncLevel.ORDINARY);
        db.close();
        saveTime();
        out(el() + " CLOSE ms=" + (System.nanoTime() - t) / 1000000 + " files=" + fileBytes());
    }

    long fileBytes() {
        long sum = 0;
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) if (f.getName().endsWith(".bergdb")) sum += f.length();
        return sum;
    }

    long kept() { return db.getStreamLength() - db.getFirstAvailablePos(); }

    void resetTx() {
        txCount = maxRecord = maxExecNs = bigRecords = recBytes = 0;
        execN = 0;
    }

    Trans exec(Trans.Builder b) {
        time += dt;
        clock.setTime(time);
        Trans t = b.build();
        long a = System.nanoTime();
        db.execute(t);
        long ns = System.nanoTime() - a;
        txCount++;
        long rec = t.nextPos - t.tpos;
        recBytes += rec;
        maxRecord = Math.max(maxRecord, rec);
        if (rec > 1000000) bigRecords++;
        maxExecNs = Math.max(maxExecNs, ns);
        if (execN < execSample.length) execSample[execN++] = ns;
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

    static long usedHeap() {
        Runtime rt = Runtime.getRuntime();
        for (int k = 0; k < 4; k++) System.gc();
        return rt.totalMemory() - rt.freeMemory();
    }

    // ---- Measures ----

    /** CleanupRule's (023-03) counting follower: key nodes by id, KEY klongs, live ones. */
    static final class Count implements PointerFollower {
        final PointerFollower inner;
        final HashSet<Long> ids = new HashSet<Long>();
        long keyKlongs, live, nodes;

        Count(PointerFollower inner) { this.inner = inner; }

        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node r = inner.followPointer(predecessor, pointerIndex, op);
            nodes++;
            if (r instanceof KeyNode && ids.add(r.getId())) {
                KeyNode kn = (KeyNode) r;
                int sz = kn.getSize();
                long del = kn.getDeleteBitmapAtTime(Klong.MAX_TIME, sz);
                for (int i = 0; i < sz; i++) {
                    long k = kn.getKlong(i);
                    if (!Klong.isKey(k)) continue;
                    keyKlongs++;
                    if (Klong.isDeleted(del, i)) continue;
                    long cv = Klong.getCompareValue(k);
                    boolean shadowed = false;
                    for (int j = i + 1; j < sz && !shadowed; j++) {
                        long k2 = kn.getKlong(j);
                        shadowed = Klong.isKey(k2) && Klong.getCompareValue(k2) == cv;
                    }
                    if (!shadowed) live++;
                }
            }
            return r;
        }
    }

    /** Counts user KVs (keys starting with "/k/"), adds none; stops after max of them. */
    static final class Counter implements GetMany.StopCondition {
        long users, all, max = Long.MAX_VALUE;
        public int handleKvt(Kvt kvt) {
            all++;
            users++;          // the scan starts at "/k/", after the internal keys "/#..."
            return users >= max ? ADD_AND_STOP_NOT_USED() : CONTINUE;
        }
        int ADD_AND_STOP_NOT_USED() { return STOP; }
        public void eod() {}
    }

    /** A scan from "/k/" of up to max user keys: time (ordinary follower). */
    String scanTimed(String label, long max) {
        GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments("/k/");
        g.inclusive = true;
        Counter c = new Counter();
        c.max = max;
        g.stopCondition = c;
        long a = System.nanoTime();
        db.getMany(g);
        long ns = System.nanoTime() - a;
        return String.format("%s keys=%d ms=%.1f ns/key=%d", label, c.users, ns / 1e6,
                c.users == 0 ? 0 : ns / c.users);
    }

    /** The same scan with the counting follower (maintenance(): loads, does not install). */
    String scanNodes(String label, long max) {
        synchronized (db.internal().getWriteLock()) {
            Count cn = new Count(db.internal().nodeCollection().maintenance());
            GetMany g = db.newGetMany();
            g.gd.pointerFollower = cn;
            g.startKey = Keys.toSegments("/k/");
            g.inclusive = true;
            Counter c = new Counter();
            c.max = max;
            g.stopCondition = c;
            long a = System.nanoTime();
            db.getMany(g);
            long ns = System.nanoTime() - a;
            return String.format("%s keys=%d keyNodes=%d follows=%d klongs=%d dead=%d ms=%.1f",
                    label, c.users, cn.ids.size(), cn.nodes, cn.keyKlongs,
                    cn.keyKlongs - cn.live, ns / 1e6);
        }
    }

    /** gets of random keys from the given list of key indexes; ns per get, p99. */
    String gets(String label, int[] idx, int count, long seed) {
        Random r = new Random(seed);
        long[] ns = new long[count];
        int miss = 0;
        long a0 = System.nanoTime();
        for (int k = 0; k < count; k++) {
            int i = idx[r.nextInt(idx.length)];
            long a = System.nanoTime();
            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(key(i)), db.newGetData());
            ns[k] = System.nanoTime() - a;
            if (v == null) miss++;
        }
        long tot = System.nanoTime() - a0;
        Arrays.sort(ns);
        if (miss > 0) throw new AssertionError(label + ": " + miss + " gets found nothing");
        return String.format("%s gets=%d us/get=%.2f p50=%.2fus p99=%.1fus max=%.1fms loads=%d",
                label, count, tot / 1e3 / count, ns[count / 2] / 1e3, ns[(int) (count * 0.99)] / 1e3,
                ns[count - 1] / 1e6, db.internal().cacheStats().loads);
    }

    String state(String label) {
        return String.format("%s len=%d kept=%d files=%d iters=%d fap=%d", label,
                db.getStreamLength(), kept(), fileBytes(), db.getReclaimIterationCount(),
                db.getFirstAvailablePos());
    }

    int[] live(int n, int keep, double frac) {
        int c = 0;
        for (int i = 0; i < n; i++) if (isLive(i, keep, frac, n)) c++;
        int[] a = new int[c];
        c = 0;
        for (int i = 0; i < n; i++) if (isLive(i, keep, frac, n)) a[c++] = i;
        return a;
    }

    static boolean isLive(int i, int keep, double frac, int n) {
        if (keep > 1 && i % keep != 0) return false;
        return i >= (long) (frac * n);
    }

    // ---- Commands ----

    void fill() throws IOException {
        int n = i("n", 1000000), vs = i("valsize", 100), batch = i("batch", 100);
        int keep = i("keep", 1);
        open(true);
        int[] o = live(n, keep, d("frac", 0));
        if (s("order", "random").equals("random")) {
            Random r = new Random(l("seed", 1));
            for (int k = o.length - 1; k > 0; k--) {
                int j = r.nextInt(k + 1);
                int t = o[k]; o[k] = o[j]; o[j] = t;
            }
        }
        long heap0 = usedHeap();
        resetTx();
        long a = System.nanoTime();
        int every = Math.max(1, o.length / 10);
        for (int k = 0; k < o.length; ) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < batch && k < o.length; j++, k++) b.put(key(o[k]), value(vs, o[k]));
            exec(b);
            if (k % every < batch) out(el() + " fill " + k + " " + state(""));
        }
        long ns = System.nanoTime() - a;
        out(String.format("%s FILL n=%d valsize=%d batch=%d order=%s puts/s=%.0f us/put=%.3f s=%.1f",
                el(), o.length, vs, batch, s("order", "random"), o.length / (ns / 1e9),
                ns / 1e3 / o.length, ns / 1e9));
        out(el() + " FILL " + txLine());
        long sa = System.nanoTime();
        db.sync(SyncLevel.ORDINARY);
        out(el() + " SYNC ms=" + (System.nanoTime() - sa) / 1000000);
        out(el() + " FILL " + state("state") + " bytes/put=" + db.getStreamLength() / o.length
                + " kept/put=" + kept() / o.length);
        long heap = usedHeap();
        out(String.format("%s HEAP after fill: %d MB, %.0f bytes/KV (default cache)", el(),
                (heap - heap0) / 1000000, (double) (heap - heap0) / o.length));
        if (i("reads", 1) == 1) {
            int g = i("gets", 1000000);
            out(el() + " WARM " + gets("gets1", o, g, 2));
            out(el() + " WARM " + gets("gets2", o, g, 3));
            out(el() + " WARM " + scanTimed("scan1", Long.MAX_VALUE));
            out(el() + " WARM " + scanTimed("scan2", Long.MAX_VALUE));
            if (i("nodes", 1) == 1) out(el() + " NODES " + scanNodes("all", Long.MAX_VALUE));
        }
        close();
    }

    void cold() throws IOException {
        int n = i("n", 1000000), keep = i("keep", 1);
        double frac = d("frac", 0);
        open(false);
        int[] o = live(n, keep, frac);
        int g = i("gets", 100000);
        out(el() + " COLD " + gets("cold-gets", o, g, 5));
        out(el() + " COLD " + gets("after-gets", o, g, 6));
        out(el() + " COLD " + gets("after-gets-1M", o, 1000000, 7));
        out(el() + " COLD " + scanTimed("scan1", Long.MAX_VALUE));
        out(el() + " COLD " + scanTimed("scan2", Long.MAX_VALUE));
        out(el() + " COLD " + state("state"));
        close();
    }

    /** start, then the head scans and nodes: (4) after (2). */
    void start() throws IOException {
        open(false);
        out(el() + " START " + scanTimed("head1000", 1000));
        out(el() + " START " + scanTimed("all", Long.MAX_VALUE));
        out(el() + " START " + scanNodes("all", Long.MAX_VALUE));
        out(el() + " START " + state("state"));
        db.close();
    }

    void massdel() throws IOException {
        int n = i("n", 1000000), batch = i("batch", 100);
        double frac = d("frac", 0.9);
        open(false);
        deleteAndDrive(n, i("keep", 1), frac, batch);
    }

    void sparse() throws IOException {
        int n = i("n", 1000000), batch = i("batch", 100), keep = i("keep", 30);
        open(false);
        deleteAndDrive(n, keep, 0, batch);
    }

    void deleteAndDrive(int n, int keep, double frac, int batch) throws IOException {
        out(el() + " BEFORE " + state("state"));
        if (i("before", 1) == 1) {
            out(el() + " BEFORE " + scanTimed("head1000", 1000));
            out(el() + " BEFORE " + scanNodes("all", Long.MAX_VALUE));
        }
        boolean nodel = i("nodel", 0) == 1;    // a twin: the drive only
        resetTx();
        long a = System.nanoTime();
        int dels = 0;
        int every = Math.max(1, n / 10);
        Trans.Builder b = db.trans();
        int inB = 0;
        for (int k = 0; k < n; k++) {
            if (nodel || isLive(k, keep, frac, n)) continue;
            b.delete(key(k));
            dels++;
            if (++inB == batch) {
                exec(b);
                b = db.trans();
                inB = 0;
            }
            if (k % every == 0) out(el() + " del " + k + " " + state(""));
        }
        if (inB > 0) exec(b);
        long ns = System.nanoTime() - a;
        out(String.format("%s DELETE dels=%d dels/s=%.0f s=%.1f", el(), dels, dels / (ns / 1e9),
                ns / 1e9));
        out(el() + " DELETE " + txLine());
        out(el() + " AFTER " + state("state"));
        int[] o = live(n, keep, frac);
        out(el() + " AFTER live=" + o.length);
        out(el() + " AFTER " + scanTimed("head1000", 1000));
        out(el() + " AFTER " + scanTimed("head1000-again", 1000));
        out(el() + " AFTER " + scanTimed("all", Long.MAX_VALUE));
        out(el() + " AFTER " + scanNodes("head1000", 1000));
        out(el() + " AFTER " + scanNodes("all", Long.MAX_VALUE));
        out(el() + " AFTER " + gets("gets", o, 100000, 9));

        // The drive: transactions of dbatch overwrites of random live keys (dvalsize bytes),
        // until kept is at most target bytes, or maxdrive transactions.
        long target = l("target", 0);
        int maxDrive = i("maxdrive", 200000), dbatch = i("dbatch", 100), dvs = i("dvalsize", 100);
        int report = i("report", 5000);
        Random r = new Random(11);
        resetTx();
        long da = System.nanoTime();
        long iters0 = db.getReclaimIterationCount();
        int k;
        long reachedAt = -1;
        for (k = 1; k <= maxDrive; k++) {
            Trans.Builder d = db.trans();
            for (int j = 0; j < dbatch; j++) {
                int x = o[r.nextInt(o.length)];
                d.put(key(x), value(dvs, x + k));
            }
            exec(d);
            if (reachedAt < 0 && target > 0 && kept() <= target) {
                reachedAt = k;
                out(el() + " DRIVE reached target=" + target + " at tx=" + k + " "
                        + state(""));
                if (i("stopattarget", 1) == 1) break;
            }
            if (k % report == 0) {
                out(String.format("%s drive tx=%d %s %s", el(), k, state(""), txLine()));
            }
        }
        long dns = System.nanoTime() - da;
        out(String.format("%s DRIVE done tx=%d reachedAt=%d itersDuring=%d s=%.1f", el(),
                Math.min(k, maxDrive), reachedAt, db.getReclaimIterationCount() - iters0, dns / 1e9));
        out(el() + " DRIVE " + txLine());
        out(el() + " END " + state("state"));
        out(el() + " END " + scanTimed("head1000", 1000));
        out(el() + " END " + scanTimed("all", Long.MAX_VALUE));
        out(el() + " END " + scanNodes("all", Long.MAX_VALUE));
        long heap = usedHeap();
        out(String.format("%s END heap=%d MB", el(), heap / 1000000));
        close();
    }

    /**
     * Keys in time order (a log, or 021-25's FIFO with fifo=1): each transaction puts lbatch
     * new keys after every key so far, and with fifo=1 deletes the lbatch oldest live keys
     * (from first=frac*n on). For CL7: the records of reclaim's last touch.
     */
    void log() throws IOException {
        int n = i("n", 1000000), lb = i("lbatch", 100), vs = i("valsize", 100);
        int maxDrive = i("maxdrive", 100000), report = i("report", 5000);
        boolean fifo = i("fifo", 1) == 1;
        long next = l("next", n), oldest = (long) (d("frac", 0.9) * n);
        open(false);
        out(el() + " LOG before " + state("state"));
        resetTx();
        long iters0 = db.getReclaimIterationCount();
        long a = System.nanoTime();
        for (int k = 1; k <= maxDrive; k++) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < lb; j++, next++) b.put(key((int) next), value(vs, next));
            if (fifo) for (int j = 0; j < lb; j++, oldest++) b.delete(key((int) oldest));
            exec(b);
            if (k % report == 0) out(String.format("%s log tx=%d %s %s", el(), k, state(""),
                    txLine()));
        }
        long ns = System.nanoTime() - a;
        out(String.format("%s LOG done tx=%d iters=%d s=%.1f tx/s=%.0f", el(), maxDrive,
                db.getReclaimIterationCount() - iters0, ns / 1e9, maxDrive / (ns / 1e9)));
        out(el() + " LOG " + txLine());
        out(el() + " LOG " + state("state"));
        out(el() + " LOG " + scanTimed("head1000", 1000));
        out(el() + " LOG " + scanNodes("all", Long.MAX_VALUE));
        close();
    }

    void mem() throws Exception {
        int n = i("n", 1000000);
        Db m = Db.builder().testSetup().mainStream(new DummyStream()).start();
        long e = usedHeap();
        for (int k = 0; k < n / 100; k++) {
            Trans.Builder b = m.trans();
            for (int j = 0; j < 100; j++) b.put("" + (k * 100 + j), new byte[0]);
            m.execute(b.build());
        }
        long f = usedHeap();
        out(String.format("MEM n=%d %.1f bytes/KV", n, (double) (f - e) / n));
        m.stop();
    }

    static void rm(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) rm(c);
        f.delete();
    }

    public static void main(String[] args) throws Exception {
        PF1 x = new PF1();
        for (int k = 1; k < args.length; k++) {
            int eq = args[k].indexOf('=');
            x.p.put(args[k].substring(0, eq), args[k].substring(eq + 1));
        }
        out("PF1 " + String.join(" ", args) + " jar=" + System.getProperty("java.class.path"));
        switch (args[0]) {
        case "fill": x.fill(); break;
        case "cold": x.cold(); break;
        case "start": x.start(); break;
        case "massdel": x.massdel(); break;
        case "sparse": x.sparse(); break;
        case "drive": x.p.put("nodel", "1"); x.massdel(); break;
        case "mem": x.mem(); break;
        case "log": x.log(); break;
        default: throw new IllegalArgumentException(args[0]);
        }
        out(x.el() + " DONE");
        System.exit(0);
    }
}
