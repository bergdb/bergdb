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
 * The node-size probe of bergdb 024-19, 2026-11-11, after 024-03's PF1. Sets the builder's
 * maxNodeSize directly (package-private), so any size runs; above 62 only on the measuring
 * build of branch 024-19-nsize (delete bits beyond 61 refused, larger array classes).
 *
 * java -cp classes:JAR bergdb.core.NS CMD key=value...
 *   run   ns n shape(k13|k24|mem) order(random|asc|queue) vs batch ups ubatch retain(s, 0 =
 *         forever) dir: a fill, the tree, then ups overwrites (queue: ups puts at the end and
 *         as many deletes of the oldest), the tree again. restart=1: close, then a start.
 *   mem   ns n shape: MEM's method (DummyStream, test setup, empty values, 100 a transaction).
 */
public class NS {
    static final long SEC = Clock.UNITS_PER_SEC;
    final Map<String, String> p = new HashMap<String, String>();
    int i(String k, int d) { return p.containsKey(k) ? Integer.parseInt(p.get(k)) : d; }
    long l(String k, long d) { return p.containsKey(k) ? Long.parseLong(p.get(k)) : d; }
    String s(String k, String d) { return p.containsKey(k) ? p.get(k) : d; }

    File dir;
    CoreTestClock clock;
    long time = 10 * SEC;
    Db db;
    long dt = 10000;
    String shape;
    final long t0 = System.nanoTime();
    long txCount, recBytes, maxRecord;

    static void out(String s) { System.out.println(s); System.out.flush(); }
    String el() { return String.format("[%.1fs]", (System.nanoTime() - t0) / 1e9); }

    String key(long i) {
        switch (shape) {
        case "k13": return String.format("/k/%010d", i);
        case "k24": return String.format("/scale/key/%013d", i);
        case "mem": return "" + i;
        default: throw new IllegalArgumentException(shape);
        }
    }

    String startKey() {
        switch (shape) {
        case "k13": return "/k/";
        case "k24": return "/scale/";
        default: return "0";
        }
    }

    static byte[] value(int size, long tag) {
        byte[] v = new byte[size];
        for (int j = 0; j < size; j++) v[j] = (byte) ('a' + (tag + j) % 26);
        for (int j = 0; j < 8 && j < size; j++) v[j] = (byte) (tag >>> (8 * j));
        return v;
    }

    DbBuilder builder() throws IOException {
        DbBuilder b = Db.builder().mainStream(new FileStream(dir)).clock(clock);
        b.maxNodeSize = i("ns", 30);
        if (p.containsKey("sd")) b.startupDistance(i("sd", 50000000));
        if (p.containsKey("cache")) b.cacheSizeIndicator(l("cache", 200000000));
        return b;
    }

    void exec(Trans.Builder b) {
        time += dt;
        clock.setTime(time);
        Trans t = b.build();
        db.execute(t);
        txCount++;
        long rec = t.nextPos - t.tpos;
        recBytes += rec;
        maxRecord = Math.max(maxRecord, rec);
    }

    long kept() { return db.getStreamLength() - db.getFirstAvailablePos(); }

    static long usedHeap() {
        Runtime rt = Runtime.getRuntime();
        for (int k = 0; k < 4; k++) System.gc();
        return rt.totalMemory() - rt.freeMemory();
    }

    /** Counts the distinct key nodes a scan or a get follows, their klongs and live keys. */
    static final class Count implements PointerFollower {
        final PointerFollower inner;
        final HashSet<Long> ids = new HashSet<Long>();
        long keyKlongs, live, klongs, leaves, keyFollows;
        long storedBytes;

        Count(PointerFollower inner) { this.inner = inner; }

        public Node followPointer(Node predecessor, int pointerIndex, OpData op) {
            Node r = inner.followPointer(predecessor, pointerIndex, op);
            if (r instanceof KeyNode) {
                keyFollows++;
                if (ids.add(r.getId())) {
                    KeyNode kn = (KeyNode) r;
                    int sz = kn.getSize();
                    klongs += sz;
                    storedBytes += 32 + 16L * sz;
                    long del = kn.getDeleteBitmapAtTime(Klong.MAX_TIME, sz);
                    for (int i = 0; i < sz; i++) {
                        long k = kn.getKlong(i);
                        if (!Klong.isKey(k)) continue;
                        keyKlongs++;
                        if (i < 62 && Klong.isDeleted(del, i)) continue;
                        long cv = Klong.getCompareValue(k);
                        boolean shadowed = false;
                        for (int j = i + 1; j < sz && !shadowed; j++) {
                            long k2 = kn.getKlong(j);
                            shadowed = Klong.isKey(k2) && Klong.getCompareValue(k2) == cv;
                        }
                        if (!shadowed) live++;
                    }
                }
            }
            return r;
        }
    }

    static final class Counter implements GetMany.StopCondition {
        long n;
        public int handleKvt(Kvt kvt) { n++; return CONTINUE; }
        public void eod() {}
    }

    /** The current tree, by a scan with the counting follower; and the path of gets. */
    String tree(String label, long[] keys) {
        synchronized (db.internal().getWriteLock()) {
            Count cn = new Count(db.internal().nodeCollection().maintenance());
            GetMany g = db.newGetMany();
            g.gd.pointerFollower = cn;
            g.startKey = Keys.toSegments(startKey());
            g.inclusive = true;
            Counter c = new Counter();
            g.stopCondition = c;
            db.getMany(g);
            // the path: key nodes a get follows, over 2,000 random keys
            Random r = new Random(5);
            long sum = 0, max = 0;
            int m = 2000;
            for (int k = 0; k < m; k++) {
                Count pc = new Count(db.internal().nodeCollection().maintenance());
                GetData gd = db.newGetData();
                gd.pointerFollower = pc;
                byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(key(keys[r.nextInt(keys.length)])), gd);
                if (v == null) throw new AssertionError("a get found nothing");
                sum += pc.keyFollows;
                max = Math.max(max, pc.keyFollows);
            }
            return String.format("%s keys=%d keyNodes=%d klongs=%d keyKlongs=%d live=%d "
                    + "stored=%d storedPerKey=%.1f klongsPerNode=%.1f livePerNode=%.1f "
                    + "path=%.2f pathMax=%d", label, c.n, cn.ids.size(), cn.klongs, cn.keyKlongs,
                    cn.live, cn.storedBytes, (double) cn.storedBytes / c.n,
                    (double) cn.klongs / cn.ids.size(), (double) cn.live / cn.ids.size(),
                    (double) sum / m, max);
        }
    }

    String gets(String label, long[] idx, int count, long seed) {
        Random r = new Random(seed);
        long loads0 = db.internal().cacheStats().loads;
        long a0 = System.nanoTime();
        for (int k = 0; k < count; k++) {
            long i = idx[r.nextInt(idx.length)];
            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(key(i)), db.newGetData());
            if (v == null) throw new AssertionError(label + ": a get found nothing");
        }
        long tot = System.nanoTime() - a0;
        long loads = db.internal().cacheStats().loads - loads0;
        return String.format("%s gets=%d us/get=%.2f loads/get=%.3f resident=%d", label, count,
                tot / 1e3 / count, (double) loads / count, db.internal().cacheStats().residentBytes);
    }

    String scan(String label) {
        GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments(startKey());
        g.inclusive = true;
        Counter c = new Counter();
        g.stopCondition = c;
        long loads0 = db.internal().cacheStats().loads;
        long a = System.nanoTime();
        db.getMany(g);
        long ns = System.nanoTime() - a;
        return String.format("%s keys=%d ms=%.1f ns/key=%d loads/key=%.3f", label, c.n, ns / 1e6,
                ns / Math.max(1, c.n), (double) (db.internal().cacheStats().loads - loads0) / c.n);
    }

    void run() throws IOException {
        shape = s("shape", "k13");
        int n = i("n", 1000000), vs = i("vs", 100), batch = i("batch", 100);
        long ups = l("ups", 0);
        int ubatch = i("ubatch", batch);
        String order = s("order", "random");
        dir = new File(s("dir", "data"));
        rm(dir);
        dir.mkdirs();
        clock = new CoreTestClock();
        clock.setTime(time);
        db = builder().start();
        long retain = l("retain", 0);
        if (retain > 0) db.setRetainDuration(retain * SEC);
        out(el() + " START ns=" + i("ns", 30) + " maxNodeSize=" + db.internal().maxNodeSize());

        long[] o = new long[n];
        for (int k = 0; k < n; k++) o[k] = k;
        if (order.equals("random")) {
            Random r = new Random(1);
            for (int k = n - 1; k > 0; k--) {
                int j = r.nextInt(k + 1);
                long t = o[k]; o[k] = o[j]; o[j] = t;
            }
        }
        long a = System.nanoTime();
        for (int k = 0; k < n; ) {
            Trans.Builder b = db.trans();
            for (int j = 0; j < batch && k < n; j++, k++) b.put(key(o[k]), value(vs, o[k]));
            exec(b);
        }
        long ns = System.nanoTime() - a;
        long len = db.getStreamLength();
        out(String.format("%s FILL n=%d shape=%s order=%s vs=%d batch=%d bytesPerPut=%.1f "
                + "bytesPerTx=%d maxRec=%d kept=%d keptPerKey=%.1f puts/s=%.0f iters=%d", el(), n,
                shape, order, vs, batch, (double) len / n, recBytes / txCount, maxRecord, kept(),
                (double) kept() / n, n / (ns / 1e9), db.getReclaimIterationCount()));
        if (!order.equals("random")) Arrays.sort(o);
        out(el() + " " + tree("TREE-FILL", o));

        long[] live = o;
        if (ups > 0) {
            Random r = new Random(11);
            long next = n, oldest = 0;
            long len20 = -1, puts20 = 0;
            long puts = 0;
            txCount = recBytes = maxRecord = 0;
            long ua = System.nanoTime();
            long tx = 0;
            while (puts < ups) {
                Trans.Builder b = db.trans();
                for (int j = 0; j < ubatch; j++, puts++) {
                    if (order.equals("queue")) {
                        b.put(key(next), value(vs, next));
                        next++;
                    } else {
                        long x = r.nextInt(n);
                        b.put(key(x), value(vs, x + tx));
                    }
                }
                if (order.equals("queue")) {
                    for (int j = 0; j < ubatch; j++, oldest++) b.delete(key(oldest));
                }
                exec(b);
                tx++;
                if (len20 < 0 && puts >= ups / 5) {
                    len20 = db.getStreamLength();
                    puts20 = puts;
                }
            }
            long uns = System.nanoTime() - ua;
            double bpp = (double) (db.getStreamLength() - len20) / (puts - puts20);
            out(String.format("%s UPD ups=%d ubatch=%d retain=%d bytesPerPut=%.1f (last 80%%) "
                    + "bytesPerTx=%d maxRec=%d kept=%d keptPerKey=%.1f len=%d iters=%d puts/s=%.0f",
                    el(), puts, ubatch, retain, bpp, recBytes / Math.max(1, txCount), maxRecord,
                    kept(), (double) kept() / n, db.getStreamLength(),
                    db.getReclaimIterationCount(), puts / (uns / 1e9)));
            if (order.equals("queue")) {
                live = new long[n];
                for (int k = 0; k < n; k++) live[k] = oldest + k;
            }
            out(el() + " " + tree("TREE-UPD", live));
        }
        int g = i("gets", 0);
        if (g > 0) {
            out(el() + " WARM " + gets("gets1", live, g, 2));
            out(el() + " WARM " + gets("gets2", live, g, 3));
        }
        if (i("scan", 0) == 1) {
            out(el() + " WARM " + scan("scan1"));
            out(el() + " WARM " + scan("scan2"));
        }
        db.sync(SyncLevel.ORDINARY);
        db.close();
        out(el() + " CLOSED files=" + fileBytes());
        if (i("restart", 0) == 1) {
            long t = System.nanoTime();
            db = builder().start();
            out(String.format("%s RESTART ms=%d len=%d", el(), (System.nanoTime() - t) / 1000000,
                    db.getStreamLength()));
            if (g > 0) {
                out(el() + " COLD " + gets("cold-gets", live, g, 5));
                out(el() + " COLD " + gets("cold-gets2", live, g, 6));
            }
            if (i("scan", 0) == 1) out(el() + " COLD " + scan("scan1"));
            db.close();
        }
        if (i("keep", 0) == 0) rm(dir);
    }

    long fileBytes() {
        long sum = 0;
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) if (f.getName().endsWith(".bergdb")) sum += f.length();
        return sum;
    }

    void mem() throws Exception {
        shape = s("shape", "mem");
        int n = i("n", 1000000);
        DbBuilder b = Db.builder().testSetup().mainStream(new DummyStream());
        b.maxNodeSize = i("ns", 30);
        Db m = b.start();
        long e = usedHeap();
        for (int k = 0; k < n / 100; k++) {
            Trans.Builder t = m.trans();
            for (int j = 0; j < 100; j++) t.put(key(k * 100 + j), new byte[0]);
            m.execute(t.build());
        }
        long f = usedHeap();
        out(String.format("MEM ns=%d shape=%s n=%d %.1f bytes/KV", i("ns", 30), shape, n,
                (double) (f - e) / n));
        m.stop();
    }

    static void rm(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) rm(c);
        f.delete();
    }

    public static void main(String[] args) throws Exception {
        NS x = new NS();
        for (int k = 1; k < args.length; k++) {
            int eq = args[k].indexOf('=');
            x.p.put(args[k].substring(0, eq), args[k].substring(eq + 1));
        }
        out("NS " + String.join(" ", args));
        switch (args[0]) {
        case "run": x.run(); break;
        case "mem": x.mem(); break;
        default: throw new IllegalArgumentException(args[0]);
        }
        out(x.el() + " DONE");
        System.exit(0);
    }
}
