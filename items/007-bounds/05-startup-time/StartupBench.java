package bergdb.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.Random;
import java.util.SplittableRandom;

import bergdb.dag.GetData;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;

/**
 * Startup time against the startup section, for bergdb 007-03, step 5 (007-05). A tool of
 * the item: it uses bergdb.jar as it is, through Db.testHooks and Db.internal().
 *
 * Two modes, one JVM each:
 *
 *   make   makes a database on disk (FileStream) in st.dir: st.keys keys of 24 bytes (key24,
 *          as 005-38's WriteBench and 004-02's ScaleBench) in random order, values of
 *          st.valsize bytes, 1,000 puts a transaction, node size 30, infinite retention,
 *          startup distance st.sd; then st.updates puts to random loaded keys, 1,000 a
 *          transaction. With st.budget > 0 the capacity controller evicts down to it.
 *          Reports the startup lag (the stream's end minus the startup pos) after every
 *          update transaction, its largest, and at the end, with D; then closes, which
 *          does not write D, so the next start reruns the section left.
 *   start  opens the database in st.dir with the budget st.budget and times start(). Reads
 *          that reach the FileStream are counted by startup phase (Db.startInner's step, or
 *          DbStarter.doOrdinaryStartup's step: rerunTransactions, linkD, ...), with their
 *          bytes and their time, and a thread samples where the starting thread is every
 *          2 ms. With st.phases=0 the reads are counted in all (a stack trace a read costs
 *          time) and the samples are 10 ms apart: for the timed runs. Then the section, the transactions rerun, D, the heap, /proc/self/io
 *          where there is one, and 2,000 random keys checked.
 *
 * Output: lines for people, and one line "RESULT {...}" for the scripts.
 *
 * Usage: java -Dst.mode=make|start -Dst.dir=DIR [-Dst.keys=N] [-Dst.updates=N] [-Dst.sd=BYTES]
 *            [-Dst.valsize=BYTES] [-Dst.budget=BYTES] -cp bergdb.jar:classes bergdb.core.StartupBench
 */
public class StartupBench {
    static String prop(String n, String d) { return System.getProperty("st." + n, d); }

    static final long SEC = bergdb.pub.util.Clock.UNITS_PER_SEC;
    static final String MARKER = "startupbench.properties";
    static final int TX = 1000;

    final String mode = prop("mode", "start");
    final File dir = new File(prop("dir", "."));
    int keys = Integer.parseInt(prop("keys", "1000000"));
    long updates = Long.parseLong(prop("updates", "0"));
    int sd = Integer.parseInt(prop("sd", "50000000"));
    int valsize = Integer.parseInt(prop("valsize", "8"));
    final long budget = Long.parseLong(prop("budget", "0"));
    /** 0: the reads are counted in all, not by phase, which costs a stack trace a read. */
    final boolean byPhase = !prop("phases", "1").equals("0");

    final CoreTestClock clock = new CoreTestClock();
    long time = SEC;
    final Map<String, Object> result = new LinkedHashMap<String, Object>();
    final long t0 = System.nanoTime();

    void say(String s) {
        System.out.println(String.format(Locale.ROOT, "[%7.1f s] %s", (System.nanoTime() - t0) / 1e9, s));
        System.out.flush();
    }

    static byte[] key(int k) {
        byte[] b = new byte[24];
        System.arraycopy("/scale/key/".getBytes(StandardCharsets.US_ASCII), 0, b, 0, 11);
        long v = k;
        for (int i = 23; i >= 11; i--) { b[i] = (byte) ('0' + v % 10); v /= 10; }
        return b;
    }

    /** The key's number in the first four bytes, a version in the fifth (if room). */
    byte[] value(int k, int version) {
        byte[] v = new byte[valsize];
        for (int i = 0; i < 4 && i < valsize; i++) v[i] = (byte) (k >>> (24 - 8 * i));
        if (valsize > 4) v[4] = (byte) version;
        return v;
    }

    // ---- The stream, with reads counted by startup phase ----

    /** Where the starting thread is: the step of startInner or of doOrdinaryStartup it is in. */
    static String phase(StackTraceElement[] st) {
        for (int i = 1; i < st.length; i++) {
            String c = st[i].getClassName(), m = st[i].getMethodName();
            if (c.equals("bergdb.core.DbStarter") && m.equals("doOrdinaryStartup")) {
                return "starter." + st[i - 1].getMethodName();
            }
        }
        for (int i = 1; i < st.length; i++) {
            if (st[i].getClassName().equals("bergdb.core.Db") && st[i].getMethodName().equals("startInner")) {
                return st[i - 1].getMethodName();
            }
        }
        return "other";
    }

    static final class Counts {
        long reads, bytes, nanos, samples;
    }

    static final class PhaseStream implements AppendOnlyStream {
        final FileStream s;
        volatile Thread watched;    // reads in this thread are counted by phase
        boolean phases = true;
        final Map<String, Counts> byPhase = new LinkedHashMap<String, Counts>();

        PhaseStream(FileStream s) { this.s = s; }

        Counts counts(String p) {
            Counts c = byPhase.get(p);
            if (c == null) byPhase.put(p, c = new Counts());
            return c;
        }

        public long getLength() { return s.getLength(); }
        public long getFirstPos() { return s.getFirstPos(); }
        public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
            long a = System.nanoTime();
            s.read(position, dest, destOffset, length);
            long e = System.nanoTime() - a;
            Thread w = watched;
            String p = w != Thread.currentThread() ? "after"
                    : phases ? phase(new Throwable().getStackTrace()) : "start";
            synchronized (this) {
                Counts c = counts(p);
                c.reads++;
                c.bytes += length;
                c.nanos += e;
            }
        }
        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            s.append(source, sourceOffset, length);
        }
        public void pretruncate(long position) throws IOException { s.pretruncate(position); }
        public void seekFirstPos(long position) throws IOException { s.seekFirstPos(position); }
        public void close() throws IOException { s.close(); }
    }

    PhaseStream stream;

    Db open(boolean create) throws IOException {
        stream = new PhaseStream(new FileStream(dir));
        clock.setTime(time);
        DbBuilder b = Db.builder().stream("main", stream).clock(clock).testId().retainForever()
                .maxNodeSize30();
        if (create) b.startupDistance(sd);
        if (budget > 0) b.cacheSizeIndicator(budget).evictionSchedule(Eviction.Schedule.BUDGET, 1);
        else b.noEvict();
        return b.build();
    }

    /** D's distinct nodes and their stream bytes. */
    static long[] dSize(Db db) {
        final HashSet<Long> seen = new HashSet<Long>();
        final long[] r = new long[2];
        db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node n, long tpos, long lastTpos) {
                if (!seen.add(n.getId())) return;
                r[0]++;
                r[1] += n instanceof KeyNode ? StoredKeyNode.getByteSize((KeyNode) n)
                        : StoredTopNode.getByteSize((TopNode) n);
            }
        });
        return r;
    }

    static long heapUsed() {
        System.gc();
        System.gc();
        return Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory();
    }

    // ---- Make ----

    long maxLag;

    void make() throws Exception {
        String[] existing = dir.list();
        if (existing != null && existing.length > 0) throw new IllegalStateException("not empty: " + dir);
        dir.mkdirs();
        final Db db = open(true);
        db.start();
        say(String.format(Locale.ROOT, "make: %d keys, values of %d bytes, sd %d, %d updates, budget %d, dir %s",
                keys, valsize, sd, updates, budget, dir));
        int[] ord = new int[keys];
        for (int i = 0; i < keys; i++) ord[i] = i;
        Random rnd = new Random(1);
        for (int i = keys - 1; i > 0; i--) { int j = rnd.nextInt(i + 1); int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        long a = System.nanoTime(), last = a;
        for (int i = 0; i < keys; i += TX) {
            Trans.Builder tb = db.trans();
            int e = Math.min(keys, i + TX);
            for (int j = i; j < e; j++) tb.put(key(ord[j]), value(ord[j], 0));
            time += SEC / 10000;
            clock.setTime(time);
            db.execute(tb.build());
            if (System.nanoTime() - last > 30e9) {
                last = System.nanoTime();
                say(String.format(Locale.ROOT, "  load: %d puts, stream %d MB", e,
                        db.internal().nodeStream().getNextPos() / 1000000));
            }
        }
        ord = null;
        double loadSec = (System.nanoTime() - a) / 1e9;
        long loadEnd = db.internal().nodeStream().getNextPos();
        say(String.format(Locale.ROOT, "load done: %.1f s, stream %d MB", loadSec, loadEnd / 1000000));
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                long lag = db.internal().nodeStream().getNextPos() - x.startupPos.get();
                if (lag > maxLag) maxLag = lag;
            }
            public void valueNodeCreated(ValueNode node, long[] key) {}
            public void nodeTouched(Node node) {}
            public void nodeReplaced(Node node) {}
        };
        SplittableRandom ur = new SplittableRandom(2);
        a = System.nanoTime();
        for (long i = 0; i < updates; i += TX) {
            Trans.Builder tb = db.trans();
            long e = Math.min(updates, i + TX);
            for (long j = i; j < e; j++) {
                int k = ur.nextInt(keys);
                tb.put(key(k), value(k, 1));
            }
            time += SEC / 10000;
            clock.setTime(time);
            db.execute(tb.build());
            if (System.nanoTime() - last > 30e9) {
                last = System.nanoTime();
                say(String.format(Locale.ROOT, "  updates: %d, stream %d MB, lag %d MB, largest %d MB", e,
                        db.internal().nodeStream().getNextPos() / 1000000,
                        (db.internal().nodeStream().getNextPos() - db.internal().getStartupPosForEvict()) / 1000000,
                        maxLag / 1000000));
            }
        }
        Db.testHooks = null;
        double updSec = (System.nanoTime() - a) / 1e9;
        db.sync(SyncLevel.STRONG);
        long end = db.internal().nodeStream().getNextPos();
        long lag = end - db.internal().getStartupPosForEvict();
        long[] d = dSize(db);
        int trans = db.internal().transSeq().getSize();
        Properties p = new Properties();
        p.setProperty("keys", Integer.toString(keys));
        p.setProperty("valsize", Integer.toString(valsize));
        p.setProperty("sd", Integer.toString(sd));
        p.setProperty("updates", Long.toString(updates));
        p.setProperty("time", Long.toString(time));
        FileOutputStream fo = new FileOutputStream(new File(dir, MARKER));
        try {
            p.store(fo, "StartupBench (bergdb 007-05)");
        } finally {
            fo.close();
        }
        result.put("mode", "make");
        result.put("keys", keys);
        result.put("valsize", valsize);
        result.put("sd", sd);
        result.put("updates", updates);
        result.put("loadSec", loadSec);
        result.put("updatesSec", updSec);
        result.put("streamBytes", end);
        result.put("lagEnd", lag);
        result.put("lagMax", maxLag);
        result.put("transInSection", trans);
        result.put("dNodes", d[0]);
        result.put("dBytes", d[1]);
        say(String.format(Locale.ROOT, "make done: stream %d MB; lag at the end %d MB (%.2f sd), largest %d MB (%.2f sd); "
                + "%d transactions in the section; D %d nodes, %d MB", end / 1000000, lag / 1000000,
                (double) lag / sd, maxLag / 1000000, (double) maxLag / sd, trans, d[0], d[1] / 1000000));
        long c = System.nanoTime();
        db.close();
        result.put("closeSec", (System.nanoTime() - c) / 1e9);
    }

    // ---- Start ----

    static long procReadBytes() {
        File f = new File("/proc/self/io");
        if (!f.exists()) return -1;
        try {
            for (String l : Files.readAllLines(f.toPath())) {
                if (l.startsWith("read_bytes:")) return Long.parseLong(l.substring(11).trim());
            }
        } catch (IOException e) {
            return -1;
        }
        return -1;
    }

    void start() throws Exception {
        Properties p = new Properties();
        FileInputStream fi = new FileInputStream(new File(dir, MARKER));
        try {
            p.load(fi);
        } finally {
            fi.close();
        }
        keys = Integer.parseInt(p.getProperty("keys"));
        valsize = Integer.parseInt(p.getProperty("valsize"));
        sd = Integer.parseInt(p.getProperty("sd"));
        updates = Long.parseLong(p.getProperty("updates"));
        time = Long.parseLong(p.getProperty("time")) + SEC;
        final Db db = open(false);
        final Thread main = Thread.currentThread();
        stream.watched = main;
        stream.phases = byPhase;
        final Map<String, Counts> samples = new LinkedHashMap<String, Counts>();
        final boolean[] stop = new boolean[1];
        Thread sampler = new Thread() {
            public void run() {
                while (!stop[0]) {
                    String ph = phase(main.getStackTrace());
                    synchronized (samples) {
                        Counts c = samples.get(ph);
                        if (c == null) samples.put(ph, c = new Counts());
                        c.samples++;
                    }
                    try {
                        Thread.sleep(byPhase ? 2 : 10);
                    } catch (InterruptedException e) {
                        return;
                    }
                }
            }
        };
        sampler.setDaemon(true);
        long io0 = procReadBytes();
        sampler.start();
        long a = System.nanoTime();
        StartInfo info = db.start();
        double sec = (System.nanoTime() - a) / 1e9;
        stop[0] = true;
        sampler.join();
        stream.watched = null;
        long io1 = procReadBytes();
        long section = info.lastPos - info.startPos + 1;
        long[] d = dSize(db);
        long heap = heapUsed();
        result.put("mode", "start");
        result.put("keys", keys);
        result.put("valsize", valsize);
        result.put("sd", sd);
        result.put("budget", budget);
        result.put("byPhase", byPhase);
        result.put("startupSec", sec);
        result.put("sectionBytes", section);
        result.put("transRerun", info.transCount - 1);
        result.put("streamBytes", db.internal().nodeStream().getNextPos());
        result.put("dNodes", d[0]);
        result.put("dBytes", d[1]);
        result.put("heapAfterStart", heap);
        CacheStats cs = db.internal().cacheStats();
        result.put("residentAfterStart", cs.residentBytes);
        result.put("loads", cs.loads);
        if (io0 >= 0) result.put("deviceReadBytes", io1 - io0);
        Map<String, Object> ph = new LinkedHashMap<String, Object>();
        long total;
        synchronized (samples) {
            total = 0;
            for (Counts c : samples.values()) total += c.samples;
            for (Map.Entry<String, Counts> e : samples.entrySet()) {
                stream.counts(e.getKey()).samples = e.getValue().samples;
            }
        }
        StringBuilder s = new StringBuilder();
        for (Map.Entry<String, Counts> e : stream.byPhase.entrySet()) {
            Counts c = e.getValue();
            double share = total == 0 ? 0 : (double) c.samples / total;
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            m.put("reads", c.reads);
            m.put("bytes", c.bytes);
            m.put("readSec", c.nanos / 1e9);
            m.put("timeShare", share);
            ph.put(e.getKey(), m);
            s.append(String.format(Locale.ROOT, "\n    %-36s %9d reads %9.1f MB %8.2f s in reads, %5.1f %% of the samples",
                    e.getKey(), c.reads, c.bytes / 1e6, c.nanos / 1e9, 100 * share));
        }
        result.put("phases", ph);
        say(String.format(Locale.ROOT, "start: %.2f s; section %d MB (%.2f sd), %d transactions rerun; "
                + "D %d nodes, %d MB; heap %d MB%s; by phase:%s", sec, section / 1000000, (double) section / sd,
                info.transCount - 1, d[0], d[1] / 1000000, heap / 1000000,
                io0 >= 0 ? String.format(Locale.ROOT, "; %d MB from the device", (io1 - io0) / 1000000) : "", s));
        check(db);
        db.close();
    }

    /** 2,000 random keys: each value names its key. */
    void check(Db db) {
        GetData gd = db.newGetData();
        SplittableRandom r = new SplittableRandom(3);
        for (int i = 0; i < 2000; i++) {
            int k = r.nextInt(keys);
            byte[] v = db.getOne(Long.MAX_VALUE, Keys.toSegments(key(k)), gd);
            if (v == null || v.length != valsize) throw new AssertionError("key " + k + ": " + (v == null ? "missing" : v.length + " bytes"));
            for (int j = 0; j < 4 && j < valsize; j++) {
                if (v[j] != (byte) (k >>> (24 - 8 * j))) throw new AssertionError("key " + k + ": wrong value");
            }
        }
        say("checked 2000 keys");
    }

    static String json(Object o) {
        if (o instanceof Map) {
            StringBuilder s = new StringBuilder("{");
            for (Map.Entry<?, ?> e : ((Map<?, ?>) o).entrySet()) {
                if (s.length() > 1) s.append(", ");
                s.append('"').append(e.getKey()).append("\": ").append(json(e.getValue()));
            }
            return s.append('}').toString();
        }
        if (o instanceof String) return "\"" + o + "\"";
        if (o instanceof Double) return String.format(Locale.ROOT, "%.6g", (Double) o);
        return String.valueOf(o);
    }

    public static void main(String[] args) throws Exception {
        StartupBench b = new StartupBench();
        if (b.mode.equals("make")) b.make();
        else if (b.mode.equals("start")) b.start();
        else throw new IllegalArgumentException("st.mode " + b.mode);
        System.out.println("RESULT " + json(b.result));
    }
}
