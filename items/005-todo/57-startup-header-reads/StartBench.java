package bergdb.core;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.SplittableRandom;

import bergdb.dag.GetData;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;

/**
 * Startup time of one database made by 007-05's StartupBench, for bergdb 005-57: the same
 * tool on release 2026.1's jar, the current code's and the prototype's (rule 4 by
 * position). From StartupBench's start mode, with what differs between the jars read by
 * reflection (Db.Internal.cacheStats() is newer than 2026.1; DbStarter.rule4Counts is the
 * prototype's).
 *
 * It opens the database in st.dir with the budget st.budget and times start(). The reads
 * that reach the FileStream are counted: with st.phases=1 by where they come from (a stack
 * trace a read, about 6 us), during the start by DbStarter's step and inside rerunTransactions
 * and linkD by kind (a 32-byte header read, or a node's), and after the start by source
 * (NodeCollection.idOf, a load, or other); with st.phases=0 in all, for timed runs. It
 * checks 2,000 random keys. With st.after=N it then executes N transactions of 1,000 random
 * updates, timed, with their reads (on a copy of the database: they write to it).
 *
 * Output: lines for people, and one line "RESULT {...}" for the scripts.
 *
 * Usage: java -Dst.dir=DIR [-Dst.budget=BYTES] [-Dst.phases=0|1] [-Dst.after=N]
 *            -cp bergdb.jar:classes bergdb.core.StartBench
 */
public class StartBench {
    static String prop(String n, String d) { return System.getProperty("st." + n, d); }

    static final long SEC = bergdb.pub.util.Clock.UNITS_PER_SEC;
    static final String MARKER = "startupbench.properties";
    static final int TX = 1000;

    final File dir = new File(prop("dir", "."));
    final long budget = Long.parseLong(prop("budget", "0"));
    final boolean byPhase = !prop("phases", "1").equals("0");
    final int after = Integer.parseInt(prop("after", "0"));
    int keys, valsize, sd;
    long time;

    final CoreTestClock clock = new CoreTestClock();
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

    // ---- The stream, with reads counted by where they come from ----

    /**
     * Where a read comes from. During the start: DbStarter's step, and in rerunTransactions
     * and linkD whether it reads a header (32 bytes). After it: idOf, a load, or other.
     */
    static String source(StackTraceElement[] st, boolean started, int length) {
        if (started) {
            for (int i = 1; i < st.length; i++) {
                String c = st[i].getClassName(), m = st[i].getMethodName();
                if (c.equals("bergdb.core.NodeCollection") && m.equals("idOf")) {
                    for (int j = i + 1; j < st.length; j++) {
                        if (st[j].getClassName().equals("bergdb.core.NodeCollection")) {
                            return "after.idOf." + st[j].getMethodName();
                        }
                    }
                    return "after.idOf";
                }
            }
            for (int i = 1; i < st.length; i++) {
                if (st[i].getClassName().equals("bergdb.core.NodeCollection")) return "after.load";
            }
            return "after.other";
        }
        for (int i = 1; i < st.length; i++) {
            String c = st[i].getClassName(), m = st[i].getMethodName();
            if (c.equals("bergdb.core.DbStarter") && m.equals("doOrdinaryStartup")) {
                String p = "starter." + st[i - 1].getMethodName();
                if (p.equals("starter.rerunTransactions") || p.equals("starter.linkD")) {
                    return p + (length == 32 ? ".header" : ".node");
                }
                return p;
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
        long reads, bytes, nanos;
    }

    static final class CountingStream implements AppendOnlyStream {
        final FileStream s;
        volatile boolean counting = false, started = false, phases = true;
        final Map<String, Counts> bySource = new LinkedHashMap<String, Counts>();

        CountingStream(FileStream s) { this.s = s; }

        public long getLength() { return s.getLength(); }
        public long getFirstPos() { return s.getFirstPos(); }
        public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
            long a = System.nanoTime();
            s.read(position, dest, destOffset, length);
            long e = System.nanoTime() - a;
            if (!counting) return;
            String p = phases ? source(new Throwable().getStackTrace(), started, length)
                    : started ? "after" : "start";
            synchronized (this) {
                Counts c = bySource.get(p);
                if (c == null) bySource.put(p, c = new Counts());
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

        synchronized Map<String, Object> take(String prefix) {
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            for (Map.Entry<String, Counts> e : bySource.entrySet()) {
                if (!e.getKey().startsWith(prefix)) continue;
                Map<String, Object> c = new LinkedHashMap<String, Object>();
                c.put("reads", e.getValue().reads);
                c.put("bytes", e.getValue().bytes);
                c.put("readSec", e.getValue().nanos / 1e9);
                m.put(e.getKey(), c);
            }
            return m;
        }
    }

    CountingStream stream;

    Db open() throws IOException {
        stream = new CountingStream(new FileStream(dir));
        clock.setTime(time);
        DbBuilder b = Db.builder().stream("main", stream).clock(clock).testId().retainForever()
                .maxNodeSize30();
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

    /** Db.Internal.cacheStats()'s loads and resident bytes, where there is one (not 2026.1). */
    static void cacheStats(Db db, Map<String, Object> result) {
        try {
            Method m = db.internal().getClass().getMethod("cacheStats");
            Object cs = m.invoke(db.internal());
            result.put("residentAfterStart", cs.getClass().getField("residentBytes").get(cs));
            result.put("loads", cs.getClass().getField("loads").get(cs));
        } catch (ReflectiveOperationException e) {
            // 2026.1: no CacheStats
        }
    }

    /** True for the prototype, which has DbStarter.rule4Counts. */
    static boolean DbStarterHasRule4Counts() {
        try {
            DbStarter.class.getField("rule4Counts");
            return true;
        } catch (NoSuchFieldException e) {
            return false;
        }
    }

    /** The prototype's counts of rule 4 (DbStarter.rule4Counts), where there are some. */
    static void rule4Counts(Map<String, Object> result) {
        try {
            Field f = DbStarter.class.getField("rule4Counts");
            long[] c = (long[]) f.get(null);
            if (c == null) return;
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            String[] names = {"examined", "linked", "headerReads", "checked", "differences", "linkedById"};
            for (int i = 0; i < c.length && i < names.length; i++) m.put(names[i], c[i]);
            result.put("rule4", m);
        } catch (ReflectiveOperationException e) {
            // 2026.1 and the current code: rule 4 by id, no counts
        }
    }

    void run() throws Exception {
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
        time = Long.parseLong(p.getProperty("time")) + SEC;
        final Db db = open();
        stream.phases = byPhase;
        stream.counting = true;
        long io0 = procReadBytes();
        long a = System.nanoTime();
        StartInfo info = db.start();
        double sec = (System.nanoTime() - a) / 1e9;
        long io1 = procReadBytes();
        stream.started = true;
        long section = info.lastPos - info.startPos + 1;
        long[] d = dSize(db);
        result.put("version", BuildInfo.BUILD + (DbStarterHasRule4Counts() ? " (rule 4 by position)" : ""));
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
        cacheStats(db, result);
        rule4Counts(result);
        if (io0 >= 0) result.put("deviceReadBytes", io1 - io0);
        Map<String, Object> startReads = stream.take("");
        result.put("startReads", startReads);
        long reads = 0;
        for (Object o : startReads.values()) reads += (Long) ((Map<?, ?>) o).get("reads");
        say(String.format(Locale.ROOT, "start: %.2f s; section %d MB (%.2f sd), %d transactions rerun; "
                + "D %d nodes, %d MB; %d reads%s; %s", sec, section / 1000000, (double) section / sd,
                info.transCount - 1, d[0], d[1] / 1000000, reads,
                io0 >= 0 ? String.format(Locale.ROOT, ", %d MB from the device", (io1 - io0) / 1000000) : "",
                result.get("version")));
        check(db);
        if (after > 0) after(db);
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

    /** 'after' transactions of 1,000 random updates, timed, with their reads by source. */
    void after(Db db) {
        synchronized (stream) {
            stream.bySource.clear();
        }
        SplittableRandom ur = new SplittableRandom(4);
        long a = System.nanoTime();
        long half = 0;
        for (int t = 0; t < after; t++) {
            Trans.Builder tb = db.trans();
            for (int j = 0; j < TX; j++) {
                int k = ur.nextInt(keys);
                tb.put(key(k), value(k, 2));
            }
            time += SEC / 10000;
            clock.setTime(time);
            db.execute(tb.build());
            if (t + 1 == after / 2) half = System.nanoTime();
        }
        db.sync(SyncLevel.STRONG);
        double sec = (System.nanoTime() - a) / 1e9;
        result.put("afterTrans", after);
        result.put("afterSec", sec);
        result.put("afterFirstHalfSec", (half - a) / 1e9);
        result.put("afterReads", stream.take("after"));
        say(String.format(Locale.ROOT, "after: %d transactions of %d updates in %.2f s (first half %.2f s); reads %s",
                after, TX, sec, (half - a) / 1e9, result.get("afterReads")));
        check(db);
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
        StartBench b = new StartBench();
        b.run();
        System.out.println("RESULT " + json(b.result));
    }
}
