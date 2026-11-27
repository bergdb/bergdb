package bergdb.core;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;
import java.util.*;

import bergdb.dag.Keys;

/**
 * Records the Core transactions of an application's run, for a replay through TraceExport
 * (workload=F) and the checkers of the Lean model (bergdb 030-31). Written 2026-11-20.
 *
 * Usage: java -cp bergdb.jar:stress:APP_CLASSES bergdb.core.AppRecord OUT_PREFIX AppClass args...
 *
 * Runs AppClass.main(args) in this JVM with Db's test hooks set (Db.TestHooks), and writes one
 * file per database that the application wrote, OUT_PREFIX-K.rec, K = 1, 2, ... in the order
 * of their first transaction. A database is known by its file stream's directory, so its
 * restarts (a new Db of the same database) are in its file, at the place they came. A file has, per committed
 * user transaction, in commit order: its time, its record's position and a hash of the
 * record's bytes, and its operations as the Dag got them (Db.TestHooks.kvApplied: the keys
 * and values after their transformations, a delete with no value); before a transaction, the
 * startup distance and reclaim's settings when they change, and RESTART when the database was
 * started again; and MAINTAIN before a transaction, when the application's calls of
 * Db.maintain() wrote records (their internal transactions, known by Reclaim.maintain on the
 * stack). Reclaim's internal transactions, and the records of the settings' calls (KVs at the
 * Core's own keys, Trans.coreKey), are counted only: the replay's reclaim makes its own, its
 * maintain() calls theirs, and the replay calls the settings from the SET lines. A refused
 * transaction never reaches the hooks.
 *
 * Why a recording and a replay, not a trace of the run itself: the trace's recorder reads run
 * A's database in memory after every record (TraceExport), which needs a memory stream, no
 * eviction and one thread; an application's run has file streams, a cache budget, threads,
 * restarts. The Core transactions and their times are what the writer gets, and the writer is
 * a function of them and the node size (PE; 030-04, 3.5, the writer's repeatability), so the
 * replay's writer makes the decisions that the application's made; the replay compares its
 * records with the application's (the time, and the bytes when the position is the same) and
 * says how many are the same. Eviction, restarts and the file stream do not change the records
 * (TraceExport's runs B and E check that). The threads are not replayed, only the order of
 * the commits; maintain() is called where the application's calls wrote records, until the
 * replay's calls have written as many (a call is not seen when it wrote nothing).
 *
 * The format, one line each:
 *   APPRECORD 1 app args...
 *   NODESIZE m
 *   SET sd retain fraction     the startup distance, the retain duration (units; -1 for
 *                              none) and the internal fraction, before the next TX
 *   RESTART                    the database was started again before the next TX
 *   MAINTAIN n tt              before the next TX (or RESTART), maintain() calls wrote n
 *                              records, the first at time tt
 *   TX tt tpos hash k          a user transaction of k operations, then k lines:
 *   P n s1 .. sn hex           a put of the key of n segments, the value in hex
 *   D n s1 .. sn               a delete
 *   INTERNAL c                 at the end: reclaim's and the Core's internal records
 */
public final class AppRecord {
    private AppRecord() {}

    /** One database's recording. */
    static final class Out {
        final PrintWriter w;
        Db db;                  // the Db of its last transaction
        String settings = "";
        int txs, internal, restarts;
        /** maintain()'s records since the last line, and the first one's time. */
        int maintain;
        long maintainTt;
        void flushMaintain() {
            if (maintain > 0) w.println("MAINTAIN " + maintain + " " + maintainTt);
            maintain = 0;
        }
        Out(String file) throws IOException {
            w = new PrintWriter(new OutputStreamWriter(new FileOutputStream(file), StandardCharsets.UTF_8));
        }
    }

    static final Map<String, Out> outs = new LinkedHashMap<String, Out>();
    static String prefix;
    static String header;
    static final ThreadLocal<List<Object[]>> ops = ThreadLocal.withInitial(ArrayList::new);
    static Field outer, storage;

    static Db dbOf(Db.ExecuteData x) throws ReflectiveOperationException {
        if (outer == null) {
            outer = Db.ExecuteData.class.getDeclaredField("this$0");
            outer.setAccessible(true);
            storage = Db.class.getDeclaredField("storageManager");
            storage.setAccessible(true);
        }
        return (Db) outer.get(x);
    }

    /** The database's name: its file stream's directory (a start has a new Db and a new
     *  database ID, the directory stays), else the Db's identity. */
    static String nameOf(Db db) throws ReflectiveOperationException {
        Object s = ((bergdb.storage.StorageManager) storage.get(db)).getMainStream();
        for (int depth = 0; depth < 4 && s != null; depth++) {
            if (s instanceof bergdb.stream.FileStream) {
                return ((bergdb.stream.FileStream) s).getDir().getAbsolutePath();
            }
            Object inner = null;
            for (Field f : s.getClass().getDeclaredFields()) {
                if (bergdb.stream.AppendOnlyStream.class.isAssignableFrom(f.getType())) {
                    f.setAccessible(true);
                    inner = f.get(s);
                    break;
                }
            }
            s = inner;
        }
        return "db@" + System.identityHashCode(db);
    }

    static synchronized void executed(Db.ExecuteData x) throws Exception {
        List<Object[]> kvs = ops.get();
        List<Object[]> mine = new ArrayList<Object[]>(kvs);
        kvs.clear();
        Db db = dbOf(x);
        String key = nameOf(db);
        Out o = outs.get(key);
        if (o == null) {
            o = new Out(prefix + "-" + (outs.size() + 1) + ".rec");
            outs.put(key, o);
            o.w.println(header);
            o.w.println("NODESIZE " + db.internal().maxNodeSize());
        } else if (o.db != db) {
            o.flushMaintain();
            o.w.println("RESTART");
            o.restarts++;
        }
        o.db = db;
        Trans t = x.trans;
        // The Core's own KVs (Trans.coreKey: the startup distance's and reclaim's) come from
        // the settings' calls, which the replay makes from the SET lines.
        boolean core = !mine.isEmpty();
        for (Object[] kv : mine) core &= Trans.coreKey((long[]) kv[0]);
        if (t.isInternal() || core) {
            o.internal++;
            if (t.isInternal() && fromMaintain()) {
                if (o.maintain++ == 0) o.maintainTt = t.tt;
            }
            return;
        }
        o.flushMaintain();
        long retain = db.getRetainDuration();
        String settings = "SET " + db.getStartupDistance() + " " + (retain == Long.MAX_VALUE ? -1 : retain)
                + " " + db.getInternalFraction();
        if (!settings.equals(o.settings)) {
            o.w.println(settings);
            o.settings = settings;
        }
        byte[] bytes = db.internal().nodeStream().readTransBytes(t.tpos);
        o.w.println("TX " + t.tt + " " + t.tpos + " " + TraceExport.hash(bytes) + " " + mine.size());
        StringBuilder b = new StringBuilder();
        for (Object[] kv : mine) {
            long[] k = (long[]) kv[0];
            byte[] v = (byte[]) kv[1];
            b.setLength(0);
            b.append(v == null ? "D " : "P ").append(k.length);
            for (long s : k) b.append(' ').append(s);
            if (v != null) {
                b.append(' ');
                if (v.length == 0) b.append('-');
                for (byte c : v) b.append(Character.forDigit((c >> 4) & 15, 16)).append(Character.forDigit(c & 15, 16));
            }
            o.w.println(b);
        }
        o.txs++;
    }

    /** Whether the transaction being executed is one of a maintain() call's. */
    static boolean fromMaintain() {
        for (StackTraceElement e : Thread.currentThread().getStackTrace()) {
            if (e.getMethodName().equals("maintain") && e.getClassName().equals(Reclaim.class.getName())) {
                return true;
            }
        }
        return false;
    }

    static synchronized void finish() {
        for (Out o : outs.values()) {
            o.w.println("INTERNAL " + o.internal);
            o.w.close();
        }
        StringBuilder b = new StringBuilder("AppRecord: " + outs.size() + " databases");
        int k = 1;
        for (Out o : outs.values()) {
            b.append("; ").append(prefix).append("-").append(k++).append(".rec: ").append(o.txs)
                    .append(" user transactions, ").append(o.restarts).append(" restarts");
        }
        System.err.println(b);
        outs.clear();
    }

    public static void main(String[] args) throws Throwable {
        if (args.length < 2) {
            System.out.println("Usage: AppRecord OUT_PREFIX AppClass args...");
            System.exit(2);
        }
        prefix = args[0];
        header = "APPRECORD 1 " + String.join(" ", Arrays.copyOfRange(args, 1, args.length));
        Db.testHooks = new Db.TestHooks() {
            public void transExecuted(Db.ExecuteData x) {
                try {
                    executed(x);
                } catch (Exception e) {
                    throw new RuntimeException("AppRecord: " + e, e);
                }
            }
            public void kvApplied(long[] key, byte[] value) {
                ops.get().add(new Object[] {key.clone(), value == null ? null : value.clone()});
            }
            public void valueNodeCreated(bergdb.dag.ValueNode node, long[] key) {}
            public void nodeTouched(bergdb.dag.Node node) {}
            public void nodeReplaced(bergdb.dag.Node node) {}
        };
        // The application may end with System.exit: the files are closed by the hook.
        Runtime.getRuntime().addShutdownHook(new Thread(AppRecord::finish));
        Method m = Class.forName(args[1]).getMethod("main", String[].class);
        m.invoke(null, (Object) Arrays.copyOfRange(args, 2, args.length));
    }

    // ======== The replay's side: a recording read (TraceExport, workload=F) ========

    /** A user transaction of a recording. */
    static final class Tx {
        long tt, tpos, hash;
        long[][] keys;
        byte[][] values;        // null: a delete
    }

    /** A recording, read for TraceExport. */
    static final class Workload {
        String name;
        int nodeSize;
        final List<Tx> txs = new ArrayList<Tx>();
        /** The settings in force at user transaction i, where they change: sd, retain, fraction. */
        final TreeMap<Integer, String[]> settings = new TreeMap<Integer, String[]>();
        final Set<Integer> restarts = new HashSet<Integer>();
        /** Before user transaction i: maintain()'s records in the application, and the time
         *  of the first. */
        final Map<Integer, long[]> maintain = new HashMap<Integer, long[]>();
        int sameTime, sameRecord, kvs, maintainRecords, replayedMaintain;

        static Workload read(String file) throws IOException {
            Workload w = new Workload();
            String base = file.substring(file.lastIndexOf('/') + 1);
            w.name = base.endsWith(".rec") ? base.substring(0, base.length() - 4) : base;
            BufferedReader r = new BufferedReader(new InputStreamReader(new FileInputStream(file),
                    StandardCharsets.UTF_8));
            String line;
            Tx tx = null;
            int left = 0;
            while ((line = r.readLine()) != null) {
                String[] p = line.split(" ");
                if (left > 0) {
                    int n = Integer.parseInt(p[1]);
                    long[] k = new long[n];
                    for (int j = 0; j < n; j++) k[j] = Long.parseLong(p[2 + j]);
                    int j = tx.keys.length - left;
                    tx.keys[j] = k;
                    if (p[0].equals("P")) {
                        String h = p[2 + n];
                        byte[] v = new byte[h.equals("-") ? 0 : h.length() / 2];
                        for (int i = 0; i < v.length; i++) {
                            v[i] = (byte) Integer.parseInt(h.substring(2 * i, 2 * i + 2), 16);
                        }
                        tx.values[j] = v;
                    } else if (!p[0].equals("D")) {
                        throw new IOException("bad operation line: " + line);
                    }
                    left--;
                    continue;
                }
                switch (p[0]) {
                case "APPRECORD":
                case "INTERNAL":
                    break;
                case "NODESIZE":
                    w.nodeSize = Integer.parseInt(p[1]);
                    break;
                case "SET":
                    w.settings.put(w.txs.size(), new String[] {p[1], p[2], p[3]});
                    break;
                case "RESTART":
                    if (!w.txs.isEmpty()) w.restarts.add(w.txs.size());
                    break;
                case "MAINTAIN": {
                    long[] m = w.maintain.get(w.txs.size());
                    long n = Long.parseLong(p[1]);
                    w.maintain.put(w.txs.size(), m == null ? new long[] {n, Long.parseLong(p[2])}
                            : new long[] {m[0] + n, m[1]});
                    break;
                }
                case "TX":
                    tx = new Tx();
                    tx.tt = Long.parseLong(p[1]);
                    tx.tpos = Long.parseLong(p[2]);
                    tx.hash = Long.parseLong(p[3]);
                    left = Integer.parseInt(p[4]);
                    tx.keys = new long[left][];
                    tx.values = new byte[left][];
                    w.kvs += left;
                    w.txs.add(tx);
                    break;
                default:
                    throw new IOException("bad line: " + line);
                }
            }
            r.close();
            if (left > 0) throw new IOException("the last transaction is cut short");
            // apptx=N: the first N user transactions only, a history of their own.
            int max = Integer.getInteger("apptx", Integer.MAX_VALUE);
            while (w.txs.size() > max) w.kvs -= w.txs.remove(w.txs.size() - 1).keys.length;
            for (Map.Entry<Integer, long[]> e : w.maintain.entrySet()) {
                if (e.getKey() < w.txs.size()) w.maintainRecords += e.getValue()[0];
            }
            return w;
        }

        /** The properties that TraceExport's fields read: n, maxnode, sd and reclaim's. */
        void setProperties() {
            String[] s = settings.isEmpty() ? new String[] {"" + Db.DEFAULT_STARTUP_DISTANCE, "-1", "0.25"}
                    : settings.firstEntry().getValue();
            System.setProperty("n", "" + txs.size());
            System.setProperty("maxnode", "" + nodeSize);
            System.setProperty("sd", s[0]);
            boolean reclaim = false;
            for (String[] x : settings.values()) reclaim |= !x[1].equals("-1");
            if (reclaim) {
                System.setProperty("retain", "1");
                System.setProperty("retainunits", s[1].equals("-1") ? "" + Long.MAX_VALUE : s[1]);
            }
            System.setProperty("fraction", s[2]);
        }

        /** Before user transaction i (i > 0): the settings that changed, as the application
         *  set them. */
        void settingsBefore(int i, Db db, CoreTestClock clock, long tt) {
            if (i == 0 || !settings.containsKey(i)) return;
            String[] s = settings.get(i);
            db.setStartupDistance(Integer.parseInt(s[0]));
            db.setRetainDuration(s[1].equals("-1") ? Long.MAX_VALUE : Long.parseLong(s[1]));
            db.setReclaimInternalFraction(Double.parseDouble(s[2]));
        }

        /** apprestarts=0: the replay without the application's restarts (bergdb 030-31: for
         *  the contract's checkers, whose grammar has no RESTART line). */
        final boolean replayRestarts = !"0".equals(System.getProperty("apprestarts"));

        boolean restartBefore(int i) {
            return replayRestarts && restarts.contains(i);
        }

        /** Before user transaction i: the application's maintain() calls, as calls of the
         *  replay's until they have written as many records (at most 100 calls, and none
         *  after a call that says nothing more is due). recs: the records so far. */
        void maintainBefore(int i, Db db, CoreTestClock clock, List<?> recs) {
            long[] m = maintain.get(i);
            if (m == null) return;
            clock.setTime(m[1]);
            int before = recs.size();
            for (int calls = 0; recs.size() - before < m[0] && calls < 100; calls++) {
                long length = db.getStreamLength();
                db.maintain(Reclaim.MAINTAIN_MIN_BUDGET);       // bergdb 031-04
                if (db.getStreamLength() == length) break;
            }
            replayedMaintain += recs.size() - before;
        }

        /** The replay's record of user transaction i against the application's. */
        void compare(int i, TraceExport.Rec rec, Db db) {
            Tx tx = txs.get(i);
            if (rec.tt == tx.tt) sameTime++;
            if (rec.tpos == tx.tpos
                    && TraceExport.hash(db.internal().nodeStream().readTransBytes(rec.tpos)) == tx.hash) {
                sameRecord++;
            }
        }

        String summary() {
            return "workload " + name + ": " + txs.size() + " user transactions, " + kvs + " operations, "
                    + restarts.size() + " restarts" + (replayRestarts ? "" : " (not replayed)")
                    + "; maintain()'s records: the application's " + maintainRecords + ", the replay's "
                    + replayedMaintain
                    + "; the application's time " + sameTime + " of "
                    + txs.size() + ", its record's bytes at its position " + sameRecord + " of " + txs.size();
        }
    }
}
