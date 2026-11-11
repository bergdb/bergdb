package bergdb.pubimp;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Duration;
import bergdb.pub.DbObject;
import bergdb.pub.Factory;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.Kv;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.Time;
import bergdb.pub.Transaction;
import bergdb.pub.TransactionInfo;
import bergdb.pub.UseIndexBuilder;
import bergdb.pub.WBuilder;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.IndexBuildException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pubimp.IndexReference.Bin;
import bergdb.pubimp.IndexReference.Call;
import bergdb.pubimp.IndexReference.Def;
import bergdb.pubimp.IndexReference.Entry;
import bergdb.pubimp.IndexReference.Level;
import bergdb.pubimp.IndexReference.Model;
import bergdb.pubimp.IndexReference.Query;
import bergdb.pubimp.IndexReference.Type;
import bergdb.pubimp.IndexReference.Write;

/**
 * The kill-and-restart harness of the Pub layer (bergdb 020-15): objects and user indexes
 * under a real kill of the process, SIGKILL, with the restart in a new JVM.
 *
 * <p>The parent starts a child JVM on a database directory, kills it at a random moment with
 * Process.destroyForcibly() (SIGKILL), and starts the next child on the same directory, many
 * times; every PER_DB kills it begins a new database. Each child (a run) opens the directory
 * (DatabaseBuilder.create()), checks the database against a journal of what the earlier runs
 * did, and then runs a random schedule until it is killed: writer threads (1 to 4) put and
 * delete objects (DbObjects and Data Objects, format 2), Strings and byte[]s at object keys
 * and at keys with a suffix, in w() and rw(), and now and then sync; an index thread creates
 * indexes (IndexBuilder ... start(), with join() or not), deletes them, joins their builds,
 * syncs, and checks the indexes and the data at a lookup time when every transaction up to
 * it is known. The kills land in each phase: during the start, during the checks while the
 * start's resumed builds and cleanups run, during the waits for the builds and cleanups,
 * during the schedule, and in it right after a creation or a deletion. So that a build or a
 * cleanup lasts long enough to be killed in, a run takes now and then build steps of 2 to 9
 * values (IndexManager.testStepValues), a sleep of 1 to 8 ms in each build step and one of 5
 * to 30 ms in each cleanup step (its test hook): a cleanup that ends within the buffer time
 * of its deletion is never seen by a start. Each database has its settings (Settings), the
 * same in all its runs: reclaim on (a retain duration of 20 s) or not, a startup distance of
 * 5 MB (bounded startup) or the default, a cache of 4 MB (eviction) or the default.</p>
 *
 * <p><b>The journal</b>, a file beside the directory, written by the children line by line
 * (each line one write() to the OS, which a kill of the process keeps; a line not ended by
 * "$" is torn and ignored): a transaction's start (T), its commit with its time (C), a sync
 * that returned (S, IS), an index operation (I) and its result with the time interval
 * around it (IR), a join that returned ACTIVE (IJ). A transaction's writes are not in the
 * journal: they are made again from the seed, the run, the thread and the sequence number.
 * Each transaction also writes a stamp, its ID at /x/sTHREAD.txt, so that the database tells
 * which transaction of a thread was its last.</p>
 *
 * <p><b>The promises checked</b> (docs/levels.md, sections 3 and 8; Database's Javadoc on
 * errors, stop() and sync(); bergdb 020-10, sections 3.2, 4 to 6):</p>
 * <ol>
 * <li>The start after a kill succeeds (a DatabaseNotCreatedException only before any start
 *     succeeded, as DatabaseBuilder.start() allows; the files are then removed as it says).</li>
 * <li>The state is a prefix: with T the latest time when the first start after the kill had
 *     started its Db, before the index manager did anything (DatabaseImp.testHookAfterStart,
 *     which writes T in the journal; later starts killed before their schedule change no
 *     data, but their resumed builds and cleanups commit transactions), every transaction of
 *     the killed run committed at or before T is there and none after it; the transaction in
 *     flight in each thread is there whole or not at all (its stamp, and its KVs by
 *     transactionInfo()); each index operation whose interval ends at or before T is there,
 *     none that started at or after T, and each name's definition is the result of a prefix
 *     of the run's operations on it.</li>
 * <li>Durability: every transaction that a sync returned for, and every one committed
 *     before a Database.sync() that returned, is there: user transactions, index creations
 *     and deletions, and the activations that a join saw before the sync. After a close()
 *     that returned (a run aimed at the phase "close" closes the database while its writers
 *     write, then waits for its kill), every transaction and index operation that returned
 *     is there (Database.close()); so too after a stop() and a return from main, when the
 *     JVM ended by itself with status 0 (a run aimed at "exit"; Database.stop()).</li>
 * <li>The data at T is the model's: each key's value, byte for byte, and each directory's
 *     primary listing (no key more, none less).</li>
 * <li>The indexes at T (020-10, sections 4 and 6): the definitions are the model's (the
 *     name, the generation, the directory and the levels; known active stays active); an
 *     active index's entries are exactly f over the data (IndexReference: an index is a
 *     function of the data at a lookup time), a building one's a part of them; every marker
 *     names a deleted generation; no entry of a generation that is neither live nor marked
 *     (no orphan); each job is ACTIVE with count 0 for an index active at the start, BUILDING
 *     or ACTIVE for one building, never FAILED; a free name has no job.</li>
 * <li>Then, in some runs and in the last run of each database: every build resumed by the
 *     start ends ACTIVE, every cleanup ends (its marker and its entries gone), and every
 *     index gives exactly the reference's scans (IndexHarness.queries) and entries.</li>
 * <li>During the schedule: index creations and deletions answer as the names in use say;
 *     joins end ACTIVE; at a lookup time with every transaction up to it known, each index
 *     is active or building as known, gives the reference's entries and scans, a free name
 *     has no index, a directory's listing is the model's, and no entry is an orphan.</li>
 * </ol>
 *
 * <p>A child that finds a fault prints "FAIL" and the reason and exits with status 3; the
 * parent then stops, prints the child's output and keeps the directory and its journal.
 * The parent's seed gives the databases' seeds and the kill plans; the kill times are not
 * reproducible, so the failure's directory and journal are what to study.</p>
 *
 * <p>Usage: java -cp bergdb.jar bergdb.pubimp.KillRestartHarness parent BASE SEED KILLS
 * [PER_DB [SECONDS]]: KILLS kills from SEED, a new database every PER_DB kills (default 40),
 * at most SECONDS seconds (default no limit), in directories under BASE (removed when their
 * database passed). Prints KILL RESTART OK and the counts at the end, or KILL RESTART FAILED.
 * The script java/stress/kill-restart.sh runs it. For a probe of one phase, the parent's
 * system properties killrestart.phase (a name of PHASES) and killrestart.delay (the longest
 * delay, ms; default 100) aim every second kill there.</p>
 *
 * @author Frans Lundberg
 */
public final class KillRestartHarness {
    private KillRestartHarness() {}

    // ======== The workload ========

    /** The directories of the data: H2's two (the second inside the first), one of Data Objects. */
    static final String[] DIRS = {"/h/a/", "/h/a/sub/", "/h/d/"};

    /** The directory of the stamps: /x/sTHREAD.txt, the ID of each writer's last transaction. */
    static final String STAMPS = "/x/";

    /** The cold names c0 to c999 of each directory, beside H2's sixteen hot names. */
    static final int COLD_NAMES = 1000;

    /** The paths of the levels of an index of /h/d/: Item's fields; "e", a boolean, gives none. */
    static final String[][] ITEM_PATHS = {{"a"}, {"b"}, {"c"}, {"d"}, {"n", "a"}, {"n", "c"},
            {"e"}};

    static final String[] INDEX_NAMES = IndexHarness.INDEX_NAMES;

    /**
     * A fault planted in a child, for the self-check (selfcheck), by the system property
     * killrestart.plant; none in a real run: "halfwrite", a transaction of three writes or
     * more without its first one now and then; "nosync", the syncs not made; "orphan", an
     * entry of a generation that does not exist; "stale", an entry of a live generation for
     * a key that has no value.
     */
    static final String PLANT = System.getProperty("killrestart.plant", "");

    /** The wait for a build or a cleanup to end, ms. */
    static final int JOB_WAIT = 120000;

    /** A Data Object (bergdb 020-09) with a field of each kind that an index takes. */
    public static final class Item {
        public Long a;
        public Double b;
        public String c;
        public byte[] d;
        public Inner n;
        public Boolean e;
    }

    /** Item's nested Data Object. */
    public static final class Inner {
        public Long a;
        public String c;
    }

    /** An Item as the model's value: a map of its fields that are not null. */
    static TreeMap<String, Object> model(Item it) {
        TreeMap<String, Object> o = new TreeMap<String, Object>();
        if (it.a != null) {
            o.put("a", it.a);
        }
        if (it.b != null) {
            o.put("b", it.b);
        }
        if (it.c != null) {
            o.put("c", it.c);
        }
        if (it.d != null) {
            o.put("d", new Bin(it.d));
        }
        if (it.n != null) {
            TreeMap<String, Object> n = new TreeMap<String, Object>();
            if (it.n.a != null) {
                n.put("a", it.n.a);
            }
            if (it.n.c != null) {
                n.put("c", it.n.c);
            }
            o.put("n", n);
        }
        if (it.e != null) {
            o.put("e", it.e);
        }
        return o;
    }

    /**
     * The longest string in a value of this harness, in chars (bergdb 024-24, section 9). A
     * longer one, one of IndexHarness.LONG_STRINGS (ASCII), is cut to its first MAX_STRING
     * chars, at most 37 bytes as a level (18 00s, each written as two, and the final 00);
     * every other string and byte[] of IndexHarness takes at most 17. So the levels of each
     * definition (def(): at most 3 levels) take at most 111 bytes, and no put is refused
     * for L6 (bergdb 024-17): this harness checks kills and restarts, and a refused put
     * would leave a transaction begun in the journal (T) that never commits. IndexHarness
     * and IndexDefinitionTester check L6.
     */
    static final int MAX_STRING = 18;

    /** v with each string longer than MAX_STRING cut to it, in objects and arrays too. */
    static Object cut(Object v) {
        if (v instanceof String) {
            String s = (String) v;
            return s.length() <= MAX_STRING ? s : s.substring(0, MAX_STRING);
        } else if (v instanceof Map) {
            TreeMap<String, Object> o = new TreeMap<String, Object>();
            for (Map.Entry<?, ?> e : ((Map<?, ?>) v).entrySet()) {
                o.put((String) e.getKey(), cut(e.getValue()));
            }
            return o;
        } else if (v instanceof List) {
            List<Object> a = new ArrayList<Object>();
            for (Object x : (List<?>) v) {
                a.add(cut(x));
            }
            return a;
        }
        return v;
    }

    static String cut(String s) {
        return (String) cut((Object) s);
    }

    /**
     * No write of tx() is refused for L6 (MAX_STRING): over 2,000 transactions, every value
     * put has levels within 111 bytes for each of 100 definitions of def(), and a string cut
     * to MAX_STRING was seen. The night run of 2026-11-11 found a put refused for L6 in the
     * child (bergdb 024-24, section 9).
     */
    @Nano
    public static void testWithinL6() {
        IndexReference ref = new IndexReference();
        Random r = new Random(20261111);
        List<Def> defs = new ArrayList<Def>();
        for (int i = 0; i < 100; i++) {
            defs.add(def("i" + i, r));
        }
        int cut = 0;
        for (int seq = 1; seq <= 2000; seq++) {
            for (Write w : tx(20261111, 1, seq % 4, seq).writes) {
                if (w.value == null) {
                    continue;
                }
                cut += String.valueOf(w.value).contains(IndexReference.repeat("a", MAX_STRING))
                        ? 1 : 0;
                for (Def d : defs) {
                    Assert.assertTrue(w.key + " " + IndexReference.show(w.value) + ", "
                            + d.levels.size() + " levels", !ref.tooLong(d, w.key, w.value));
                }
            }
        }
        Assert.assertTrue("cut " + cut, cut > 0);
    }

    static Item item(Random r) {
        Item it = new Item();
        if (r.nextInt(5) != 0) {
            it.a = IndexHarness.longValue(r);
        }
        if (r.nextInt(5) != 0) {
            it.b = IndexHarness.doubleValue(r);
        }
        if (r.nextInt(5) != 0) {
            it.c = cut(IndexHarness.stringValue(r));
        }
        if (r.nextInt(5) != 0) {
            it.d = IndexHarness.bytesValue(r).bytes();
        }
        if (r.nextBoolean()) {
            it.n = new Inner();
            if (r.nextInt(5) != 0) {
                it.n.a = IndexHarness.longValue(r);
            }
            if (r.nextInt(5) != 0) {
                it.n.c = cut(IndexHarness.stringValue(r));
            }
        }
        if (r.nextInt(5) == 0) {
            it.e = r.nextBoolean();
        }
        return it;
    }

    /** A seed made of several numbers. */
    static long mix(long... xs) {
        long h = 0x9E3779B97F4A7C15L;
        for (long x : xs) {
            h ^= x;
            h *= 0xBF58476D1CE4E5B9L;
            h ^= h >>> 31;
            h *= 0x94D049BB133111EBL;
            h ^= h >>> 29;
        }
        return h;
    }

    /** A key: a directory, then a hot name (H2's), a cold one, or one with a suffix. */
    static String key(Random r) {
        int k = r.nextInt(100);
        String dir = k < 45 ? DIRS[0] : k < 60 ? DIRS[1] : DIRS[2];
        int n = r.nextInt(100);
        if (n < 8) {
            return dir + IndexHarness.OTHER_NAMES[r.nextInt(IndexHarness.OTHER_NAMES.length)];
        } else if (n < 65) {
            return dir + IndexHarness.OBJECT_NAMES[r.nextInt(IndexHarness.OBJECT_NAMES.length)];
        }
        return dir + "c" + r.nextInt(COLD_NAMES);
    }

    static String stampKey(int thread) {
        return STAMPS + "s" + thread + ".txt";
    }

    /** A user transaction: its writes (the model's values) and the values given to the puts. */
    static final class Tx {
        final int run;
        final int thread;
        final int seq;
        boolean rw;
        final List<Write> writes = new ArrayList<Write>();
        final List<Object> values = new ArrayList<Object>();
        /** In rw(), a key the action reads first, or null. */
        String readKey;
        /** The sync after the commit: 0 none, 1 Transaction's, 2 Connection's, 3 Database's. */
        int sync;

        Tx(int run, int thread, int seq) {
            this.run = run;
            this.thread = thread;
            this.seq = seq;
        }

        String id() {
            return run + "." + thread + "." + seq;
        }

        void add(String key, Object model, Object value) {
            writes.add(new Write(key, model));
            values.add(value);
        }

        public String toString() {
            return id() + (rw ? " rw " : " w ") + writes;
        }
    }

    /**
     * The transaction seq of the thread in the run, made from the seed alone: 1 to 4 puts or
     * deletes, at /h/d/ half the objects Data Objects (Item); then the thread's stamp.
     */
    static Tx tx(long seed, int run, int thread, int seq) {
        Random r = new Random(mix(seed, run, thread, seq));
        Tx tx = new Tx(run, thread, seq);
        tx.rw = r.nextBoolean();
        for (int i = 1 + r.nextInt(4); i > 0; i--) {
            String key = key(r);
            if (r.nextInt(5) == 0) {
                tx.add(key, null, null);
            } else if (key.startsWith(DIRS[2]) && IndexReference.isObjectKey(key)
                    && r.nextBoolean()) {
                Item it = item(r);
                tx.add(key, model(it), it);
            } else {
                Object v = cut(IndexHarness.keyValue(key, r));
                tx.add(key, v, IndexHarness.javaValue(v));
            }
        }
        if (tx.rw && r.nextBoolean()) {
            tx.readKey = key(r);
        }
        int s = r.nextInt(60);
        tx.sync = s < 3 ? s + 1 : 0;
        tx.add(stampKey(thread), tx.id(), tx.id());
        return tx;
    }

    static Transaction execute(Connection c, final Tx tx) {
        if (tx.rw) {
            return c.rw(env -> {
                if (tx.readKey != null) {
                    env.get(tx.readKey, byte[].class);
                }
                for (int i = 0; i < tx.writes.size(); i++) {
                    Write w = tx.writes.get(i);
                    if (w.value == null) {
                        env.delete(w.key);
                    } else {
                        env.put(w.key, tx.values.get(i));
                    }
                }
            });
        }
        WBuilder b = c.w();
        for (int i = 0; i < tx.writes.size(); i++) {
            Write w = tx.writes.get(i);
            if (w.value == null) {
                b.delete(w.key);
            } else {
                b.put(w.key, tx.values.get(i));
            }
        }
        return b.execute();
    }

    /** An index's definition: 1 to 3 levels, mostly of the type that the field prefers. */
    static Def def(String name, Random r) {
        int k = r.nextInt(10);
        String dir = k < 5 ? DIRS[0] : k < 7 ? DIRS[1] : DIRS[2];
        List<Level> levels = new ArrayList<Level>();
        for (int i = 1 + r.nextInt(3); i > 0; i--) {
            String[] path;
            if (dir.equals(DIRS[2]) && r.nextInt(3) != 0) {
                path = ITEM_PATHS[r.nextInt(ITEM_PATHS.length)];
            } else {
                path = r.nextInt(100) < 85 ? IndexHarness.PATHS[r.nextInt(9)]
                        : IndexHarness.PATHS[9 + r.nextInt(2)];
            }
            Type type = r.nextInt(4) != 0 ? IndexHarness.preferred(path[path.length - 1])
                    : Type.values()[r.nextInt(4)];
            levels.add(new Level(type, call(path, r), path));
        }
        return new Def(name, dir, levels);
    }

    private static Call call(String[] path, Random r) {
        boolean dotted = false;
        for (String part : path) {
            dotted |= part.indexOf('.') >= 0;
        }
        int k = r.nextInt(10);
        if (path.length == 1) {
            return k < 7 ? Call.FIELD : !dotted && k < 9 ? Call.NESTED_STRING : Call.NESTED_ARRAY;
        }
        return dotted || k < 4 ? Call.NESTED_ARRAY : Call.NESTED_STRING;
    }

    /** A definition as the journal's text: the directory, then each level's type, call, path. */
    static String defText(Def d) {
        StringBuilder s = new StringBuilder(d.dir);
        for (Level l : d.levels) {
            s.append(';').append(l.type.string).append(':').append(l.call.name()).append(':')
                    .append(String.join("|", l.path));
        }
        return s.toString();
    }

    static Def parseDef(String name, String text) {
        String[] parts = text.split(";");
        List<Level> levels = new ArrayList<Level>();
        for (int i = 1; i < parts.length; i++) {
            String[] f = parts[i].split(":", 3);
            Type type = null;
            for (Type t : Type.values()) {
                if (t.string.equals(f[0])) {
                    type = t;
                }
            }
            levels.add(new Level(type, Call.valueOf(f[1]), f[2].split("\\|", -1)));
        }
        return new Def(name, parts[0], levels);
    }

    static Job start(Database db, Def def) {
        IndexBuilder b = db.indexBuilder(def.name).dir(def.dir);
        for (Level l : def.levels) {
            b.type(l.type.string);
            switch (l.call) {
            case FIELD:
                b.field(l.path[0]);
                break;
            case NESTED_STRING:
                b.nestedField(String.join(".", l.path));
                break;
            default:
                b.nestedField(l.path.clone());
            }
        }
        return b.start();
    }

    /** Whether the stored definition is def: the directory, each level's type and path. */
    static boolean same(IndexDefinition d, Def def) {
        if (!d.dir().equals(def.dir) || d.levelCount() != def.levels.size()) {
            return false;
        }
        for (int i = 0; i < d.levelCount(); i++) {
            if (!d.typeName(i).equals(def.type(i).string)
                    || !Arrays.equals(d.path(i), def.levels.get(i).path)) {
                return false;
            }
        }
        return true;
    }

    /** The model's value as the stored bytes: an object's format 2, a String's UTF-8. */
    static byte[] bytes(Object v) {
        if (v == null) {
            return null;
        } else if (v instanceof Map) {
            return IndexHarness.toDbObject(v).getBytes();
        } else if (v instanceof String) {
            return ((String) v).getBytes(StandardCharsets.UTF_8);
        }
        return ((Bin) v).bytes();
    }

    static String show(Object v) {
        return IndexReference.show(v);
    }

    static String showBytes(byte[] b) {
        return b == null ? "none" : new Bin(b).toString();
    }

    static void check(boolean ok, String message) {
        if (!ok) {
            throw new AssertionError(message);
        }
    }

    // ======== The journal ========

    /** The journal's writer: one write() of each line. */
    static final class Journal {
        private final FileOutputStream out;

        Journal(File file) throws IOException {
            boolean torn = file.length() > 0 && !new String(Files.readAllBytes(file.toPath()),
                    StandardCharsets.UTF_8).endsWith("\n");
            out = new FileOutputStream(file, true);
            if (torn) {
                out.write('\n');
            }
        }

        synchronized void line(Object... fields) {
            StringBuilder s = new StringBuilder();
            for (Object f : fields) {
                s.append(f).append('\t');
            }
            s.append("$\n");
            try {
                out.write(s.toString().getBytes(StandardCharsets.UTF_8));
            } catch (IOException e) {
                throw new AssertionError("the journal: " + e, e);
            }
        }
    }

    /** An index operation of a run, by the journal. */
    static final class IndexOp {
        final int op;
        final boolean create;
        final String name;
        final String defText;
        /** ok, exists, nosuch; null while in flight (no IR line). */
        String result;
        long gen = -1;
        long lo = -1;
        long hi = -1;

        IndexOp(int op, boolean create, String name, String defText) {
            this.op = op;
            this.create = create;
            this.name = name;
            this.defText = defText;
        }

        public String toString() {
            return "op " + op + " " + (create ? "create " : "delete ") + show(name)
                    + (create ? " " + defText : "") + ": " + (result == null ? "in flight"
                    : result + (gen > 0 ? " gen " + gen : "") + " in (" + lo + ", " + hi + "]");
        }
    }

    /**
     * What a verifier found of a run: per thread {its last seq there, that one's time if it was
     * in flight}; per index name {its generation, 0 for none; active}.
     */
    static final class Resolution {
        final TreeMap<Integer, long[]> threads = new TreeMap<Integer, long[]>();
        final TreeMap<String, long[]> names = new TreeMap<String, long[]>();
    }

    /** A run as the journal tells it. */
    static final class RunLog {
        final int run;
        int threads;
        boolean ok;
        boolean started;
        /** The latest time when its Db had started, before the index manager's start; or -1. */
        long startTime = -1;
        /** Its schedule ended with a close() that returned. */
        boolean closed;
        /** Its schedule ended with a stop() and a return from main, and the JVM ended (PX). */
        boolean stopped;
        boolean exited;
        /** thread, seq: the commit's time, or -1 if not committed (in flight at the kill). */
        final TreeMap<Integer, TreeMap<Integer, Long>> txs =
                new TreeMap<Integer, TreeMap<Integer, Long>>();
        final Set<String> synced = new HashSet<String>();
        final List<IndexOp> ops = new ArrayList<IndexOp>();
        final Map<Integer, IndexOp> opsByNumber = new HashMap<Integer, IndexOp>();
        /** The joins that returned ACTIVE: name, gen, a time after the activation. */
        final List<Object[]> joins = new ArrayList<Object[]>();
        final Map<Integer, Long> syncBegins = new HashMap<Integer, Long>();
        final Set<Integer> syncsDone = new HashSet<Integer>();
        final Map<Integer, Resolution> resolutions = new HashMap<Integer, Resolution>();
        /** The resolution that a verifier wrote in full (VE), or null. */
        Resolution complete;

        RunLog(int run) {
            this.run = run;
        }

        TreeMap<Integer, Long> txs(int thread) {
            TreeMap<Integer, Long> t = txs.get(thread);
            if (t == null) {
                t = new TreeMap<Integer, Long>();
                txs.put(thread, t);
            }
            return t;
        }
    }

    /** Reads the journal: the runs by number; torn lines (no final "$") are left out. */
    static TreeMap<Integer, RunLog> readJournal(File file) throws IOException {
        TreeMap<Integer, RunLog> logs = new TreeMap<Integer, RunLog>();
        if (!file.exists()) {
            return logs;
        }
        String s = new String(Files.readAllBytes(file.toPath()), StandardCharsets.UTF_8);
        for (String line : s.split("\n")) {
            String[] f = line.split("\t", -1);
            if (f.length < 3 || !f[f.length - 1].equals("$")) {
                continue;
            }
            int run = Integer.parseInt(f[1]);
            RunLog log = logs.get(run);
            if (log == null && !f[0].startsWith("V")) {
                log = new RunLog(run);
                logs.put(run, log);
            }
            switch (f[0]) {
            case "R":
                log.threads = Integer.parseInt(f[2]);
                break;
            case "ST":
                log.started = true;
                log.startTime = Long.parseLong(f[2]);
                break;
            case "OK":
                log.ok = true;
                break;
            case "T":
                log.txs(Integer.parseInt(f[2])).put(Integer.parseInt(f[3]), -1L);
                break;
            case "C":
                log.txs(Integer.parseInt(f[2])).put(Integer.parseInt(f[3]), Long.parseLong(f[4]));
                break;
            case "S":
                log.synced.add(f[2] + "." + f[3]);
                break;
            case "I": {
                IndexOp op = new IndexOp(Integer.parseInt(f[2]), f[3].equals("create"), f[4],
                        f[6]);
                log.ops.add(op);
                log.opsByNumber.put(op.op, op);
                break;
            }
            case "IR": {
                IndexOp op = log.opsByNumber.get(Integer.parseInt(f[2]));
                op.result = f[3];
                op.gen = Long.parseLong(f[4]);
                op.lo = Long.parseLong(f[5]);
                op.hi = Long.parseLong(f[6]);
                break;
            }
            case "IJ":
                log.joins.add(new Object[] {f[2], Long.parseLong(f[3]), Long.parseLong(f[4])});
                break;
            case "ISB":
                log.syncBegins.put(Integer.parseInt(f[2]), Long.parseLong(f[3]));
                break;
            case "IS":
                log.syncsDone.add(Integer.parseInt(f[2]));
                break;
            case "CK":
            case "CB":
                break;
            case "CE":
                log.closed = true;
                break;
            case "XB":
                log.stopped = true;
                break;
            case "PX":
                log.exited = true;
                break;
            case "V": {
                RunLog about = logs.get(Integer.parseInt(f[2]));
                Resolution res = about.resolutions.get(run);
                if (res == null) {
                    res = new Resolution();
                    about.resolutions.put(run, res);
                }
                if (f[3].equals("T")) {
                    res.threads.put(Integer.parseInt(f[4]),
                            new long[] {Long.parseLong(f[5]), Long.parseLong(f[6])});
                } else {
                    res.names.put(f[4], new long[] {Long.parseLong(f[5]), Long.parseLong(f[6])});
                }
                break;
            }
            case "VE": {
                RunLog about = logs.get(Integer.parseInt(f[2]));
                Resolution res = about.resolutions.get(run);
                about.complete = res == null ? new Resolution() : res;
                break;
            }
            default:
                throw new AssertionError("a journal line of an unknown kind: " + line);
            }
        }
        return logs;
    }

    // ======== The child ========

    /**
     * A database's settings, the same in each of its runs: a retain duration (reclaim on), a
     * startup distance (bounded startup) and a cache size (eviction), each 0 for the default.
     */
    static final class Settings {
        final int retainSeconds;
        final int startupDistanceMb;
        final int cacheMb;

        Settings(int retainSeconds, int startupDistanceMb, int cacheMb) {
            this.retainSeconds = retainSeconds;
            this.startupDistanceMb = startupDistanceMb;
            this.cacheMb = cacheMb;
        }

        static Settings random(Random r) {
            return new Settings(r.nextInt(5) < 2 ? 20 : 0, r.nextBoolean() ? 5 : 0,
                    r.nextInt(5) < 2 ? 4 : 0);
        }

        String[] args() {
            return new String[] {Integer.toString(retainSeconds),
                    Integer.toString(startupDistanceMb), Integer.toString(cacheMb)};
        }

        public String toString() {
            return "retain " + (retainSeconds == 0 ? "forever" : retainSeconds + " s")
                    + ", startup distance " + (startupDistanceMb == 0 ? "default"
                    : startupDistanceMb + " MB") + ", cache " + (cacheMb == 0 ? "default"
                    : cacheMb + " MB");
        }
    }

    /** An index of the model: its definition, its generation, whether it is known active. */
    static final class LiveIdx {
        final Def def;
        final long gen;
        volatile boolean activeKnown;

        LiveIdx(Def def, long gen, boolean activeKnown) {
            this.def = def;
            this.gen = gen;
            this.activeKnown = activeKnown;
        }

        public String toString() {
            return def + ", gen " + gen + (activeKnown ? ", known active" : "");
        }
    }

    static final class Child {
        final File dir;
        final long seed;
        final int run;
        final Journal journal;
        final TreeMap<Integer, RunLog> logs;
        final IndexReference ref = new IndexReference();
        /** The data: each key's versions by time. Writers commit to it under its lock. */
        final Model m = new Model();
        /** The live indexes; in the schedule, the index thread's alone. */
        final TreeMap<String, LiveIdx> live = new TreeMap<String, LiveIdx>();
        /** Every generation known of each name. */
        final Map<String, Set<Long>> gens = new HashMap<String, Set<Long>>();
        final ReentrantReadWriteLock quiesce = new ReentrantReadWriteLock(true);
        final Map<String, Long> info = new LinkedHashMap<String, Long>();
        Database db;
        DatabaseImp dbi;
        IndexManager im;
        /** The latest time when the Db had started, before the index manager's start. */
        long ts = -1;

        Child(File dir, long seed, int run, Journal journal, TreeMap<Integer, RunLog> logs) {
            this.dir = dir;
            this.seed = seed;
            this.run = run;
            this.journal = journal;
            this.logs = logs;
        }

        void count(String what, long n) {
            Long v = info.get(what);
            info.put(what, (v == null ? 0 : v) + n);
        }

        Set<Long> gens(String name) {
            Set<Long> s = gens.get(name);
            if (s == null) {
                s = new HashSet<Long>();
                gens.put(name, s);
            }
            return s;
        }

        long now() {
            return db.currentTime().units();
        }

        // -------- The start --------

        void open(Settings settings, int stepValues, final int stepSleep,
                final int cleanupSleep) {
            boolean everStarted = false;
            for (RunLog log : logs.values()) {
                everStarted |= log.run < run && log.started;
            }
            final long[] t = {-1};
            // The start's time, in the journal before the index manager starts anything.
            DatabaseImp.testHookAfterStart = d -> {
                t[0] = d.lookupTime(Long.MAX_VALUE);
                journal.line("ST", run, t[0]);
            };
            long t0 = System.nanoTime();
            DatabaseBuilder b = Factory.database().create(dir.getPath());
            if (settings.startupDistanceMb > 0) {
                b.startupDistanceInMb(settings.startupDistanceMb);
            }
            if (settings.cacheMb > 0) {
                b.cacheSizeInMb(settings.cacheMb);
            }
            try {
                db = b.start();
            } catch (DatabaseNotCreatedException e) {
                // Allowed only if no start succeeded before (DatabaseBuilder.start()).
                check(!everStarted, "DatabaseNotCreatedException after a start that "
                        + "succeeded: " + e);
                count("notCreated", 1);
                for (File f : dir.listFiles()) {
                    if (f.getName().endsWith(".bergdb") || f.getName().equals("created.txt")) {
                        check(f.delete(), "removed " + f);
                    }
                }
                db = b.start();
            } finally {
                DatabaseImp.testHookAfterStart = null;
            }
            count("startMs", (System.nanoTime() - t0) / 1000000);
            ts = t[0];
            check(ts >= 0, "the hook after the start was not called");
            dbi = (DatabaseImp) db;
            im = dbi.getIndexManager();
            if (stepValues > 0) {
                im.testStepValues = stepValues;
            }
            if (settings.retainSeconds > 0) {
                // A transaction of the database's own, in the first run; nothing after.
                db.setRetainDuration(Duration.units(settings.retainSeconds
                        * Clock.UNITS_PER_SEC));
            }
            if (stepSleep > 0 || cleanupSleep > 0) {
                im.testHook = point -> {
                    if (point.equals(IndexManager.BUILD_STEP)) {
                        sleep(stepSleep);
                    } else if (point.equals(IndexManager.CLEANUP_STEP)) {
                        sleep(cleanupSleep);
                    }
                };
            }
        }

        // -------- The model from the journal --------

        /**
         * Builds the model from the runs before this one and checks the database at ts: the
         * run that was killed (the last run with a schedule whose outcome no verifier has
         * written) is resolved from the database, and its resolution written.
         */
        void verify() {
            RunLog pending = null;
            for (RunLog j : logs.values()) {
                if (j.run >= run || !j.ok) {
                    continue;
                }
                check(pending == null, "run " + (pending == null ? 0 : pending.run)
                        + " was not resolved, and run " + j.run + " ran its schedule");
                if (j.complete != null) {
                    applyData(j, j.complete);
                    applyIndexes(j, j.complete);
                } else {
                    pending = j;
                }
            }
            Connection c = db.newConnection();
            c.setLookupTime(Time.units(ts));
            if (pending != null) {
                // The state right after its kill: the first start after it. Later runs killed
                // before their schedule changed no data, but their resumed builds and cleanups
                // committed transactions after that time.
                long tsj = ts;
                for (RunLog l : logs.values()) {
                    if (l.run > pending.run && l.run < run && l.startTime >= 0) {
                        tsj = l.startTime;
                        break;
                    }
                }
                Connection cj = db.newConnection();
                cj.setLookupTime(Time.units(tsj));
                Resolution res = resolve(pending, cj, tsj);
                for (Map.Entry<Integer, long[]> e : res.threads.entrySet()) {
                    journal.line("V", run, pending.run, "T", e.getKey(), e.getValue()[0],
                            e.getValue()[1]);
                }
                for (Map.Entry<String, long[]> e : res.names.entrySet()) {
                    journal.line("V", run, pending.run, "I", e.getKey(), e.getValue()[0],
                            e.getValue()[1]);
                }
                journal.line("VE", run, pending.run);
            }
            checkAtStart(c);
        }

        /** The run's transactions that are there, in the order of their times, into the model. */
        void applyData(RunLog j, Resolution res) {
            List<Object[]> there = new ArrayList<Object[]>();
            for (Map.Entry<Integer, long[]> e : res.threads.entrySet()) {
                int thread = e.getKey();
                int last = (int) e.getValue()[0];
                TreeMap<Integer, Long> txs = j.txs(thread);
                for (int seq = 1; seq <= last; seq++) {
                    Long t = txs.get(seq);
                    check(t != null, "run " + j.run + ", thread " + thread + ": transaction "
                            + seq + " is not in the journal");
                    long time = t >= 0 ? t : e.getValue()[1];
                    check(time >= 0, "run " + j.run + ", thread " + thread + ": transaction "
                            + seq + " has no time");
                    there.add(new Object[] {time, tx(seed, j.run, thread, seq)});
                }
            }
            Collections.sort(there, Comparator.comparing(o -> (Long) o[0]));
            for (Object[] o : there) {
                m.commit((Long) o[0], ((Tx) o[1]).writes);
            }
        }

        /** The run's index operations: each name's live generation as the resolution found it. */
        void applyIndexes(RunLog j, Resolution res) {
            for (IndexOp op : j.ops) {
                if (op.create && "ok".equals(op.result)) {
                    gens(op.name).add(op.gen);
                }
            }
            for (Map.Entry<String, long[]> e : res.names.entrySet()) {
                String name = e.getKey();
                long gen = e.getValue()[0];
                boolean active = e.getValue()[1] != 0;
                LiveIdx before = live.get(name);
                if (gen == 0) {
                    live.remove(name);
                } else if (before != null && before.gen == gen) {
                    before.activeKnown |= active;
                } else {
                    live.put(name, new LiveIdx(defOfGen(j, name, gen), gen, active));
                    gens(name).add(gen);
                }
            }
        }

        /** The definition of the run's creation of the name with the generation gen. */
        Def defOfGen(RunLog j, String name, long gen) {
            IndexOp last = null;
            for (IndexOp op : j.ops) {
                if (op.name.equals(name)) {
                    if (op.create && op.gen == gen) {
                        return parseDef(name, op.defText);
                    }
                    last = op;
                }
            }
            check(last != null && last.create && last.result == null, "run " + j.run
                    + ": no creation of " + show(name) + " with the generation " + gen);
            return parseDef(name, last.defText);
        }

        /**
         * Resolves the killed run j from the database at ts, the time of the first start after
         * its kill (the parameter, not the field): which of its transactions and
         * index operations are there; checks that they are a prefix, by time, of what the run
         * did, with every synced one; and applies them to the model.
         */
        Resolution resolve(RunLog j, Connection c, long ts) {
            Resolution res = new Resolution();
            // After a close() that returned, every transaction that had returned is durable.
            // So too after a stop() and a return from main, when the JVM ended by itself.
            boolean all = j.closed || j.stopped && j.exited;
            long synced = all ? Long.MAX_VALUE : syncPoint(j);
            if (all) {
                count(j.closed ? "closedRuns" : "exitedRuns", 1);
            }
            int lost = 0;
            int there = 0;
            Map<Integer, Integer> inflightThere = new HashMap<Integer, Integer>();
            Map<Integer, List<Kv<byte[]>>> inflightKvs = new HashMap<Integer, List<Kv<byte[]>>>();
            for (int th = 0; th < j.threads; th++) {
                TreeMap<Integer, Long> txs = j.txs(th);
                int cmax = 0;
                int inflight = 0;
                int expected = 1;
                long lastTime = -1;
                long cmaxTime = -1;
                for (Map.Entry<Integer, Long> e : txs.entrySet()) {
                    int seq = e.getKey();
                    long t = e.getValue();
                    check(seq == expected++, "run " + j.run + ", thread " + th + ": the "
                            + "transactions are not 1, 2, 3...: " + txs.keySet());
                    if (t < 0) {
                        check(seq == txs.lastKey(), "run " + j.run + ", thread " + th
                                + ": transaction " + seq + " has no commit, and later ones do");
                        inflight = seq;
                        continue;
                    }
                    check(t > lastTime, "run " + j.run + ", thread " + th + ": the times of "
                            + "its transactions do not increase at " + seq);
                    lastTime = t;
                    if (t <= ts) {
                        cmax = seq;
                        cmaxTime = t;
                    } else {
                        lost++;
                        check(t > synced, "run " + j.run + ", thread " + th + ": transaction "
                                + seq + ", committed at " + t + ", is lost (the start's time is "
                                + ts + "), but a sync returned for the transactions up to "
                                + synced);
                    }
                }
                there += cmax;
                String stamp = c.get(stampKey(th), String.class);
                String prefix = j.run + "." + th + ".";
                int s = stamp != null && stamp.startsWith(prefix)
                        ? Integer.parseInt(stamp.substring(prefix.length())) : 0;
                long tf = -1;
                if (s != cmax) {
                    check(inflight > 0 && s == inflight && cmax == inflight - 1,
                            "run " + j.run + ", thread " + th + ": its stamp at the start's "
                            + "time " + ts + " is " + stamp + ", but the journal has its "
                            + "transactions committed up to " + cmax + " by then (at "
                            + cmaxTime + "), the last committed one at " + lastTime
                            + ", and " + (inflight > 0 ? inflight + " in flight" : "none in "
                            + "flight") + ": a committed transaction lost, or one there "
                            + "that was not committed by then");
                    TransactionInfo ti = c.transactionInfo();
                    tf = ti.time().units();
                    check(tf <= ts && tf > cmaxTime, "run " + j.run + ", thread " + th
                            + ": the transaction in flight is there, at the time " + tf
                            + ", not in (" + cmaxTime + ", " + ts + "]");
                    inflightThere.put(th, s);
                    inflightKvs.put(th, ti.kvs());
                    count("inflightThere", 1);
                } else if (inflight > 0) {
                    count("inflightLost", 1);
                }
                res.threads.put(th, new long[] {s, tf});
            }
            count("txThere", there);
            count("txLost", lost);

            applyData(j, res);
            // The KVs of each transaction in flight that is there: all of it (whole or not at all).
            for (Map.Entry<Integer, Integer> e : inflightThere.entrySet()) {
                int th = e.getKey();
                long tf = res.threads.get(th)[1];
                Tx tx = tx(seed, j.run, th, e.getValue());
                LinkedHashMap<String, Object> last = new LinkedHashMap<String, Object>();
                for (Write w : tx.writes) {
                    last.remove(w.key);
                    last.put(w.key, w.value);
                }
                Map<String, byte[]> expected = new TreeMap<String, byte[]>();
                for (Map.Entry<String, Object> w : last.entrySet()) {
                    if (w.getValue() != null || m.valueAt(w.getKey(), tf - 1) != null) {
                        expected.put(w.getKey(), bytes(w.getValue()));
                    }
                }
                Map<String, byte[]> got = new TreeMap<String, byte[]>();
                for (Kv<byte[]> kv : inflightKvs.get(th)) {
                    got.put(kv.key(), kv.value());
                }
                boolean equal = expected.keySet().equals(got.keySet());
                for (String k : expected.keySet()) {
                    equal &= Arrays.equals(expected.get(k), got.get(k));
                }
                check(equal, "run " + j.run + ", thread " + th + ": the transaction in flight "
                        + tx + " is there, with the KVs " + got.keySet() + ", not "
                        + expected.keySet() + " (or other values)");
            }

            resolveIndexes(j, res, synced, ts);
            applyIndexes(j, res);
            return res;
        }

        /**
         * The time up to which a sync returned in the run: every transaction at or before it
         * was durable when the sync returned. A sync after a transaction (Transaction.sync(),
         * Connection.sync() or Database.sync() in its writer thread) gives its time; a
         * Database.sync() of the index thread the database's currentTime() before the call,
         * which is at or after every transaction completed by then (it need not be one's).
         */
        static long syncPoint(RunLog j) {
            long synced = -1;
            for (Map.Entry<Integer, TreeMap<Integer, Long>> e : j.txs.entrySet()) {
                for (Map.Entry<Integer, Long> tx : e.getValue().entrySet()) {
                    if (j.synced.contains(e.getKey() + "." + tx.getKey())) {
                        synced = Math.max(synced, tx.getValue());
                    }
                }
            }
            for (int op : j.syncsDone) {
                synced = Math.max(synced, j.syncBegins.get(op));
            }
            return synced;
        }

        /**
         * Each name's definition at ts must be the result of a prefix of the run's operations
         * on the name: those that ended at or before ts, or before a sync that returned, there;
         * none that began at or after ts.
         */
        void resolveIndexes(RunLog j, Resolution res, long synced, long ts) {
            long there = Math.max(ts, synced);
            Map<String, IndexDefinition> defs = defsAt(ts);
            for (String name : INDEX_NAMES) {
                IndexDefinition obs = defs.get(name);
                long obsGen = obs == null ? 0 : obs.gen();
                LiveIdx before = live.get(name);
                List<IndexOp> ops = new ArrayList<IndexOp>();
                for (IndexOp op : j.ops) {
                    if (op.name.equals(name) && (op.result == null || op.result.equals("ok"))) {
                        ops.add(op);
                    }
                }
                List<Integer> candidates = new ArrayList<Integer>();
                long state = before == null ? 0 : before.gen;
                for (int p = 0; p <= ops.size(); p++) {
                    if (p > 0) {
                        IndexOp op = ops.get(p - 1);
                        state = !op.create ? 0 : op.result == null ? -2 : op.gen;
                    }
                    // A creation in flight that is there has a generation of its own: not the
                    // one before the run, nor one of the run's other creations. It may equal a
                    // lost creation's of an earlier run, whose time was never there.
                    boolean fresh = obsGen > 0 && (before == null || before.gen != obsGen);
                    for (IndexOp op : ops) {
                        fresh &= !(op.create && op.gen == obsGen);
                    }
                    boolean match = state == obsGen || state == -2 && fresh;
                    for (int i = 1; i <= ops.size() && match; i++) {
                        IndexOp op = ops.get(i - 1);
                        if (op.result != null && op.hi <= there && p < i) {
                            match = false;      // Ended by ts or a sync: must be there.
                        }
                        if (op.result != null && op.lo >= ts && p >= i) {
                            match = false;      // Began after ts: must not be there.
                        }
                    }
                    if (match) {
                        candidates.add(p);
                    }
                }
                check(!candidates.isEmpty(), "run " + j.run + ": the index " + show(name)
                        + " at the start's time " + ts + " is " + (obs == null ? "absent"
                        : obs + " (gen " + obsGen + ")") + ", which no prefix of the run's "
                        + "operations on it gives; before the run: " + before + "; the "
                        + "operations: " + ops);
                if (obs != null) {
                    int p = candidates.get(candidates.size() - 1);
                    Def def = p == 0 ? before.def : parseDef(name, ops.get(p - 1).defText);
                    check(same(obs, def), "run " + j.run + ": the index " + show(name)
                            + " at the start's time is " + obs + ", not " + def);
                    boolean known = before != null && before.gen == obsGen && before.activeKnown;
                    for (Object[] jn : j.joins) {
                        known |= jn[0].equals(name) && (Long) jn[1] == obsGen
                                && (Long) jn[2] <= there;
                    }
                    check(obs.isActive() || !known, "run " + j.run + ": the index "
                            + show(name) + " is building at the start's time, but it was "
                            + "known active by then");
                }
                if (candidates.size() > 1) {
                    count("indexOpsUnresolved", 1);
                } else {
                    // The operations that returned: there, or lost (not synced).
                    int p = candidates.get(0);
                    for (int i = 1; i <= ops.size(); i++) {
                        if (ops.get(i - 1).result != null) {
                            count(i <= p ? "indexOpsThere" : "indexOpsLost", 1);
                        }
                    }
                }
                res.names.put(name, new long[] {obsGen, obs != null && obs.isActive() ? 1 : 0});
            }
        }

        /** The definitions at t, read from the stream. */
        Map<String, IndexDefinition> defsAt(long t) {
            Map<String, IndexDefinition> defs = new TreeMap<String, IndexDefinition>();
            for (Kvt kvt : im.scan(IndexKeys.definitionsPrefix(), t, Integer.MAX_VALUE)) {
                String name = IndexKeys.nameOfDefinitionKey(Keys.toBytes(kvt.key));
                defs.put(name, IndexDefinition.fromBytes(name, kvt.value));
            }
            return defs;
        }

        // -------- The checks --------

        /** The checks at ts, right after the start (the class Javadoc's 4 and 5). */
        void checkAtStart(Connection c) {
            int keys = 0;
            for (String key : m.versions.keySet()) {
                byte[] got = c.get(key, byte[].class);
                byte[] expected = bytes(m.valueAt(key, Long.MAX_VALUE));
                check(Arrays.equals(got, expected), "the value at " + show(key) + " at the start's "
                        + "time " + ts + " is " + showBytes(got) + ", not "
                        + show(m.valueAt(key, Long.MAX_VALUE)));
                keys += got == null ? 0 : 1;
            }
            count("keys", keys);
            for (String d : DIRS) {
                checkDir(c, d, Long.MAX_VALUE);
            }
            checkDir(c, STAMPS, Long.MAX_VALUE);

            Map<String, IndexDefinition> defs = defsAt(ts);
            check(defs.keySet().equals(live.keySet()), "the indexes at the start's time "
                    + ts + " are " + defs.keySet() + ", not " + live.keySet());
            int building = 0;
            for (LiveIdx li : live.values()) {
                IndexDefinition d = defs.get(li.def.name);
                check(d.gen() == li.gen && same(d, li.def), "the index " + show(li.def.name)
                        + " at the start's time is " + d + ", gen " + d.gen() + ", not " + li);
                check(d.isActive() || !li.activeKnown, "the index " + show(li.def.name)
                        + " is building at the start's time, but was known active: " + li);
                IndexDefinition mem = im.definition(li.def.name);
                check(mem != null && mem.gen() == li.gen, "the index " + show(li.def.name)
                        + " in memory after the start: " + mem + ", not gen " + li.gen);
                List<Entry> expected = ref.entries(li.def, m.dirAt(li.def.dir, Long.MAX_VALUE));
                List<Entry> raw = rawEntries(li, ts);
                count("entries", raw.size());
                if (d.isActive()) {
                    li.activeKnown = true;
                    check(raw.equals(expected), "the entries of the active " + li + " at the "
                            + "start's time: " + raw + ", not " + expected);
                } else {
                    building++;
                    check(expected.containsAll(raw), "an entry of the building " + li + " at "
                            + "the start's time is not f of a value: " + raw + ", f: " + expected);
                }
            }
            count("building", building);
            Random r = new Random(mix(seed, run, 11));
            Long[] times = m.times.toArray(new Long[0]);
            for (int i = 0; i < 3 && times.length > 0; i++) {
                checkPast(times[r.nextInt(times.length)]);
            }
            List<IndexKeys.Marker> markers = checkMarkers(ts);
            count("markers", markers.size());
            for (String name : INDEX_NAMES) {
                LiveIdx li = live.get(name);
                if (li == null) {
                    try {
                        db.indexJob(name);
                        check(false, "a job for the free name " + show(name));
                    } catch (NoSuchIndexException e) {
                        // Expected.
                    }
                    continue;
                }
                JobStatus s = db.indexJob(name).getStatus();
                check(s.state() != JobStatus.State.FAILED, "the job of " + li + " after the "
                        + "start: " + s.note());
                if (defs.get(name).isActive()) {
                    check(s.state() == JobStatus.State.ACTIVE && s.count() == 0, "the job of "
                            + "the index " + li + ", active at the start: " + s.note());
                }
            }
        }

        /**
         * The history at t, a time of a transaction that is there: each directory's listing is
         * the model's at t; each index stored at t (its definition read at t, whatever its
         * generation) has f over the data at t as its entries if it was active, a part of them
         * if building, and useIndex at t works if and only if it was active. Skipped if reclaim
         * has cut t.
         */
        void checkPast(long t) {
            if (t < db.getFirstAvailableLookupTime().units()) {
                return;
            }
            try {
                Connection rc = db.newConnection();
                rc.setLookupTime(Time.units(t));
                for (String d : DIRS) {
                    checkDir(rc, d, t);
                }
                for (Map.Entry<String, IndexDefinition> e : defsAt(t).entrySet()) {
                    IndexDefinition d = e.getValue();
                    List<Level> levels = new ArrayList<Level>();
                    for (int i = 0; i < d.levelCount(); i++) {
                        Type type = null;
                        for (Type x : Type.values()) {
                            type = x.string.equals(d.typeName(i)) ? x : type;
                        }
                        levels.add(new Level(type, Call.NESTED_ARRAY, d.path(i)));
                    }
                    LiveIdx li = new LiveIdx(new Def(e.getKey(), d.dir(), levels), d.gen(),
                            d.isActive());
                    boolean active;
                    try {
                        rc.useIndex(e.getKey(), DbObject.class);
                        active = true;
                    } catch (NoSuchIndexException x) {
                        active = false;
                    }
                    check(active == d.isActive(), "useIndex(" + show(e.getKey()) + ") at the "
                            + "past time " + t + (active ? " works" : " throws") + ", and the "
                            + "definition then is " + d);
                    List<Entry> expected = ref.entries(li.def, m.dirAt(li.def.dir, t));
                    List<Entry> raw = rawEntries(li, t);
                    count("pastEntries", raw.size());
                    if (d.isActive()) {
                        check(raw.equals(expected), "the entries of the active " + li + " at the "
                                + "past time " + t + ": " + raw + ", not " + expected);
                    } else {
                        check(expected.containsAll(raw), "an entry of the building " + li
                                + " at the past time " + t + " is not f of a value: " + raw
                                + ", f: " + expected);
                    }
                }
                count("pastChecked", 1);
            } catch (LookupTimeNotAvailableException e) {
                // Reclaim cut t meanwhile.
            }
        }

        /** The markers at t: each of a deleted generation; and no orphan entry. */
        List<IndexKeys.Marker> checkMarkers(long t) {
            List<IndexKeys.Marker> markers = im.markers(t);
            List<byte[]> allowed = new ArrayList<byte[]>();
            for (IndexKeys.Marker mk : markers) {
                LiveIdx li = live.get(mk.name);
                check(gens(mk.name).contains(mk.gen) && (li == null || li.gen != mk.gen),
                        "at " + t + ", " + mk + " is not of a deleted generation; the "
                        + "generations of the name: " + gens(mk.name) + ", live: " + li);
                allowed.add(IndexKeys.generationPrefix(mk.name, mk.gen));
            }
            for (LiveIdx li : live.values()) {
                allowed.add(IndexKeys.generationPrefix(li.def.name, li.gen));
            }
            for (Kvt kvt : im.scan(IndexKeys.entriesPrefix(), t, Integer.MAX_VALUE)) {
                byte[] key = Keys.toBytes(kvt.key);
                boolean ok = false;
                for (byte[] p : allowed) {
                    ok |= IndexKeys.startsWith(key, p);
                }
                check(ok, "at " + t + ", an index entry of no live or deleted generation: "
                        + IndexKeys.show(key) + "; live: " + live + "; markers: " + markers);
            }
            return markers;
        }

        /** A directory's primary listing at t: the model's keys and values. */
        void checkDir(Connection c, String d, long t) {
            SortedMap<String, Object> expected;
            synchronized (m) {
                expected = new TreeMap<String, Object>(m.dirAt(d, t));
            }
            Map<String, byte[]> got = new TreeMap<String, byte[]>();
            for (Kv<byte[]> kv : c.usePrimary(byte[].class).dir(d).kvs()) {
                check(got.put(kv.key(), kv.value()) == null, "the listing of " + d + " has "
                        + show(kv.key()) + " twice");
            }
            check(got.keySet().equals(expected.keySet()), "the listing of " + d + " at " + t
                    + ": " + got.keySet() + ", not " + expected.keySet());
            for (Map.Entry<String, Object> e : expected.entrySet()) {
                check(Arrays.equals(got.get(e.getKey()), bytes(e.getValue())), "the listing of "
                        + d + " at " + t + ": the value at " + show(e.getKey()) + " is "
                        + showBytes(got.get(e.getKey())) + ", not " + show(e.getValue()));
            }
        }

        /** The generation's entries at t, parsed into the reference's Entry. */
        List<Entry> rawEntries(LiveIdx li, long t) {
            Def def = li.def;
            char[] types = new char[def.levels.size()];
            for (int i = 0; i < types.length; i++) {
                types[i] = IndexKeys.type(def.type(i).string);
            }
            byte[] prefix = IndexKeys.generationPrefix(def.name, li.gen);
            List<Entry> result = new ArrayList<Entry>();
            for (byte[] key : im.entries(def.name, li.gen, t)) {
                IndexKeys.Entry e = IndexKeys.parseEntry(key, prefix, types);
                List<Object> levels = new ArrayList<Object>();
                for (int i = 0; i < types.length; i++) {
                    Object v = e.value(i);
                    levels.add(v instanceof byte[] ? new Bin((byte[]) v) : v);
                }
                result.add(new Entry(levels, def.dir + e.fileName().substring(1), null));
            }
            return result;
        }

        /**
         * The index of the name at t: absent for a free name; active if it must be; if active,
         * its entries are f over the data and its scans the reference's; if building, its
         * entries a part of f.
         */
        void checkIndexAt(Connection rc, long t, String name, LiveIdx li, Random r) {
            boolean active;
            try {
                rc.useIndex(name, DbObject.class);
                active = true;
            } catch (NoSuchIndexException e) {
                active = false;
            }
            if (li == null) {
                check(!active, "useIndex(" + show(name) + ") at " + t + " works for a free name");
                return;
            }
            check(active || !li.activeKnown, "useIndex(" + show(name) + ") at " + t
                    + ": NoSuchIndexException, for an index known active: " + li);
            List<Entry> expected;
            synchronized (m) {
                expected = ref.entries(li.def, m.dirAt(li.def.dir, t));
            }
            List<Entry> raw = rawEntries(li, t);
            count("entriesChecked", raw.size());
            if (!active) {
                check(expected.containsAll(raw), "an entry of the building " + li + " at " + t
                        + " is not f of a value: " + raw + ", f: " + expected);
                return;
            }
            check(raw.equals(expected), "the entries of the active " + li + " at " + t + ": "
                    + raw + ", not " + expected);
            Def def = li.def;
            for (Query q : IndexHarness.queries(def, expected, r)) {
                List<Entry> want = ref.filter(def, expected, q);
                List<Kv<DbObject>> got = new ArrayList<Kv<DbObject>>();
                for (Kv<DbObject> kv : use(rc, def, q).kvs()) {
                    got.add(kv);
                }
                count("scans", 1);
                int n = Math.min(got.size(), want.size());
                for (int i = 0; i < n; i++) {
                    Entry e = want.get(i);
                    Kv<DbObject> kv = got.get(i);
                    check(e.key.equals(kv.key()), "scan " + q + " of " + def + " at " + t
                            + ", result " + i + ": " + show(kv.key()) + ", not " + e
                            + "; all: " + want);
                    check(Arrays.equals(IndexHarness.toDbObject(e.value).getBytes(),
                            kv.value().getBytes()), "scan " + q + " of " + def + " at " + t
                            + ", the value at " + e.key);
                }
                check(got.size() == want.size(), "scan " + q + " of " + def + " at " + t
                        + ": " + got.size() + " results, not " + want.size() + ": " + want);
            }
        }

        // -------- After the checks: the builds and cleanups end --------

        /** Every build ends ACTIVE, every cleanup ends; then the indexes and scans are exact. */
        void settle(Random r) {
            for (String name : new ArrayList<String>(live.keySet())) {
                LiveIdx li = live.get(name);
                JobStatus s;
                try {
                    s = db.indexJob(name).join(JOB_WAIT);
                } catch (IndexBuildException e) {
                    throw new AssertionError("the build of " + li + " failed: " + e, e);
                }
                check(s.state() == JobStatus.State.ACTIVE, "the build of " + li + " after "
                        + JOB_WAIT + " ms: " + s.note());
                li.activeKnown = true;
            }
            long deadline = System.currentTimeMillis() + JOB_WAIT;
            while (!im.markers(Long.MAX_VALUE).isEmpty()) {
                check(System.currentTimeMillis() < deadline, "a cleanup not done in " + JOB_WAIT
                        + " ms: " + im.markers(Long.MAX_VALUE));
                sleep(20);
            }
            long t = dbi.getDb().lookupTime(Long.MAX_VALUE);
            Connection rc = db.newConnection();
            rc.setLookupTime(Time.units(t));
            for (String name : INDEX_NAMES) {
                checkIndexAt(rc, t, name, live.get(name), r);
            }
            check(checkMarkers(t).isEmpty(), "a marker came back");
        }

        // -------- The schedule --------

        /** Set before the close of the schedule: a writer that then fails ends quietly. */
        volatile boolean closing;

        /**
         * A sleep between a commit and its journal line, ms, in some runs: so that a kill
         * finds more transactions committed and not yet in the journal (resolved by stamps).
         */
        int commitLag;

        void schedule(int threads, int closeAfterMs) {
            for (int th = 0; th < threads; th++) {
                final int k = th;
                Thread w = new Thread(() -> writer(k), "writer-" + th);
                w.setDaemon(true);
                w.start();
            }
            indexThread(new Random(mix(seed, run, 1000)), closeAfterMs == 0 ? Long.MAX_VALUE
                    : System.currentTimeMillis() + Math.abs(closeAfterMs), closeAfterMs < 0);
        }

        /**
         * Stops the database while the writers write and builds or cleanups may run, and
         * returns from main: every transaction that has returned is written, "also when the
         * program returns from main right after this method" (Database.stop()). The parent
         * writes PX in the journal when the JVM has ended with status 0.
         */
        void stopAndExit() {
            closing = true;
            journal.line("XB", run);
            System.out.println("P exit");
            db.stop();
        }

        /**
         * Closes the database while the writers write and builds or cleanups may run: when
         * close() returns, every transaction that has returned is durable (Database.close()),
         * which the journal's CE line tells the next start. Then waits for its kill.
         */
        void close() {
            closing = true;
            journal.line("CB", run);
            System.out.println("P close");
            db.close();
            journal.line("CE", run);
            System.out.println("P closed");
            while (true) {
                sleep(1000);
            }
        }

        void writer(int th) {
            try {
                writeLoop(th);
            } catch (RuntimeException e) {
                if (!closing) {
                    throw e;
                }
                // The database closes: a refusal, or a sync that met the stop.
            }
        }

        void writeLoop(int th) {
            Connection c = db.newConnection();
            Random r = new Random(mix(seed, run, th, -1));
            for (int seq = 1; ; seq++) {
                Tx tx = tx(seed, run, th, seq);
                journal.line("T", run, th, seq);
                Transaction t;
                long time;
                quiesce.readLock().lock();
                try {
                    Tx exec = tx;
                    if (PLANT.equals("halfwrite") && tx.writes.size() >= 3 && seq % 5 == 0) {
                        exec = new Tx(tx.run, tx.thread, tx.seq);
                        exec.rw = tx.rw;
                        for (int i = 1; i < tx.writes.size(); i++) {
                            exec.add(tx.writes.get(i).key, tx.writes.get(i).value,
                                    tx.values.get(i));
                        }
                    }
                    t = execute(c, exec);
                    time = t.getTime().units();
                    synchronized (m) {
                        m.commit(time, tx.writes);
                    }
                } finally {
                    quiesce.readLock().unlock();
                }
                if (commitLag > 0) {
                    sleep(commitLag);
                }
                journal.line("C", run, th, seq, time);
                if (tx.sync != 0) {
                    if (PLANT.equals("nosync")) {
                        // Planted: no sync.
                    } else if (tx.sync == 1) {
                        t.sync();
                    } else if (tx.sync == 2) {
                        c.sync();
                    } else {
                        db.sync();
                    }
                    journal.line("S", run, th, seq);
                }
                int p = r.nextInt(10);
                if (p < 3) {
                    sleep(p);
                }
            }
        }

        void indexThread(Random r, long closeAt, boolean exit) {
            for (int op = 1; ; op++) {
                sleep(r.nextInt(100));
                if (System.currentTimeMillis() >= closeAt) {
                    if (exit) {
                        stopAndExit();
                        return;
                    }
                    close();
                }
                int k = r.nextInt(100);
                if (k < 30) {
                    create(op, r);
                } else if (k < 52) {
                    deleteIndex(op, r);
                } else if (k < 62) {
                    join(r);
                } else if (k < 70) {
                    sync(op);
                } else {
                    checkNow(r);
                }
            }
        }

        /** Database.sync(): every transaction committed before it is then durable. */
        void sync(int op) {
            journal.line("ISB", run, op, now());
            if (!PLANT.equals("nosync")) {
                db.sync();
            }
            journal.line("IS", run, op);
        }

        private boolean planted;

        /** Plants an orphan or a stale entry, once a run, through the Core. */
        void plant() {
            if (planted) {
                return;
            }
            byte[] key = null;
            if (PLANT.equals("orphan")) {
                byte[] p = IndexKeys.generationPrefix("i9", 1);
                key = Arrays.copyOf(p, p.length + 2);
                key[p.length] = 'c';
                key[p.length + 1] = 'd';
            } else {
                for (LiveIdx li : live.values()) {
                    List<byte[]> keys = im.entries(li.def.name, li.gen, Long.MAX_VALUE);
                    if (keys.isEmpty()) {
                        continue;
                    }
                    char[] types = new char[li.def.levels.size()];
                    for (int i = 0; i < types.length; i++) {
                        types[i] = IndexKeys.type(li.def.type(i).string);
                    }
                    byte[] prefix = IndexKeys.generationPrefix(li.def.name, li.gen);
                    IndexKeys.Entry e = IndexKeys.parseEntry(keys.get(0), prefix, types);
                    key = IndexKeys.entryKey(prefix, e.levels(),
                            IndexKeys.fileKey(PubKeys.udir2idir(li.def.dir) + "-zzz"));
                    break;
                }
            }
            if (key != null) {
                dbi.getDb().execute(dbi.getDb().trans().put(key, new byte[0]).build());
                planted = true;
            }
        }

        void create(int op, Random r) {
            List<String> free = new ArrayList<String>();
            for (String name : INDEX_NAMES) {
                if (!live.containsKey(name)) {
                    free.add(name);
                }
            }
            String name;
            if (!live.isEmpty() && (free.isEmpty() || r.nextInt(6) == 0)) {
                name = new ArrayList<String>(live.keySet()).get(r.nextInt(live.size()));
            } else {
                name = free.get(r.nextInt(free.size()));
            }
            boolean used = live.containsKey(name);
            boolean join = r.nextBoolean();
            Def def = def(name, r);
            journal.line("I", run, op, "create", name, join ? 1 : 0, defText(def));
            long lo = now();
            Job job;
            try {
                job = start(db, def);
            } catch (IndexAlreadyExistsException e) {
                check(used, "IndexAlreadyExistsException for the free name " + show(name));
                journal.line("IR", run, op, "exists", 0, lo, now());
                return;
            }
            long hi = now();
            check(!used, "a creation of the used name " + show(name) + " did not throw");
            long gen = im.definition(name).gen();
            journal.line("IR", run, op, "ok", gen, lo, hi);
            LiveIdx li = new LiveIdx(def, gen, false);
            live.put(name, li);
            gens(name).add(gen);
            count("creations", 1);
            if (r.nextBoolean()) {
                sync(op);
            }
            System.out.println("P build");
            if (join) {
                join(name, job);
            }
        }

        void join(String name, Job job) {
            LiveIdx li = live.get(name);
            JobStatus s;
            try {
                s = job.join(JOB_WAIT);
            } catch (IndexBuildException e) {
                throw new AssertionError("the build of " + li + " failed: " + e, e);
            }
            check(s.state() == JobStatus.State.ACTIVE, "join of " + li + ": " + s.note());
            journal.line("IJ", run, name, li.gen, now());
            li.activeKnown = true;
        }

        void join(Random r) {
            if (!live.isEmpty()) {
                String name = new ArrayList<String>(live.keySet()).get(r.nextInt(live.size()));
                join(name, db.indexJob(name));
            }
        }

        void deleteIndex(int op, Random r) {
            String name = !live.isEmpty() && r.nextInt(5) != 0
                    ? new ArrayList<String>(live.keySet()).get(r.nextInt(live.size()))
                    : INDEX_NAMES[r.nextInt(INDEX_NAMES.length)];
            LiveIdx li = live.get(name);
            journal.line("I", run, op, "delete", name, "-", "-");
            long lo = now();
            try {
                db.deleteIndex(name);
            } catch (NoSuchIndexException e) {
                check(li == null, "NoSuchIndexException for the index in use " + li);
                journal.line("IR", run, op, "nosuch", 0, lo, now());
                return;
            }
            long hi = now();
            check(li != null, "deleteIndex of the free name " + show(name) + " did not throw");
            journal.line("IR", run, op, "ok", li.gen, lo, hi);
            live.remove(name);
            count("deletions", 1);
            if (r.nextBoolean()) {
                sync(op);
            }
            System.out.println("P cleanup");
        }

        /** The checks at a lookup time with every transaction up to it in the model. */
        void checkNow(Random r) {
            if (PLANT.equals("orphan") || PLANT.equals("stale")) {
                plant();
            }
            long t;
            quiesce.writeLock().lock();
            try {
                t = now();
            } finally {
                quiesce.writeLock().unlock();
            }
            Connection rc = db.newConnection();
            rc.setLookupTime(Time.units(t));
            for (String name : INDEX_NAMES) {
                checkIndexAt(rc, t, name, live.get(name), r);
            }
            checkDir(rc, DIRS[r.nextInt(DIRS.length)], t);
            checkMarkers(t);
            journal.line("CK", run, t);
        }
    }

    static void sleep(long ms) {
        try {
            Thread.sleep(ms);
        } catch (InterruptedException e) {
            throw new AssertionError(e);
        }
    }

    /** The builder of q on the index, as IndexHarness's. */
    static UseIndexBuilder<DbObject> use(Connection rc, Def def, Query q) {
        UseIndexBuilder<DbObject> b = rc.useIndex(def.name, DbObject.class);
        for (Object v : q.eq) {
            if (v instanceof Long) {
                b.eq((Long) v);
            } else if (v instanceof Double) {
                b.eq((Double) v);
            } else if (v instanceof String) {
                b.eq((String) v);
            } else {
                b.eq(((Bin) v).bytes());
            }
        }
        if (q.from != null) {
            if (q.from instanceof Long) {
                b.from((Long) q.from, q.fromInclusive);
            } else if (q.from instanceof Double) {
                b.from((Double) q.from, q.fromInclusive);
            } else if (q.from instanceof String) {
                b.from((String) q.from, q.fromInclusive);
            } else {
                b.from(((Bin) q.from).bytes(), q.fromInclusive);
            }
        }
        if (q.to != null) {
            if (q.to instanceof Long) {
                b.to((Long) q.to, q.toInclusive);
            } else if (q.to instanceof Double) {
                b.to((Double) q.to, q.toInclusive);
            } else if (q.to instanceof String) {
                b.to((String) q.to, q.toInclusive);
            } else {
                b.to(((Bin) q.to).bytes(), q.toInclusive);
            }
        }
        if (q.prefix instanceof String) {
            b.prefix((String) q.prefix);
        } else if (q.prefix instanceof Bin) {
            b.prefix(((Bin) q.prefix).bytes());
        }
        if (q.backward) {
            b.backward();
        }
        return b;
    }

    /** Prints FAIL with the error and ends the process with status 3, at once. */
    static void fail(Throwable e) {
        java.io.StringWriter w = new java.io.StringWriter();
        e.printStackTrace(new java.io.PrintWriter(w));
        System.out.println("FAIL " + e);
        System.out.println(w);
        System.out.flush();
        Runtime.getRuntime().halt(3);
    }

    /**
     * The child: args child DIR SEED RUN (run|last) RETAIN_S STARTUP_DISTANCE_MB CACHE_MB
     * (Settings) CLOSE_AFTER_MS (a close() in the schedule after that time; below 0, a stop()
     * and a return from main after -CLOSE_AFTER_MS; 0 neither).
     */
    static void child(String[] a) throws IOException {
        Thread.setDefaultUncaughtExceptionHandler((t, e) -> fail(e));
        File dir = new File(a[1]);
        long seed = Long.parseLong(a[2]);
        int run = Integer.parseInt(a[3]);
        boolean last = a[4].equals("last");
        Settings settings = new Settings(Integer.parseInt(a[5]), Integer.parseInt(a[6]),
                Integer.parseInt(a[7]));
        int closeAfterMs = Integer.parseInt(a[8]);
        File jf = journalOf(dir);
        TreeMap<Integer, RunLog> logs = readJournal(jf);
        Journal journal = new Journal(jf);
        Random r = new Random(mix(seed, run, 7));
        int threads = 1 + r.nextInt(4);
        int stepValues = r.nextBoolean() ? 2 + r.nextInt(8) : 0;
        int stepSleep = r.nextInt(3) == 0 ? 0 : 1 + r.nextInt(8);
        int cleanupSleep = r.nextInt(3) == 0 ? 0 : 5 + r.nextInt(26);
        int commitLag = r.nextInt(3) == 0 ? 1 + r.nextInt(3) : 0;
        journal.line("R", run, threads, stepValues, stepSleep, cleanupSleep, commitLag);
        Child c = new Child(dir, seed, run, journal, logs);
        c.commitLag = commitLag;
        try {
            System.out.println("P open");
            c.open(settings, stepValues, stepSleep, cleanupSleep);
            System.out.println("P started");
            c.verify();
            System.out.println("P verified");
            boolean settle = last || r.nextInt(3) == 0;
            if (settle) {
                c.settle(r);
                System.out.println("P settled");
            }
            StringBuilder s = new StringBuilder("INFO");
            for (Map.Entry<String, Long> e : c.info.entrySet()) {
                s.append(' ').append(e.getKey()).append('=').append(e.getValue());
            }
            System.out.println(s);
            if (last) {
                c.db.close();
                System.out.println("P done");
                System.out.flush();
                return;
            }
            journal.line("OK", run);
            System.out.println("P running");
            c.schedule(threads, closeAfterMs);
            System.out.flush();     // A return from main after stop() (closeAfterMs < 0).
        } catch (Throwable e) {
            fail(e);
        }
    }

    static File journalOf(File dir) {
        return new File(dir.getParentFile(), dir.getName() + ".journal");
    }

    // ======== The parent ========

    /**
     * The phases that a kill aims at, by the line the child prints when it enters one: its
     * start, its checks, the waits for the builds and cleanups (in some runs), its schedule,
     * in the schedule right after a creation (its build runs) or a deletion (its cleanup
     * runs), and during or after a close() that the schedule makes after a random time; and
     * "exit", no kill: the schedule calls stop() and returns from main, and the JVM must end
     * with status 0 within 60 s. A kill aimed at build, cleanup or close that sees no such line
     * in 8 s after the schedule began is made then, and counted as "late".
     */
    static final String[] PHASES = {"open", "started", "verified", "running", "build",
            "cleanup", "late", "close", "exit"};

    /** A child's run: its output, whether it failed, its INFO counts. */
    static final class ChildRun {
        final StringBuilder out = new StringBuilder();
        String failure;
        /** A kill aimed after a creation or a deletion, made without one. */
        boolean late;
        final Map<String, Long> info = new TreeMap<String, Long>();
    }

    static ChildRun runChild(String java, String cp, File dir, long seed, int run, boolean last,
            Settings settings, int closeAfterMs, int phase, int delay)
            throws IOException, InterruptedException {
        ChildRun cr = new ChildRun();
        List<String> cmd = new ArrayList<String>(Arrays.asList(java, "-ea", "-Xmx400m",
                "-Dkillrestart.plant=" + System.getProperty("killrestart.plant", ""), "-cp", cp,
                KillRestartHarness.class.getName(), "child", dir.getPath(), Long.toString(seed),
                Integer.toString(run), last ? "last" : "run"));
        cmd.addAll(Arrays.asList(settings.args()));
        cmd.add(Integer.toString(closeAfterMs));
        Process p = new ProcessBuilder(cmd).redirectErrorStream(true).start();
        final LinkedBlockingQueue<String> lines = new LinkedBlockingQueue<String>();
        Thread reader = new Thread(() -> {
            try (BufferedReader in = new BufferedReader(new InputStreamReader(p.getInputStream(),
                    StandardCharsets.UTF_8))) {
                String line;
                while ((line = in.readLine()) != null) {
                    lines.add(line);
                }
            } catch (IOException e) {
                // The child was killed.
            }
            lines.add("\u0000EOF");
        });
        reader.start();
        String want = last ? "P done" : "P " + PHASES[phase];
        long deadline = System.currentTimeMillis() + 300000;
        long running = -1;
        boolean found = false;
        boolean eof = false;
        while (!found && !eof) {
            String line = lines.poll(100, TimeUnit.MILLISECONDS);
            if (line == null) {
                if (!last && phase >= 4 && running > 0
                        && System.currentTimeMillis() - running > 8000) {
                    found = true;
                    cr.late = true;
                } else if (System.currentTimeMillis() > deadline) {
                    cr.failure = "no \"" + want + "\" in 300 s: a hang";
                    break;
                }
                continue;
            }
            if (line.equals("\u0000EOF")) {
                eof = true;
                break;
            }
            cr.out.append(line).append('\n');
            if (line.equals("P running")) {
                running = System.currentTimeMillis();
            }
            found = line.equals(want);
        }
        if (found && !last && phase == 8 && !cr.late) {
            // stop() and a return from main: the JVM ends by itself, with status 0.
            if (!p.waitFor(60, TimeUnit.SECONDS)) {
                cr.failure = "stop() and a return from main: the JVM did not end in 60 s";
            } else if (p.exitValue() != 0) {
                cr.failure = "stop() and a return from main: the JVM ended with status "
                        + p.exitValue();
            } else {
                new Journal(journalOf(dir)).line("PX", run);
            }
        } else if (found && !last) {
            long end = System.currentTimeMillis() + delay;
            while (System.currentTimeMillis() < end && p.isAlive()) {
                Thread.sleep(Math.max(1, Math.min(10, end - System.currentTimeMillis())));
            }
            if (!p.isAlive()) {
                cr.failure = "the child ended before its kill, with status " + p.exitValue();
            }
        }
        if (last) {
            p.waitFor(60, TimeUnit.SECONDS);
        }
        p.destroyForcibly();
        p.waitFor();
        reader.join(10000);
        String line;
        while ((line = lines.poll()) != null) {
            if (!line.equals("\u0000EOF")) {
                cr.out.append(line).append('\n');
            }
        }
        for (String l : cr.out.toString().split("\n")) {
            if (l.startsWith("FAIL")) {
                cr.failure = l;
            } else if (l.startsWith("INFO")) {
                for (String kv : l.substring(4).trim().split(" ")) {
                    int eq = kv.indexOf('=');
                    if (eq > 0) {
                        cr.info.put(kv.substring(0, eq), Long.parseLong(kv.substring(eq + 1)));
                    }
                }
            }
        }
        if (cr.failure == null && last && (!found || p.exitValue() != 0)) {
            cr.failure = "the last run did not end with \"P done\" and status 0 (status "
                    + p.exitValue() + ")";
        }
        if (cr.failure == null && !found && !last) {
            cr.failure = "the child ended without \"" + want + "\", status " + p.exitValue();
        }
        return cr;
    }

    static void deleteTree(File f) {
        File[] children = f.listFiles();
        if (children != null) {
            for (File c : children) {
                deleteTree(c);
            }
        }
        f.delete();
    }

    /** The parent prints only its failure's line, as "Found: ..." (the self-check). */
    static boolean quiet;

    static void say(String s) {
        if (!quiet) {
            System.out.println(s);
        }
    }

    /** The parent: args parent BASE SEED KILLS [PER_DB [SECONDS]]. Returns the exit status. */
    static int parent(String[] a) throws IOException, InterruptedException {
        File base = new File(a[1]);
        long seed = Long.parseLong(a[2]);
        int kills = Integer.parseInt(a[3]);
        int perDb = a.length > 4 ? Integer.parseInt(a[4]) : 40;
        long seconds = a.length > 5 ? Long.parseLong(a[5]) : Long.MAX_VALUE / 2000;
        String java = System.getProperty("java.home") + "/bin/java";
        String cp = System.getProperty("java.class.path");
        base.mkdirs();
        Random r = new Random(seed);
        long t0 = System.currentTimeMillis();
        long end = t0 + seconds * 1000;
        int done = 0;
        int[] byPhase = new int[PHASES.length];
        int exits = 0;
        Map<String, Long> totals = new TreeMap<String, Long>();
        say("KillRestartHarness: seed " + seed + ", " + kills + " kills, a new "
                + "database every " + perDb + ", in " + base);
        for (int d = 0; done < kills && System.currentTimeMillis() < end; d++) {
            File dir = new File(base, "db" + d);
            deleteTree(dir);
            journalOf(dir).delete();
            long dbSeed = mix(seed, d);
            Settings settings = Settings.random(new Random(mix(dbSeed, 5)));
            say("Database " + d + ": " + settings);
            int dbKills = 0;
            for (int run = 1; ; run++) {
                boolean last = dbKills >= perDb || done >= kills
                        || System.currentTimeMillis() >= end;
                int k = r.nextInt(100);
                int phase = k < 12 ? 0 : k < 25 ? 1 : k < 33 ? 2 : k < 57 ? 3 : k < 72 ? 4
                        : k < 87 ? 5 : k < 95 ? 7 : 8;
                int delay = phase == 0 ? r.nextInt(250) : phase == 1 ? r.nextInt(150)
                        : phase == 2 ? r.nextInt(400) : phase == 3 ? (r.nextBoolean()
                        ? r.nextInt(300) : r.nextInt(2500)) : phase == 4 ? r.nextInt(300)
                        : phase == 5 ? r.nextInt(150) : r.nextInt(200);
                String forced = System.getProperty("killrestart.phase");
                if (forced != null && run % 2 == 0) {
                    // A probe: every second kill in the phase given, within killrestart.delay
                    // ms; the others as planned, so that the database has data and indexes.
                    phase = Arrays.asList(PHASES).indexOf(forced);
                    delay = r.nextInt(Integer.getInteger("killrestart.delay", 100) + 1);
                }
                int closeAfter = phase == 7 ? 50 + r.nextInt(1500)
                        : phase == 8 ? -(50 + r.nextInt(1500)) : 0;
                ChildRun cr = runChild(java, cp, dir, dbSeed, run, last, settings, closeAfter,
                        phase, delay);
                for (Map.Entry<String, Long> e : cr.info.entrySet()) {
                    Long v = totals.get(e.getKey());
                    totals.put(e.getKey(), (v == null ? 0 : v) + e.getValue());
                }
                if (cr.failure != null) {
                    say(cr.out.toString());
                    String why = quiet && cr.failure.length() > 300
                            ? cr.failure.substring(0, 300) + "..." : cr.failure;
                    System.out.println((quiet ? "Found: " : "KILL RESTART FAILED: ")
                            + why + "; seed " + seed
                            + ", database " + d + " (seed " + dbSeed + "; " + settings + "), run "
                            + run
                            + (last ? ", the last" : ", kill in phase " + PHASES[phase] + " + "
                            + delay + " ms") + "; kept: " + dir + " and " + journalOf(dir));
                    return 1;
                }
                if (last) {
                    break;
                }
                byPhase[cr.late ? 6 : phase]++;
                dbKills++;
                if (phase == 8 && !cr.late) {
                    exits++;            // Not a kill: the JVM ended by itself.
                    continue;
                }
                done++;
                if (done % 50 == 0) {
                    say(done + " kills, " + (System.currentTimeMillis() - t0) / 1000
                            + " s");
                }
            }
            deleteTree(dir);
            journalOf(dir).delete();
        }
        StringBuilder s = new StringBuilder();
        for (int i = 0; i < PHASES.length; i++) {
            s.append(i == 0 ? "" : ", ").append(PHASES[i]).append(' ').append(byPhase[i]);
        }
        s.append(" (exit: a stop() and a return from main, no kill)");
        say("Kills by phase: " + s);
        say("Counts: " + totals);
        say("KILL RESTART OK: " + done + " kills and " + exits + " exits in "
                + (System.currentTimeMillis() - t0) / 1000 + " s, seed " + seed);
        return 0;
    }

    /** The planted faults of the self-check. */
    static final String[] PLANTS = {"halfwrite", "nosync", "orphan", "stale"};

    /**
     * The harness's own check: each planted fault (PLANT) is found, in at most 60 kills or
     * 3 minutes each. Returns the exit status.
     */
    static int selfCheck(File base, long seed) throws IOException, InterruptedException {
        quiet = true;
        for (String plant : PLANTS) {
            System.setProperty("killrestart.plant", plant);
            File dir = new File(base, plant);
            int status = parent(new String[] {"parent", dir.getPath(), Long.toString(seed),
                    "60", "30", "180"});
            deleteTree(dir);
            if (status == 0) {
                System.out.println("SELF-CHECK FAILED: the planted fault " + plant
                        + " was not found");
                return 1;
            }
            System.out.println("The planted fault " + plant + " was found.");
        }
        System.clearProperty("killrestart.plant");
        System.out.println("SELF-CHECK OK: each planted fault was found");
        return 0;
    }

    public static void main(String[] args) throws Exception {
        if (args.length > 0 && args[0].equals("child")) {
            child(args);
        } else if (args.length >= 4 && args[0].equals("parent")) {
            System.exit(parent(args));
        } else if (args.length >= 3 && args[0].equals("selfcheck")) {
            System.exit(selfCheck(new File(args[1]), Long.parseLong(args[2])));
        } else {
            System.out.println("Usage: KillRestartHarness parent BASE SEED KILLS [PER_DB "
                    + "[SECONDS]] | selfcheck BASE SEED");
            System.exit(2);
        }
    }
}
