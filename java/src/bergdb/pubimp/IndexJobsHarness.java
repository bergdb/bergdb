package bergdb.pubimp;

import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;

import bergdb.core.Db;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.Kv;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.WBuilder;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.JobStatus.State;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.pubimp.IndexReference.Bin;
import bergdb.pubimp.IndexReference.Call;
import bergdb.pubimp.IndexReference.Def;
import bergdb.pubimp.IndexReference.Entry;
import bergdb.pubimp.IndexReference.Level;
import bergdb.pubimp.IndexReference.Type;
import bergdb.storage.StreamIoException;
import bergdb.stream.MemoryStream;

/**
 * Harness H3 of the user indexes: the jobs under faults (bergdb 020-10, section 9.3), in
 * the way of harness 6.2 (018-03). A run is a workload on a database in memory: values in
 * the directory /j/ (objects with the indexed fields, and values with no entry: an object
 * whose field is of another kind, a String and a byte[] at object keys, keys with a suffix,
 * a subdirectory), the creation of the index "j" and its build, the deletion of the index,
 * a creation of the name again at once (another definition, a new generation) and its build
 * while the old generation's cleanup runs, a few writes, a close and a restart. At the first
 * step of each build, another thread writes a value that the step read, so that its
 * transaction runs again. A fault is injected at the nth call of one point of the index
 * manager's test hook (Point): a refusal (DbException), an expiry
 * (LookupTimeNotAvailableException), an interrupt of the thread, a stop of the database, a
 * RuntimeException or an Error (Fault).
 *
 * <p>The checks, by the rules of 020-10, sections 3.2, 6.1 and 6.2, and of docs/levels.md,
 * section 3 (errors and interrupts):</p>
 * <ol>
 * <li><b>Calls.</b> A creation or a deletion that a fault refused before its commit threw
 *     the fault and changed nothing, in memory or in the stream, and the same call then
 *     works (015-23, S2-F27); after an interrupt the call works and the thread's flag is
 *     kept (005-46); a call that returned made its change, in memory and in the stream; a
 *     deletion frees the name at once.</li>
 * <li><b>Statuses.</b> Each build's last status: ACTIVE; BUILDING after a stop (S2-F11);
 *     FAILED with the cause's class and message after a RuntimeException (019-42); FAILED
 *     "deleted" after a deletion during the build. A refusal, an expiry and an interrupt are
 *     taken again (019-38, 015-37). Every status read earlier is unchanged (a snapshot,
 *     015-39); a status's count is the values that its committed steps read.</li>
 * <li><b>Failures.</b> The database fails after an Error, and the call in the caller's thread
 *     throws the Error as it is; it fails after nothing else but a throw after a commit,
 *     where failing is one of the two outcomes allowed (the other: the call returns, its
 *     change made).</li>
 * <li><b>Memory and stream agree</b> when no job runs: the definition, and the markers
 *     (none, but the one of a cleanup that a RuntimeException ended: a start resumes it).</li>
 * <li><b>Entries.</b> An active index's entries are the index function of the directory's
 *     values (IndexReference), a building one's a part of them with no stale entry, and no
 *     other generation has an entry once its marker is gone.</li>
 * <li><b>Restart.</b> A start on the stream works; the definition is the one the calls left
 *     (for a database that did not fail); a build that a fault ended is resumed and ends
 *     ACTIVE, an index active at the start has a job ACTIVE with count 0; every marker goes
 *     (the cleanup resumed); the entries are the function of the data read back, and no
 *     other generation's entry is left; the data is the data the calls wrote.</li>
 * <li><b>No hang, no thread left.</b> Every call and join returns within its bound, and no
 *     thread of BergDB is alive two seconds after a close.</li>
 * </ol>
 *
 * <p>The unit test injects every fault at every point once (a middle step of the first
 * build, the second step of the cleanup), with 110 objects, so that the cleanup takes two
 * steps (IndexManager.CLEANUP_KEYS = 100) and a build five (IndexBuilderImp.STEP_VALUES =
 * 25). The night test injects every fault at every call of every point with 500 objects,
 * then random runs with a writer thread and deletions during a build. main() repeats a
 * night's runs by its seed. The faults that the harness finds and that are not fixed yet
 * are in KNOWN.</p>
 *
 * @author Frans Lundberg
 */
public final class IndexJobsHarness {
    private IndexJobsHarness() {}

    /** The index's name, and its directory. */
    static final String NAME = "j";
    static final String DIR = "/j/";

    private static final long LATEST = Long.MAX_VALUE;

    /** The bound of a call or a join (a hang beyond it is a finding), ms. */
    static final int JOIN_MS = 10000;

    /** The longest wait for a cleanup to remove its marker, ms. */
    static final int CLEANUP_MS = 5000;

    /** The longest wait for BergDB's threads to end after a close, ms. */
    static final int THREADS_MS = 2000;

    /** The objects of the unit test's runs: a cleanup of two steps. */
    static final int UNIT_OBJECTS = IndexManager.CLEANUP_KEYS + 10;

    /** The objects of the night test's runs (bergdb 020-10, section 9.3). */
    static final int NIGHT_OBJECTS = 500;

    /** The first creation's definition: one long level on n. */
    static final Def DEF1 = new Def(NAME, DIR, Arrays.asList(
            new Level(Type.LONG, Call.FIELD, "n")));

    /** The second creation's, of the same name: a string level on s, then a long on n. */
    static final Def DEF2 = new Def(NAME, DIR, Arrays.asList(
            new Level(Type.STRING, Call.FIELD, "s"), new Level(Type.LONG, Call.FIELD, "n")));

    private static final IndexReference REF = new IndexReference();

    // ======== The values ========

    /** An object of the directory: a Data Object (bergdb 020-09) with both indexed fields. */
    public static class Item {
        public long n;
        public String s;

        public Item() {}

        Item(long n, String s) {
            this.n = n;
            this.s = s;
        }
    }

    /** An object whose field n is a String: no entry in a long level (020-10, 3.3). */
    public static class Other {
        public String n;

        public Other() {}

        Other(String n) {
            this.n = n;
        }
    }

    /** The strings of the field s; null leaves it out (no entry in DEF2). */
    private static final String[] STRINGS = {"a", "b", "é", "😀", "a\u0000", null};

    /** A value as the harness wrote it: its Java value for IndexReference and its bytes. */
    static final class Val {
        final Object value;
        final Bin bytes;

        Val(Object value, Bin bytes) {
            this.value = value;
            this.bytes = bytes;
        }

        public String toString() {
            return IndexReference.show(value);
        }
    }

    /**
     * The Java value (a Map for an object, a String, or a Bin) and the stored bytes of a value
     * that the workload puts: an Item, an Other, a String (its UTF-8) or a byte[] (as it is).
     */
    static Val val(Object o) {
        if (o instanceof Item) {
            Item item = (Item) o;
            TreeMap<String, Object> map = new TreeMap<String, Object>();
            map.put("n", item.n);
            if (item.s != null) {
                map.put("s", item.s);
            }
            return new Val(map, new Bin(DbObject.toDbObject(item).getBytes()));
        } else if (o instanceof Other) {
            TreeMap<String, Object> map = new TreeMap<String, Object>();
            map.put("n", ((Other) o).n);
            return new Val(map, new Bin(DbObject.toDbObject(o).getBytes()));
        } else if (o instanceof String) {
            return new Val(o, new Bin(((String) o).getBytes(StandardCharsets.UTF_8)));
        }
        Bin b = new Bin((byte[]) o);
        return new Val(b, b);
    }

    static String key(int i) {
        return String.format("%sk%03d", DIR, i);
    }

    // ======== The points and the faults ========

    /** A point of IndexManager.testHook where the harness injects a fault (I2's contract). */
    enum Point {
        CREATE_BEFORE(IndexManager.DEFINITION_BEFORE + "create"),
        CREATE_AFTER(IndexManager.DEFINITION_AFTER + "create"),
        BUILD_STEP(IndexManager.BUILD_STEP),
        ACTIVATE_BEFORE(IndexManager.DEFINITION_BEFORE + "activate"),
        ACTIVATE_AFTER(IndexManager.DEFINITION_AFTER + "activate"),
        DELETE_BEFORE(IndexManager.DEFINITION_BEFORE + "delete"),
        DELETE_AFTER(IndexManager.DEFINITION_AFTER + "delete"),
        CLEANUP_STEP(IndexManager.CLEANUP_STEP),
        CLEANUP_END(IndexManager.CLEANUP_END);

        final String hook;

        Point(String hook) {
            this.hook = hook;
        }

        /** The point of a hook's string, or null for a write's points and any other. */
        static Point of(String hook) {
            for (Point p : values()) {
                if (p.hook.equals(hook)) {
                    return p;
                }
            }
            return null;
        }

        /** A creation's or a deletion's: in the thread of the call. */
        boolean inCall() {
            return this == CREATE_BEFORE || this == CREATE_AFTER || this == DELETE_BEFORE
                    || this == DELETE_AFTER;
        }

        /** A build's: in its thread. */
        boolean inBuild() {
            return this == BUILD_STEP || this == ACTIVATE_BEFORE || this == ACTIVATE_AFTER;
        }

        /** A cleanup's: in its thread. */
        boolean inCleanup() {
            return this == CLEANUP_STEP || this == CLEANUP_END;
        }

        /** After its definition's transaction committed. */
        boolean afterCommit() {
            return this == CREATE_AFTER || this == ACTIVATE_AFTER || this == DELETE_AFTER;
        }
    }

    /** A fault that the hook makes at its point (bergdb 020-10, section 9.3). */
    enum Fault {
        REFUSAL, EXPIRY, INTERRUPT, STOP, RUNTIME, ERROR;

        boolean throwsIt() {
            return this == REFUSAL || this == EXPIRY || this == RUNTIME || this == ERROR;
        }

        Throwable make(String message) {
            switch (this) {
            case REFUSAL:
                return new DbException(message);
            case EXPIRY:
                return new LookupTimeNotAvailableException(message);
            case RUNTIME:
                return new InjectedBug(message);
            case ERROR:
                return new InjectedError(message);
            default:
                throw new IllegalStateException(this + " is not thrown");
            }
        }
    }

    /** The RuntimeException that the harness injects: a bug, neither a refusal nor an expiry. */
    static final class InjectedBug extends RuntimeException {
        private static final long serialVersionUID = 1L;

        InjectedBug(String message) {
            super(message);
        }
    }

    /** The Error that the harness injects. */
    static final class InjectedError extends Error {
        private static final long serialVersionUID = 1L;

        InjectedError(String message) {
            super(message);
        }
    }

    // ======== A run's configuration ========

    /** What a run does: the fault, where; the workload's size and variants. */
    static final class Config {
        /** The point of the fault, or null for none. */
        Point point;
        /** The call of the point that gets the fault: 1 for the first. */
        int n = 1;
        Fault fault;
        int objects = UNIT_OBJECTS;
        long seed = 1;
        /** At each build's first step, another thread writes two values (one the step read). */
        boolean racingWrites = true;
        /** At the first build's third step call, another thread deletes the index. */
        boolean deleteDuringBuild;
        /** A thread writes the directory, its own keys, while the jobs run. */
        boolean writer;

        Config() {}

        Config(Point point, int n, Fault fault) {
            this.point = point;
            this.n = n;
            this.fault = fault;
        }

        public String toString() {
            return (point == null ? "no fault" : fault + " at " + point + " " + n) + ", "
                    + objects + " objects, seed " + seed + (racingWrites ? "" : ", no racing writes")
                    + (deleteDuringBuild ? ", deleted during the build" : "")
                    + (writer ? ", a writer" : "");
        }
    }

    /** A status as read: the object, and its values at the read. */
    static final class Snap {
        final int build;
        final String where;
        final JobStatus status;
        final State state;
        final long count;
        final String reason;
        final String note;

        Snap(int build, String where, JobStatus status) {
            this.build = build;
            this.where = where;
            this.status = status;
            this.state = status.state();
            this.count = status.count();
            this.reason = status.reason();
            this.note = status.note();
        }

        /** The values the status gives now, if they differ from those read; else null. */
        String changed() {
            if (status.state() != state || status.count() != count
                    || !Objects.equals(status.reason(), reason)
                    || !Objects.equals(status.note(), note)) {
                return status.state() + " " + status.count() + " " + status.reason() + " \""
                        + status.note() + "\"";
            }
            return null;
        }

        public String toString() {
            return "build " + build + " " + where + ": " + state + ", count " + count
                    + ", reason " + reason + ", \"" + note + "\"";
        }
    }

    /** What a call returned or threw, and whether it left the thread's interrupt flag set. */
    static final class Outcome {
        final String what;
        Object result;
        Throwable thrown;
        boolean interrupted;
        long ms;

        Outcome(String what) {
            this.what = what;
        }

        boolean returned() {
            return thrown == null;
        }

        public String toString() {
            return what + (thrown == null ? " returned" : " threw " + describe(thrown));
        }
    }

    // ======== A run ========

    /** One run: the workload with its fault, the checks, the findings. */
    static final class Run {
        final Config cfg;
        final List<String[]> findings = Collections.synchronizedList(new ArrayList<String[]>());
        final Thread main = Thread.currentThread();
        MemoryStream stream;
        volatile Database db;

        // The hook's state.
        private final int[] calls = new int[Point.values().length];
        volatile boolean fired;
        volatile Thread firedThread;
        /** The call in whose thread the fault fired, if a call's point. */
        volatile String firedCall;
        /** The build in whose thread the fault fired, or 0. */
        volatile int firedBuild;
        /** The count that the build's status gave at the fault, or -1. */
        volatile long firedCount = -1;
        volatile Throwable injected;
        /** The call that each thread of the workload makes now. */
        final Map<Thread, String> currentCall = new ConcurrentHashMap<Thread, String>();
        /** The build that the latest creation started: 1 or 2. */
        volatile int building;
        final Map<Thread, Integer> buildOfThread = new ConcurrentHashMap<Thread, Integer>();
        final int[] buildSteps = new int[3];
        final Job[] jobs = new Job[3];
        final JobStatus[] finals = new JobStatus[3];
        final int[] ownAtCreation = new int[3];
        final List<Snap> snaps = new ArrayList<Snap>();

        // The data: each key's value by the calls that returned; every value's bytes.
        final TreeMap<String, Val> model = new TreeMap<String, Val>();
        final Map<Bin, Object> known = new ConcurrentHashMap<Bin, Object>();

        // What the stream must hold.
        /** The generation of the name's definition by the calls that returned; 0: none. */
        long expectGen;
        /** The generations of the run's creations that returned. */
        final Set<Long> gens = new TreeSet<Long>();
        /** The generation whose cleanup a RuntimeException ended: its marker stays. */
        volatile long stuckMarker;
        volatile boolean deletedDuringBuild;
        /** The database failed (a read threw DbFailedException); its failure. */
        volatile boolean failed;
        volatile Throwable failure;
        int retries;
        JobStatus restartStatus;
        /**
         * A finding left the run's state unknown (an Error or a throw after a commit, and the
         * database went on): the workload stops, and the restart's checks of what the calls
         * left are not made.
         */
        volatile boolean broken;
        Writer writer;
        final Set<Thread> before = bergdbThreads();

        Run(Config cfg) {
            this.cfg = cfg;
        }

        void finding(String check, String message) {
            findings.add(new String[] {check, message});
        }

        // ======== The run ========

        void execute() {
            stream = new MemoryStream();
            db = start(stream);
            try {
                manager(db).testHook = this::hook;
                Connection c = db.newConnection();
                putData(c);
                c.sync();
                if (cfg.writer) {
                    writer = new Writer(this, cfg.seed);
                    writer.start();
                }
                live(c);
            } catch (RuntimeException | Error e) {
                finding("workload", "it threw " + describe(e) + "\n" + stack(e));
            } finally {
                stopWriter();
                closeAndCheck(db, "the live database");
            }
            checkSnapshots("after the close");
            restart();
        }

        /** The live phase: creation, build, deletion, creation at once, cleanup, writes. */
        private void live(Connection c) {
            Job job1 = create(1, DEF1, false);
            if (job1 != null) {
                joinBuild(1);
            }
            if (broken || !alive("after the first build")) {
                return;
            }
            if (!deletedDuringBuild) {
                if (!deleteCall("the deletion") || broken || !alive("after the deletion")) {
                    return;
                }
            }
            Job job2 = create(2, DEF2, false);
            if (job2 != null) {
                joinBuild(2);
            }
            if (broken || !alive("after the second build")) {
                return;
            }
            if (!awaitCleanup() || !alive("after the cleanup")) {
                return;
            }
            stopWriter();
            writes(c);
            if (!alive("after the writes")) {
                return;
            }
            checkLive();
        }

        private void stopWriter() {
            if (writer != null) {
                writer.finish();
                writer = null;
            }
        }

        // ======== The hook ========

        void hook(String hook) {
            Point point = Point.of(hook);
            if (point == null) {
                return;
            }
            int n;
            synchronized (calls) {
                n = ++calls[point.ordinal()];
            }
            Thread t = Thread.currentThread();
            int b = 0;
            long count = -1;
            if (point.inBuild()) {
                Integer bo = buildOfThread.get(t);
                if (bo == null) {
                    bo = building;
                    buildOfThread.put(t, bo);
                }
                b = bo;
                if (point == Point.BUILD_STEP) {
                    int k = ++buildSteps[b];
                    Snap s = snapshot(b, "at step call " + k);
                    count = s == null ? -1 : s.count;
                    workloadAtStep(b, k);
                }
            }
            if (!fired && point == cfg.point && n == cfg.n) {
                fired = true;
                firedThread = t;
                firedCall = currentCall.get(t);
                firedBuild = b;
                firedCount = count;
                inject(point + " " + n + " in " + t.getName());
            }
        }

        private void inject(String where) {
            switch (cfg.fault) {
            case INTERRUPT:
                Thread.currentThread().interrupt();
                return;
            case STOP:
                db.stop();
                return;
            default:
                Throwable e = cfg.fault.make("H3: " + cfg.fault + " injected at " + where);
                injected = e;
                if (e instanceof Error) {
                    throw (Error) e;
                }
                throw (RuntimeException) e;
            }
        }

        /** The workload's own actions at a build's step: racing writes, a deletion. */
        private void workloadAtStep(int b, int k) {
            if (cfg.racingWrites && k == 1) {
                helper("the racing writes of build " + b, () -> {
                    Map<String, Object> w = new LinkedHashMap<String, Object>();
                    w.put(key(0), new Item(1000 + b, "r" + b));
                    w.put(key(cfg.objects - 1), new Item(2000 + b, null));
                    Connection c = db.newConnection();
                    write(c, w, "racing writes");
                    c.sync();
                });
            }
            if (cfg.deleteDuringBuild && b == 1 && k == 3) {
                helper("a deletion during build 1", () -> {
                    if (deleteCall("a deletion during build 1")) {
                        deletedDuringBuild = true;
                    }
                });
            }
        }

        /** Runs r in another thread and waits for it; a stop or a failure in it is no finding. */
        private void helper(String what, Runnable r) {
            Thread t = new Thread(() -> {
                try {
                    r.run();
                } catch (RuntimeException | Error e) {
                    if (!isStopOrFailure(e)) {
                        finding("workload", what + " threw " + describe(e) + "\n" + stack(e));
                    }
                }
            }, "IndexJobsHarness-helper");
            t.start();
            // An interrupt flag that a fault left on this thread does not end the wait; the
            // flag is set again after it.
            boolean interrupted = false;
            long end = System.nanoTime() + JOIN_MS * 1000000L;
            while (t.isAlive() && System.nanoTime() < end) {
                try {
                    t.join(Math.max(1, (end - System.nanoTime()) / 1000000));
                } catch (InterruptedException e) {
                    interrupted = true;
                }
            }
            if (interrupted) {
                Thread.currentThread().interrupt();
            }
            if (t.isAlive()) {
                finding("hang", what + " did not end in " + JOIN_MS + " ms:\n"
                        + stack(t.getStackTrace()));
            }
        }

        // ======== The data ========

        private void putData(Connection c) {
            Random r = new Random(cfg.seed);
            Map<String, Object> w = new LinkedHashMap<String, Object>();
            for (int i = 0; i < cfg.objects; i++) {
                w.put(key(i), new Item(r.nextInt(Math.max(4, cfg.objects / 4)) - 5,
                        STRINGS[r.nextInt(STRINGS.length)]));
                if (w.size() == 50) {
                    write(c, w, "the data");
                    w.clear();
                }
            }
            w.put(DIR + "other", new Other("7"));
            w.put(DIR + "text", "text");
            w.put(DIR + "bytes", new byte[] {1, 2, 3});
            w.put(DIR + "x.txt", "t");
            w.put(DIR + "y.obj", new Item(3, "y"));
            w.put(DIR + "z.bin", DbObject.toDbObject(new Item(4, "z")).getBytes());
            w.put(DIR + "sub/k", new Item(1, "s"));
            w.put("/q/k", new Item(2, "q"));
            write(c, w, "the data");
        }

        /** The writes after the jobs: a delete, a String over an object, and back, new keys. */
        private void writes(Connection c) {
            Map<String, Object> w = new LinkedHashMap<String, Object>();
            w.put(key(1), null);
            w.put(key(2), "a String over an object");
            w.put(DIR + "text", new Item(7, "b"));
            w.put(DIR + "new", new Item(-3, "a"));
            w.put(DIR + "sub/k2", new Item(5, "s"));
            Outcome o = call("the writes", () -> {
                write(c, w, "the writes");
                c.sync();
                return null;
            });
            if (!o.returned() && !isStopOrFailure(o.thrown)) {
                finding("workload", o.toString());
            }
        }

        /** A transaction of puts (and deletes, a null value); the model takes it when it returns. */
        void write(Connection c, Map<String, Object> ops, String what) {
            Map<String, Val> vals = new LinkedHashMap<String, Val>();
            WBuilder w = c.w();
            for (Map.Entry<String, Object> e : ops.entrySet()) {
                if (e.getValue() == null) {
                    w.delete(e.getKey());
                    vals.put(e.getKey(), null);
                } else {
                    w.put(e.getKey(), e.getValue());
                    Val v = val(e.getValue());
                    known.put(v.bytes, v.value);
                    vals.put(e.getKey(), v);
                }
            }
            w.execute();
            synchronized (model) {
                for (Map.Entry<String, Val> e : vals.entrySet()) {
                    if (e.getValue() == null) {
                        model.remove(e.getKey());
                    } else {
                        model.put(e.getKey(), e.getValue());
                    }
                }
            }
        }

        /** The directory's own values in the model, as IndexReference takes them. */
        Map<String, Object> ownValues() {
            TreeMap<String, Object> values = new TreeMap<String, Object>();
            synchronized (model) {
                for (Map.Entry<String, Val> e : model.entrySet()) {
                    if (IndexReference.Model.inDir(e.getKey(), DIR)) {
                        values.put(e.getKey(), e.getValue().value);
                    }
                }
            }
            return values;
        }

        // ======== The calls ========

        /** Makes a call in this thread, labelled 'what' for the hook; times it. */
        Outcome call(String what, Supplier<Object> f) {
            Thread t = Thread.currentThread();
            currentCall.put(t, what);
            Outcome o = new Outcome(what);
            long t0 = System.nanoTime();
            try {
                o.result = f.get();
            } catch (RuntimeException | Error e) {
                o.thrown = e;
            } finally {
                currentCall.remove(t);
            }
            o.ms = (System.nanoTime() - t0) / 1000000;
            o.interrupted = Thread.interrupted();
            if (o.ms >= JOIN_MS) {
                finding("hang", what + " took " + o.ms + " ms");
            }
            return o;
        }

        /** Whether the fault fired in the call o. */
        boolean firedIn(Outcome o) {
            return fired && o.what.equals(firedCall);
        }

        /**
         * Creation b of the definition def; returns its build's job, or null if it was not
         * made, or the database stopped or failed. A refusal by the fault is checked, and the
         * creation made again.
         */
        Job create(int b, Def def, boolean again) {
            String what = "creation " + b + (again ? " (again)" : "");
            IndexDefinition memBefore = manager(db).definition(NAME);
            IndexDefinition streamBefore = streamDefinition();
            if (memBefore != null) {
                finding("workload", what + ": the name is in use: " + memBefore);
            }
            synchronized (model) {
                ownAtCreation[b] = ownValues().size();
            }
            building = b;
            Outcome o = call(what, () -> startIndex(db, def));
            if (o.thrown instanceof IndexAlreadyExistsException) {
                finding("name free at once", what + " threw " + describe(o.thrown)
                        + ": a deletion that returned frees the name at once (020-10, 3.2)");
                return null;
            }
            int done = checkCall(o, memBefore, streamBefore);
            if (done == REFUSED) {
                retries++;
                return create(b, def, true);
            }
            if (done != DONE || !o.returned()) {
                return null;
            }
            Job job = (Job) o.result;
            jobs[b] = job;
            snapshot(b, "after start()");
            IndexDefinition d = manager(db).definition(NAME);
            if (d == null) {
                if (alive(what)) {
                    finding("call made its change", what + " returned, and memory has no "
                            + "definition");
                }
                return job;
            }
            for (long g : gens) {
                if (d.gen() <= g) {
                    finding("generation", what + ": generation " + d.gen() + ", not above an "
                            + "earlier creation's " + g + " (020-10, 4.3)");
                }
            }
            gens.add(d.gen());
            expectGen = d.gen();
            if (!sameLevels(def(d), def)) {
                finding("definition", what + ": memory has " + d + ", not " + def);
            }
            if (alive(what)) {
                IndexDefinition s = streamDefinition();
                if (s == null || s.gen() != d.gen()) {
                    finding("call made its change", what + " returned; memory has " + d
                            + ", the stream " + s);
                }
            }
            return job;
        }

        /** Deletes the index; true if it was deleted. A refusal is checked, and made again. */
        boolean deleteCall(String what) {
            IndexDefinition memBefore = manager(db).definition(NAME);
            IndexDefinition streamBefore = streamDefinition();
            Outcome o = call(what, () -> {
                db.deleteIndex(NAME);
                return null;
            });
            int done = checkCall(o, memBefore, streamBefore);
            if (done == REFUSED) {
                retries++;
                return deleteCall(what + " (again)");
            }
            if (done != DONE) {
                return false;
            }
            expectGen = 0;
            if (o.returned()) {
                IndexDefinition d = manager(db).definition(NAME);
                if (d != null) {
                    finding("name free at once", what + " returned, and memory still has " + d);
                }
                if (alive(what)) {
                    IndexDefinition s = streamDefinition();
                    if (s != null) {
                        finding("name free at once", what + " returned, and the stream still "
                                + "has " + s);
                    }
                    try {
                        db.indexJob(NAME);
                        finding("name free at once", what + " returned, and indexJob() "
                                + "still gives a job");
                    } catch (NoSuchIndexException e) {
                        // Expected.
                    }
                    if (memBefore != null) {
                        checkMarkerOrClean(memBefore.gen(), what);
                    }
                }
            }
            return true;
        }

        /**
         * After a deletion of the generation gen returned: its marker is in the stream, or its
         * cleanup is done already (no entry): the definition's delete and the marker are one
         * transaction (020-10, 6.2).
         */
        private void checkMarkerOrClean(long gen, String what) {
            for (IndexKeys.Marker m : manager(db).markers(LATEST)) {
                if (m.name.equals(NAME) && m.gen == gen) {
                    return;
                }
            }
            if (!rawKeys(dbOf(db), IndexKeys.generationPrefix(NAME, gen)).isEmpty()) {
                finding("deletion", what + " returned: no marker of generation " + gen
                        + ", and its entries are there");
            }
        }

        static final int DONE = 1, NOT_DONE = 0, REFUSED = -1;

        /**
         * The checks of a creation's or a deletion's call by the fault that fired in it, if
         * any; returns DONE if its change is made (in the stream, also when the database then
         * failed), REFUSED if the fault refused it and the database goes on (the workload
         * then makes it again), NOT_DONE else.
         */
        int checkCall(Outcome o, IndexDefinition memBefore, IndexDefinition streamBefore) {
            if (!firedIn(o)) {
                if (o.returned()) {
                    return DONE;
                }
                if (!isStopOrFailure(o.thrown) || alive(o.what)) {
                    finding("call", o + " with no fault in it\n" + stack(o.thrown));
                }
                return NOT_DONE;
            }
            Point p = cfg.point;
            Fault f = cfg.fault;
            switch (f) {
            case INTERRUPT:
                if (!o.interrupted) {
                    finding("interrupt flag kept", o.what + " cleared the thread's interrupt "
                            + "flag (docs/levels.md, section 3; 005-46)");
                }
                if (o.returned()) {
                    return DONE;
                }
                if (o.thrown instanceof DbException && !isStopOrFailure(o.thrown)) {
                    checkUnchanged(o, memBefore, streamBefore);
                    return alive(o.what) ? REFUSED : NOT_DONE;
                }
                finding("interrupt", "after an interrupt at " + p + ", " + o
                        + ": an interrupt fails no call (005-46)\n" + stack(o.thrown));
                return NOT_DONE;
            case STOP:
                if (o.returned()) {
                    return DONE;
                }
                if (p.afterCommit()) {
                    finding("stop after the commit", o + " after its commit: its change is "
                            + "made, and the caller told otherwise");
                    return DONE;
                }
                if (!isStop(o.thrown)) {
                    finding("stop", "after a stop at " + p + ", " + o + ": a stop fails "
                            + "nothing\n" + stack(o.thrown));
                }
                checkMemoryUnchanged(o, memBefore);
                return NOT_DONE;
            case ERROR:
                if (o.thrown != injected) {
                    finding("Error as it is", o + ", not the Error injected at " + p
                            + " as it is (docs/levels.md, section 3)");
                }
                alive(o.what);      // A finding if the database goes on.
                return p.afterCommit() ? DONE : NOT_DONE;
            default:
                // A refusal, an expiry or a bug.
                if (!p.afterCommit()) {
                    if (o.returned()) {
                        finding("refusal thrown", o + " after the " + f + " injected before "
                                + "its commit (020-10, 3.2: refused or done)");
                        return DONE;
                    }
                    if (!inChain(o.thrown, injected)) {
                        finding("refusal thrown", o + ", not the " + f + " injected before "
                                + "its commit (020-10, 3.2: refused or done)");
                    }
                    checkUnchanged(o, memBefore, streamBefore);
                    return alive(o.what) ? REFUSED : NOT_DONE;
                }
                if (o.returned()) {
                    return DONE;
                }
                if (alive(o.what)) {
                    finding("throw after the commit", o + " after its commit, and the database "
                            + "goes on with the change made: refused or done (020-10, 3.2); "
                            + "an exception after a commit fails the database (docs/levels.md, "
                            + "section 3)");
                    broken = true;
                }
                return DONE;
            }
        }

        /** A refused call changed nothing: memory, the stream, the markers; no job. */
        private void checkUnchanged(Outcome o, IndexDefinition memBefore,
                IndexDefinition streamBefore) {
            checkMemoryUnchanged(o, memBefore);
            if (!alive(o.what)) {
                return;
            }
            IndexDefinition s = streamDefinition();
            if (!Objects.equals(s, streamBefore)) {
                finding("refused changes nothing", o + ": the stream has " + s + ", before "
                        + streamBefore + " (015-23, S2-F27)");
            }
            if (memBefore == null) {
                try {
                    db.indexJob(NAME);
                    finding("refused changes nothing", o + ": indexJob() gives a job");
                } catch (NoSuchIndexException e) {
                    // Expected.
                }
                int other = 0;
                for (byte[] k : rawKeys(dbOf(db), namePrefix())) {
                    boolean earlier = false;
                    for (long g : gens) {
                        earlier |= IndexKeys.startsWith(k, IndexKeys.generationPrefix(NAME, g));
                    }
                    other += earlier ? 0 : 1;
                }
                if (other > 0) {
                    finding("refused changes nothing", o + ": " + other + " entries of the "
                            + "name in a generation no creation made");
                }
            } else {
                for (IndexKeys.Marker m : manager(db).markers(LATEST)) {
                    if (m.gen == memBefore.gen()) {
                        finding("refused changes nothing", o + ": a marker of the index");
                    }
                }
                // The index is still kept: a write, then its entries.
                Map<String, Object> w = new LinkedHashMap<String, Object>();
                w.put(key(3), new Item(-1, "a"));
                write(db.newConnection(), w, "a write after the refusal");
                checkEntries(memBefore, ownValues(), "after a refused deletion and a write");
            }
        }

        private void checkMemoryUnchanged(Outcome o, IndexDefinition memBefore) {
            IndexDefinition m = manager(db).definition(NAME);
            if (!Objects.equals(m, memBefore)) {
                finding("refused changes nothing", o + ": memory has " + m + ", before "
                        + memBefore + " (015-23, S2-F27)");
            }
        }

        // ======== The builds and the cleanup ========

        /** Takes a status of build b's job and keeps it; null if there is no job yet. */
        Snap snapshot(int b, String where) {
            Job job = jobs[b];
            if (job == null) {
                return null;
            }
            synchronized (snaps) {
                Snap s = new Snap(b, where, job.getStatus());
                snaps.add(s);
                return s;
            }
        }

        /** Waits for build b and checks its last status. */
        void joinBuild(int b) {
            long t0 = System.nanoTime();
            JobStatus st = jobs[b].join(JOIN_MS);
            long ms = (System.nanoTime() - t0) / 1000000;
            if (Thread.interrupted()) {
                finding("workload", "the workload's thread was interrupted in join()");
            }
            synchronized (snaps) {
                snaps.add(new Snap(b, "join()", st));
            }
            finals[b] = st;
            if (st.state() == State.BUILDING && ms >= JOIN_MS - 100) {
                finding("hang", "build " + b + " did not end in " + JOIN_MS + " ms");
            }
            boolean up = alive("after build " + b);
            checkFinal(b, st, up);
            if (up && st.state() != State.BUILDING) {
                IndexDefinition d = manager(db).definition(NAME);
                if (d != null && d.isActive() != (st.state() == State.ACTIVE)) {
                    finding("memory and stream", "build " + b + " is " + st.state()
                            + ", and memory has " + d);
                }
                IndexDefinition str = streamDefinition();
                if (!Objects.equals(d, str)) {
                    finding("memory and stream", "build " + b + " ended " + st.state()
                            + "; memory has " + d + ", the stream " + str);
                }
                if (d != null && !deletedDuringBuild) {
                    try {
                        State s = db.indexJob(NAME).getStatus().state();
                        if (s != st.state()) {
                            finding("indexJob", "indexJob() of build " + b + " is " + s
                                    + ", its job " + st.state() + " (020-10, 3.2)");
                        }
                    } catch (NoSuchIndexException e) {
                        finding("indexJob", "indexJob() of build " + b + ": " + describe(e));
                    }
                }
            }
        }

        /** Build b's last status, by the fault (020-10, sections 3.2 and 6.1). */
        void checkFinal(int b, JobStatus st, boolean up) {
            State s = st.state();
            Set<State> allowed;
            String rule;
            boolean countAtFault = false;
            if (fired && firedBuild == b) {
                Fault f = cfg.fault;
                if (cfg.point == Point.ACTIVATE_AFTER) {
                    allowed = up || f == Fault.INTERRUPT || f == Fault.STOP
                            ? EnumSet.of(State.ACTIVE) : EnumSet.allOf(State.class);
                    rule = "after the activation's commit, ACTIVE, unless the database failed";
                } else if (f == Fault.STOP) {
                    allowed = EnumSet.of(State.BUILDING);
                    rule = "BUILDING after a stop (S2-F11)";
                    countAtFault = cfg.point == Point.BUILD_STEP;
                } else if (f == Fault.RUNTIME) {
                    allowed = EnumSet.of(State.FAILED);
                    rule = "FAILED after a RuntimeException (019-42)";
                    countAtFault = cfg.point == Point.BUILD_STEP;
                    if (s == State.FAILED && !namesInjected(st.reason())) {
                        finding("status", "build " + b + ": the reason \"" + st.reason()
                                + "\" does not give the class and message of " + injected
                                + " (020-10, 3.2)");
                    }
                } else if (f == Fault.ERROR) {
                    allowed = EnumSet.of(State.BUILDING, State.FAILED);
                    rule = "an Error ends the build and fails the database";
                } else {
                    allowed = EnumSet.of(State.ACTIVE);
                    rule = "a refusal, an expiry and an interrupt are taken again (019-38, "
                            + "015-37)";
                }
            } else if (cfg.deleteDuringBuild && b == 1 && deletedDuringBuild) {
                allowed = up ? EnumSet.of(State.FAILED) : EnumSet.of(State.FAILED, State.BUILDING);
                rule = "FAILED \"deleted\" after a deletion during the build (020-10, 3.2)";
                if (s == State.FAILED && (st.reason() == null || !st.reason().contains("deleted"))) {
                    finding("status", "build " + b + " deleted during the build: the reason "
                            + "is \"" + st.reason() + "\", not \"deleted\"");
                }
            } else if (!up) {
                allowed = EnumSet.of(State.ACTIVE, State.BUILDING);
                rule = "a build that a stop or a failure of the database ends is BUILDING";
            } else {
                allowed = EnumSet.of(State.ACTIVE);
                rule = "with no fault, a build ends ACTIVE";
            }
            if (!allowed.contains(s)) {
                finding("status", "build " + b + " ended " + s + " (" + st.note() + "), not "
                        + allowed + ": " + rule);
            }
            if (s == State.FAILED && st.reason() == null || s != State.FAILED && st.reason() != null) {
                finding("status", "build " + b + ": " + s + " with the reason " + st.reason());
            }
            if (countAtFault && firedCount >= 0 && st.count() != firedCount) {
                finding("status count", "build " + b + " ended " + s + " with count "
                        + st.count() + ", and its status gave " + firedCount + " at the fault: "
                        + "the count is the values of the committed steps (020-10, 6.1)");
            }
            if (s == State.ACTIVE && !cfg.writer && st.count() != ownAtCreation[b]) {
                finding("status count", "build " + b + " ended ACTIVE with count " + st.count()
                        + ", and the directory has " + ownAtCreation[b] + " values (020-10, 6.1)");
            }
        }

        private boolean namesInjected(String reason) {
            return reason != null && injected != null
                    && reason.contains(injected.getClass().getSimpleName())
                    && reason.contains(injected.getMessage());
        }

        /**
         * Waits until the markers are gone, or the cleanup ended by the fault: a
         * RuntimeException at a cleanup's point leaves its marker. False if the database
         * stopped or failed.
         */
        boolean awaitCleanup() {
            long end = System.nanoTime() + CLEANUP_MS * 1000000L;
            long firedAt = -1;
            while (true) {
                if (!alive("in the cleanup")) {
                    return false;
                }
                List<IndexKeys.Marker> markers = manager(db).markers(LATEST);
                if (markers.isEmpty()) {
                    return true;
                }
                if (fired && cfg.point.inCleanup() && cfg.fault == Fault.RUNTIME) {
                    if (firedAt < 0) {
                        firedAt = System.nanoTime();
                    } else if (System.nanoTime() - firedAt > 50000000L) {
                        stuckMarker = markers.get(0).gen;
                        return true;
                    }
                }
                if (System.nanoTime() > end) {
                    finding("cleanup", "markers left after " + CLEANUP_MS + " ms: " + markers);
                    return true;
                }
                sleep(2);
            }
        }

        // ======== The state of the database ========

        /**
         * The database's state by a read: true if active. A stop or a failure is checked
         * against the fault: a stop only after the fault STOP; a failure only after an Error,
         * or after a throw at a point after a commit. After an Error in a job's thread, waits
         * up to 2 s for the failure.
         */
        boolean alive(String where) {
            String state = probe();
            if (state.equals("active") && fired && cfg.fault == Fault.ERROR
                    && firedThread != Thread.currentThread() && !cfg.point.inCall()) {
                long end = System.nanoTime() + 2000000000L;
                while (state.equals("active") && System.nanoTime() < end) {
                    sleep(2);
                    state = probe();
                }
            }
            if (state.equals("failed")) {
                failed = true;
                boolean allowed = fired && (cfg.fault == Fault.ERROR
                        || cfg.point.afterCommit() && cfg.fault.throwsIt());
                if (!allowed) {
                    finding("failed only after an Error", "the database failed " + where + ": "
                            + describe(failure) + "\n" + stack(failure));
                } else if (cfg.fault == Fault.ERROR && !inChain(failure, injected)) {
                    finding("failed only after an Error", "the database failed " + where
                            + ", not by the Error injected: " + describe(failure));
                }
                return false;
            }
            if (state.equals("stopped")) {
                if (!(fired && cfg.fault == Fault.STOP)) {
                    finding("stop", "the database stopped " + where + " with no stop");
                }
                return false;
            }
            if (fired && cfg.fault == Fault.ERROR) {
                finding("Error fails the database", "an Error at " + cfg.point + " in "
                        + firedThread.getName() + ", and the database goes on " + where
                        + " (019-10's error model; 010-01, P7)");
                broken = true;
                return false;
            }
            return true;
        }

        /** "active", "stopped" or "failed" (with 'failure' set), by a get and the Db's state. */
        private String probe() {
            try {
                db.newConnection().get("/q/k", byte[].class);
                return dbOf(db).internal().isActive() ? "active" : "stopped";
            } catch (DbFailedException e) {
                failure = e;
                return "failed";
            } catch (IllegalDbStateException | StreamIoException e) {
                return "stopped";
            }
        }

        // ======== The checks ========

        /** The definition of the name in the stream, at the latest time. */
        IndexDefinition streamDefinition() {
            return IndexDefinition.read(dbOf(db), NAME, LATEST);
        }

        /** The entries of the index d at the latest time against f over values. */
        void checkEntries(IndexDefinition d, Map<String, Object> values, String where) {
            checkEntries(db, d, values, where);
        }

        void checkEntries(Database database, IndexDefinition d, Map<String, Object> values,
                String where) {
            List<Entry> got;
            try {
                got = parse(d, manager(database).entries(NAME, d.gen(), LATEST));
            } catch (RuntimeException e) {
                finding("entries", where + ": the entries of " + d + " do not parse: "
                        + describe(e));
                return;
            }
            List<Entry> want = REF.entries(def(d), values);
            if (d.isActive() ? !got.equals(want) : !new HashSet<Entry>(want).containsAll(got)) {
                finding("entries", where + ": the entries of " + d + " are not f over the "
                        + "directory's values (" + (d.isActive() ? "an active index: exactly"
                        : "a building one: a part") + "): " + diff(got, want));
            }
        }

        /** The checks at the live phase's end: nothing runs. */
        void checkLive() {
            checkSnapshots("at the end");
            IndexManager m = manager(db);
            IndexDefinition mem = m.definition(NAME);
            IndexDefinition str = streamDefinition();
            if (!Objects.equals(mem, str)) {
                finding("memory and stream", "at the end, memory has " + mem + ", the stream "
                        + str);
            }
            Set<Long> markers = new TreeSet<Long>();
            for (IndexKeys.Marker k : m.markers(LATEST)) {
                if (!k.name.equals(NAME)) {
                    finding("markers", "a marker of another name: " + k);
                }
                markers.add(k.gen);
            }
            Set<Long> want = new TreeSet<Long>();
            if (stuckMarker != 0) {
                want.add(stuckMarker);
            }
            if (!markers.equals(want)) {
                finding("markers", "at the end, markers of " + markers + ", expected " + want);
            }
            if (mem != null && markers.contains(mem.gen())) {
                finding("markers", "a marker of the live generation " + mem.gen());
            }
            if (mem != null) {
                checkEntries(mem, ownValues(), "at the end");
            }
            for (byte[] k : rawKeys(dbOf(db), IndexKeys.entriesPrefix())) {
                boolean ok = mem != null && IndexKeys.startsWith(k, mem.generationPrefix())
                        || stuckMarker != 0 && IndexKeys.startsWith(k,
                                IndexKeys.generationPrefix(NAME, stuckMarker));
                if (!ok) {
                    finding("entries", "at the end, an entry of no live generation: "
                            + IndexKeys.show(k));
                    break;
                }
            }
        }

        /** Every status read is as it was read; each build's statuses in order are sane. */
        void checkSnapshots(String where) {
            List<Snap> all;
            synchronized (snaps) {
                all = new ArrayList<Snap>(snaps);
            }
            Snap[] last = new Snap[3];
            for (Snap s : all) {
                String now = s.changed();
                if (now != null) {
                    finding("status snapshot", where + ": the status " + s + " now gives "
                            + now + " (015-39)");
                }
                if (s.note == null || s.note.isEmpty() || s.note.indexOf('\n') >= 0) {
                    finding("status", s + ": the note is one English line");
                }
                if (s.state == State.BUILDING && !cfg.writer
                        && s.count % IndexBuilderImp.STEP_VALUES != 0
                        && s.count != ownAtCreation[s.build]) {
                    finding("status count", s + ": a building status's count is the values "
                            + "of whole committed steps, " + IndexBuilderImp.STEP_VALUES
                            + " each but the last");
                }
                Snap p = last[s.build];
                if (p != null && (p.state != State.BUILDING && (s.state != p.state
                        || s.count != p.count) || s.count < p.count)) {
                    finding("status order", "build " + s.build + ": " + p + ", then " + s);
                }
                last[s.build] = s;
            }
        }

        // ======== The close and the restart ========

        /** Closes; the close returns, the jobs' joins return, no thread of BergDB is left. */
        void closeAndCheck(Database d, String what) {
            long t0 = System.nanoTime();
            try {
                d.close();
            } catch (RuntimeException | Error e) {
                if (!failed) {
                    finding("close", what + ": close() threw " + describe(e));
                }
            }
            long ms = (System.nanoTime() - t0) / 1000000;
            if (ms >= JOIN_MS) {
                finding("hang", what + ": close() took " + ms + " ms");
            }
            for (int b = 1; b <= 2; b++) {
                if (jobs[b] != null && d == db) {
                    long j0 = System.nanoTime();
                    jobs[b].join(THREADS_MS);
                    if ((System.nanoTime() - j0) / 1000000 >= THREADS_MS) {
                        finding("thread left", what + ": build " + b + "'s join() did not "
                                + "return in " + THREADS_MS + " ms after the close");
                    }
                }
            }
            long end = System.nanoTime() + THREADS_MS * 1000000L;
            Set<Thread> left;
            while (true) {
                left = bergdbThreads();
                left.removeAll(before);
                left.remove(Thread.currentThread());
                if (left.isEmpty() || System.nanoTime() > end) {
                    break;
                }
                sleep(1);
            }
            for (Thread t : left) {
                finding("thread left", what + ": the thread " + t.getName() + " is alive "
                        + THREADS_MS + " ms after the close:\n" + stack(t.getStackTrace()));
            }
        }

        /**
         * A start on a copy of the stream: the definition that the calls left, its build
         * resumed and ACTIVE, every marker gone, the entries f over the data read back, no
         * other generation's entry, the data as written.
         */
        void restart() {
            Database d;
            try {
                d = start(stream.copy());
            } catch (RuntimeException | Error e) {
                finding("restart", "the start threw " + describe(e) + "\n" + stack(e));
                return;
            }
            try {
                IndexManager m = manager(d);
                Map<String, Object> values = readBack(d);
                IndexDefinition def = m.definition(NAME);
                IndexDefinition str = IndexDefinition.read(dbOf(d), NAME, LATEST);
                if (!Objects.equals(def, str)) {
                    finding("restart", "after the start, memory has " + def + ", the stream "
                            + str);
                }
                long g = def == null ? 0 : def.gen();
                if (!failed && !broken && g != expectGen) {
                    finding("restart", "the start has the generation " + g + ", and the "
                            + "calls that returned left " + expectGen);
                } else if (failed && g != 0 && !gens.contains(g) && !cfg.point.afterCommit()) {
                    finding("restart", "the start has the generation " + g
                            + ", which no creation made: " + gens);
                }
                if (def != null) {
                    checkResumed(d, def, values.size());
                    def = m.definition(NAME);
                } else {
                    try {
                        d.indexJob(NAME);
                        finding("restart", "no index, and indexJob() gives a job");
                    } catch (NoSuchIndexException e) {
                        // Expected.
                    }
                }
                long end = System.nanoTime() + CLEANUP_MS * 1000000L;
                List<IndexKeys.Marker> markers;
                while (!(markers = m.markers(LATEST)).isEmpty() && System.nanoTime() < end) {
                    sleep(2);
                }
                if (!markers.isEmpty()) {
                    finding("restart", "markers left " + CLEANUP_MS + " ms after the start: "
                            + markers + " (020-10, 6.2: a start resumes the cleanup)");
                }
                if (def != null) {
                    checkEntries(d, def, values, "after the restart");
                }
                for (byte[] k : rawKeys(dbOf(d), IndexKeys.entriesPrefix())) {
                    if (def == null || !IndexKeys.startsWith(k, def.generationPrefix())) {
                        finding("restart", "after the restart, an entry of no live "
                                + "generation: " + IndexKeys.show(k));
                        break;
                    }
                }
            } catch (RuntimeException | Error e) {
                finding("restart", "the checks threw " + describe(e) + "\n" + stack(e));
            } finally {
                closeAndCheck(d, "the restarted database");
            }
        }

        /** The build of def resumed at the start, or its job ACTIVE with count 0. */
        private void checkResumed(Database d, IndexDefinition def, int own) {
            Job job;
            try {
                job = d.indexJob(NAME);
            } catch (NoSuchIndexException e) {
                finding("restart", "the start has " + def + ", and indexJob() threw "
                        + describe(e));
                return;
            }
            JobStatus first = job.getStatus();
            if (def.isActive() && (first.state() != State.ACTIVE || first.count() != 0)) {
                finding("restart", "an index active at the start: its job is " + first.state()
                        + " with count " + first.count() + ", not ACTIVE with 0 (020-10, 3.2)");
            }
            long t0 = System.nanoTime();
            JobStatus st = job.join(JOIN_MS);
            restartStatus = st;
            if (st.state() != State.ACTIVE) {
                finding("restart", "the build resumed at the start ended " + st.state() + " ("
                        + st.note() + ")" + ((System.nanoTime() - t0) / 1000000 >= JOIN_MS - 100
                        ? ", after " + JOIN_MS + " ms" : ""));
            } else if (!def.isActive() && st.count() != own) {
                finding("restart", "the build resumed at the start: count " + st.count()
                        + ", and the directory has " + own + " values");
            }
            IndexDefinition now = manager(d).definition(NAME);
            if (st.state() == State.ACTIVE && (now == null || !now.isActive())) {
                finding("restart", "the resumed build is ACTIVE, and memory has " + now);
            }
        }

        /**
         * The values of the directory's own keys in the restarted database, as Java values: each
         * read back as its bytes and taken from the values the harness wrote. For a database
         * that did not fail, the model's exactly; after a failure, a write that returned may be
         * missing (docs/levels.md, section 3), so f is over the data read back.
         */
        Map<String, Object> readBack(Database d) {
            TreeMap<String, Object> values = new TreeMap<String, Object>();
            TreeMap<String, Bin> bytes = new TreeMap<String, Bin>();
            for (Kv<byte[]> kv : d.newConnection().usePrimary(byte[].class).dir(DIR).kvs()) {
                Bin b = new Bin(kv.value());
                Object v = known.get(b);
                if (v == null) {
                    finding("restart", "the value at " + kv.key() + ", " + b + ", is none "
                            + "that the harness wrote");
                    v = b;
                }
                values.put(kv.key(), v);
                bytes.put(kv.key(), b);
            }
            if (!failed) {
                TreeMap<String, Bin> want = new TreeMap<String, Bin>();
                synchronized (model) {
                    for (Map.Entry<String, Val> e : model.entrySet()) {
                        if (IndexReference.Model.inDir(e.getKey(), DIR)) {
                            want.put(e.getKey(), e.getValue().bytes);
                        }
                    }
                }
                if (!want.equals(bytes)) {
                    finding("restart", "the data after the restart is not the data written: "
                            + "keys " + bytes.keySet() + ", written " + want.keySet());
                }
            }
            return values;
        }
    }

    // ======== The writer of the night runs ========

    /** A thread that writes the directory while the jobs run: its own keys, w00 to w19. */
    static final class Writer extends Thread {
        private final Run run;
        private final Random r;
        private volatile boolean done;

        Writer(Run run, long seed) {
            super("IndexJobsHarness-writer");
            this.run = run;
            this.r = new Random(seed * 31 + 7);
        }

        public void run() {
            Connection c = run.db.newConnection();
            while (!done) {
                Map<String, Object> w = new LinkedHashMap<String, Object>();
                for (int i = 1 + r.nextInt(3); i > 0; i--) {
                    String key = String.format("%sw%02d", DIR, r.nextInt(20));
                    int k = r.nextInt(10);
                    w.put(key, k < 2 ? null : k < 3 ? "w" : new Item(r.nextInt(50),
                            STRINGS[r.nextInt(STRINGS.length)]));
                }
                try {
                    run.write(c, w, "the writer");
                } catch (RuntimeException e) {
                    if (isStopOrFailure(e)) {
                        return;
                    }
                    if (!(e instanceof DbException)) {
                        run.finding("workload", "the writer threw " + describe(e));
                        return;
                    }
                }
                IndexJobsHarness.sleep(5);
            }
            try {
                c.sync();
            } catch (RuntimeException e) {
                // A stopped or failed database: the run's checks say so.
            }
        }

        /** Stops the writer and waits for it. */
        void finish() {
            done = true;
            try {
                join(JOIN_MS);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
            if (isAlive()) {
                run.finding("hang", "the writer did not end in " + JOIN_MS + " ms");
            }
        }
    }

    // ======== Helpers ========

    static Database start(MemoryStream stream) {
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        return builder.start();
    }

    static IndexManager manager(Database d) {
        return ((DatabaseImp) d).getIndexManager();
    }

    static Db dbOf(Database d) {
        return ((DatabaseImp) d).getDb();
    }

    /** Creates the index def with IndexBuilder (020-10, section 3.1). */
    static Job startIndex(Database d, Def def) {
        IndexBuilder b = d.indexBuilder(def.name).dir(def.dir);
        for (Level l : def.levels) {
            b.type(l.type.string).field(l.path[0]);
        }
        return b.start();
    }

    /** IndexReference's definition of an IndexDefinition. */
    static Def def(IndexDefinition d) {
        List<Level> levels = new ArrayList<Level>();
        for (int i = 0; i < d.levelCount(); i++) {
            Type t = Type.valueOf(d.typeName(i).toUpperCase(Locale.ROOT));
            levels.add(new Level(t, Call.FIELD, d.path(i)));
        }
        return new Def(d.name(), d.dir(), levels);
    }

    static boolean sameLevels(Def a, Def b) {
        if (!a.dir.equals(b.dir) || a.levels.size() != b.levels.size()) {
            return false;
        }
        for (int i = 0; i < a.levels.size(); i++) {
            if (a.type(i) != b.type(i)
                    || !Arrays.equals(a.levels.get(i).path, b.levels.get(i).path)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Raw entry keys of the definition d, parsed with IndexKeys (020-10, section 4.4), as
     * IndexReference's entries: the levels' values (a byte[] as a Bin) and the user's key.
     */
    static List<Entry> parse(IndexDefinition d, List<byte[]> keys) {
        List<Entry> result = new ArrayList<Entry>();
        for (byte[] k : keys) {
            IndexKeys.Entry e = IndexKeys.parseEntry(k, d.generationPrefix(), d.types());
            List<Object> levels = new ArrayList<Object>();
            for (int i = 0; i < e.levelCount(); i++) {
                Object v = e.value(i);
                levels.add(v instanceof byte[] ? new Bin((byte[]) v) : v);
            }
            result.add(new Entry(levels, PubKeys.i2u(d.idir() + e.fileName()), null));
        }
        return result;
    }

    /** The prefix of every entry of the name, whatever its generation: bkey(/#i/dient/dNAME/). */
    static byte[] namePrefix() {
        byte[] p = IndexKeys.generationPrefix(NAME, 1);
        return Arrays.copyOf(p, p.length - 8);
    }

    /** The keys that start with prefix, at the latest time, with Db.getMany. */
    static List<byte[]> rawKeys(Db db, final byte[] prefix) {
        GetMany g = db.newGetMany();
        g.startKey = Keys.toSegments(prefix);
        g.inclusive = true;
        g.lookupTime = LATEST;
        g.stopCondition = new GetMany.StopCondition() {
            public int handleKvt(Kvt kvt) {
                return IndexKeys.startsWith(Keys.toBytes(kvt.key), prefix)
                        ? GetMany.StopCondition.ADD : GetMany.StopCondition.STOP;
            }

            public void eod() {}
        };
        db.getMany(g);
        List<byte[]> keys = new ArrayList<byte[]>();
        for (Kvt kvt : g.result) {
            keys.add(Keys.toBytes(kvt.key));
        }
        return keys;
    }

    /** The difference of two lists of entries, for a finding. */
    static String diff(List<Entry> got, List<Entry> want) {
        List<Entry> extra = new ArrayList<Entry>(got);
        extra.removeAll(want);
        List<Entry> missing = new ArrayList<Entry>(want);
        missing.removeAll(got);
        String s = got.size() + " entries, expected " + want.size() + "; extra " + head(extra)
                + "; missing " + head(missing);
        if (extra.isEmpty() && missing.isEmpty()) {
            s += "; the order differs";
        }
        return s;
    }

    private static String head(List<Entry> entries) {
        return entries.size() <= 3 ? entries.toString()
                : entries.subList(0, 3) + " and " + (entries.size() - 3) + " more";
    }

    /** A stop of the database or its failure, as a call meets it. */
    static boolean isStopOrFailure(Throwable e) {
        return e instanceof IllegalDbStateException || e instanceof StreamIoException;
    }

    static boolean isStop(Throwable e) {
        return isStopOrFailure(e) && !(e instanceof DbFailedException);
    }

    /** Whether target is e, or a cause or a suppressed exception of it. */
    static boolean inChain(Throwable e, Throwable target) {
        Set<Throwable> seen = new HashSet<Throwable>();
        List<Throwable> todo = new ArrayList<Throwable>();
        if (e != null) {
            todo.add(e);
        }
        while (!todo.isEmpty()) {
            Throwable x = todo.remove(todo.size() - 1);
            if (x == target) {
                return true;
            }
            if (seen.add(x)) {
                if (x.getCause() != null) {
                    todo.add(x.getCause());
                }
                todo.addAll(Arrays.asList(x.getSuppressed()));
            }
        }
        return false;
    }

    static String describe(Throwable e) {
        return e == null ? "null" : e.getClass().getSimpleName() + ": " + e.getMessage()
                + (e.getCause() == null ? "" : " (cause " + describe(e.getCause()) + ")");
    }

    static String stack(Throwable e) {
        return e == null ? "" : stack(e.getStackTrace());
    }

    static String stack(StackTraceElement[] frames) {
        StringBuilder s = new StringBuilder();
        for (int i = 0; i < frames.length && i < 12; i++) {
            s.append("    at ").append(frames[i]).append('\n');
        }
        return s.toString();
    }

    /** The threads alive now that run code of BergDB (not the tests' runner). */
    static Set<Thread> bergdbThreads() {
        Set<Thread> result = new HashSet<Thread>();
        for (Map.Entry<Thread, StackTraceElement[]> e : Thread.getAllStackTraces().entrySet()) {
            if (!e.getKey().isAlive()) {
                continue;
            }
            for (StackTraceElement f : e.getValue()) {
                String c = f.getClassName();
                if (c.startsWith("bergdb.") && !c.startsWith("bergdb.nanotest.")
                        && !c.startsWith("bergdb.dev.")) {
                    result.add(e.getKey());
                    break;
                }
            }
        }
        return result;
    }

    static void sleep(long ms) {
        try {
            Thread.sleep(ms);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    // ======== Runs and results ========

    /** Runs one configuration. */
    static Run run(Config cfg) {
        Run r = new Run(cfg);
        r.execute();
        return r;
    }

    /**
     * The faults that the harness finds in the code and that are not fixed yet, by the
     * signature of their findings (the check; the fault at the point): Results lists them
     * apart and does not fail for them; testEveryPointAndFault fails when one is no longer
     * found, so that its fix removes its line here. Each is a fault of IndexManager (020-10,
     * step I2), found by this harness on 2026-11-09 at 5b08db5.
     */
    static final String[][] KNOWN = {
        // H3-F1: an Error in a creation's or a deletion's call, before or after its commit,
        // is thrown as it is, and the database goes on; 019-10's error model: an Error in
        // any call fails the database (docs/levels.md, section 3). IndexManager.execute()
        // catches nothing around its hooks and the maps' change.
        {"Error fails the database; ERROR at CREATE_BEFORE", "H3-F1"},
        {"Error fails the database; ERROR at CREATE_AFTER", "H3-F1"},
        {"Error fails the database; ERROR at DELETE_BEFORE", "H3-F1"},
        {"Error fails the database; ERROR at DELETE_AFTER", "H3-F1"},
        // H3-F2: an exception after a creation's or a deletion's commit, before the maps
        // change, reaches the caller, and the database goes on with the change in the stream
        // and not in memory: neither refused nor done (020-10, 3.2); docs/levels.md, section
        // 3: an exception after a transaction's go point fails the database.
        {"throw after the commit; REFUSAL at CREATE_AFTER", "H3-F2"},
        {"throw after the commit; EXPIRY at CREATE_AFTER", "H3-F2"},
        {"throw after the commit; RUNTIME at CREATE_AFTER", "H3-F2"},
        {"throw after the commit; REFUSAL at DELETE_AFTER", "H3-F2"},
        {"throw after the commit; EXPIRY at DELETE_AFTER", "H3-F2"},
        {"throw after the commit; RUNTIME at DELETE_AFTER", "H3-F2"},
        // H3-F3: a RuntimeException after the activation's commit, before the maps change,
        // ends the build FAILED, and the database goes on with the definition active in the
        // stream and building in memory.
        {"memory and stream; RUNTIME at ACTIVATE_AFTER", "H3-F3"},
        {"status; RUNTIME at ACTIVATE_AFTER", "H3-F3"},
    };

    /** The known fault of a finding's signature, or null. */
    static String known(String signature) {
        for (String[] k : KNOWN) {
            if (k[0].equals(signature)) {
                return k[1];
            }
        }
        return null;
    }

    /** The findings of many runs: one example of each signature (the check, the fault), counts. */
    static final class Results {
        /** The known faults' signatures found, with an example. */
        final TreeMap<String, String> knownFound = new TreeMap<String, String>();
        final TreeMap<String, String> examples = new TreeMap<String, String>();
        final TreeMap<String, Integer> counts = new TreeMap<String, Integer>();
        final List<String> notReached = new ArrayList<String>();
        int runs;
        int fired;

        void add(Run r) {
            add(r, true);
        }

        /** Adds the run's findings; reach: a fault that did not fire is a finding. */
        void add(Run r, boolean reach) {
            runs++;
            if (r.fired) {
                fired++;
            } else if (r.cfg.point != null && reach) {
                notReached.add(r.cfg.toString());
            }
            synchronized (r.findings) {
                for (String[] f : r.findings) {
                    String sig = f[0] + "; " + (r.cfg.point == null ? "no fault"
                            : r.cfg.fault + " at " + r.cfg.point);
                    if (known(sig) != null) {
                        if (!knownFound.containsKey(sig)) {
                            knownFound.put(sig, known(sig) + ", " + r.cfg + ": " + f[1]);
                        }
                        continue;
                    }
                    if (!examples.containsKey(sig)) {
                        examples.put(sig, r.cfg + ": " + f[1]);
                    }
                    Integer c = counts.get(sig);
                    counts.put(sig, c == null ? 1 : c + 1);
                }
            }
        }

        String summary() {
            StringBuilder s = new StringBuilder(runs + " runs, the fault made in " + fired + "; "
                    + examples.size() + " kinds of findings, " + knownFound.size()
                    + " of known faults");
            for (Map.Entry<String, String> e : examples.entrySet()) {
                s.append("\n* ").append(e.getKey()).append(" (").append(counts.get(e.getKey()))
                        .append(" times), e.g. ").append(e.getValue());
            }
            return s.toString();
        }

        void assertClean() {
            if (!examples.isEmpty()) {
                throw new AssertionError(summary());
            }
        }
    }

    /** The call of each point that the unit test's faults take: a middle step, the 2nd cleanup step. */
    static int unitCall(Point p) {
        switch (p) {
        case BUILD_STEP:
            return 3;   // Step 2 of build 1: call 1 is step 1, call 2 its run again after the racing writes.
        case CLEANUP_STEP:
            return 2;   // The cleanup's second step, after the first deleted 100 entries.
        default:
            return 1;
        }
    }

    // ======== Tests ========

    /**
     * The workload with no fault: no finding; every point of the hook is reached, as often
     * as the contract says: two creations and activations, one deletion, a cleanup of two
     * steps and its end, and at least the steps of the two builds.
     */
    @Nano
    public static void testNoFault() {
        Run r = run(new Config());
        Results res = new Results();
        res.add(r);
        res.assertClean();
        int own = r.ownAtCreation[1];
        int steps = (own + IndexBuilderImp.STEP_VALUES - 1) / IndexBuilderImp.STEP_VALUES;
        int[] c = r.calls;
        String counts = Arrays.toString(Point.values()) + " " + Arrays.toString(c);
        check(c[Point.CREATE_BEFORE.ordinal()] == 2 && c[Point.CREATE_AFTER.ordinal()] == 2
                && c[Point.ACTIVATE_BEFORE.ordinal()] == 2 && c[Point.ACTIVATE_AFTER.ordinal()] == 2
                && c[Point.DELETE_BEFORE.ordinal()] == 1 && c[Point.DELETE_AFTER.ordinal()] == 1
                && c[Point.CLEANUP_STEP.ordinal()] == 2 && c[Point.CLEANUP_END.ordinal()] == 1
                && c[Point.BUILD_STEP.ordinal()] >= 2 * steps + 2, "the hook's calls: " + counts);
        check(r.finals[1].state() == State.ACTIVE && r.finals[2].state() == State.ACTIVE,
                "both builds active");
        check(r.restartStatus != null && r.restartStatus.state() == State.ACTIVE
                && r.restartStatus.count() == 0, "the index active at the restart: "
                + r.restartStatus);
    }

    /**
     * Every fault at every point once (bergdb 020-10, section 9.3): the first call of each
     * point, a middle step of the first build (step 2), the cleanup's second step.
     */
    @Nano
    public static void testEveryPointAndFault() {
        Results res = new Results();
        for (Point p : Point.values()) {
            for (Fault f : Fault.values()) {
                res.add(run(new Config(p, unitCall(p), f)));
            }
        }
        res.assertClean();
        check(res.notReached.isEmpty(), "points not reached: " + res.notReached);
        for (String[] k : KNOWN) {
            check(res.knownFound.containsKey(k[0]), "the known fault " + k[1] + " is no longer "
                    + "found (" + k[0] + "): if it is fixed, remove its line from KNOWN");
        }
    }

    /**
     * S2-F27 (020-10, section 8, F5): a creation refused at its transaction (a refusal, an
     * expiry, a bug thrown before the commit) throws it and leaves nothing: no definition in
     * memory or in the stream, no job, no entry of the name; the name stays free, and the
     * same creation then works.
     */
    @Nano
    public static void testCreationRefused() {
        for (Fault f : new Fault[] {Fault.REFUSAL, Fault.EXPIRY, Fault.RUNTIME}) {
            Run r = run(new Config(Point.CREATE_BEFORE, 1, f));
            Results res = new Results();
            res.add(r);
            res.assertClean();
            check(r.fired && r.retries == 1 && r.finals[1] != null
                    && r.finals[1].state() == State.ACTIVE, f + ": refused once, then made");
        }
    }

    /**
     * 015-23 (020-10, section 8, F5): a deletion refused at its transaction throws the fault
     * and changes nothing: the index is in memory and in the stream as before, with no
     * marker, and a write still keeps its entries; the deletion then works, the name is free
     * at once, and the cleanup removes the old generation.
     */
    @Nano
    public static void testDeletionRefused() {
        for (Fault f : new Fault[] {Fault.REFUSAL, Fault.EXPIRY, Fault.RUNTIME}) {
            Run r = run(new Config(Point.DELETE_BEFORE, 1, f));
            Results res = new Results();
            res.add(r);
            res.assertClean();
            check(r.fired && r.retries == 1 && r.finals[2] != null
                    && r.finals[2].state() == State.ACTIVE, f + ": refused once, then made");
        }
    }

    /**
     * S2-F11 (020-10, section 8, F5): a stop of the database in a build's second step ends
     * the build BUILDING, with the count of its one committed step, not done; the next start
     * resumes it from the directory's first key, and it ends ACTIVE with the function's
     * entries.
     */
    @Nano
    public static void testStopDuringBuild() {
        Config cfg = new Config(Point.BUILD_STEP, 2, Fault.STOP);
        cfg.racingWrites = false;
        Run r = run(cfg);
        Results res = new Results();
        res.add(r);
        res.assertClean();
        JobStatus st = r.finals[1];
        check(r.fired && st != null && st.state() == State.BUILDING
                && st.count() == IndexBuilderImp.STEP_VALUES && st.reason() == null,
                "BUILDING with one step's count: " + (st == null ? null : st.note()));
        check(r.restartStatus != null && r.restartStatus.state() == State.ACTIVE
                && r.restartStatus.count() == r.ownAtCreation[1], "resumed and ACTIVE: "
                + (r.restartStatus == null ? null : r.restartStatus.note()));
    }

    /**
     * A deletion during a build (in its second step): the build ends FAILED "deleted", the
     * name is free at once, the cleanup removes every entry of the generation, also one that
     * the build wrote, and a creation of the name at once builds the new generation.
     */
    @Nano
    public static void testDeletedDuringBuild() {
        Config cfg = new Config();
        cfg.deleteDuringBuild = true;
        Run r = run(cfg);
        Results res = new Results();
        res.add(r);
        res.assertClean();
        check(r.deletedDuringBuild && r.finals[1] != null
                && r.finals[1].state() == State.FAILED, "deleted during the build: "
                + (r.finals[1] == null ? null : r.finals[1].note()));
    }

    private static void check(boolean ok, String message) {
        if (!ok) {
            throw new AssertionError(message);
        }
    }

    // ======== The night ========

    /**
     * The night test: every fault at every call of every point with 500 objects; then 200
     * random runs (a random point, call and fault; a writer thread; a deletion during the
     * build), from the day's seed, printed so that main() repeats them.
     */
    @Nano("night")
    public static void testJobsNight(TestEnvironment c) {
        long base = System.currentTimeMillis() / 86400000L * 1000;
        c.out().println("IndexJobsHarness: every point and call, then 200 random runs from "
                + "seed " + base);
        Results res = sweep(NIGHT_OBJECTS);
        res.assertClean();
        Results random = randomRuns(base, 200, NIGHT_OBJECTS);
        c.out().println("IndexJobsHarness: " + res.runs + " + " + random.runs + " runs");
        random.assertClean();
    }

    /** Every fault at every call of every point, until a point's call is not reached. */
    static Results sweep(int objects) {
        Results res = new Results();
        for (Point p : Point.values()) {
            for (Fault f : Fault.values()) {
                for (int n = 1; ; n++) {
                    Config cfg = new Config(p, n, f);
                    cfg.objects = objects;
                    Run r = run(cfg);
                    res.add(r, false);
                    if (!r.fired) {
                        break;     // The workload ended before call n: a run with no fault.
                    }
                }
            }
        }
        return res;
    }

    /** Random runs from seed: a random point, call and fault; a writer; a deletion during the build. */
    static Results randomRuns(long seed, int runs, int objects) {
        Results res = new Results();
        for (int i = 0; i < runs; i++) {
            Random r = new Random(seed + i);
            Config cfg = new Config();
            cfg.seed = seed + i;
            cfg.objects = objects;
            cfg.writer = r.nextBoolean();
            cfg.deleteDuringBuild = r.nextInt(4) == 0;
            cfg.racingWrites = r.nextInt(4) != 0;
            if (r.nextInt(10) != 0) {
                cfg.point = Point.values()[r.nextInt(Point.values().length)];
                cfg.fault = Fault.values()[r.nextInt(Fault.values().length)];
                int most = cfg.point == Point.BUILD_STEP ? 2 * objects / IndexBuilderImp.STEP_VALUES
                        : cfg.point == Point.CLEANUP_STEP ? objects / IndexManager.CLEANUP_KEYS : 2;
                cfg.n = 1 + r.nextInt(Math.max(1, most));
            }
            res.add(run(cfg), false);
        }
        return res;
    }

    /** Usage: IndexJobsHarness [SEED [RUNS [OBJECTS]]]: random runs; with no SEED, the sweep too. */
    public static void main(String[] args) {
        long seed = args.length > 0 ? Long.parseLong(args[0]) : System.nanoTime();
        int runs = args.length > 1 ? Integer.parseInt(args[1]) : 50;
        int objects = args.length > 2 ? Integer.parseInt(args[2]) : NIGHT_OBJECTS;
        long t0 = System.nanoTime();
        if (args.length == 0) {
            Results res = sweep(objects);
            System.out.println("IndexJobsHarness: the sweep, " + res.summary() + ", "
                    + (System.nanoTime() - t0) / 1000000 + " ms");
        }
        Results res = randomRuns(seed, runs, objects);
        System.out.println("IndexJobsHarness: seed " + seed + ", " + res.summary() + ", "
                + (System.nanoTime() - t0) / 1000000 + " ms");
    }
}
