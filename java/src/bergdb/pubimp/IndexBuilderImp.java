package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;

import bergdb.core.Db;
import bergdb.core.InternalDataException;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.DataFormatException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.util.DbException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.storage.StreamIoException;

/**
 * The builder of a user index (bergdb 020-10, section 3.1) and its build (section 6.1).
 *
 * @see bergdb.pub.IndexBuilder
 * @author Frans Lundberg
 */
public class IndexBuilderImp implements IndexBuilder {

    /** The values a build step reads at most (020-10, section 6.1). */
    static final int STEP_VALUES = 25;

    /** The longest pause after a build or cleanup step, ns (020-10, section 6.1; N10). */
    static final long MAX_PAUSE = 1000000000L;

    private final DatabaseImp database;
    private final String indexName;
    private String dir;
    private final List<String> types = new ArrayList<>();
    private final List<String[]> paths = new ArrayList<>();
    private boolean spent;

    /** A builder of the index 'indexName', whose name is checked (IndexKeys.checkName). */
    IndexBuilderImp(String indexName, DatabaseImp database) {
        assert indexName != null;
        assert database != null;
        this.indexName = indexName;
        this.database = database;
    }

    private void checkNotSpent() {
        if (spent) {
            throw new IllegalStateException("The builder is spent: start() was called.");
        }
    }

    public IndexBuilder dir(String udir) {
        checkNotSpent();
        if (dir != null) {
            throw new IllegalStateException("dir() was called before: an index has one "
                    + "directory (bergdb 020-10, section 3.1).");
        }
        PubKeys.udir2idir(udir);    // throws IllegalArgumentException
        this.dir = udir;
        return this;
    }

    public IndexBuilder type(String type) {
        checkNotSpent();
        if (dir == null) {
            throw new IllegalStateException("Call dir() before type().");
        }
        if (!types.isEmpty() && paths.get(paths.size() - 1) == null) {
            throw new IllegalStateException("The level before has no field: call field() or "
                    + "nestedField() after type().");
        }
        if (types.size() == IndexDefinition.MAX_LEVELS) {
            throw new IllegalStateException("An index has at most "
                    + IndexDefinition.MAX_LEVELS + " levels.");
        }
        IndexKeys.type(type);       // throws IllegalArgumentException
        types.add(type);
        paths.add(null);
        return this;
    }

    public IndexBuilder field(String name) {
        return path(new String[] {name}, "field");
    }

    public IndexBuilder nestedField(String path) {
        checkLevel("nestedField");
        if (path == null) {
            throw new IllegalArgumentException("path == null not allowed");
        }
        return path(path.split("\\.", -1), "nestedField");
    }

    public IndexBuilder nestedField(String[] parts) {
        checkLevel("nestedField");
        if (parts == null || parts.length == 0) {
            throw new IllegalArgumentException("A nested field has 1 to "
                    + IndexDefinition.MAX_PARTS + " parts, not none.");
        }
        return path(parts.clone(), "nestedField");
    }

    private void checkLevel(String method) {
        checkNotSpent();
        if (types.isEmpty()) {
            throw new IllegalStateException("Call type() before " + method + "().");
        }
        if (paths.get(paths.size() - 1) != null) {
            throw new IllegalStateException("The level has its field: call type() for the "
                    + "next level.");
        }
    }

    /** The level's path: 1 to 16 parts, each a name of 1 to 255 UTF-8 bytes (S2-F15). */
    private IndexBuilder path(String[] parts, String method) {
        checkLevel(method);
        if (parts.length > IndexDefinition.MAX_PARTS) {
            throw new IllegalArgumentException("A nested field has 1 to "
                    + IndexDefinition.MAX_PARTS + " parts, not " + parts.length + ".");
        }
        for (int i = 0; i < parts.length; i++) {
            if (parts[i] == null) {
                throw new IllegalArgumentException("A field's name is null (part " + (i + 1)
                        + ").");
            }
            try {
                ObjectFormat.nameBytes(parts[i]);
            } catch (IllegalArgumentException e) {
                throw new IllegalArgumentException("Bad field name " + IndexKeys.quote(parts[i])
                        + (parts.length > 1 ? " (part " + (i + 1) + ")" : "") + ": "
                        + e.getMessage(), e);
            }
        }
        paths.set(paths.size() - 1, parts);
        return this;
    }

    public Job start() {
        checkNotSpent();
        spent = true;
        if (dir == null) {
            throw new IllegalStateException("No directory: call dir() before start().");
        }
        if (types.isEmpty()) {
            throw new IllegalStateException("No level: call type() and field() before "
                    + "start().");
        }
        if (paths.get(paths.size() - 1) == null) {
            throw new IllegalStateException("The last level has no field.");
        }
        return database.getIndexManager().create(indexName, dir,
                types.toArray(new String[0]), paths.toArray(new String[0][]));
    }

    // ======== The build (020-10, section 6.1) ========

    /**
     * The build of an index in this process: its status, a snapshot at each getStatus()
     * (015-39), and its thread.
     */
    static final class BuildJob implements Job {
        private final String name;
        private JobStatus.State state = JobStatus.State.BUILDING;
        private long count;
        private String reason;
        private Thread thread;

        BuildJob(String name) {
            this.name = name;
        }

        synchronized void setThread(Thread thread) {
            this.thread = thread;
        }

        synchronized void counted(long n) {
            count += n;
        }

        synchronized void activated(long n) {
            count += n;
            state = JobStatus.State.ACTIVE;
        }

        synchronized void failed(String why) {
            state = JobStatus.State.FAILED;
            reason = why;
        }

        public synchronized JobStatus getStatus() {
            return new Status(name, state, count, reason);
        }

        public JobStatus join() {
            return join(0);
        }

        public JobStatus join(int millis) {
            Thread t;
            synchronized (this) {
                t = thread;
            }
            if (t != null) {
                try {
                    t.join(millis);
                } catch (InterruptedException e) {
                    // The wait ends, the build goes on (bergdb 005-46).
                    Thread.currentThread().interrupt();
                }
            }
            return getStatus();
        }
    }

    /** A status: immutable. */
    private static final class Status implements JobStatus {
        private final String name;
        private final State state;
        private final long count;
        private final String reason;

        Status(String name, State state, long count, String reason) {
            this.name = name;
            this.state = state;
            this.count = count;
            this.reason = reason;
        }

        public State state() {
            return state;
        }

        public long count() {
            return count;
        }

        public String reason() {
            return reason;
        }

        public String note() {
            switch (state) {
            case ACTIVE:
                return "The index " + name + " is active; its build read " + count
                        + " values in this process.";
            case FAILED:
                return "The build of the index " + name + " failed after " + count
                        + " values: " + reason + ". The next start takes it again.";
            default:
                return "The index " + name + " is building: " + count + " values read.";
            }
        }

        public String toString() {
            return note();
        }
    }

    /** Thrown in a build step's action when its index was deleted. */
    private static final class DeletedException extends RuntimeException {
        private static final long serialVersionUID = 1L;
    }

    /**
     * Starts the build of a live index in state building, in a daemon thread of the lowest
     * priority, on its own connection, from the first key of its directory (020-10, section
     * 6.1). A step is an rw(): a getMany of at most STEP_VALUES values of the directory's own
     * keys after the last key of the step before (its prefix idir and '-', so it stops at the
     * directory's end: 015-30, S2-F16); the definition's key hash in its read set; if the index
     * was deleted, the build ends FAILED "deleted"; else each value's entry is put (a value
     * with no entry is counted and skipped; a key without an ikey is skipped, bergdb 021-06).
     * The values' hashes are in the read set, so a concurrent write of one makes the step run
     * again. After a step, a pause of half its time, at most a second (N10). At the end, the
     * activation. Errors: a stop of the database ends the thread, BUILDING; a refusal or an
     * expiry waits 10 to 640 ms and takes the step again (019-38); any other RuntimeException,
     * a DataFormatException or an InternalDataException included, ends the build FAILED, the
     * database going on (019-42); an Error fails the database (019-10).
     */
    static void startBuild(DatabaseImp database, IndexManager m, IndexManager.Live live) {
        Thread thread = new Thread(new Build(database, m, live));
        thread.setPriority(Thread.MIN_PRIORITY);
        thread.setDaemon(true);
        thread.setName("IndexBuild-" + live.def.name() + "-" + live.def.gen());
        live.job.setThread(thread);
        thread.start();
    }

    private static final class Build implements Runnable {
        private final IndexManager m;
        private final IndexManager.Live live;
        private final IndexDefinition def;
        private final ConnectionImp connection;
        private final Db db;
        private final long[] prefix;
        private final long defKeyHash;

        // The step's results, set by its action (which may run again).
        private long[] lastKey;
        private int count;
        private boolean ended;

        Build(DatabaseImp database, IndexManager m, IndexManager.Live live) {
            this.m = m;
            this.live = live;
            this.def = live.def;
            this.connection = new ConnectionImp(database);
            this.db = database.getDb();
            this.prefix = Keys.toSegments(Keys.toBytes(def.idir() + PubKeys.FILE_PREFIX));
            this.defKeyHash = Keys.hash(Keys.toSegments(def.key()));
        }

        public void run() {
            long[] start = prefix;
            long retryWait = RwTransaction.FIRST_SLEEP;
            while (true) {
                long t0 = System.nanoTime();
                final long[] from = start;
                try {
                    connection.rw(env -> step((RwEnvironmentImp) env, from));
                } catch (DeletedException e) {
                    live.job.failed("deleted");
                    return;
                } catch (StreamIoException | IllegalDbStateException e) {
                    return;         // A stop of the database; the next start takes the build.
                } catch (DataFormatException | InternalDataException e) {
                    // Data that the build cannot take, such as an object of format 1 (bergdb
                    // 020-08, step 3): not a refusal, though a DbException.
                    live.job.failed(e.getClass().getName() + ": " + e.getMessage());
                    return;
                } catch (DbException | LookupTimeNotAvailableException e) {
                    retryWait = waitToRetry(retryWait);
                    continue;
                } catch (RuntimeException e) {
                    live.job.failed(e.getClass().getName() + ": " + e.getMessage());
                    return;
                } catch (Throwable e) {
                    db.internal().fail(e);
                    return;
                }
                retryWait = RwTransaction.FIRST_SLEEP;
                if (lastKey != null) {
                    start = lastKey;
                }
                if (ended) {
                    live.job.counted(count);
                    activate();
                    return;
                }
                live.job.counted(count);
                pause(System.nanoTime() - t0);
            }
        }

        private void step(RwEnvironmentImp env, long[] from) {
            lastKey = null;
            count = 0;
            final int max = m.testStepValues > 0 ? m.testStepValues : STEP_VALUES;
            final boolean[] end = new boolean[1];
            GetMany g = db.newGetMany();
            g.startKey = from;
            g.inclusive = false;
            g.stopCondition = new GetMany.StopCondition() {
                private int n = 0;

                public int handleKvt(Kvt kvt) {
                    if (!Keys.isPrefix(prefix, kvt.key)) {
                        end[0] = true;
                        return GetMany.StopCondition.STOP;
                    }
                    n++;
                    return n >= max ? GetMany.StopCondition.ADD_AND_STOP
                            : GetMany.StopCondition.ADD;
                }

                public void eod() {
                    end[0] = true;
                }
            };
            env.getMany(g);
            env.addReadHash(defKeyHash);
            if (!m.isLive(live)) {
                throw new DeletedException();
            }
            m.hook(IndexManager.BUILD_STEP);
            for (Kvt kvt : g.result) {
                lastKey = kvt.key;
                count++;
                String ikey = Keys.bkey2ikeyOrNull(Keys.toBytes(kvt.key));
                if (ikey == null) {
                    continue;
                }
                byte[] entry = def.entry(ikey, kvt.value);
                if (entry != null) {
                    env.set(entry, new byte[0], null);
                }
            }
            ended = end[0] || g.result.size() < max;
        }

        private void activate() {
            long retryWait = RwTransaction.FIRST_SLEEP;
            while (true) {
                try {
                    if (m.activate(live)) {
                        live.job.activated(0);
                    } else {
                        live.job.failed("deleted");
                    }
                    return;
                } catch (StreamIoException | IllegalDbStateException e) {
                    return;
                } catch (DataFormatException | InternalDataException e) {
                    live.job.failed(e.getClass().getName() + ": " + e.getMessage());
                    return;
                } catch (DbException | LookupTimeNotAvailableException e) {
                    retryWait = waitToRetry(retryWait);
                } catch (RuntimeException e) {
                    live.job.failed(e.getClass().getName() + ": " + e.getMessage());
                    return;
                } catch (Throwable e) {
                    db.internal().fail(e);
                    return;
                }
            }
        }
    }

    /**
     * Waits 'ms' milliseconds before an index job takes its step again after a refusal or an
     * expired read, as an rw-transaction waits after a conflict (bergdb 019-38). An interrupt
     * ends the wait, and the job goes on (bergdb 005-46).
     *
     * @return The wait before the next try, ms.
     */
    static long waitToRetry(long ms) {
        try {
            Thread.sleep(ms);
        } catch (InterruptedException e) {
            // BergDB's own thread goes on (bergdb 005-46).
        }
        return RwTransaction.nextSleep(ms);
    }

    /**
     * The pause after a step of 'stepNanos': half its time, at most MAX_PAUSE (020-10, section
     * 6.1). Until 2026-11-09 the cap was computed and not used (N10).
     */
    static long pauseNanos(long stepNanos) {
        return Math.max(0, Math.min(stepNanos / 2, MAX_PAUSE));
    }

    /** Sleeps pauseNanos(stepNanos); an interrupt ends the pause, the job goes on (005-46). */
    static void pause(long stepNanos) {
        long ns = pauseNanos(stepNanos);
        try {
            Thread.sleep(ns / 1000000, (int) (ns % 1000000));
        } catch (InterruptedException e) {
            // BergDB's own thread goes on (bergdb 005-46).
        }
    }

    /** N10: the pause is half the step's time, at most a second. */
    @Nano
    public static void testPauseCapped() {
        Assert.assertEquals(0, pauseNanos(0));
        Assert.assertEquals(5000000, pauseNanos(10000000));
        Assert.assertEquals(MAX_PAUSE, pauseNanos(2 * MAX_PAUSE));
        Assert.assertEquals(MAX_PAUSE, pauseNanos(60L * MAX_PAUSE));
        Assert.assertEquals(0, pauseNanos(-5));
    }
}
