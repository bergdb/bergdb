package bergdb.pubimp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;

import bergdb.core.Db;
import bergdb.core.InternalDataException;
import bergdb.core.RerunException;
import bergdb.core.Trans;
import bergdb.dag.Dag;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.DataFormatException;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.Job;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.storage.StreamIoException;
import bergdb.storage.VersioningStreamException;

/**
 * The user indexes of a database: their definitions in memory, their creation, activation
 * and deletion, the cleanup of a deleted index's entries, and what a start reads (bergdb
 * 020-10, sections 4 to 6). One object per database (DatabaseImp).
 *
 * <p><b>The stored layout</b> (020-10, section 4; IndexKeys, IndexDefinition): a definition
 * per name at /#i/didef/-NAME, a stored object of format 2; the entries of an index under
 * bkey(/#i/dient/dNAME/) and its generation G, the creation's time, so that no index ever
 * sees another's entries; the marker /#i/didel/dNAME/-G16 of a deleted generation until its
 * cleanup ends. The definitions of format 1 (/#i/dii/) refuse a start.</p>
 *
 * <p><b>The lock rule</b> (020-10, section 5.2): a definition's change (a creation, an
 * activation, a deletion) takes the lock, executes its one transaction, and only when that
 * succeeded changes the maps; a refused transaction leaves memory as it was (015-23,
 * S2-F27). A writer reads a directory's index set under the lock after its read time R is
 * fixed (RwEnvironmentImp.indexEntries): if the change committed after R, the writer's hash of
 * the directory's virtual key conflicts with the change's write of it (creations and
 * deletions write it), and the writer runs again; if at or before R, the writer's set has it.
 * An activation does not change the set and writes no virtual key.</p>
 *
 * @author Frans Lundberg
 */
class IndexManager {

    /** The keys a cleanup step deletes at most (020-10, section 6.2). */
    static final int CLEANUP_KEYS = 100;

    /** The virtual keys' directory: only hashes, nothing stored (020-10, section 4.1). */
    private static final String INDEX_VDIR = "/#i/div/";

    /**
     * Guards byName and byIdir, and orders the definitions' changes and the writers' reads
     * of the index sets (020-10, section 5.2).
     */
    private final Object lock = new Object();

    /** The live indexes, building or active, by name. Guarded by 'lock'. */
    private final Map<String, Live> byName = new HashMap<>();

    /** The definitions of the live indexes by their directory's idir. Guarded by 'lock'. */
    private final Map<String, IndexDefinition[]> byIdir = new HashMap<>();

    private DatabaseImp database;
    private Db db;

    /** A live index in this process: its definition, its build's job; deleted once. */
    static final class Live {
        volatile IndexDefinition def;          // Changed by the activation, under 'lock'
        volatile boolean deleted;              // Set by the deletion, under 'lock'
        final IndexBuilderImp.BuildJob job;

        Live(IndexDefinition def, IndexBuilderImp.BuildJob job) {
            this.def = def;
            this.job = job;
        }
    }

    public IndexManager() {}

    // ======== The test hooks (bergdb 020-10, sections 9.2 and 9.3) ========

    /** A write, after its read time is fixed, before it reads the directory's index set. */
    static final String WRITE_BEFORE_SET = "write: before the index set";

    /** A write, after it read the directory's index set. */
    static final String WRITE_AFTER_SET = "write: after the index set";

    /** A definition's change, under the lock, before its transaction; + create, activate or delete. */
    static final String DEFINITION_BEFORE = "definition: before the commit of ";

    /** A definition's change, under the lock, after its transaction; + create, activate or delete. */
    static final String DEFINITION_AFTER = "definition: after the commit of ";

    /** A creation, after its transaction and the lock's release, before its build starts. */
    static final String CREATE_BEFORE_BUILD = "create: before the build starts";
    
    /** A build step, in its action, after its reads, before its transaction. */
    static final String BUILD_STEP = "build: step";

    /** A cleanup step, before its transaction. */
    static final String CLEANUP_STEP = "cleanup: step";

    /** A cleanup's end, before the transaction that deletes the marker. */
    static final String CLEANUP_END = "cleanup: end";

    /**
     * For tests only: called with the points above; null else. A hook may throw, to inject a
     * fault there, interrupt the thread, or stop the database.
     */
    volatile Consumer<String> testHook;
    
    /** For tests only: the values of a build step, if above 0; else STEP_VALUES. */
    volatile int testStepValues;
    
    /** For tests only: if set, the pointer listener of scan()'s reads (020-18, F5). */
    volatile Dag.PointerListener testScanListener;

    /** Calls the test hook, if any, with 'point'. */
    void hook(String point) {
        Consumer<String> h = testHook;
        if (h != null) {
            h.accept(point);
        }
    }

    // ======== The start (020-10, section 4.5) ========

    /**
     * Reads the definitions and the markers at the start's time, after Db.start(): (1) a key
     * under /#i/dii/ (definitions of format 1) refuses the database; (2) every definition is
     * checked (IndexDefinition.fromBytes) and held in memory; (3) every marker starts a
     * cleanup, and one whose generation is a live definition's is an InternalDataException;
     * (4) every definition in state building starts its build. It reads no entry and no user
     * value.
     *
     * @throws VersioningStreamException  If the database holds definitions of format 1.
     * @throws InternalDataException  If a definition or a marker breaks 020-10, section 4.
     */
    void start(DatabaseImp database) {
        this.database = database;
        this.db = database.getDb();
        long t = db.lookupTime(Long.MAX_VALUE);

        if (!scan(IndexKeys.format1Prefix(), t, 1).isEmpty()) {
            throw new VersioningStreamException("The database holds index definitions in the "
                    + "object format of BergDB 2026.3 and before (format 1), which 2026.4 does "
                    + "not read (bergdb 020-02, section 4.11). Make the database again from "
                    + "its data.");
        }

        List<Live> builds = new ArrayList<>();
        synchronized (lock) {
            for (Kvt kvt : scan(IndexKeys.definitionsPrefix(), t, Integer.MAX_VALUE)) {
                String name = IndexKeys.nameOfDefinitionKey(Keys.toBytes(kvt.key));
                IndexDefinition def = IndexDefinition.fromBytes(name, kvt.value);
                IndexBuilderImp.BuildJob job = new IndexBuilderImp.BuildJob(name);
                if (def.isActive()) {
                    job.activated(0);
                    job.ended();
                }
                Live live = new Live(def, job);
                byName.put(name, live);
                add(def);
                if (!def.isActive()) {
                    builds.add(live);
                }
            }
        }

        List<IndexKeys.Marker> markers = markers(t);
        for (IndexKeys.Marker m : markers) {
            Live live = byName.get(m.name);
            if (live != null && live.def.gen() == m.gen) {
                throw new InternalDataException("The marker of a deleted index " + m.name
                        + ", generation " + m.gen + ", names a live definition's generation "
                        + "(bergdb 020-10, section 4.5).");
            }
        }
        for (IndexKeys.Marker m : markers) {
            startCleanup(m.name, m.gen);
        }
        for (Live live : builds) {
            IndexBuilderImp.startBuild(database, this, live);
        }
    }

    // ======== The writers' side (020-10, section 5) ========

    /**
     * The definitions of the indexes of a directory, building and active, read under the lock
     * (020-10, section 5.1, step 3); null if it has none. 'idir' ends with '/'.
     */
    IndexDefinition[] getActiveIndexesForDir(String idir) {
        synchronized (lock) {
            return byIdir.get(idir);
        }
    }

    /** The hash of the virtual key of a directory, /#i/div/IDIR (020-10, section 4.1). */
    public static long vhashOfDir(String idir) {
        long hash = Keys.hash(Keys.toSegments(INDEX_VDIR + idir));
        assert hash > 0;
        return hash;
    }

    // ======== The definitions' changes (020-10, sections 3 and 6) ========

    /**
     * Creates an index (020-10, section 3.1): under the lock, its generation G is the latest
     * transaction's time; one transaction writes its definition, in state building, and the
     * directory's virtual key; then the maps; then its build starts. Returns the build's job.
     *
     * @throws IndexAlreadyExistsException  If an index of the name is live.
     * @throws IllegalArgumentException  If the definition's values break its rules.
     * @throws DbException  If the transaction is refused; nothing changed.
     */
    Job create(String name, String dir, String[] typeNames, String[][] paths) {
        try {
            return createInner(name, dir, typeNames, paths);
        } catch (Error e) {
            throw failed(e);
        }
    }
    
    private Job createInner(String name, String dir, String[] typeNames, String[][] paths) {
        Live live;
        synchronized (lock) {
            if (byName.containsKey(name)) {
                throw new IndexAlreadyExistsException("An index named '" + name
                        + "' exists already.");
            }
            IndexDefinition def = null;
            while (true) {
                long g = Math.max(1, db.lookupTime(Long.MAX_VALUE));
                def = new IndexDefinition(name, dir, g, false, typeNames, paths);
                Trans.Builder b = db.trans();
                b.lookupTime(g);
                b.addReadHash(keyHash(def));
                b.put(def.key(), def.toBytes());
                b.addVirtualWriteHash(vhashOfDir(def.idir()));
                if (execute(b, "create")) {
                    break;
                }
            }
            live = new Live(def, new IndexBuilderImp.BuildJob(name));
            try {
                afterCommit("create");
            } finally {
                byName.put(name, live);
                add(def);
            }
        }
        hook(CREATE_BEFORE_BUILD);
        try {
            IndexBuilderImp.startBuild(database, this, live);
        } catch (RuntimeException e) {
            live.job.failed(e);
            live.job.ended();
            throw e;
        }
        return live.job;
    }

    /**
     * Activates a building index at the end of its build (020-10, section 6.1): under the
     * lock, one transaction rewrites the definition in state active, with its key's hash in the
     * read set; then the maps. Returns false, changing nothing, if the index was deleted.
     *
     * @throws DbException  If the transaction is refused; nothing changed.
     */
    boolean activate(Live live) {
        try {
            return activateInner(live);
        } catch (Error e) {
            throw failed(e);
        }
    }
    
    private boolean activateInner(Live live) {
        synchronized (lock) {
            if (live.deleted || byName.get(live.def.name()) != live) {
                return false;
            }
            IndexDefinition active = live.def.activated();
            while (true) {
                if (live.deleted || byName.get(live.def.name()) != live) {
                    return false;           // Deleted meanwhile (a hook of a test, reentrant)
                }
                Trans.Builder b = db.trans();
                b.lookupTime(db.lookupTime(Long.MAX_VALUE));
                b.addReadHash(keyHash(active));
                b.put(active.key(), active.toBytes());
                if (execute(b, "activate")) {
                    break;
                }
            }
            try {
                afterCommit("activate");
            } finally {
                remove(live.def);
                live.def = active;
                add(active);
            }
            return true;
        }
    }

    /**
     * Deletes an index (020-10, section 6.2): under the lock, one transaction deletes its
     * definition, puts the marker of its generation and writes the directory's virtual key;
     * then the maps, and the index is deleted in memory (its build ends at its next step);
     * then its cleanup starts. When this returns, the name is free.
     *
     * @throws NoSuchIndexException  If no index of the name is live.
     * @throws DbException  If the transaction is refused; nothing changed.
     */
    void delete(String name) {
        try {
            deleteInner(name);
        } catch (Error e) {
            throw failed(e);
        }
    }
    
    private void deleteInner(String name) {
        IndexDefinition def;
        synchronized (lock) {
            Live live = name == null ? null : byName.get(name);
            if (live == null) {
                throw new NoSuchIndexException("No index named '" + name + "'.");
            }
            while (true) {
                if (live.deleted || byName.get(name) != live) {
                    throw new NoSuchIndexException("No index named '" + name + "'.");
                }
                def = live.def;
                Trans.Builder b = db.trans();
                b.lookupTime(db.lookupTime(Long.MAX_VALUE));
                b.addReadHash(keyHash(def));
                b.delete(def.key());
                b.put(IndexKeys.markerKey(def.name(), def.gen()), new byte[0]);
                b.addVirtualWriteHash(vhashOfDir(def.idir()));
                if (execute(b, "delete")) {
                    break;
                }
            }
            try {
                afterCommit("delete");
            } finally {
                byName.remove(name);
                remove(def);
                live.deleted = true;
            }
        }
        startCleanup(def.name(), def.gen());
    }

    /**
     * Fails the database with an Error met in a definition's change, before or after its
     * commit, and returns it to be thrown as it is (bergdb 019-10; 010-01, P7): the change
     * runs on the caller's thread, outside executeRw(), whose catch does the same for a
     * transaction; after the commit, memory and stream would disagree.
     */
    private Error failed(Error e) {
        db.internal().fail(e);
        return e;
    }
    
    /**
     * Executes a definition's change, with the test hook before its commit: true if done,
     * false after a conflict (taken again by the caller, under the lock).
     */
    private boolean execute(Trans.Builder b, String what) {
        hook(DEFINITION_BEFORE + what);
        try {
            db.execute(b.build());
        } catch (RerunException e) {
            return false;
        }
        return true;
    }
    
    /**
     * What comes after a definition's commit, before its change in memory, which its caller
     * makes in a finally: after the commit the change is made in memory too, whatever is
     * thrown (H3-F2, F3: a throw there left the change in the stream and not in memory). A
     * RuntimeException here is swallowed, the change done; an Error is thrown, after the
     * change in memory, and fails the database (failed()).
     */
    private void afterCommit(String what) {
        try {
            hook(DEFINITION_AFTER + what);
        } catch (RuntimeException e) {
            // The change is committed: it stands, and is made in memory (020-10, 3.2).
        }
    }

    /**
     * The job of the live index's build in this process (020-10, section 3.2).
     *
     * @throws NoSuchIndexException  If no index of the name is live.
     */
    Job job(String name) {
        synchronized (lock) {
            Live live = name == null ? null : byName.get(name);
            if (live == null) {
                throw new NoSuchIndexException("No index named '" + name + "'.");
            }
            return live.job;
        }
    }

    /**
     * Runs 'r' under the lock: a build's step after refused tries (IndexBuilderImp), so that
     * only writers that read the index set before can collide with it.
     */
    void underLock(Runnable r) {
        synchronized (lock) {
            r.run();
        }
    }
    
    /** Whether the live index is still the name's (not deleted). */
    boolean isLive(Live live) {
        synchronized (lock) {
            return !live.deleted && byName.get(live.def.name()) == live;
        }
    }

    private void add(IndexDefinition def) {
        IndexDefinition[] a = byIdir.get(def.idir());
        IndexDefinition[] b = a == null ? new IndexDefinition[1] : Arrays.copyOf(a, a.length + 1);
        b[b.length - 1] = def;
        byIdir.put(def.idir(), b);
    }

    private void remove(IndexDefinition def) {
        IndexDefinition[] a = byIdir.get(def.idir());
        if (a == null) {
            return;
        }
        List<IndexDefinition> b = new ArrayList<>();
        for (IndexDefinition d : a) {
            if (d != def) {
                b.add(d);
            }
        }
        if (b.isEmpty()) {
            byIdir.remove(def.idir());
        } else {
            byIdir.put(def.idir(), b.toArray(new IndexDefinition[0]));
        }
    }

    private static long keyHash(IndexDefinition def) {
        return Keys.hash(Keys.toSegments(def.key()));
    }

    // ======== The cleanup (020-10, section 6.2) ========

    /**
     * Starts the cleanup of a deleted generation, in a daemon thread: steps of a getMany of
     * up to CLEANUP_KEYS entry keys of the generation at the latest time, after the last key
     * deleted (bergdb 020-18, F5), and one transaction that deletes them, with no read set (no
     * one writes a deleted generation); when a step finds none, and a read from the prefix
     * finds none, one transaction deletes the marker, and the thread ends. A stop of the
     * database ends it (the next start resumes it); a refusal or an expiry waits and takes
     * the step again; any other RuntimeException ends it, the marker staying; an Error fails
     * the database.
     */
    void startCleanup(final String name, final long gen) {
        final byte[] prefix = IndexKeys.generationPrefix(name, gen);
        final byte[] marker = IndexKeys.markerKey(name, gen);
        Thread thread = new Thread(() -> {
            long retryWait = RwTransaction.FIRST_SLEEP;
            // The last key deleted, or null: a step reads the keys after it, not from the
            // prefix, as a read visits the deleted keys before it (the Core keeps them for
            // earlier lookup times), and the cleanup took the square of the entries' number
            // (bergdb 020-18, F5). When none is left after it, one read from the prefix, then
            // the marker's deletion.
            long[] after = null;
            while (true) {
                long t0 = System.nanoTime();
                try {
                    List<Kvt> keys = scan(prefix, after, Long.MAX_VALUE, CLEANUP_KEYS);
                    if (keys.isEmpty()) {
                        if (after != null) {
                            after = null;
                            continue;
                        }
                        hook(CLEANUP_END);
                        db.execute(db.trans().delete(marker).build());
                        return;
                    }
                    hook(CLEANUP_STEP);
                    Trans.Builder b = db.trans();
                    for (Kvt kvt : keys) {
                        b.delete(kvt.key);
                    }
                    db.execute(b.build());
                    after = keys.get(keys.size() - 1).key;
                    retryWait = RwTransaction.FIRST_SLEEP;
                } catch (StreamIoException | IllegalDbStateException e) {
                    return;         // A stop of the database; the next start resumes it.
                } catch (DataFormatException | InternalDataException e) {
                    return;         // Not a refusal: the marker stays.
                } catch (DbException | LookupTimeNotAvailableException e) {
                    retryWait = IndexBuilderImp.waitToRetry(retryWait);
                    continue;
                } catch (RuntimeException e) {
                    return;         // The marker stays; the next start resumes the cleanup.
                } catch (Throwable e) {
                    db.internal().fail(e);
                    return;
                }
                IndexBuilderImp.pause(System.nanoTime() - t0);
            }
        });
        thread.setPriority(Thread.MIN_PRIORITY);
        thread.setDaemon(true);
        thread.setName("IndexCleanup-" + name + "-" + gen);
        thread.start();
    }

    // ======== Reads of the internal keys ========

    /**
     * The KVs whose keys start with 'prefix' at 'lookupTime', at most 'max', in key order.
     */
    List<Kvt> scan(byte[] prefix, long lookupTime, final int max) {
        return scan(prefix, null, lookupTime, max);
    }

    /** As scan(prefix, lookupTime, max), the keys after 'after' only, if not null. */
    List<Kvt> scan(byte[] prefix, long[] after, long lookupTime, final int max) {
        final long[] prefixSegments = Keys.toSegments(prefix);
        List<Kvt> result = new ArrayList<>();
        long[] start = after == null ? prefixSegments : after;
        boolean inclusive = after == null;
        while (result.size() < max) {
            final int room = max - result.size();
            final boolean[] ended = new boolean[1];
            GetMany g = db.newGetMany();
            g.startKey = start;
            g.inclusive = inclusive;
            g.lookupTime = lookupTime;
            g.stopCondition = new GetMany.StopCondition() {
                private int count = 0;

                public int handleKvt(Kvt kvt) {
                    if (!Keys.isPrefix(prefixSegments, kvt.key)) {
                        ended[0] = true;
                        return GetMany.StopCondition.STOP;
                    }
                    count++;
                    return count >= Math.min(room, 1000) ? GetMany.StopCondition.ADD_AND_STOP
                            : GetMany.StopCondition.ADD;
                }

                public void eod() {
                    ended[0] = true;
                }
            };
            Dag.PointerListener listener = testScanListener;
            if (listener != null) {
                g.gd.pointerListener = listener;
            }
            db.getMany(g);
            result.addAll(g.result);
            if (ended[0] || g.result.isEmpty()) {
                break;
            }
            start = g.result.get(g.result.size() - 1).key;
            inclusive = false;
        }
        return result;
    }

    // ======== For tests ========

    /** The live definition of the name, or null. */
    IndexDefinition definition(String name) {
        synchronized (lock) {
            Live live = byName.get(name);
            return live == null ? null : live.def;
        }
    }

    /** The raw entry keys of a generation at 'lookupTime', in key order. */
    List<byte[]> entries(String name, long gen, long lookupTime) {
        List<byte[]> keys = new ArrayList<>();
        for (Kvt kvt : scan(IndexKeys.generationPrefix(name, gen), lookupTime,
                Integer.MAX_VALUE)) {
            keys.add(Keys.toBytes(kvt.key));
        }
        return keys;
    }

    /** The markers of deleted generations at 'lookupTime'. */
    List<IndexKeys.Marker> markers(long lookupTime) {
        List<IndexKeys.Marker> markers = new ArrayList<>();
        for (Kvt kvt : scan(IndexKeys.markersPrefix(), lookupTime, Integer.MAX_VALUE)) {
            markers.add(IndexKeys.parseMarker(Keys.toBytes(kvt.key)));
        }
        return markers;
    }

    @Nano
    public static void testVhashOfDir() {
        Assert.assertTrue(vhashOfDir("/dp/") != vhashOfDir("/dq/"));
        Assert.assertEquals(vhashOfDir("/dp/"), vhashOfDir("/dp/"));
    }
}
