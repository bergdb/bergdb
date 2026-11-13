package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.channels.FileChannel;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StreamIoException;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;
import bergdb.stream.StrictStream;

/**
 * Harness 6.2 of bergdb 018-01, failures and interrupts in storage (bergdb 018-03). A short
 * workload (a start, puts, gets, syncs, reclaim on, eviction at every chance or none, then
 * stop() and close(), or close()) runs on a FileStream in a directory of its own, on a new
 * database or on one that the first half of the workload made, and a fault is made at the
 * Nth call of one layer, for N = 1, 2, ... until the workload ends before the Nth call. The
 * layers: the stream's calls (StrictStream's hook, above the FileStream) and the file calls
 * (FileStreamIo, below it: opens, writes, forces, deletes, renames). The faults: an
 * IOException, an unchecked exception, an Error, an interrupt of the calling thread, an
 * interrupt of the calling thread and of every thread of BergDB, and a stop() in a call
 * that the workload's thread makes.
 *
 * <p>The checks after each run (bergdb 018-03, section 1):</p>
 * <ul>
 * <li>P7: after a call that threw DbFailedException, or the fault's Error as it is (bergdb
 * 019-10: an Error during a call fails the database), every later transaction and read is
 * refused with a DbFailedException;</li>
 * <li>an interrupt fails no call but sync() (bergdb 005-46, InterruptTester);</li>
 * <li>close() returns, within 10 s; normally if an earlier call reported a failure (bergdb
 * 019-09, option (a));</li>
 * <li>the directory's lock is released: a new FileStream on it opens;</li>
 * <li>no thread of BergDB is left;</li>
 * <li>after a failed write of the storage thread, the next transaction or read fails the
 * database (bergdb 015-35);</li>
 * <li>close() throws if the storage had failed and no call reported it (bergdb 019-09), or
 * if the close met the fault (its Javadoc);</li>
 * <li>a stop() fails nothing, and a transaction that threw at it is not in the stream
 * (bergdb 015-53);</li>
 * <li>a restart works and holds every transaction that a sync() confirmed, and, if no call
 * and not close() reported a failure, every transaction that returned; none that was
 * refused; and the transactions it holds are a prefix of those made, the refused ones
 * aside;</li>
 * <li>no breach of the stream contract (StrictStream).</li>
 * </ul>
 *
 * <p>Test code only. The Nano test "unit" runs a sample of the call numbers; "night" runs
 * them all.</p>
 */
public class StorageFaultTester {
    static final long SEC = Clock.UNITS_PER_SEC;

    /** Where the fault is made. */
    enum Layer { STREAM, IO }

    /** What the fault is. */
    enum Fault { IO_EXCEPTION, UNCHECKED, ERROR, INTERRUPT, INTERRUPT_ALL, STOP }

    /**
     * Known faults that the harness skips, one line per entry, as 018-02's skip list (bergdb
     * 018-03, section 2): a finding of an entry in the list is printed and does not fail the
     * test. A fix removes its line. With -Dbergdb.storagefault.skip=none nothing is skipped.
     */
    static final String[] SKIP = {
    };

    /**
     * Which entry a finding is: the entry, the check, and a regular expression that the
     * finding's text (its signature and example) matches. A finding that no line matches is
     * a new fault.
     */
    static final String[][] FAULTS = {
        // One writer at a time: a call beside the storage thread's append (bergdb 015-80).
        {"015-80", "contract OVERLAP", ".*"},
        // A read in a transaction or a get throws an unchecked exception or an Error from the
        // stream, and the database goes on (bergdb 019-10).
        {"019-10", "met", ".*READ.*"},
        // An Error while a FileStream opens keeps the directory's lock (bergdb 015-32).
        {"015-32", "lock", ".*IO ERROR.*in thread StorageFaultTester-runner.*"},
        // A failed write of the storage thread that no call met: close() returns normally.
        {"019-09", "close", ".*the storage had failed.*no call reported it.*"},
        {"019-09", "restart", ".*it returned, and no call reported a failure.*"},
        // The close meets the fault, and close() returns normally: the storage thread
        // discarded its close's failure (bergdb 015-78, with 015-34's fix, 1b66a34).
        {"015-78", "close", ".*the close met the fault.*"},
        // A failed background write, and a call goes on (bergdb 015-35).
        {"015-35", "background", ".*"},
        // A transaction that runs when stop() comes throws, and is committed (bergdb 015-53).
        {"015-53", "restart", ".*STOP.*was refused.*and is there.*"},
    };

    /** The entries whose findings depend on timing: their lines are not checked for passing. */
    static final String[] TIMING = {
    };

    /** The names of BergDB's threads start with one of these. */
    static final String[] THREAD_PREFIXES = {
        "BufferedStream-consumer-", "bergdb-evictor", "Db-close-", "FileStream-cut",
        "DBMonitor.MThread"
    };

    private static final int TRANSACTIONS = 40;
    private static final int VALUE_SIZE = 3000;
    private static final int BUFFER = 8000;

    private StorageFaultTester() {}

    // ======== The faults ========

    /** An unchecked exception made by the harness. */
    static final class InjectedException extends RuntimeException {
        private static final long serialVersionUID = 1L;
        InjectedException(String message) {
            super(message);
        }
    }

    /** An Error made by the harness. */
    static final class InjectedError extends Error {
        private static final long serialVersionUID = 1L;
        InjectedError(String message) {
            super(message);
        }
    }

    /**
     * For a test: after a STOP, the call waits until the stop's close has ended (up to 30 s),
     * so that a read goes on on the closed stream (bergdb 019-43).
     */
    static volatile boolean waitForCloseAtStop = false;

    private static void waitUntilClosed(Db db) {
        long end = System.nanoTime() + 30L * 1000 * 1000 * 1000;
        while (!db.internal().isClosed() && System.nanoTime() < end) {
            try {
                Thread.sleep(1);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return;
            }
        }
    }

    /** Counts the calls of one layer, and makes the fault at call number 'at'. */
    static final class Injector {
        final Layer layer;
        final Fault fault;
        final long at;
        final AtomicLong count = new AtomicLong();
        volatile boolean fired = false;
        volatile String where = null;
        /** Set by the workload when it calls stop() or close(). */
        volatile boolean closing = false;
        /** Whether the fault came after closing was set, and in which thread. */
        volatile boolean firedClosing = false;
        volatile Thread firedIn = null;
        /** The database, for STOP. */
        volatile Db db = null;
        /** The workload's thread. */
        volatile Thread runner = null;

        Injector(Layer layer, Fault fault, long at) {
            this.layer = layer;
            this.fault = fault;
            this.at = at;
        }

        /**
         * A call of a layer. A checked IOException is not made in a call that cannot throw
         * one (getLength(), getFirstPos()): such a call does not count.
         */
        void call(Layer l, String what, boolean canThrowIo) throws IOException {
            if (l != layer || (fault == Fault.IO_EXCEPTION && !canThrowIo)) {
                return;
            }
            if (fault == Fault.STOP && (db == null || Thread.currentThread() != runner
                    || closing)) {
                return;     // a stop in the workload's thread, in a call of the database's
            }
            long n = count.incrementAndGet();
            if (n != at || fired) {
                return;
            }
            fired = true;
            firedClosing = closing;
            firedIn = Thread.currentThread();
            where = layer + " call " + n + ", " + what + ", in thread "
                    + Thread.currentThread().getName();
            switch (fault) {
            case IO_EXCEPTION:
                throw new IOException("injected IOException at " + where);
            case UNCHECKED:
                throw new InjectedException("injected unchecked exception at " + where);
            case ERROR:
                throw new InjectedError("injected Error at " + where);
            case INTERRUPT:
                Thread.currentThread().interrupt();
                break;
            case INTERRUPT_ALL:
                Thread.currentThread().interrupt();
                for (Thread t : bergdbThreads()) {
                    t.interrupt();
                }
                break;
            case STOP:
                db.stop();      // as if another thread called it now; it does not wait
                if (waitForCloseAtStop) {
                    waitUntilClosed(db);
                }
                break;
            default:
                throw new AssertionError(fault);
            }
        }
    }

    /** FileStreamIo with the injector's calls, and no forces (they cost tens of ms each). */
    static final class FaultIo extends FileStreamIo {
        final Injector inj;

        FaultIo(Injector inj) {
            this.inj = inj;
        }

        protected RandomAccessFile open(File file) throws IOException {
            inj.call(Layer.IO, "open " + file.getName(), true);
            return super.open(file);
        }

        protected void write(File file, RandomAccessFile handle, byte[] bytes, int offset,
                int length) throws IOException {
            inj.call(Layer.IO, "write " + length + " bytes to " + file.getName(), true);
            super.write(file, handle, bytes, offset, length);
        }

        protected void forceFile(File file, RandomAccessFile handle, Force why)
                throws IOException {
            inj.call(Layer.IO, "force " + file.getName() + " (" + why + ")", true);
        }

        protected FileChannel openRead(File file) throws IOException {
            inj.call(Layer.IO, "openRead " + file.getName(), true);
            return super.openRead(file);
        }

        protected void forceDirectory(File directory) throws IOException {
            inj.call(Layer.IO, "forceDirectory", true);
        }

        protected boolean delete(File file) throws IOException {
            inj.call(Layer.IO, "delete " + file.getName(), true);
            return super.delete(file);
        }

        protected boolean rename(File file, File destination) throws IOException {
            inj.call(Layer.IO, "rename " + file.getName(), true);
            return super.rename(file, destination);
        }
    }

    // ======== One run ========

    /** What a run found: each a check that failed, with what it saw. */
    static final class Run {
        final Layer layer;
        final Fault fault;
        final long at;
        final boolean stopFirst;
        /** The run reopens a database that the first half of the transactions made. */
        final boolean reopen;
        /** Eviction at every chance, or none: every other pair of N. */
        final boolean evict;
        Injector inj;
        final List<String[]> findings = new ArrayList<String[]>();     // {check, detail}

        boolean waitedForStorage = false;
        /** A call that threw the fault, or one caused by it, and did not fail the database. */
        String metWithoutFailure = null;
        /** The first call that threw DbFailedException: the database failed. */
        String failedCall = null;
        Throwable failure = null;
        /** The first call that threw, but a sync() that an interrupt ended. */
        String thrownCall = null;
        Throwable thrown = null;
        /** Each transaction's fate: RETURNED, REFUSED, UNCERTAIN, or PENDING until known. */
        final int[] status = new int[TRANSACTIONS];
        /** The transactions before it that returned are confirmed by a sync(). */
        int confirmed = 0;
        boolean closeThrew = false;
        long reclaims = 0, length = 0, firstPos = 0;
        int made = 0;                    // transactions attempted

        int count(int st) {
            int n = 0;
            for (int i = 0; i < made; i++) {
                if (status[i] == st) {
                    n++;
                }
            }
            return n;
        }

        Run(Layer layer, Fault fault, long at, boolean stopFirst, boolean reopen) {
            this.reopen = reopen;
            this.evict = ((at >> 1) & 1) == 0;
            this.layer = layer;
            this.fault = fault;
            this.at = at;
            this.stopFirst = stopFirst;
        }

        void finding(String check, String detail) {
            findings.add(new String[] {check, detail});
        }

        String name() {
            return layer + " " + fault + " at " + at + (stopFirst ? ", stop()" : "")
                    + (reopen ? ", reopened" : "") + (evict ? "" : ", no eviction");
        }
    }

    static final int RETURNED = 1, REFUSED = 2, UNCERTAIN = 3, PENDING = 4;

    private static String key(int i) {
        return "/t" + (1000 + i);
    }

    private static byte[] value(int i) {
        byte[] v = new byte[VALUE_SIZE];
        for (int j = 0; j < v.length; j++) {
            v[j] = (byte) (i * 31 + j);
        }
        return v;
    }

    private static boolean isInterrupt(Fault f) {
        return f == Fault.INTERRUPT || f == Fault.INTERRUPT_ALL;
    }

    /** True if 't' is the harness's fault, or has it as a cause. */
    static boolean causedByFault(Throwable t) {
        for (int i = 0; t != null && i < 20; i++, t = t.getCause()) {
            if (t instanceof InjectedException || t instanceof InjectedError
                    || (t instanceof IOException && t.getMessage() != null
                    && t.getMessage().startsWith("injected IOException"))) {
                return true;
            }
        }
        return false;
    }

    private static boolean isThrown(Fault f) {
        return f == Fault.IO_EXCEPTION || f == Fault.UNCHECKED || f == Fault.ERROR;
    }

    /**
     * Before a transaction or a read: if the fault was thrown in a thread of BergDB, waits
     * up to 0.5 s until the storage has failed. If it has, the call must fail the database
     * (bergdb 015-35: a failed background write fails the database at the next call).
     */
    private static boolean storageFailedBefore(Run run) {
        Injector inj = run.inj;
        Db db = inj.db;
        if (db == null || !inj.fired || !isThrown(run.fault) || inj.firedIn == inj.runner
                || run.failure != null) {
            return false;
        }
        if (!run.waitedForStorage) {
            run.waitedForStorage = true;
            long end = System.nanoTime() + 500L * 1000 * 1000;
            while (!db.internal().storageFailed() && System.nanoTime() < end) {
                try {
                    Thread.sleep(1);
                } catch (InterruptedException e) {
                    break;
                }
            }
        }
        return db.internal().storageFailed();
    }

    /**
     * A call of the workload. Returns true if it returned normally. Checks P7: after a
     * DbFailedException, or the fault's Error, which fails the database and is thrown as it
     * is (2026-11-06, bergdb 019-10), every later transaction and read is refused with a
     * DbFailedException (sync() still works, by its Javadoc); and that an interrupt fails no
     * call but sync(). A call that throws something else may leave the database going on: a
     * transaction that threw, and after which a call returned, was refused; but not after
     * the fault ("met").
     */
    private static boolean call(Run run, String what, Runnable r) {
        final boolean failedBefore = run.failure != null;
        final boolean sync = what.startsWith("sync");
        final boolean storageFailed = !sync && storageFailedBefore(run);
        final String met = run.metWithoutFailure;
        if (!sync) {
            run.metWithoutFailure = null;
        }
        try {
            r.run();
            if (met != null && !sync && run.failure == null) {
                run.finding("met", met + ", and the database went on: " + what
                        + " returned (a database whose storage failed, or that has a bug, does "
                        + "not run on)");
            }
            if (storageFailed && run.failure == null) {
                run.finding("background", what + " returned after the storage had failed "
                        + "(the fault at " + run.inj.where + "), and no call had reported it");
            }
            if (failedBefore && !sync) {
                run.finding("P7", what + " returned after the failure of " + run.failedCall
                        + ": " + run.failure);
            }
            if (!failedBefore && !sync) {
                for (int i = 0; i < run.made; i++) {
                    if (run.status[i] == PENDING) {
                        run.status[i] = REFUSED;    // it threw, and the database went on
                    }
                }
            }
            return true;
        } catch (Throwable t) {
            if (sync && t instanceof StreamIoException && isInterrupt(run.fault)
                    && !failedBefore) {
                return false;       // sync() throws on an interrupt; the database goes on
            }
            if (failedBefore) {
                if (!(t instanceof DbFailedException)) {
                    run.finding("P7", what + " threw " + t + " after the failure of "
                            + run.failedCall + ", not DbFailedException");
                }
                return false;
            }
            if (run.thrown == null) {
                run.thrownCall = what;
                run.thrown = t;
            }
            // An Error is a failure (bergdb 019-10): until then, an Error before a
            // transaction's go point, as in a read, left the database going on. One that is
            // not the fault's fails the database too, and is a bug (bergdb 019-40).
            final boolean failure = t instanceof DbFailedException || t instanceof Error;
            if (t instanceof Error && !causedByFault(t)) {
                run.finding("bug", what + " threw " + t + ", not the fault's Error");
            }
            if (!failure && causedByFault(t)) {
                run.metWithoutFailure = what + " threw " + t + " (the fault at "
                        + run.inj.where + ")";
            }
            if (failure) {
                run.failedCall = what;
                run.failure = t;
                for (int i = 0; i < run.made; i++) {
                    if (run.status[i] == PENDING) {
                        run.status[i] = UNCERTAIN;  // as an Error after the go point
                    }
                }
            }
            if (isInterrupt(run.fault)) {
                run.finding("interrupt", what + " threw " + t + " after an interrupt at "
                        + run.inj.where);
            }
            if (run.fault == Fault.STOP && t instanceof DbFailedException) {
                run.finding("stop", what + " threw " + t + " after a stop() at "
                        + run.inj.where);
            }
            return false;
        } finally {
            Thread.interrupted();
        }
    }

    /** Runs the workload under the injector; returns the run, with its findings. */
    static Run run(Layer layer, Fault fault, long at, boolean stopFirst, boolean reopen)
            throws Exception {
        final Run run = new Run(layer, fault, at, stopFirst, reopen);
        final Injector inj = new Injector(layer, fault, at);
        run.inj = inj;
        final File dir = Files.createTempDirectory("bergdb-storagefault-").toFile();
        final Set<Long> threadsBefore = threadIds(bergdbThreads());
        final StrictStream[] strict = new StrictStream[1];
        try {
            final Throwable[] escaped = new Throwable[1];
            Thread runner = new Thread(new Runnable() {
                public void run() {
                    try {
                        workload(run, inj, dir, strict);
                    } catch (Throwable t) {
                        escaped[0] = t;
                    }
                }
            }, "StorageFaultTester-runner");
            inj.runner = runner;
            runner.start();
            runner.join(10 * 1000);
            if (runner.isAlive()) {
                run.finding("close returns", "the workload or close() hangs, 10 s: "
                        + stack(runner));
                return run;     // the directory and the threads are left
            }
            if (escaped[0] != null) {
                run.finding("harness", "the workload threw " + stackOf(escaped[0]));
            }
            checkThreads(run, threadsBefore);
            checkRestart(run, dir);
            if (strict[0] != null) {
                for (StrictStream.Breach b : strict[0].breaches()) {
                    if (b.kind == StrictStream.Kind.UNCHECKED && b.getCause() != null
                            && (b.getCause() instanceof InjectedException
                            || b.getCause() instanceof InjectedError)) {
                        continue;       // the harness's own fault, from below the FileStream
                    }
                    run.finding("contract " + b.kind, b.getMessage());
                }
            }
        } finally {
            remove(dir);
        }
        return run;
    }

    /** The workload, in the runner thread. */
    private static void workload(final Run run, final Injector inj, File dir,
            StrictStream[] strict) {
        final CoreTestClock clock = new CoreTestClock();
        clock.setTime(SEC);
        final Db[] dbs = new Db[1];
        if (run.reopen) {
            prefill(run, dir, clock);
        }
        FileStream fs;
        try {
            fs = new FileStream(dir, new FaultIo(inj), false);
        } catch (Throwable t) {
            Thread.interrupted();
            run.thrownCall = "new FileStream";
            run.thrown = t;
            if (isInterrupt(run.fault)) {
                run.finding("interrupt", "new FileStream threw " + t + " after an interrupt at "
                        + inj.where);
            }
            return;
        }
        final StrictStream s = new StrictStream(fs);
        strict[0] = s;
        s.tolerate(StrictStream.Kind.values());
        s.setHook(new StrictStream.Hook() {
            public void before(StrictStream.Op op, long n) throws IOException {
                inj.call(Layer.STREAM, op.toString(), op != StrictStream.Op.GET_LENGTH
                        && op != StrictStream.Op.GET_FIRST_POS);
            }
        });
        boolean started = call(run, "start", new Runnable() {
            public void run() {
                dbs[0] = builder(clock, s, run.evict).build();
                dbs[0].start();
            }
        });
        final Db db = dbs[0];
        inj.db = db;
        if (!started) {
            if (db != null) {
                closeAfterFailedStart(run, db);
            } else {
                try {
                    s.close();
                } catch (Throwable t) {
                    // The start failed before the database owned the stream.
                }
            }
            return;
        }
        call(run, "setRetainDuration", new Runnable() {
            public void run() {
                db.setRetainDuration(SEC);
            }
        });
        for (int i = run.made; i < TRANSACTIONS; i++) {
            final int k = i;
            clock.setTime(clock.getTime() + SEC / 4);
            final boolean failedBefore = run.failure != null;
            run.made = i + 1;
            boolean ok = call(run, "execute " + i, new Runnable() {
                public void run() {
                    db.execute(db.trans().put(key(k), value(k))
                            .put("/h" + (k % 5), value(k + 1000)).build());
                }
            });
            if (ok) {
                run.status[i] = RETURNED;
            } else if (failedBefore) {
                run.status[i] = REFUSED;
            } else if (run.failure != null) {
                run.status[i] = UNCERTAIN;      // it failed the database
            } else if (run.fault == Fault.STOP) {
                run.status[i] = REFUSED;        // refused by the stop; it fails nothing
            } else {
                run.status[i] = PENDING;
            }
            if (i % 4 == 1) {
                // A read of the last transaction, likely served from memory (bergdb 015-35).
                call(run, "get " + i, new Runnable() {
                    public void run() {
                        byte[] v = DbUtil.get(db, key(k));
                        if (v != null && !Arrays.equals(v, value(k))) {
                            throw new AssertionError("get of " + key(k) + ": a wrong value");
                        }
                    }
                });
            }
            if (i % 3 == 2) {
                final int g = i / 2;
                call(run, "get " + g, new Runnable() {
                    public void run() {
                        byte[] v = DbUtil.get(db, key(g));
                        if (v != null && !Arrays.equals(v, value(g))) {
                            throw new AssertionError("get of " + key(g) + ": a wrong value");
                        }
                    }
                });
            }
            if (i % 8 == 5) {      // the last two transactions have no sync (bergdb 019-09)
                final int upTo = run.made;
                boolean synced = call(run, "sync after " + i, new Runnable() {
                    public void run() {
                        db.sync(SyncLevel.ORDINARY);
                    }
                });
                if (synced && run.failure == null) {
                    run.confirmed = upTo;
                }
            }
        }
        try {
            run.reclaims = db.getReclaimIterationCount();
            run.length = db.getStreamLength();
            run.firstPos = db.getFirstAvailablePos();
        } catch (Throwable t) {
            // For a run by hand only.
        }
        close(run, db);
        for (int i = 0; i < run.made; i++) {
            if (run.status[i] == PENDING) {
                run.status[i] = UNCERTAIN;
            }
        }
    }

    /**
     * With 'evict', eviction at every chance; without, none (the cache is unbounded), and
     * reads are served from memory but reclaim's.
     */
    private static DbBuilder builder(CoreTestClock clock, bergdb.stream.AppendOnlyStream s,
            boolean evict) {
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        b.clock(clock).stream("main", s, BUFFER, 10).maxNodeSize8().startupDistance(1000);
        if (evict) {
            b.evictionSchedule(Eviction.Schedule.EVERY, 1);
        }
        return b;
    }

    /**
     * For a run that reopens: the first half of the transactions, with no fault, and a
     * close. They are confirmed.
     */
    private static void prefill(Run run, File dir, CoreTestClock clock) {
        try {
            Db db = builder(clock, new FileStream(dir, new NoForceIo(), false), run.evict)
                    .start();
            db.setRetainDuration(SEC);
            for (int i = 0; i < TRANSACTIONS / 2; i++) {
                clock.setTime(clock.getTime() + SEC / 4);
                db.execute(db.trans().put(key(i), value(i))
                        .put("/h" + (i % 5), value(i + 1000)).build());
                run.status[i] = RETURNED;
            }
            db.close();
            run.made = TRANSACTIONS / 2;
            run.confirmed = run.made;
        } catch (IOException e) {
            throw new java.io.UncheckedIOException(e);
        }
    }

    /** A FileStreamIo without forces. */
    static final class NoForceIo extends FileStreamIo {
        protected void forceFile(File file, RandomAccessFile handle, Force why) {}
        protected void forceDirectory(File directory) {}
    }

    private static void closeAfterFailedStart(Run run, Db db) {
        try {
            db.close();
        } catch (Throwable t) {
            // The start's failure was reported by start().
        } finally {
            Thread.interrupted();
        }
    }

    private static void close(Run run, Db db) {
        Injector inj = run.inj;
        if (!inj.fired) {
            // The fault comes after the last call: a background flush meets it first, before
            // the close (bergdb 019-09). The buffer's time is 10 ms.
            try {
                Thread.sleep(50);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        // Before the close begins (bergdb 019-09). A stop() at the fault began it there: a read
        // that ran on and met the stream that its close had closed threw, and the storage
        // records that as failed; it is the close, not a failure before it (bergdb 019-43).
        boolean storageFailed = !(run.fault == Fault.STOP && inj.fired)
                && db.internal().storageFailed();
        inj.closing = true;
        try {
            if (run.stopFirst) {
                db.stop();
            }
            db.close();
            if (run.failure == null && storageFailed) {
                run.finding("close", "the storage had failed (the fault at " + inj.where
                        + "), no call reported it, and close() returned normally (019-09)");
            } else if (run.failure == null && inj.fired && inj.firedClosing
                    && isThrown(run.fault)) {
                run.finding("close", "the close met the fault at " + inj.where
                        + ", and close() returned normally (its Javadoc: a failed final flush "
                        + "or storage close throws StreamIoException)");
            }
        } catch (Throwable t) {
            run.closeThrew = true;
            if (run.failure != null) {
                run.finding("close", "close() threw " + t + " after the failure was reported by "
                        + run.failedCall + " (019-09, option (a): it returns normally)");
            }
            if (isInterrupt(run.fault) && run.thrown == null) {
                run.finding("interrupt", "close() threw " + t + " after an interrupt at "
                        + run.inj.where);
            }
            if (run.fault == Fault.STOP) {
                run.finding("stop", "close() threw " + t + " after a stop() at "
                        + run.inj.where);
            }
        } finally {
            Thread.interrupted();
        }
    }

    // ======== The checks after a run ========

    private static void checkThreads(Run run, Set<Long> before) throws InterruptedException {
        long end = System.nanoTime() + 30L * 1000 * 1000 * 1000;
        List<Thread> left = new ArrayList<Thread>();
        for (Thread t : bergdbThreads()) {
            if (!before.contains(t.getId())) {
                left.add(t);
            }
        }
        for (Thread t : left) {
            t.join(Math.max(1, (end - System.nanoTime()) / 1000000));
        }
        for (Thread t : left) {
            if (t.isAlive()) {
                run.finding("threads", "thread " + t.getName() + " is left after close(): "
                        + stack(t));
            }
        }
    }

    private static void checkRestart(Run run, File dir) {
        FileStream fs;
        try {
            fs = new FileStream(dir, new NoForceIo(), false);
        } catch (Throwable t) {
            run.finding("lock", "a new FileStream on the directory threw " + t);
            return;
        }
        Db db = null;
        try {
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(1000 * SEC);
            db = Db.builder().testSetup(fs).clock(clock).maxNodeSize8().startupDistance(1000)
                    .start();
            boolean allReturned = run.failure == null && !run.closeThrew;
            int gapAt = -1;
            for (int i = 0; i < run.made; i++) {
                byte[] v = DbUtil.get(db, key(i));
                int st = run.status[i];
                if (v != null) {
                    if (st == REFUSED) {
                        run.finding("restart", "transaction " + i + " was refused ("
                                + (run.failure != null ? "after the failure of " + run.failedCall
                                : "it threw, and the database went on") + "), and is there");
                    } else if (gapAt >= 0) {
                        run.finding("restart", "transaction " + i + " is there, an earlier "
                                + "one, " + gapAt + ", is not: not a prefix");
                    }
                    if (!Arrays.equals(v, value(i))) {
                        run.finding("restart", "transaction " + i + ": a wrong value");
                    }
                } else if (st != REFUSED) {
                    if (gapAt < 0) {
                        gapAt = i;
                    }
                    if (st == RETURNED && (allReturned || i < run.confirmed)) {
                        run.finding("restart", "transaction " + i + " is lost; "
                                + (allReturned ? "it returned, and no call reported a failure"
                                : "a sync confirmed it") + "; " + run.confirmed
                                + " confirmed, " + run.count(RETURNED) + " returned");
                        break;
                    }
                }
            }
        } catch (Throwable t) {
            run.finding("restart", "the restart threw " + stackOf(t));
        } finally {
            try {
                if (db != null) {
                    db.close();
                } else {
                    fs.close();
                }
            } catch (Throwable t) {
                run.finding("restart", "the restart's close threw " + t);
            }
        }
    }

    // ======== Helpers ========

    static List<Thread> bergdbThreads() {
        List<Thread> result = new ArrayList<Thread>();
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            for (String p : THREAD_PREFIXES) {
                if (t.getName().startsWith(p) && t.isAlive()) {
                    result.add(t);
                    break;
                }
            }
        }
        return result;
    }

    private static Set<Long> threadIds(List<Thread> ts) {
        Set<Long> ids = new HashSet<Long>();
        for (Thread t : ts) {
            ids.add(t.getId());
        }
        return ids;
    }

    private static String stack(Thread t) {
        StringBuilder sb = new StringBuilder(t.getName());
        for (StackTraceElement e : t.getStackTrace()) {
            sb.append("\n        at ").append(e);
        }
        return sb.toString();
    }

    private static String stackOf(Throwable t) {
        java.io.StringWriter w = new java.io.StringWriter();
        t.printStackTrace(new java.io.PrintWriter(w));
        return w.toString();
    }

    private static void remove(File f) {
        File[] fs = f.listFiles();
        if (fs != null) {
            for (File c : fs) {
                remove(c);
            }
        }
        f.delete();
    }

    // ======== The sweep ========

    /** The findings of a sweep, one example of each (check, layer, fault, call) kept. */
    static final class Results {
        int runs = 0;
        final List<String> slow = new ArrayList<String>();
        final Map<String, String> examples = new LinkedHashMap<String, String>();
        final Map<String, Integer> counts = new LinkedHashMap<String, Integer>();

        void add(Run run) {
            runs++;
            Set<String> sigs = new HashSet<String>();
            for (String[] f : run.findings) {
                String where = run.inj.where == null ? "-" : run.inj.where
                        .replaceAll(" call [0-9]+", "").replaceAll("[0-9]+", "N");
                String sig = f[0] + " | " + run.layer + " " + run.fault
                        + (run.reopen ? " reopened" : "") + " | " + where;
                if (!sigs.add(sig)) {
                    continue;
                }
                Integer c = counts.get(sig);
                counts.put(sig, c == null ? 1 : c + 1);
                if (!examples.containsKey(sig)) {
                    examples.put(sig, run.name() + ": " + f[1]);
                }
            }
        }

        String report() {
            StringBuilder sb = new StringBuilder();
            for (Map.Entry<String, String> e : examples.entrySet()) {
                sb.append(e.getKey()).append(" (").append(counts.get(e.getKey()))
                        .append(" runs)\n    ").append(e.getValue()).append('\n');
            }
            return sb.toString();
        }
    }

    /**
     * Runs every N from 1 until the workload ends before the Nth call of the layer, taking
     * every 'stride'th N (and N = 1 to 3), for each fault.
     */
    static Results sweep(Layer layer, int stride, long seed) throws Exception {
        return sweep(new Results(), layer, stride, seed);
    }

    static Results sweep(Results results, Layer layer, int stride, long seed)
            throws Exception {
        for (boolean reopen : new boolean[] {false, true}) {
            for (Fault fault : Fault.values()) {
                // The end: a run with eviction (which makes the most calls) whose workload
                // ended before call N, or eight runs in a row.
                int ended = 0;
                // After N = 1 to 3, every stride'th N from 4 + (seed % stride).
                for (long at = 1; ended < 8;
                        at = at < 3 ? at + 1 : at == 3 ? 4 + seed % stride : at + stride) {
                    long t0 = System.nanoTime();
                    Run run = run(layer, fault, at, ((at + seed) & 1) == 0, reopen);
                    long ms = (System.nanoTime() - t0) / 1000000;
                    if (ms > 200 && results.slow.size() < 20) {
                        results.slow.add(run.name() + ": " + ms + " ms, at " + run.inj.where);
                    }
                    results.add(run);
                    ended = run.inj.fired ? 0 : run.evict ? 8 : ended + 1;
                }
            }
        }
        return results;
    }

    /**
     * A sample for the unit tests: a few calls of each layer, for each fault, on a new
     * database and on a reopened one: the stream's calls 1, 3 (the first append, without
     * eviction), 500 and 1,500 (with eviction); the file calls 2 (the open), 11 (an early
     * write, without eviction), 60, 147 (the last flush, before the close, in a new run) and
     * 148 (the close's force). They fail on the known faults that the harness catches
     * (bergdb 018-03, section 4). About 4 s; a full workload takes about 40 ms.
     */
    @Nano
    public static void testSample() throws Exception {
        Results r = new Results();
        for (boolean reopen : new boolean[] {false, true}) {
            for (Fault fault : Fault.values()) {
                for (long at : new long[] {1, 3, 500, 1500}) {
                    r.add(run(Layer.STREAM, fault, at, (at & 1) == 0, reopen));
                }
                for (long at : new long[] {2, 11, 60, 147, 148}) {
                    r.add(run(Layer.IO, fault, at, (at & 1) == 0, reopen));
                }
            }
        }
        report(r, false);
    }

    /**
     * A stop() at a read of the workload's thread, which then goes on only when the stop's
     * close has ended (2026-11-06, bergdb 019-43): the read meets the closed stream ("File
     * closed"), the storage records it as failed, and the call throws StreamIoException, as a
     * read while the database stops does (027-01, levels.md section 3). Nothing that returned is
     * lost, and close() returns normally. Harness 6.2's oracle counted it as a failure before
     * the close that no call reported; with JDK 17 the stop's thread sometimes closed the
     * stream before the read, on s1 and F53. Calls 1 (a transaction's warm-up) and 3 (a get).
     */
    @Nano
    public static void testStopWhileReading() throws Exception {
        Results r = new Results();
        waitForCloseAtStop = true;
        try {
            for (long at : new long[] {1, 3}) {
                Run run = run(Layer.STREAM, Fault.STOP, at, false, true);
                if (!(run.thrown instanceof StreamIoException)) {
                    throw new AssertionError("call " + at + ": the read did not meet the "
                            + "closed stream: " + run.thrownCall + " threw " + run.thrown);
                }
                r.add(run);
            }
        } finally {
            waitForCloseAtStop = false;
        }
        report(r, false);
    }

    /**
     * Every 5th call of the stream (and the first three), for each fault, new and reopened,
     * from an offset of the day, so that five nights run every call: about 3,900 runs, 160 s
     * on F53 in a night's load. Every call took 806 s with the file calls' test (2026-11-06).
     */
    @Nano("night")
    public static void testStreamLayerAll() throws Exception {
        long day = java.time.LocalDate.now().getDayOfYear();
        System.out.println("StorageFaultTester: every 5th stream call from " + (4 + day % 5));
        report(sweep(Layer.STREAM, 5, day), true);
    }

    /** Every file call, for each fault, new and reopened: about 1,190 runs, 40 s. */
    @Nano("night")
    public static void testIoLayerAll() throws Exception {
        report(sweep(Layer.IO, 1, 0), true);
    }

    /** The entry of a finding, or null. */
    static String entryOf(String check, String text) {
        for (String[] f : FAULTS) {
            if (check.equals(f[1]) && text.matches("(?s)" + f[2])) {
                return f[0];
            }
        }
        return null;
    }

    private static boolean skipped(String entry) {
        if ("none".equals(System.getProperty("bergdb.storagefault.skip"))) {
            return false;
        }
        return entry != null && Arrays.asList(SKIP).contains(entry);
    }

    /**
     * Prints the findings, each with its entry; fails if one is not skipped. With 'all'
     * (every N was run), a skipped entry whose checks all passed fails too: its fix removes
     * its line, as in 018-02's skip list.
     */
    private static void report(Results r, boolean all) {
        System.out.println("StorageFaultTester: " + r.runs + " runs");
        StringBuilder failures = new StringBuilder();
        Set<String> seen = new HashSet<String>();
        Map<String, Integer> skips = new LinkedHashMap<String, Integer>();
        for (Map.Entry<String, String> e : r.examples.entrySet()) {
            String check = e.getKey().substring(0, e.getKey().indexOf(" | "));
            String text = e.getKey() + "\n" + e.getValue();
            String entry = entryOf(check, text);
            seen.add(entry);
            String line = e.getKey() + " (" + r.counts.get(e.getKey()) + " runs)\n    "
                    + e.getValue() + "\n";
            if (skipped(entry)) {
                Integer n = skips.get(entry);
                if (n == null) {
                    System.out.println("Known fault " + entry + ", skipped: " + line);
                }
                skips.put(entry, (n == null ? 0 : n) + r.counts.get(e.getKey()));
            } else if (entry != null) {
                failures.append(entry).append(": ").append(line);
            } else {
                failures.append("No entry, a new fault: ").append(line);
            }
        }
        for (Map.Entry<String, Integer> e : skips.entrySet()) {
            System.out.println("Known fault " + e.getKey() + ", skipped in " + e.getValue()
                    + " runs (the first shown)");
        }
        if (all) {
            for (String entry : SKIP) {
                if (skipped(entry) && !seen.contains(entry)
                        && !Arrays.asList(TIMING).contains(entry)) {
                    failures.append(entry).append(": in the skip list, "
                            + "StorageFaultTester.SKIP, but its checks pass; its fix removes "
                            + "the line\n");
                }
            }
        }
        if (failures.length() > 0) {
            System.out.println(failures);
            throw new AssertionError("findings:\n" + failures);
        }
    }

    /**
     * For a run by hand: StorageFaultTester LAYER STRIDE (a sweep), LAYER FAULT N [stop]
     * [reopen] (one run), or SAMPLE (the unit test's sample). With
     * -Dbergdb.storagefault.waitclose=true a STOP waits for the stop's close (bergdb 019-43).
     */
    public static void main(String[] args) throws Exception {
        waitForCloseAtStop = Boolean.getBoolean("bergdb.storagefault.waitclose");
        if (args.length == 1 && args[0].equals("SAMPLE")) {
            try {
                testSample();
                System.out.println("SAMPLE PASSED");
            } catch (AssertionError e) {
                System.out.println("SAMPLE FAILED");
            }
            System.exit(0);
        }
        if (args.length >= 3) {
            Run run = run(Layer.valueOf(args[0]), Fault.valueOf(args[1]),
                    Long.parseLong(args[2]), args.length > 3 && args[3].contains("stop"),
                    args.length > 3 && args[3].contains("reopen"));
            System.out.println(run.name() + ", at " + run.inj.where + ": failed call "
                    + run.failedCall + ", " + run.failure + "; thrown first by "
                    + run.thrownCall + "; made " + run.made + ", status "
                    + Arrays.toString(Arrays.copyOf(run.status, run.made)) + ", confirmed "
                    + run.confirmed + ", close threw " + run.closeThrew + "; reclaims "
                    + run.reclaims + ", length " + run.length + ", first pos " + run.firstPos
                    + "; calls " + run.inj.count.get());
            if (run.thrown != null) {
                run.thrown.printStackTrace(System.out);
            }
            for (String[] f : run.findings) {
                System.out.println(f[0] + ": " + f[1]);
            }
            System.exit(0);
        }
        Layer layer = args.length > 0 ? Layer.valueOf(args[0]) : Layer.STREAM;
        int stride = args.length > 1 ? Integer.parseInt(args[1]) : 1;
        long t0 = System.nanoTime();
        Results r = sweep(layer, stride, 0);
        System.out.println(r.runs + " runs, " + (System.nanoTime() - t0) / 1000000 + " ms");
        for (String x : r.slow) {
            System.out.println("slow: " + x);
        }
        System.out.println(r.report());
        System.exit(0);
    }
}
