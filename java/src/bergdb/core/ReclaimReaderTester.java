package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.util.Random;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.dag.GetMany;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Pointer;
import bergdb.dag.Kvt;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.util.Clock;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.FileStream;
import bergdb.stream.ReadBelowFirstPosException;

/**
 * Tests of readers and reclaim cuts (2026-10-13, docs/levels.md, W1).
 *
 * <p>A read is admitted by comparing its lookup time with the first available lookup time.
 * Reclaim can move that time, and cut the stream, while the read runs. A read that
 * reaches the bytes of the cut must fail alone (decision D1 = A): with a
 * LookupTimeNotAvailableException, and without making the stream or the database faulty.
 * Before 2026-10-13 it failed with a StreamIoException, and FileStream remembered the
 * failure so that every later read and append failed too.</p>
 *
 * <p>The reader is held with a stop condition of a GetMany scan, which runs between node
 * reads and so holds no pointer lock; the writer is then driven until the cut is made.
 * The test needs no sleeps.</p>
 */
public class ReclaimReaderTester {
    private static final long SEC = Clock.UNITS_PER_SEC;
    private static final long WAIT_SEC = 60;

    private ReclaimReaderTester() {}

    // ---- The stream of a scenario ----

    /** How a scenario opens, restarts and examines its stream. */
    private interface Kit {
        AppendOnlyStream open() throws IOException;

        /** Called after db.stop() has closed 'old'. */
        AppendOnlyStream reopen(AppendOnlyStream old) throws IOException;

        long firstPos(AppendOnlyStream s);
    }

    /** CutStream: an exact cut; a read below it throws ReadBelowFirstPosException. */
    private static final class CutKit implements Kit {
        public AppendOnlyStream open() {
            return new CutStream();
        }

        public AppendOnlyStream reopen(AppendOnlyStream old) {
            return ((CutStream) old).copy();
        }

        public long firstPos(AppendOnlyStream s) {
            return ((CutStream) s).getCut();
        }
    }

    /** FileStream: whole files are deleted; the case that stopped the database. */
    private static final class FileKit implements Kit {
        private final File dir;

        FileKit(File dir) {
            this.dir = dir;
        }

        public AppendOnlyStream open() throws IOException {
            return new FileStream(dir);
        }

        public AppendOnlyStream reopen(AppendOnlyStream old) throws IOException {
            return new FileStream(dir);
        }

        public long firstPos(AppendOnlyStream s) {
            return ((FileStream) s).getFirstPos();
        }
    }

    static Db start(AppendOnlyStream stream, CoreTestClock clock) {
        Db db = Db.builder().testSetup(stream).clock(clock).maxNodeSize8()
                .startupDistance(2000).start();
        db.setRetainDuration(1 * SEC);
        return db;
    }

    // ---- The scenario ----

    /** What happened to the reader and then to the database. */
    private static final class Outcome {
        Throwable readerError;          // null if the scan finished
        int readerKvs;
        boolean writesAfter;            // the database accepted a write and read it back
        String failure;                 // why writesAfter is false, or null
    }

    private static void put(Db db, Random r, int valueSize) {
        byte[] v = new byte[valueSize / 2 + r.nextInt(valueSize / 2 + 1)];
        r.nextBytes(v);
        db.execute(db.trans().put("/k/" + r.nextInt(50), v).build());
    }

    /**
     * Runs until the first cut, restarts (cold cache), starts a scan at the first
     * available lookup time and holds it after its first KV, runs the writer until
     * the next cut is made, releases the scan, and reports what it did.
     */
    private static Outcome scenario(Kit kit, int valueSize, long seed) throws Exception {
        return scenario(kit, valueSize, seed, false);
    }

    private static Outcome scenario(Kit kit, int valueSize, long seed, final boolean latest)
            throws Exception {
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        AppendOnlyStream stream = kit.open();
        Db db = start(stream, clock);
        Random r = new Random(seed);

        int n = 0;
        while (kit.firstPos(stream) == 0) {
            Assert.assertTrue("no first cut after " + n + " transactions", n++ < 30000);
            time += SEC / 20;
            clock.setTime(time);
            put(db, r, valueSize);
            if (n % 10 == 0) {
                db.sync(SyncLevel.ORDINARY);
            }
        }

        db.sync(SyncLevel.STRONG);
        db.stop();
        stream = kit.reopen(stream);
        clock = new CoreTestClock();
        clock.setTime(time);
        db = start(stream, clock);

        final long t0 = latest ? db.lookupTime(Long.MAX_VALUE)
                : db.getFirstAvailableLookupTime();
        final long pos0 = kit.firstPos(stream);
        final long requiredCut = latest ? db.getStreamLength() : pos0;
        final Db readerDb = db;
        final AppendOnlyStream readerStream = stream;
        final CountDownLatch arrived = new CountDownLatch(1);
        final CountDownLatch release = new CountDownLatch(1);
        final Outcome outcome = new Outcome();
        final AtomicReference<Boolean> done = new AtomicReference<Boolean>(false);

        Thread reader = new Thread(new Runnable() {
            public void run() {
                try {
                    GetMany g = readerDb.newGetMany();
                    g.lookupTime = latest ? Long.MAX_VALUE : t0;
                    g.stopCondition = new GetMany.StopCondition() {
                        private boolean first = true;

                        public int handleKvt(Kvt kvt) {
                            if (first) {
                                first = false;
                                arrived.countDown();
                                try {
                                    release.await();
                                } catch (InterruptedException e) {
                                    throw new RuntimeException(e);
                                }
                                if (latest) {
                                    // Force a backing read even if the writer's rewrites warmed
                                    // the remaining graph. The cut passed the original stream
                                    // length, so this snapshot's first value is now on disk
                                    // below the cut. This isolates expiry classification for
                                    // Long.MAX_VALUE, which was clamped to the finite t0.
                                    try {
                                        readerStream.read(kvt.spos, new byte[1], 0, 1);
                                    } catch (IOException e) {
                                        throw new StreamIoException(e);
                                    }
                                    throw new AssertionError("the backing read was not cut");
                                }
                            }
                            return ADD;
                        }

                        public void eod() {}
                    };
                    readerDb.getMany(g);
                    outcome.readerKvs = g.result.size();
                } catch (Throwable e) {
                    outcome.readerError = e;
                } finally {
                    done.set(true);
                }
            }
        });
        reader.setName("scenario-reader");
        reader.start();
        Assert.assertTrue("the reader did not reach its first KV",
                arrived.await(WAIT_SEC, TimeUnit.SECONDS));

        // The writer: on until the cut has passed the reader's lookup time and been made.
        n = 0;
        while (kit.firstPos(stream) <= requiredCut || db.getFirstAvailableLookupTime() <= t0) {
            if (n++ > 40000) {
                release.countDown();
                throw new AssertionError("no second cut after " + n + " transactions");
            }
            time += SEC / 20;
            clock.setTime(time);
            put(db, r, valueSize);
            if (n % 10 == 0) {
                db.sync(SyncLevel.ORDINARY);
            }
        }

        release.countDown();
        reader.join(WAIT_SEC * 1000);
        Assert.assertTrue("the reader did not end", done.get());

        // Is the database still usable?
        try {
            byte[] v = new byte[] {1, 2, 3};
            time += SEC / 20;
            clock.setTime(time);
            db.execute(db.trans().put("/after", v).build());
            Assert.assertArrayEquals(v, DbUtil.get(db, "/after"));
            GetMany g = db.newGetMany();
            g.lookupTime = db.getFirstAvailableLookupTime();
            db.getMany(g);
            db.checkNodes();
            outcome.writesAfter = true;
        } catch (Throwable e) {
            outcome.failure = e.toString();
        }
        try {
            db.stop();
        } catch (Throwable e) {
            // A database that has failed may fail again here; the outcome says it.
        }
        return outcome;
    }

    /**
     * Runs the scenario with seeds from firstSeed on, and checks the first one whose reader
     * reaches the bytes of the cut. Whether a held reader still needs a version below the
     * cut depends on where the versions lie, which a change of what the writer writes moves:
     * since 2026-10-16 (a transaction is one model transaction, docs/level2-alignment.md, M1
     * and M2), seed 1 of the CutStream scenario ends without reaching the cut, as seeds 2, 8
     * and 11 did before. A reader that does not reach the cut must end with every KV, and the
     * database must go on.
     */
    private static void checkSomeSeed(Kit kit, int valueSize, long firstSeed) throws Exception {
        for (long seed = firstSeed; seed < firstSeed + 10; seed++) {
            Outcome o = scenario(kit, valueSize, seed);
            if (o.readerError == null) {
                Assert.assertTrue("seed " + seed + ": the reader ended without all KVs: "
                        + o.readerKvs, o.readerKvs >= 50);
                Assert.assertTrue("seed " + seed + ": the database failed after the reader: "
                        + o.failure, o.writesAfter);
                continue;
            }
            check(o);
            return;
        }
        throw new AssertionError("no reader reached the cut, seeds " + firstSeed + " to "
                + (firstSeed + 9));
    }

    private static void check(Outcome o) {
        Assert.assertTrue("the reader did not expire; it ended with: " + o.readerError
                + ", KVs: " + o.readerKvs, o.readerError instanceof LookupTimeNotAvailableException);
        boolean cause = false;
        for (Throwable t = o.readerError; t != null; t = t.getCause()) {
            cause |= t instanceof ReadBelowFirstPosException;
        }
        Assert.assertTrue("the cause was not a read below the first position", cause);
        Assert.assertTrue("the database failed after the reader expired: " + o.failure,
                o.writesAfter);
    }

    // ---- Tests ----

    /** Copying and array growth must preserve a slot during a one-way reader swizzle. */
    @Nano
    public static void testCopiesAreCoherentDuringReaderSwizzling() throws Exception {
        final long streamPos = 123456;
        final KeyNode child = new KeyNode();
        child.setSpos(234567);
        final AtomicReference<KeyNode> offered = new AtomicReference<KeyNode>();
        final AtomicInteger complete = new AtomicInteger();
        final AtomicBoolean stop = new AtomicBoolean();
        Thread reader = new Thread(new Runnable() {
            public void run() {
                while (!stop.get()) {
                    KeyNode parent = offered.getAndSet(null);
                    if (parent == null) {
                        Thread.yield();
                        continue;
                    }
                    parent.setPointer(1, child, -10000);
                    complete.incrementAndGet();
                }
            }
        });
        reader.setDaemon(true);
        reader.start();
        try {
            for (int trial = 0; trial < 30000; trial++) {
                KeyNode parent = KeyNode.nodeWithTime(1);
                parent.addToEnd(Klong.createKey(new byte[] {1}), null, streamPos);
                boolean grow = trial % 2 == 1;
                if (grow) {
                    while (parent.size < parent.klongs.length) {
                        parent.addToEnd(Klong.createKey(new byte[] {(byte) parent.size}),
                                null, streamPos);
                    }
                }
                offered.set(parent);
                KeyNode copy;
                if (grow) {
                    parent.addToEnd(Klong.createKey(new byte[] {100}), null, streamPos);
                    copy = parent;
                } else {
                    copy = parent.lastVersion(1);
                }
                Pointer edge = new Pointer();
                copy.getPointer(1, edge);
                Assert.assertTrue("incoherent copied stream pointer at trial " + trial
                        + ": " + edge.pos, edge.node != null || edge.pos == streamPos);
                while (complete.get() <= trial) {
                    Thread.yield();
                }
            }
        } finally {
            stop.set(true);
            reader.join(WAIT_SEC * 1000);
        }
        Assert.assertTrue("the swizzling reader did not end", !reader.isAlive());
    }

    /**
     * Regression test for a data race found 2026-10-13 (java/stress/ReclaimReaders.java,
     * docs/levels.md, "Level 3 follow-up"). A reader that follows a stream pointer replaces it with a
     * memory pointer: the node, then the position (access data instead of a stream
     * position). The writer reads the pair when it serializes the key node. Read as null and
     * then the new position, it took the access data for a stream position: "Bad stream
     * pointer" (with -ea), or a wrong pointer in the stream. KeyNode.getPointer() must give
     * a coherent pair.
     */
    @Nano
    public static void testPointerPairIsCoherent() throws Exception {
        final KeyNode parent = KeyNode.nodeWithTime(1);
        final KeyNode child = new KeyNode();
        final long streamPos = 123456;
        final long accessData = -10000;
        parent.setPointer(0, null, streamPos);
        final AtomicBoolean stop = new AtomicBoolean(false);
        
        Thread flipper = new Thread(new Runnable() {
            public void run() {
                while (!stop.get()) {
                    parent.setPointer(0, child, accessData);    // What a reader does.
                    parent.setPointer(0, null, streamPos);
                }
            }
        });
        flipper.setDaemon(true);
        flipper.start();
        
        Pointer p = new Pointer();
        long deadline = System.nanoTime() + 1500L * 1000 * 1000;
        long reads = 0;
        try {
            while (System.nanoTime() < deadline) {
                for (int i = 0; i < 1000; i++, reads++) {
                    parent.getPointer(0, p);
                    if (p.node == null && p.pos != streamPos) {
                        throw new AssertionError("A stream pointer with position " + p.pos 
                                + ", not " + streamPos + ", after " + reads + " reads.");
                    }
                }
            }
        } finally {
            stop.set(true);
            flipper.join();
        }
    }

    /**
     * Exact cut (CutStream). A scan admitted before the next cut reaches bytes of the cut:
     * it expires, and the database goes on.
     */
    @Nano
    public static void testReaderExpiresWhenCutOvertakesIt() throws Exception {
        checkSomeSeed(new CutKit(), 40, 1);
    }

    /** A default-time scan uses a finite snapshot, which can expire while it is paused. */
    @Nano
    public static void testLatestReaderExpiresWhenCutOvertakesIt() throws Exception {
        check(scenario(new CutKit(), 40, 1, true));
    }

    /**
     * FileStream. Before the fix, the failed read made the stream remember an IOException,
     * and every later read and append failed: one late reader stopped the database.
     */
    @Nano("f")
    public static void testReaderExpiresWhenFilesAreDeleted(TestEnvironment c) throws Exception {
        checkSomeSeed(new FileKit(c.createTempDir()), 1000, 2);
    }
}
