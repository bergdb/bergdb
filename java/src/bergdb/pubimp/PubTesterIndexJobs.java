package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import bergdb.core.Db;
import bergdb.core.InternalDataException;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
import bergdb.pub.DataFormatException;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.IndexBuilder;
import bergdb.pub.Kv;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.ObjectCreationException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.IndexBuildException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.MemoryStream;

/**
 * Tests of the user indexes' jobs and definitions (bergdb 020-10, sections 3, 4 and 6): the
 * builder's checks, the builds and their status, the deletion in one transaction and its
 * cleanup, the generations (a later index of a name never sees an earlier one's entries:
 * 015-21, 015-22, S2-F12), and the rows of 020-10, section 8, that are step I2's. The
 * builds are steered with IndexManager's test hooks.
 *
 * @author Frans Lundberg
 */
public class PubTesterIndexJobs {

    public static class Item {
        public long amount;
        public long other;

        public Item() {}

        public Item(long amount, long other) {
            this.amount = amount;
            this.other = other;
        }
    }

    /**
     * An object with an indexed String field, which may be null (bergdb 019-42), and so
     * absent since format 2 (bergdb 020-04, N11).
     */
    public static class Named {
        public String name;

        public Named() {}

        public Named(String name) {
            this.name = name;
        }
    }

    private static Database start(MemoryStream stream) {
        DatabaseBuilder builder = Factory.database();
        ((DatabaseBuilderImp) builder).getDbBuilder().testSetup(stream);
        return builder.start();
    }

    private static IndexManager manager(Database db) {
        return ((DatabaseImp) db).getIndexManager();
    }

    /** The field 'other' of the objects that the index 'by-field' gives, in its order. */
    private static String others(Database db) {
        List<Long> result = new ArrayList<Long>();
        for (Item item : db.newConnection().useIndex("by-field", Item.class).objects()) {
            result.add(item.other);
        }
        return result.toString();
    }

    private static void putNew(Database db) {
        db.newConnection().w().put("/items/new", new Item(50, 100)).execute();
    }

    /**
     * Deletes the index 'by-field', creates it again on the field 'other', and puts an object
     * (amount 50, other 100): the new index gives [100, 200], the old object's too.
     */
    private static void deleteAndReplace(Database db) {
        db.deleteIndex("by-field");
        db.indexBuilder("by-field").dir("/items/").type("long").field("other").start().join();
        putNew(db);
        Assert.assertEquals("[100, 200]", others(db));
    }

    /** After a restart, the new index still gives [100, 200] and nothing of the old build. */
    private static void checkAfterRestart(MemoryStream stream) {
        Database db = start(stream.copy());
        try {
            Assert.assertEquals("[100, 200]", others(db));
            Assert.assertEquals(JobStatus.State.ACTIVE, db.indexJob("by-field").getStatus()
                    .state());
        } finally {
            db.close();
        }
    }

    /**
     * The build was deleted: join() throws, FAILED "deleted", with no cause; the note does
     * not say that the next start takes the build again (020-18, F2: it did, as for a
     * failure).
     */
    private static void assertDeleted(Job job) {
        IndexBuildException e = assertJoinThrows(job, "by-field");
        Assert.assertEquals("deleted", e.getStatus().reason());
        Assert.assertTrue("no cause", e.getCause() == null);
        String note = e.getStatus().note();
        Assert.assertTrue(note, note.contains("deleted") && !note.contains("next start"));
    }

    /**
     * The job's build failed: join() throws an IndexBuildException, each time, and so do
     * join(millis), join(0) and join(1), all with the status FAILED, the same reason and
     * count, the same cause, and a message that names the index and the reason (Frans,
     * 2026-11-09); getStatus() gives the status without a throw. Returns the first exception.
     */
    static IndexBuildException assertJoinThrows(Job job, String name) {
        IndexBuildException first = null;
        for (int i = 0; i < 5; i++) {
            try {
                JobStatus s = i < 2 ? job.join() : job.join(i == 2 ? 10000 : i == 3 ? 0 : 1);
                throw new AssertionError("join() of a failed build returned " + s.note());
            } catch (IndexBuildException e) {
                JobStatus s = e.getStatus();
                Assert.assertEquals(s.note(), JobStatus.State.FAILED, s.state());
                Assert.assertTrue(e.getMessage(), s.reason() != null
                        && e.getMessage().contains("index " + name + " ")
                        && e.getMessage().contains(s.reason()));
                if (first == null) {
                    first = e;
                } else {
                    Assert.assertTrue("the same cause", e.getCause() == first.getCause());
                    Assert.assertEquals(first.getStatus().reason(), s.reason());
                    Assert.assertEquals(first.getStatus().count(), s.count());
                }
            }
        }
        JobStatus polled = job.getStatus();
        Assert.assertEquals(polled.note(), JobStatus.State.FAILED, polled.state());
        Assert.assertEquals(first.getStatus().reason(), polled.reason());
        Assert.assertEquals(first.getStatus().count(), polled.count());
        return first;
    }

    /** A gate: a hook that waits at a point, once, until opened. */
    static final class Gate {
        final CountDownLatch reached = new CountDownLatch(1);
        final CountDownLatch open = new CountDownLatch(1);
        private final AtomicBoolean once = new AtomicBoolean(true);

        /** Waits at 'point' the first time it is reached, else runs 'other' if not null. */
        void at(String p, String point) {
            if (p.equals(point) && once.compareAndSet(true, false)) {
                reached.countDown();
                await(open);
            }
        }

        void awaitReached() {
            await(reached);
        }

        void open() {
            open.countDown();
        }
    }

    static void await(CountDownLatch latch) {
        try {
            if (!latch.await(10, TimeUnit.SECONDS)) {
                throw new AssertionError("not reached in 10 s");
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError(e);
        }
    }

    // ======== The generations: a build or a cleanup of a deleted index (015-21, 015-22) ========

    /**
     * bergdb 015-22 (review R3-F2): a build waits before its first step while its index is
     * deleted and created again on another field. The old build writes nothing into the new
     * index, ends FAILED with the reason "deleted"; also after a restart.
     */
    @Nano
    public static void testBuildDeletedBeforeItsStep() {
        buildDeleted(true);
    }

    /**
     * bergdb 015-22: the deletion and the new index come in the build's step, after its read
     * and before its transaction: the transaction runs again (the definition's key is in its
     * read set) and the build ends FAILED "deleted".
     */
    @Nano
    public static void testBuildDeletedInItsStep() {
        buildDeleted(false);
    }

    private static void buildDeleted(boolean beforeRead) {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        try {
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            // The step waits after its reads; before its read: the step is then refused
            // once, and taken again after the deletion, from new reads.
            Gate gate = new Gate();
            AtomicBoolean refuse = new AtomicBoolean(beforeRead);
            manager(db).testHook = p -> {
                gate.at(p, IndexManager.BUILD_STEP);
                if (p.equals(IndexManager.BUILD_STEP) && refuse.compareAndSet(true, false)) {
                    throw new DbException("a refusal, by the test");
                }
            };
            Job old = db.indexBuilder("by-field").dir("/items/").type("long").field("amount")
                    .start();
            gate.awaitReached();
            deleteAndReplace(db);
            gate.open();
            assertDeleted(old);
            Assert.assertEquals("[100, 200]", others(db));
        } finally {
            db.close();
        }
        checkAfterRestart(stream);
    }

    /**
     * bergdb 015-22: the deletion comes after the build's last step, as its activation starts
     * (the hook before the activation's commit, under the lock): the activation's transaction
     * conflicts, and it finds the index deleted; the build ends FAILED "deleted".
     */
    @Nano
    public static void testBuildDeletedBeforeActivation() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        try {
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            AtomicBoolean once = new AtomicBoolean(true);
            manager(db).testHook = p -> {
                if (p.equals(IndexManager.DEFINITION_BEFORE + "activate")
                        && once.compareAndSet(true, false)) {
                    db.deleteIndex("by-field");
                }
            };
            Job job = db.indexBuilder("by-field").dir("/items/").type("long").field("amount")
                    .start();
            assertDeleted(job);
            manager(db).testHook = null;
            Assert.assertNull(manager(db).definition("by-field"));
            db.indexBuilder("by-field").dir("/items/").type("long").field("other").start()
                    .join();
            putNew(db);
            Assert.assertEquals("[100, 200]", others(db));
        } finally {
            db.close();
        }
        Database db2 = start(stream.copy());
        try {
            Assert.assertEquals("[100, 200]", others(db2));
        } finally {
            db2.close();
        }
    }

    /**
     * The index is deleted in a build step, after its reads and its check that the index is
     * live, before its commit (the hook BUILD_STEP): the deletion writes the definition's
     * key, which the step read, so the step does not commit, and no entry of the deleted
     * generation is written after the deletion; the build ends FAILED "deleted" (020-10,
     * section 6.1). The cleanup waits meanwhile, so that it cannot remove such an entry
     * first. No test showed it before 020-13, part 2: its fault P10 (no hash of the
     * definition's key in the step's read set) passed the gate.
     */
    @Nano
    public static void testBuildStepDeletedBeforeItsCommit() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        CountDownLatch cleanup = new CountDownLatch(1);
        try {
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            AtomicBoolean once = new AtomicBoolean(true);
            manager(db).testHook = p -> {
                if (p.equals(IndexManager.CLEANUP_STEP) || p.equals(IndexManager.CLEANUP_END)) {
                    await(cleanup);
                } else if (p.equals(IndexManager.BUILD_STEP)
                        && once.compareAndSet(true, false)) {
                    db.deleteIndex("by-field");
                }
            };
            Job job = db.indexBuilder("by-field").dir("/items/").type("long")
                    .field("amount").start();
            assertDeleted(job);
            Assert.assertEquals("the deleted generation's entries", "[]", PubTesterIndexRaces
                    .rawEntries(((DatabaseImp) db).getDb(), "by-field").toString());
            cleanup.countDown();
            PubTesterIndexRaces.awaitCleanups(manager(db));
            manager(db).testHook = null;
        } finally {
            cleanup.countDown();
            db.close();
        }
    }

    /**
     * bergdb 015-21 (review R3-F1), S2-F12: an index deleted twice (the second call refused:
     * the name is free at the first's return), and created again at once on another field
     * while the first deletion's cleanup waits at its step. The cleanup deletes only its own
     * generation's entries: the new index keeps its entry; also after a restart.
     */
    @Nano
    public static void testDeleteTwice() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").start()
                    .join();
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            Gate gate = new Gate();
            manager(db).testHook = p -> gate.at(p, IndexManager.CLEANUP_STEP);
            db.deleteIndex("by-field");
            try {
                db.deleteIndex("by-field");
                throw new AssertionError("a second deletion");
            } catch (NoSuchIndexException e) {
                // Expected: the name is free.
            }
            gate.awaitReached();
            db.indexBuilder("by-field").dir("/items/").type("long").field("other").start()
                    .join();
            putNew(db);
            gate.open();
            PubTesterIndexRaces.awaitCleanups(manager(db));
            manager(db).testHook = null;
            Assert.assertEquals("[100, 200]", others(db));
        } finally {
            db.close();
        }
        Database db2 = start(stream.copy());
        try {
            Assert.assertEquals("[100, 200]", others(db2));
        } finally {
            db2.close();
        }
    }

    /**
     * S2-F12 (020-10, section 8): an index deleted and created again of the same name, with a
     * write between: the new index holds the entries of its own generation only, and the old
     * generation's are gone once its cleanup ended.
     */
    @Nano
    public static void testRaceDeleteRecreate() {
        Database db = start(new MemoryStream());
        try {
            Connection c = db.newConnection();
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").start()
                    .join();
            c.put("/items/a", new Item(1, 10));
            long g1 = manager(db).definition("by-field").gen();
            db.deleteIndex("by-field");
            c.put("/items/b", new Item(2, 20));
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").start()
                    .join();
            long g2 = manager(db).definition("by-field").gen();
            Assert.assertTrue("a new generation", g2 > g1);
            PubTesterIndexRaces.awaitCleanups(manager(db));
            Assert.assertEquals(0, manager(db).entries("by-field", g1, Long.MAX_VALUE).size());
            Assert.assertEquals(2, manager(db).entries("by-field", g2, Long.MAX_VALUE).size());
            Assert.assertEquals("[10, 20]", others(db));
        } finally {
            db.close();
        }
    }

    // ======== Faults in a build (019-10, 019-38, 019-42) ========

    /**
     * bergdb 019-10: an Error in an index build's step fails the database, as on BergDB's
     * other threads; every later call is refused with a DbFailedException whose cause is the
     * Error, and the build's join() returns BUILDING. A RuntimeException ends the build
     * FAILED, with its class and message as the reason, and the database goes on (bergdb
     * 019-42): join() throws an IndexBuildException with the exception as its cause (Frans,
     * 2026-11-09); the definition stays building, so the next start takes the build again
     * and ends ACTIVE.
     */
    @Nano
    public static void testErrorInBuildFailsTheDatabase() {
        for (Throwable thrown : new Throwable[] {new OutOfMemoryError("by the test"),
                new IllegalStateException("by the test")}) {
            MemoryStream stream = new MemoryStream();
            Database db = start(stream);
            try {
                db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
                AtomicBoolean once = new AtomicBoolean(true);
                manager(db).testHook = p -> {
                    if (p.equals(IndexManager.BUILD_STEP) && once.compareAndSet(true, false)) {
                        if (thrown instanceof Error) {
                            throw (Error) thrown;
                        }
                        throw (RuntimeException) thrown;
                    }
                };
                Job job = db.indexBuilder("by-field").dir("/items/").type("long")
                        .field("amount").start();
                if (thrown instanceof Error) {
                    Assert.assertEquals(JobStatus.State.BUILDING, job.join().state());
                    Assert.assertEquals(JobStatus.State.BUILDING, job.join(1000).state());
                    try {
                        putNew(db);
                        throw new AssertionError("the database went on after an Error");
                    } catch (DbFailedException e) {
                        Assert.assertTrue(e.getCause() == thrown);
                    }
                    continue;
                }
                IndexBuildException e = assertJoinThrows(job, "by-field");
                Assert.assertTrue("the cause", e.getCause() == thrown);
                JobStatus status = e.getStatus();
                Assert.assertTrue(status.reason(), status.reason().contains(
                        "IllegalStateException") && status.reason().contains("by the test"));
                assertJoinThrows(db.indexJob("by-field"), "by-field");
                putNew(db);
                db.sync();
            } finally {
                db.close();
            }
            Database db2 = start(stream.copy());
            try {
                Assert.assertEquals(JobStatus.State.ACTIVE, db2.indexJob("by-field").join()
                        .state());
                Assert.assertEquals("[200, 100]", others(db2));
            } finally {
                db2.close();
            }
        }
    }

    /**
     * bergdb 019-42 (020-01, N1, its probe V1Probe): a build over an object that its index
     * cannot read, since 2026.4 an object of format 1 (020-08, step 3), ends FAILED with a
     * reason that names the key and the format, and the database goes on; join() throws, the
     * DataFormatException the cause, also on the job of indexJob(). A start takes the build
     * again, which fails again; the index can be deleted, and the next start has no index. A
     * null String, which failed the build until format 2, is absent: the object gives no
     * entry, as one without the field, and the build ends ACTIVE with the entries of the
     * other two (020-04, N11); after a restart its job is ACTIVE with count 0.
     */
    @Nano
    public static void testBuildOverAnObjectItCannotIndex() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        try {
            db.newConnection().w().put("/named/1", new Named("a"))
                    .put("/named/2", PubTester.format1Payment())
                    .put("/named/3", new Named("c")).execute();
            Job job = db.indexBuilder("by-name").dir("/named/").type("string").field("name")
                    .start();
            Throwable cause = checkFailed(job);
            Assert.assertTrue(db.indexJob("by-name") == job);
            Assert.assertTrue("the same cause", checkFailed(db.indexJob("by-name")) == cause);
            putNew(db);         // DbFailedException if the build failed the database.
        } finally {
            db.close();
        }
        
        MemoryStream restarted = stream.copy();
        db = start(restarted);
        try {
            checkFailed(db.indexJob("by-name"));
            putNew(db);
            db.deleteIndex("by-name");
            PubTesterIndexRaces.awaitCleanups(manager(db));
        } finally {
            db.close();
        }
        
        db = start(restarted.copy());
        try {
            Assert.assertNull(manager(db).definition("by-name"));
            putNew(db);
        } finally {
            db.close();
        }
        
        stream = new MemoryStream();
        db = start(stream);
        try {
            db.newConnection().w().put("/named/1", new Named("a")).put("/named/2", new Named(null))
                    .put("/named/3", new Named("c")).execute();
            JobStatus status = db.indexBuilder("by-name").dir("/named/").type("string")
                    .field("name").start().join();
            Assert.assertEquals(status.note(), JobStatus.State.ACTIVE, status.state());
            Assert.assertEquals(3, status.count());
            StringBuilder names = new StringBuilder();
            for (Named n : db.newConnection().useIndex("by-name", Named.class).objects()) {
                names.append(n.name);
            }
            Assert.assertEquals("ac", names.toString());
        } finally {
            db.close();
        }
        
        db = start(stream.copy());
        try {
            JobStatus status = db.indexJob("by-name").join();
            Assert.assertEquals(JobStatus.State.ACTIVE, status.state());
            Assert.assertEquals(0, status.count());
            putNew(db);
        } finally {
            db.close();
        }
    }
    
    /**
     * join() throws: FAILED, with a reason that names the format-1 object's key and its
     * format, and a DataFormatException as the cause, which is returned.
     */
    private static Throwable checkFailed(Job job) {
        IndexBuildException e = assertJoinThrows(job, "by-name");
        JobStatus status = e.getStatus();
        Assert.assertTrue(status.reason(), status.reason().contains("/dnamed/-2")
                && status.reason().contains("format 1"));
        Assert.assertTrue(String.valueOf(e.getCause()),
                e.getCause() instanceof DataFormatException);
        return e.getCause();
    }

    /**
     * bergdb 019-38 (015-37, N6): an interrupt of an index build's thread while its step waits
     * to run again after a conflict. The hook writes the object that the step read, then
     * interrupts the thread; the step's transaction conflicts, and its wait to run again ends
     * with a refusal (DbException). The build takes the step again and ends ACTIVE, and the
     * database goes on (bergdb 005-46).
     */
    @Nano
    public static void testInterruptInBuildIsNotAFailure() {
        final Database db = start(new MemoryStream());
        try {
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            final AtomicBoolean once = new AtomicBoolean(true);
            manager(db).testHook = p -> {
                if (p.equals(IndexManager.BUILD_STEP) && once.compareAndSet(true, false)) {
                    db.newConnection().w().put("/items/old", new Item(2, 300)).execute();
                    Thread.currentThread().interrupt();
                }
            };
            checkBuildDone(db, once, "[300, 100]");
        } finally {
            db.close();
        }
    }

    /**
     * bergdb 019-38: an expired read (LookupTimeNotAvailableException) and a refusal (a
     * DbException), each thrown once in an index build's step. The build takes the step again
     * and ends ACTIVE, and the database goes on.
     */
    @Nano
    public static void testExpiryOrRefusalInBuildIsNotAFailure() {
        for (final RuntimeException thrown : new RuntimeException[] {
                new LookupTimeNotAvailableException("an expired read, by the test"),
                new DbException("a refusal, by the test")}) {
            final Database db = start(new MemoryStream());
            try {
                db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
                final AtomicBoolean once = new AtomicBoolean(true);
                manager(db).testHook = p -> {
                    if (p.equals(IndexManager.BUILD_STEP) && once.compareAndSet(true, false)) {
                        throw thrown;
                    }
                };
                checkBuildDone(db, once, "[200, 100]");
            } finally {
                db.close();
            }
        }
    }

    /**
     * Runs the build of the index 'by-field' on the field 'amount' to its end: the hook has
     * thrown, the database takes a put, the build is ACTIVE, and the index gives 'expected'.
     */
    private static void checkBuildDone(Database db, AtomicBoolean once, String expected) {
        JobStatus status = db.indexBuilder("by-field").dir("/items/").type("long")
                .field("amount").start().join();
        Assert.assertFalse(once.get());
        putNew(db);         // DbFailedException if the build failed the database.
        Assert.assertEquals(status.note(), JobStatus.State.ACTIVE, status.state());
        Assert.assertEquals(expected, others(db));
    }

    // ======== join() of a failed build throws (Frans, 2026-11-09) ========

    /**
     * bergdb 020-19, F1: a build that ends because its index was deleted is FAILED with the
     * reason "deleted" and no cause, and the index is gone (Database.deleteIndex()), so its
     * note (JobStatus.note()) must not say that the next start takes the build again, as it
     * said; it says so, rightly, for a build that failed over data that it cannot index.
     */
    @Nano
    public static void testNoteOfADeletedBuild() {
        try (final Database db = Factory.database().memory().start()) {
            Connection c = db.connection();
            c.put("/acc/1", new Item(1, 1));
            final Gate gate = new Gate();
            manager(db).testHook = p -> gate.at(p, IndexManager.BUILD_STEP);
            final Job job = db.indexBuilder("i").dir("/acc/").type("long").field("amount")
                    .start();
            gate.awaitReached();
            db.deleteIndex("i");
            gate.open();
            IndexBuildException e = null;
            try {
                job.join();
            } catch (IndexBuildException x) {
                e = x;
            }
            Assert.assertTrue("join() throws", e != null);
            JobStatus s = e.getStatus();
            Assert.assertEquals(JobStatus.State.FAILED, s.state());
            Assert.assertEquals("deleted", s.reason());
            Assert.assertNull(e.getCause());
            Assert.assertTrue(s.note(), s.note().contains("deleted"));
            Assert.assertFalse(s.note(), s.note().contains("next start"));
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("index i failed: deleted"));
            try {
                db.indexJob("i");
                throw new AssertionError("the index is not gone");
            } catch (NoSuchIndexException x) {
                // gone
            }
        }
    }

    /**
     * Each kind of failure of a build makes join() and join(millis) throw an
     * IndexBuildException, each time, with the status FAILED and the exception that failed
     * the build as its cause, on the job that start() returned and on indexJob()'s, while
     * getStatus() gives FAILED without a throw (020-10, section 3.2; Frans, 2026-11-09: "Do
     * as you propose"). Here, thrown once by the hook: data that the build cannot take (a
     * DataFormatException, an InternalDataException) in a step, and a RuntimeException, a
     * bug, in a step and in the activation. The deletion ("deleted", no cause) and an object
     * of format 1 are tested above. The database goes on.
     */
    @Nano
    public static void testJoinThrowsForAFailedBuild() {
        RuntimeException[] faults = {new DataFormatException("bad data, by the test"),
                new InternalDataException("bad internal data, by the test"),
                new IllegalStateException("a bug, by the test"),
                new IllegalStateException("a bug in the activation, by the test")};
        for (int i = 0; i < faults.length; i++) {
            final RuntimeException thrown = faults[i];
            final String point = i < 3 ? IndexManager.BUILD_STEP
                    : IndexManager.DEFINITION_BEFORE + "activate";
            Database db = start(new MemoryStream());
            try {
                db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
                AtomicBoolean once = new AtomicBoolean(true);
                manager(db).testHook = p -> {
                    if (p.equals(point) && once.compareAndSet(true, false)) {
                        throw thrown;
                    }
                };
                Job job = db.indexBuilder("by-field").dir("/items/").type("long")
                        .field("amount").start();
                IndexBuildException e = assertJoinThrows(job, "by-field");
                Assert.assertTrue(thrown + ": the cause", e.getCause() == thrown);
                String reason = e.getStatus().reason();
                Assert.assertTrue(reason, reason.contains(thrown.getClass().getName())
                        && reason.contains(thrown.getMessage()));
                Assert.assertEquals("the values of the committed steps", i < 3 ? 0 : 1,
                        e.getStatus().count());
                Assert.assertTrue(db.indexJob("by-field") == job);
                Assert.assertTrue("the same cause", assertJoinThrows(db.indexJob("by-field"),
                        "by-field").getCause() == thrown);
                putNew(db);         // DbFailedException if the build failed the database.
            } finally {
                db.close();
            }
        }
    }

    /**
     * join() of a build that did not fail returns (Frans, 2026-11-09): BUILDING when the
     * calling thread is interrupted, the build going on and the flag kept (bergdb 005-46),
     * then ACTIVE at the end. join() of a failed build throws also with the flag set, and
     * keeps it. A stop: testStartResumesBuildsAndCleanups; join(millis)'s time:
     * testJoinFromAnotherThread.
     */
    @Nano
    public static void testJoinReturnsAfterAnInterrupt() {
        Database db = start(new MemoryStream());
        try {
            db.newConnection().put("/items/a", new Item(1, 2));
            Gate gate = new Gate();
            manager(db).testHook = p -> gate.at(p, IndexManager.BUILD_STEP);
            Job job = db.indexBuilder("by-field").dir("/items/").type("long").field("amount")
                    .start();
            gate.awaitReached();
            try {
                Thread.currentThread().interrupt();
                Assert.assertEquals(JobStatus.State.BUILDING, job.join().state());
                Assert.assertTrue("the flag kept", Thread.currentThread().isInterrupted());
                Assert.assertEquals(JobStatus.State.BUILDING, job.join(10000).state());
                Assert.assertTrue("the flag kept", Thread.currentThread().isInterrupted());
            } finally {
                Thread.interrupted();
            }
            gate.open();
            Assert.assertEquals(JobStatus.State.ACTIVE, job.join().state());

            manager(db).testHook = p -> {
                if (p.equals(IndexManager.BUILD_STEP)) {
                    throw new IllegalStateException("a bug, by the test");
                }
            };
            Job failed = db.indexBuilder("other").dir("/items/").type("long").field("other")
                    .start();
            assertJoinThrows(failed, "other");
            Thread.currentThread().interrupt();
            try {
                failed.join();
                throw new AssertionError("join() of a failed build returned");
            } catch (IndexBuildException e) {
                Assert.assertTrue("the flag kept", Thread.currentThread().isInterrupted());
            } finally {
                Thread.interrupted();
            }
        } finally {
            db.close();
        }
    }

    // ======== Faults in a cleanup (020-10, section 6.2) ========

    /**
     * bergdb 019-38: an expired read in a cleanup's step, thrown once: the cleanup takes the
     * step again and ends, its marker gone, and the database goes on.
     */
    @Nano
    public static void testExpiryInCleanupIsNotAFailure() {
        Database db = start(new MemoryStream());
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").start()
                    .join();
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            AtomicBoolean once = new AtomicBoolean(true);
            manager(db).testHook = p -> {
                if (p.equals(IndexManager.CLEANUP_STEP) && once.compareAndSet(true, false)) {
                    throw new LookupTimeNotAvailableException("an expired read, by the test");
                }
            };
            db.deleteIndex("by-field");
            PubTesterIndexRaces.awaitCleanups(manager(db));
            Assert.assertFalse(once.get());
            putNew(db);
        } finally {
            db.close();
        }
    }

    /**
     * 020-10, section 6.2: an unexpected RuntimeException in a cleanup ends it silently: the
     * marker stays, the database goes on, and the next start resumes the cleanup to its end.
     * A deletion has no job (015-61, 019-40 C5: gone).
     */
    @Nano
    public static void testBugInCleanupLeavesTheMarker() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        long gen = 0;
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").start()
                    .join();
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            gen = manager(db).definition("by-field").gen();
            Gate gate = new Gate();
            manager(db).testHook = p -> {
                if (p.equals(IndexManager.CLEANUP_STEP)) {
                    gate.reached.countDown();
                    throw new IllegalStateException("a bug, by the test");
                }
            };
            db.deleteIndex("by-field");
            gate.awaitReached();
            putNew(db);
            db.sync();
        } finally {
            db.close();
        }
        db = start(stream.copy());
        try {
            PubTesterIndexRaces.awaitCleanups(manager(db));
            Assert.assertEquals(0, manager(db).entries("by-field", gen, Long.MAX_VALUE).size());
        } finally {
            db.close();
        }
    }

    // ======== Fixes from the review of I2 (2026-11-09) ========

    /**
     * Job.join() from another thread waits until the build ends, also when it is called
     * before the build's thread starts (the review of I2: a thread that called
     * indexJob(name).join() between the creation's commit and the build's start got
     * BUILDING at once, the database running). Forced by the hook between the lock's release
     * and the build's start.
     */
    @Nano
    public static void testJoinFromAnotherThread() throws InterruptedException {
        Database db = start(new MemoryStream());
        try {
            db.newConnection().put("/items/a", new Item(1, 2));
            final java.util.concurrent.atomic.AtomicReference<JobStatus> got =
                    new java.util.concurrent.atomic.AtomicReference<>();
            final Thread[] b = new Thread[1];
            final boolean[] waited = new boolean[1];
            manager(db).testHook = p -> {
                if (p.equals(IndexManager.CREATE_BEFORE_BUILD)) {
                    b[0] = new Thread(() -> got.set(db.indexJob("by-field").join()));
                    b[0].start();
                    try {
                        b[0].join(200);
                    } catch (InterruptedException e) {
                        throw new AssertionError(e);
                    }
                    waited[0] = b[0].isAlive();
                }
            };
            Assert.assertEquals(JobStatus.State.ACTIVE, db.indexBuilder("by-field")
                    .dir("/items/").type("long").field("amount").start().join().state());
            b[0].join(60 * 1000);      // a hang guard; 5 s until bergdb 028-23
            Assert.assertFalse("the other thread's join() returned", b[0].isAlive());
            Assert.assertTrue("join() waited for the build that had not started", waited[0]);
            Assert.assertEquals(JobStatus.State.ACTIVE, got.get().state());
            
            // A job of an index active at a start ends at once; join(millis) waits at most
            // millis.
            Assert.assertEquals(JobStatus.State.ACTIVE, db.indexJob("by-field").join(1)
                    .state());
            Gate gate = new Gate();
            manager(db).testHook = p -> gate.at(p, IndexManager.BUILD_STEP);
            Job job = db.indexBuilder("other").dir("/items/").type("long").field("other")
                    .start();
            gate.awaitReached();
            long t0 = System.nanoTime();
            Assert.assertEquals(JobStatus.State.BUILDING, job.join(50).state());
            Assert.assertTrue("join(50) waited", System.nanoTime() - t0 >= 40000000L);
            gate.open();
            Assert.assertEquals(JobStatus.State.ACTIVE, job.join().state());
        } finally {
            db.close();
        }
    }

    /**
     * An Error in a definition's change, before or after its commit (here thrown by the
     * hooks), fails the database (bergdb 019-10; 010-01, P7): every later call is refused
     * with a DbFailedException whose cause is the Error, so memory and stream cannot go on
     * disagreeing.
     */
    @Nano
    public static void testErrorInDefinitionChangeFailsTheDatabase() {
        String[] points = {IndexManager.DEFINITION_AFTER + "create",
                IndexManager.DEFINITION_BEFORE + "create", IndexManager.DEFINITION_AFTER + "delete"};
        for (String point : points) {
            Database db = start(new MemoryStream());
            try {
                if (point.endsWith("delete")) {
                    db.indexBuilder("by-field").dir("/items/").type("long").field("amount")
                            .start().join();
                }
                Error thrown = new OutOfMemoryError("by the test, at " + point);
                manager(db).testHook = p -> {
                    if (p.equals(point)) {
                        throw thrown;
                    }
                };
                try {
                    if (point.endsWith("delete")) {
                        db.deleteIndex("by-field");
                    } else {
                        db.indexBuilder("by-field").dir("/items/").type("long").field("amount")
                                .start();
                    }
                    throw new AssertionError(point + ": no Error");
                } catch (OutOfMemoryError e) {
                    Assert.assertTrue(e == thrown);
                }
                try {
                    putNew(db);
                    throw new AssertionError(point + ": the database went on after an Error");
                } catch (DbFailedException e) {
                    Assert.assertTrue(point, e.getCause() == thrown);
                }
            } finally {
                db.close();
            }
        }
    }

    /**
     * A build ends while writers write its small directory hard (the review of I1: with 3 or
     * 6 writers on 40 keys at about 130,000 writes a second, each step's transaction was
     * refused by a write of a value it read, again and again, and the build stayed BUILDING
     * after 30 s). After a few refused tries a step runs under the index manager's lock,
     * which writers take before their Core transaction (020-10, 5.2): only the writers that
     * read the index set before it can collide with it. The entries are then exact.
     */
    @Nano
    public static void testBuildEndsUnderWriters() throws InterruptedException {
        Database db = start(new MemoryStream());
        try {
            int keys = 40;
            Connection c0 = db.newConnection();
            for (int k = 0; k < keys; k++) {
                c0.put("/items/k" + k, new Item(k, k));
            }
            AtomicBoolean stop = new AtomicBoolean();
            Thread[] writers = new Thread[3];
            for (int t = 0; t < writers.length; t++) {
                final java.util.Random r = new java.util.Random(t);
                writers[t] = new Thread(() -> {
                    Connection c = db.newConnection();
                    while (!stop.get()) {
                        if (r.nextBoolean()) {
                            c.rw(env -> {
                                env.get("/items/k" + r.nextInt(keys), byte[].class);
                                env.put("/items/k" + r.nextInt(keys), new Item(r.nextInt(100),
                                        1));
                            });
                        } else {
                            c.put("/items/k" + r.nextInt(keys), new Item(r.nextInt(100), 1));
                        }
                    }
                });
                writers[t].start();
            }
            JobStatus status;
            try {
                Thread.sleep(50);
                status = db.indexBuilder("by-field").dir("/items/").type("long")
                        .field("amount").start().join(10000);
            } finally {
                stop.set(true);
                for (Thread t : writers) {
                    t.join(60_000);
                    Assert.assertFalse("a writer thread did not end within 60 s", t.isAlive());
                }
            }
            Assert.assertEquals(status.note(), JobStatus.State.ACTIVE, status.state());
            Assert.assertEquals(keys, entries(db, "by-field"));
        } finally {
            db.close();
        }
    }

    /**
     * 020-18, F1: a write of a key with a suffix in the directory, which has no entry, never
     * makes a build step run again. Such a write takes no index manager's lock (it keeps no
     * index), and it collided with every step that had read its key: after a few refused tries
     * the step ran under the lock and collided with it again and again, while every write at
     * an object key, in any directory, and every index's change waited for the lock (on F53,
     * 24 threads that wrote keys with a suffix of a directory of 10 objects held another
     * directory's object puts up to 0.4 s, against 30 ms without the build). Here a hook writes
     * the step's key k2.txt at each of its first ten tries: the step commits at its first.
     */
    @Nano
    public static void testSuffixWriteDoesNotRerunABuildStep() {
        Database db = start(new MemoryStream());
        try {
            Connection c0 = db.newConnection();
            for (int k = 0; k < 5; k++) {
                c0.put("/items/k" + k, new Item(k, k));
                c0.put("/items/k" + k + ".txt", "text " + k);
            }
            IndexManager m = manager(db);
            Connection w = db.newConnection();
            int[] tries = new int[1];
            m.testHook = p -> {
                if (p.equals(IndexManager.BUILD_STEP) && ++tries[0] <= 10) {
                    w.put("/items/k2.txt", "changed " + tries[0]);
                }
            };
            JobStatus status = db.indexBuilder("by-field").dir("/items/").type("long")
                    .field("amount").start().join(10000);
            m.testHook = null;
            Assert.assertEquals(status.note(), JobStatus.State.ACTIVE, status.state());
            Assert.assertEquals("the tries of the build's one step", 1, tries[0]);
            Assert.assertEquals(5, entries(db, "by-field"));
        } finally {
            db.close();
        }
    }

    /** An object with an indexed field and a large one (020-18, F3). */
    public static class Blob {
        public long n;
        public byte[] data;

        public Blob() {}

        public Blob(long n, int size) {
            this.n = n;
            this.data = new byte[size];
        }
    }

    /**
     * 020-18, F3: a build step reads at most 25 values and stops after the value that takes
     * it to IndexBuilderImp.STEP_BYTES of values. A step that has met writers three times
     * runs under the index manager's lock, reads included, and every write at an object key,
     * in any directory, waits for it: with 100 objects of 4 MB in a memory database and three
     * writers of them, a step of 25 values took about 0.6 s, the lock was held up to 0.84 s,
     * and a small put of another directory waited 0.83 to 1.25 s (0.13 s without the build).
     * Ten objects of 300,000 bytes: three steps, of 4, 4 and 2 values, each of them an entry.
     */
    @Nano
    public static void testBuildStepBoundedByBytes() {
        Database db = start(new MemoryStream());
        try {
            Connection c = db.newConnection();
            for (int k = 0; k < 10; k++) {
                c.put("/blobs/b" + k, new Blob(k, 300000));
            }
            int[] steps = new int[1];
            manager(db).testHook = p -> {
                if (p.equals(IndexManager.BUILD_STEP)) {
                    steps[0]++;
                }
            };
            JobStatus status = db.indexBuilder("by-n").dir("/blobs/").type("long").field("n")
                    .start().join(10000);
            manager(db).testHook = null;
            Assert.assertEquals(status.note(), JobStatus.State.ACTIVE, status.state());
            Assert.assertEquals(10, status.count());
            Assert.assertEquals("the build's steps", 3, steps[0]);
            Assert.assertEquals(10, entries(db, "by-n"));
        } finally {
            db.close();
        }
    }

    /**
     * 020-18, F4: a build reads the directory up to its last key when the build begins; the
     * keys put after it were put after the creation, by writers that keep the index. It read
     * to the directory's end at each step, so writers that appended to the directory faster
     * than the build read it kept it BUILDING for as long as they wrote (on F53, four writers
     * appending 57,000 objects a second: BUILDING after 30 s and 777,200 values read, from a
     * directory of 20,000; ACTIVE 14 s after the writers stopped). Here three objects, steps
     * of two values, and a hook at the first step that appends 30 objects: the build reads 3
     * values, and the index has all 33 entries.
     */
    @Nano
    public static void testBuildReadsUpToItsStartsLastKey() {
        Database db = start(new MemoryStream());
        try {
            Connection c = db.newConnection();
            for (int k = 0; k < 3; k++) {
                c.put("/items/k" + k, new Item(k, k));
            }
            IndexManager m = manager(db);
            m.testStepValues = 2;
            Connection w = db.newConnection();
            boolean[] once = {true};
            m.testHook = p -> {
                if (p.equals(IndexManager.BUILD_STEP) && once[0]) {
                    once[0] = false;
                    for (int k = 0; k < 30; k++) {
                        w.put("/items/x" + k, new Item(100 + k, k));
                    }
                }
            };
            JobStatus status = db.indexBuilder("by-field").dir("/items/").type("long")
                    .field("amount").start().join(10000);
            m.testHook = null;
            Assert.assertEquals(status.note(), JobStatus.State.ACTIVE, status.state());
            Assert.assertEquals("the values the build read", 3, status.count());
            Assert.assertEquals(33, entries(db, "by-field"));
        } finally {
            db.close();
        }
    }

    /**
     * 020-18, F5: a cleanup step goes on after the key that the step before deleted. It read
     * from the generation's prefix each time, and a read visits the deleted keys before the
     * live ones (the Core keeps them for earlier lookup times), so the cleanup's work grew as
     * the square of the entries' number: its reads followed 3.9 times the pointers of one
     * read of all the entries for 1,000 entries, 6.4 times for 2,000, 53 times for 20,000
     * (100,000 entries: a step's read took 0.23 ms at the start and 9.8 ms at the end on F53;
     * 10,000,000 would take about 13 hours). Now 1.6 times, whatever the number. Counted with
     * IndexManager's test listener, for 2,000 entries: at most three times.
     */
    @Nano
    public static void testCleanupWorkIsLinear() throws InterruptedException {
        Database db = start(new MemoryStream());
        try {
            Connection c = db.newConnection();
            for (int i = 0; i < 2000; i += 500) {
                bergdb.pub.WBuilder w = c.w();
                for (int k = i; k < i + 500; k++) {
                    w.put(String.format("/many/k%06d", k), new Item(k, k));
                }
                w.execute();
            }
            db.indexBuilder("by-field").dir("/many/").type("long").field("amount").start()
                    .join();
            IndexManager m = manager(db);
            long gen = m.definition("by-field").gen();
            java.util.concurrent.atomic.AtomicLong all = new java.util.concurrent.atomic.AtomicLong();
            java.util.concurrent.atomic.AtomicLong cleanup =
                    new java.util.concurrent.atomic.AtomicLong();
            m.testScanListener = new bergdb.dag.Dag.PointerListener() {
                public void superRootAccessed(bergdb.dag.TopNode superRoot) {}

                public void pointerFollowed(bergdb.dag.Node predecessor, int pointerIndex,
                        bergdb.dag.Node result, int pointerType) {
                    all.incrementAndGet();
                    if (Thread.currentThread().getName().startsWith("IndexCleanup-")) {
                        cleanup.incrementAndGet();
                    }
                }
            };
            Assert.assertEquals(2000, m.entries("by-field", gen, Long.MAX_VALUE).size());
            long oneRead = all.get();
            db.deleteIndex("by-field");
            long end = System.currentTimeMillis() + 10000;
            while (!m.markers(Long.MAX_VALUE).isEmpty()) {
                Assert.assertTrue("the cleanup ended in 10 s", System.currentTimeMillis() < end);
                Thread.sleep(2);
            }
            m.testScanListener = null;
            Assert.assertEquals(0, m.entries("by-field", gen, Long.MAX_VALUE).size());
            Assert.assertTrue("the cleanup's reads followed " + cleanup.get() + " pointers, one "
                    + "read of the entries " + oneRead, cleanup.get() <= 3 * oneRead);
        } finally {
            db.close();
        }
    }

    // ======== The builder (020-10, section 3.1) ========

    /** S2-F20: dir() twice is refused at once; the builder needs dir() first. */
    @Nano
    public static void testDirTwice() {
        Database db = start(new MemoryStream());
        try {
            assertState(() -> db.indexBuilder("d").dir("/a/").dir("/b/"));
            assertState(() -> db.indexBuilder("d").type("long"));
            assertState(() -> db.indexBuilder("d").dir("/a/").field("x"));
            assertState(() -> db.indexBuilder("d").dir("/a/").type("long").field("x")
                    .field("y"));
            assertState(() -> db.indexBuilder("d").dir("/a/").type("long").type("long"));
            assertState(() -> db.indexBuilder("d").start());
            assertState(() -> db.indexBuilder("d").dir("/a/").start());
            assertState(() -> db.indexBuilder("d").dir("/a/").type("long").start());
            IndexBuilder nine = db.indexBuilder("d").dir("/a/");
            for (int i = 0; i < 8; i++) {
                nine.type("long").field("f" + i);
            }
            assertState(() -> nine.type("long"));
            assertArgument(() -> db.indexBuilder("d").dir("/a/").type("string/unicode"));
            assertArgument(() -> db.indexBuilder("d").dir("/a/").type("int"));
            assertArgument(() -> db.indexBuilder("d").dir("a/"));
            assertArgument(() -> db.indexBuilder("a b"));
            assertArgument(() -> db.indexBuilder("a/b"));
            assertArgument(() -> db.indexBuilder(""));

            // The builder is spent after start(), whatever it threw.
            IndexBuilder b = db.indexBuilder("d").dir("/a/").type("long");
            assertState(() -> b.start());
            assertState(() -> b.field("x"));
            IndexBuilder c = db.indexBuilder("d").dir("/a/").type("long").field("x");
            c.start().join();
            assertState(() -> c.start());
            try {
                db.indexBuilder("d").dir("/b/").type("long").field("y").start();
                throw new AssertionError("an existing name");
            } catch (IndexAlreadyExistsException e) {
                // Expected.
            }
        } finally {
            db.close();
        }
    }

    /**
     * S2-F15: a nested field's empty part is refused at the call, as a name that is not 1 to
     * 255 UTF-8 bytes; a part may hold '.' when the parts are given; 16 parts at most.
     */
    @Nano
    public static void testNestedFieldEmptyPart() {
        Database db = start(new MemoryStream());
        try {
            for (String path : new String[] {"a..b", ".a", "a.", ".", ""}) {
                assertArgument(() -> db.indexBuilder("n").dir("/a/").type("long")
                        .nestedField(path));
            }
            assertArgument(() -> db.indexBuilder("n").dir("/a/").type("long")
                    .nestedField(new String[] {"a", ""}));
            assertArgument(() -> db.indexBuilder("n").dir("/a/").type("long")
                    .nestedField(new String[0]));
            assertArgument(() -> db.indexBuilder("n").dir("/a/").type("long")
                    .nestedField((String[]) null));
            assertArgument(() -> db.indexBuilder("n").dir("/a/").type("long").field(""));
            assertArgument(() -> db.indexBuilder("n").dir("/a/").type("long").field(null));
            assertArgument(() -> db.indexBuilder("n").dir("/a/").type("long")
                    .field(IndexKeysTester.repeat("x", 256)));
            assertArgument(() -> db.indexBuilder("n").dir("/a/").type("long")
                    .field("a\ud800"));
            String[] seventeen = new String[17];
            java.util.Arrays.fill(seventeen, "a");
            assertArgument(() -> db.indexBuilder("n").dir("/a/").type("long")
                    .nestedField(seventeen));
            db.indexBuilder("n").dir("/a/").type("long").nestedField(new String[] {"a.b", "c"})
                    .start().join();
            Assert.assertEquals("[a.b, c]", java.util.Arrays.toString(
                    manager(db).definition("n").path(0)));
        } finally {
            db.close();
        }
    }

    /**
     * 015-29: "primary" is a name like any other: deleteIndex("primary") of no such index is
     * NoSuchIndexException (it was a Bug, the primary scan's pseudo-index), and an index of
     * the name is created and deleted.
     */
    @Nano
    public static void testIndexNamedPrimary() {
        Database db = start(new MemoryStream());
        try {
            try {
                db.deleteIndex("primary");
                throw new AssertionError("deleted");
            } catch (NoSuchIndexException e) {
                // Expected.
            }
            db.newConnection().put("/items/a", new Item(1, 2));
            Assert.assertEquals(JobStatus.State.ACTIVE, db.indexBuilder("primary").dir("/items/")
                    .type("long").field("amount").start().join().state());
            Assert.assertEquals(1, manager(db).entries("primary",
                    manager(db).definition("primary").gen(), Long.MAX_VALUE).size());
            db.deleteIndex("primary");
            Assert.assertNull(manager(db).definition("primary"));
        } finally {
            db.close();
        }
    }

    // ======== The build (020-10, section 6.1) ========

    /**
     * 015-30, S2-F16: a build reads its directory's own keys only: not its subdirectories',
     * not the keys after it; the coordinator's probe (2026-11-09): an index on "/" after an
     * index on "/p/" with five objects reads neither the other index's entries nor the
     * internal keys (since 021-06 a key without an ikey failed such a build).
     */
    @Nano
    public static void testBuildStopsAtDir() {
        Database db = start(new MemoryStream());
        try {
            Connection c = db.newConnection();
            c.put("/a/x", new Item(1, 1));
            c.put("/a/sub/y", new Item(2, 2));
            c.put("/b/z", new Item(3, 3));
            c.put("/az", new Item(4, 4));
            JobStatus s = db.indexBuilder("a").dir("/a/").type("long").field("amount").start()
                    .join();
            Assert.assertEquals(JobStatus.State.ACTIVE, s.state());
            Assert.assertEquals("values read", 1, s.count());
            Assert.assertEquals(1, entries(db, "a"));

            db.indexBuilder("p").dir("/p/").type("long").field("amount").start().join();
            for (int i = 0; i < 5; i++) {
                c.put("/p/" + i, new Item(i, i));
            }
            s = db.indexBuilder("root").dir("/").type("long").field("amount").start().join();
            Assert.assertEquals(s.note(), JobStatus.State.ACTIVE, s.state());
            Assert.assertEquals("the root's own values", 1, s.count());
            Assert.assertEquals(1, entries(db, "root"));
        } finally {
            db.close();
        }
    }

    /** S2-F16: an index of a directory has no entry of its subdirectories' values. */
    @Nano
    public static void testSubdirNotIndexed() {
        Database db = start(new MemoryStream());
        try {
            Connection c = db.newConnection();
            db.indexBuilder("a").dir("/a/").type("long").field("amount").start().join();
            c.put("/a/sub/y", new Item(2, 2));
            c.put("/a/x", new Item(1, 1));
            Assert.assertEquals(1, entries(db, "a"));
            int n = 0;
            for (Kv<Item> kv : c.useIndex("a", Item.class).kvs()) {
                Assert.assertEquals("/a/x", kv.key());
                n++;
            }
            Assert.assertEquals(1, n);
        } finally {
            db.close();
        }
    }

    /**
     * N7: a value whose levels take more than 111 bytes (L6; 4,096 until bergdb 024-24), put
     * before the index, has no entry, so no step can be too large to commit; the build ends
     * ACTIVE. With the index there, a put of such a value is refused with
     * IllegalArgumentException, nothing written (QL4; until 024-24 it was taken with no
     * entry); one at 111 bytes, a string of 110, is taken with its entry.
     */
    @Nano
    public static void testLargeValueNoEntry() {
        Database db = start(new MemoryStream());
        try {
            Connection c = db.newConnection();
            c.put("/named/big", new Named(IndexKeysTester.repeat("x", 5000)));
            c.put("/named/small", new Named("s"));
            JobStatus s = db.indexBuilder("n").dir("/named/").type("string").field("name")
                    .start().join();
            Assert.assertEquals(JobStatus.State.ACTIVE, s.state());
            Assert.assertEquals(1, entries(db, "n"));
            for (int n : new int[] {5000, IndexKeys.MAX_LEVEL_BYTES}) {
                try {
                    c.put("/named/big2", new Named(IndexKeysTester.repeat("y", n)));
                    throw new AssertionError("a put of levels over L6 was taken");
                } catch (IllegalArgumentException e) {
                    Assert.assertTrue(e.getMessage(), 
                            e.getMessage().contains("(bergdb 024-17, L6)"));
                }
                Assert.assertNull(c.get("/named/big2", byte[].class));
                Assert.assertEquals(1, entries(db, "n"));
            }
            c.put("/named/big2", new Named(IndexKeysTester.repeat("y", 
                    IndexKeys.MAX_LEVEL_BYTES - 1)));
            Assert.assertEquals(2, entries(db, "n"));
        } finally {
            db.close();
        }
    }

    /**
     * 015-39: a status is a snapshot: one read while building stays BUILDING, with its count,
     * after the build ends.
     */
    @Nano
    public static void testStatusIsSnapshot() {
        Database db = start(new MemoryStream());
        try {
            db.newConnection().put("/items/a", new Item(1, 2));
            Gate gate = new Gate();
            manager(db).testHook = p -> gate.at(p, IndexManager.BUILD_STEP);
            Job job = db.indexBuilder("by-field").dir("/items/").type("long").field("amount")
                    .start();
            gate.awaitReached();
            JobStatus early = job.getStatus();
            gate.open();
            JobStatus end = job.join();
            Assert.assertEquals(JobStatus.State.BUILDING, early.state());
            Assert.assertEquals(0, early.count());
            Assert.assertNull(early.reason());
            Assert.assertEquals(JobStatus.State.ACTIVE, end.state());
            Assert.assertEquals(1, end.count());
            Assert.assertTrue(db.indexJob("by-field") == job);
            Assert.assertEquals(JobStatus.State.BUILDING, early.state());
        } finally {
            db.close();
        }
    }

    /**
     * 015-36: deleteIndex() with the caller's interrupt flag set: one transaction, done, the
     * flag kept; there is no job to interrupt.
     */
    @Nano
    public static void testDeleteWithInterruptFlag() {
        Database db = start(new MemoryStream());
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").start()
                    .join();
            Thread.currentThread().interrupt();
            try {
                db.deleteIndex("by-field");
                Assert.assertTrue("the flag kept", Thread.currentThread().isInterrupted());
            } finally {
                Thread.interrupted();
            }
            Assert.assertNull(manager(db).definition("by-field"));
            try {
                db.indexJob("by-field");
                throw new AssertionError("a job of a deleted index");
            } catch (NoSuchIndexException e) {
                // Expected.
            }
        } finally {
            db.close();
        }
    }

    /**
     * N11 (020-10, section 5.3): with key replace, only the value's name K of an entry is
     * replaced, not an indexed string that holds "${transactionTime}".
     */
    @Nano
    public static void testKeyReplaceIndexedText() {
        Database db = start(new MemoryStream());
        try {
            Connection c = db.newConnection();
            c.setEnableKeyReplace(true);
            db.indexBuilder("n").dir("/named/").type("bytes").field("raw").start().join();
            db.indexBuilder("s").dir("/named/").type("string").field("name").start().join();
            String text = "${transactionTime}";
            byte[] raw = Keys.toBytes(text);      // Bytes as a key holds the text
            c.put("/named/k${transactionTime}", new Raw(text, raw));
            IndexDefinition s = manager(db).definition("s");
            List<byte[]> e = manager(db).entries("s", s.gen(), Long.MAX_VALUE);
            Assert.assertEquals(1, e.size());
            IndexKeys.Entry entry = IndexKeys.parseEntry(e.get(0), s.generationPrefix(),
                    s.types());
            Assert.assertEquals(text, entry.value(0));
            Assert.assertFalse(entry.fileName().contains("${"));
            IndexDefinition n = manager(db).definition("n");
            List<byte[]> f = manager(db).entries("n", n.gen(), Long.MAX_VALUE);
            Assert.assertEquals(1, f.size());
            IndexKeys.Entry fe = IndexKeys.parseEntry(f.get(0), n.generationPrefix(),
                    n.types());
            Assert.assertArrayEquals(raw, (byte[]) fe.value(0));
            Assert.assertEquals(1, count(c.useIndex("s", Raw.class).eq(text).objects()));
        } finally {
            db.close();
        }
    }

    /**
     * The Codex review's X1 (bergdb 020-14): with key replace, a put at an object key whose
     * directory holds "${transactionTime}" is refused with IllegalArgumentException at the
     * call, by Connection.put, WBuilder.put and RwEnvironment.put, for an object, a String and
     * a byte[], before anything is written: the directory the put lands in is known only at
     * the commit, after the maintenance (020-10, section 5.1) has read its index set. Until
     * 2026-11-09 the maintenance took the key as written: an index of the directory as written
     * lost the entry of an object that the put did not change, and an index of the directory
     * the put landed in missed the new object, also after a restart. A delete's key is taken
     * as written, so a delete there works; key replace off, the key is the key as written.
     */
    @Nano
    public static void testKeyReplaceInDirectoryRefused() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        final String dir = "/p/${transactionTime}/";
        try {
            final Connection c = db.newConnection();
            c.put(dir + "k", new Item(7, 1));             // key replace off: as written
            c.put(dir + "d", new Item(8, 1));
            db.indexBuilder("by-field").dir(dir).type("long").field("amount").start().join();
            c.setEnableKeyReplace(true);
            for (final Object value : new Object[] {new Item(9, 2), "text", new byte[] {1}}) {
                assertArgument(() -> c.put(dir + "k", value));
                assertArgument(() -> c.w().put(dir + "k", value));
                assertArgument(() -> c.rw(env -> env.put(dir + "k", value)));
                assertArgument(() -> c.put("/q/${transactionTime}/x${transactionTime}", value));
            }
            Assert.assertEquals(7L, c.get(dir + "k", Item.class).amount);
            Assert.assertEquals(1, count(c.useIndex("by-field", Item.class).eq(7L).objects()));
            c.put(dir + "k.txt", "replaced");             // a suffix: never indexed
            c.delete(dir + "d");                          // as written
            Assert.assertEquals(null, c.get(dir + "d", Item.class));
            Assert.assertEquals(0, count(c.useIndex("by-field", Item.class).eq(8L).objects()));
            c.setEnableKeyReplace(false);
            c.put(dir + "m", new Item(9, 3));
            Assert.assertEquals(1, count(c.useIndex("by-field", Item.class).eq(9L).objects()));
        } finally {
            db.close();
        }
        db = start(stream.copy());
        try {
            Connection c = db.newConnection();
            Assert.assertEquals(7L, c.get(dir + "k", Item.class).amount);
            Assert.assertEquals(1, count(c.useIndex("by-field", Item.class).eq(7L).objects()));
            Assert.assertEquals(0, count(c.useIndex("by-field", Item.class).eq(8L).objects()));
            Assert.assertEquals(1, count(c.useIndex("by-field", Item.class).eq(9L).objects()));
            Assert.assertEquals(2, entries(db, "by-field"));
        } finally {
            db.close();
        }
    }

    /**
     * A sibling of X1 (bergdb 020-14): with key replace, a put at an object key whose name
     * holds "${transactionTime}" leaves the object at the key as written, and its index
     * entry, as they were: the put lands at a new key, whose name holds the transaction's
     * time, after every earlier one. Until 2026-11-09 the maintenance read the previous value
     * at the key as written and deleted that object's entry: an index lookup missed it, also
     * after a restart.
     */
    @Nano
    public static void testKeyReplaceInNameKeepsTheKeyAsWritten() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        String key = "/n/${transactionTime}";
        String replaced;
        try {
            Connection c = db.newConnection();
            c.put(key, new Item(7, 1));                   // key replace off: as written
            db.indexBuilder("by-field").dir("/n/").type("long").field("amount").start().join();
            c.setEnableKeyReplace(true);
            long time = c.put(key, new Item(9, 2)).getTime().units();
            replaced = "/n/" + String.format(java.util.Locale.ROOT, "%018d", time);
            Assert.assertEquals(9L, c.get(replaced, Item.class).amount);
            Assert.assertEquals(7L, c.get(key, Item.class).amount);
            Assert.assertEquals("[1]", others(c, 7));
            Assert.assertEquals("[2]", others(c, 9));
        } finally {
            db.close();
        }
        db = start(stream.copy());
        try {
            Connection c = db.newConnection();
            Assert.assertEquals("[1]", others(c, 7));
            Assert.assertEquals("[2]", others(c, 9));
            Assert.assertEquals(2, entries(db, "by-field"));
        } finally {
            db.close();
        }
    }

    /** The field 'other' of the objects that the index 'by-field' gives for 'amount'. */
    private static String others(Connection c, long amount) {
        List<Long> result = new ArrayList<Long>();
        for (Item item : c.useIndex("by-field", Item.class).eq(amount).objects()) {
            result.add(item.other);
        }
        return result.toString();
    }

    /** An object with a String and a byte[]. */
    public static class Raw {
        public String name;
        public byte[] raw;

        public Raw() {}

        public Raw(String name, byte[] raw) {
            this.name = name;
            this.raw = raw;
        }
    }

    // ======== The scan, as far as the layout needs (020-10, section 10.1) ========

    /**
     * A scan of a class that a get does not take is refused at the call, before any entry
     * (020-09, section 3.3); a wrapper class over objects without the field p gives null
     * values, not an AssertionError (020-09, section 5.9; review of 020-08, step 8).
     */
    @Nano
    public static void testScanTypes() {
        Database db = start(new MemoryStream());
        try {
            Connection c = db.newConnection();
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").start()
                    .join();
            try {
                c.useIndex("by-field", Thread.class);
                throw new AssertionError("Thread.class taken");
            } catch (ObjectCreationException e) {
                // Expected, with no entry.
            }
            c.put("/items/a", new Item(1, 2));
            int n = 0;
            for (Integer i : c.useIndex("by-field", Integer.class).objects()) {
                Assert.assertNull(i);
                n++;
            }
            Assert.assertEquals(1, n);
        } finally {
            db.close();
        }
    }

    /**
     * A build skips a key under its directory's file prefix whose name holds a '/', written
     * through the Core: no key of the directory, which usePrimary skips too. Before, the
     * first ("/ditems/-a/b") failed the build with the IllegalArgumentException of
     * IndexKeys.fileKey, as a bug, at every start, and the others got an entry, whose K
     * names another key (bergdb 020-16, F16-3).
     */
    @Nano
    public static void testBuildSkipsKeysWithASlashInTheName() {
        for (String junk : new String[] {"/ditems/-a/b", "/ditems/-a/-b", "/ditems/-a/dq/-c"}) {
            Database db = start(new MemoryStream());
            try {
                Connection c = db.newConnection();
                c.put("/items/x", new Item(1, 2));
                Db core = db(db);
                core.execute(core.trans().put(Keys.toBytes(junk),
                        bergdb.pub.DbObject.toDbObject(new Item(1, 3)).getBytes()).build());
                JobStatus status = db.indexBuilder("by-field").dir("/items/").type("long")
                        .field("amount").start().join();
                Assert.assertTrue(junk + ": " + status.note(),
                        status.state() == JobStatus.State.ACTIVE);
                long gen = manager(db).definition("by-field").gen();
                Assert.assertEquals(junk + ": the entries", 1,
                        manager(db).entries("by-field", gen, Long.MAX_VALUE).size());
                int n = 0;
                for (Kv<Item> kv : c.useIndex("by-field", Item.class).eq(1).kvs()) {
                    Assert.assertEquals("/items/x", kv.key());
                    n++;
                }
                Assert.assertEquals(1, n);
            } finally {
                db.close();
            }
        }
    }

    // ======== The start (020-10, section 4.5) ========

    /**
     * A start reads the definitions and the markers: a key under /#i/dii/ (a definition of
     * format 1, 2026.3's) refuses the database with VersioningStreamException (020-08,
     * section 5); a definition that breaks 4.2 and a marker of a live generation are
     * InternalDataExceptions; each refused start closes its database. A value at exactly
     * /#i/dii/, /#i/didef/ or /#i/didel/, written through the Core, is refused too: it ended
     * the start's scan of its prefix, so every definition (or marker) after it was not read,
     * the database started without its indexes, and a write was not indexed (bergdb 020-16,
     * F16-2).
     */
    @Nano
    public static void testStartRefusesBadIndexData() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        long gen;
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").start()
                    .join();
            gen = manager(db).definition("by-field").gen();
            db.sync();
        } finally {
            db.close();
        }
        byte[][][] bad = {
            {Keys.toBytes("/#i/dii/-old"), new byte[] {'b', 'e', 'r', 'g', 'o', 1, 0, 0}},
            {IndexKeys.definitionKey("bad"), new byte[] {(byte) 0x82, 0x48, 0}},
            {IndexKeys.markerKey("by-field", gen), new byte[0]},
            {IndexKeys.format1Prefix(), new byte[] {1}},
            {IndexKeys.definitionsPrefix(), new byte[] {1}},
            {IndexKeys.markersPrefix(), new byte[0]},
        };
        Class<?>[] refusals = {bergdb.storage.VersioningStreamException.class,
                bergdb.core.InternalDataException.class, bergdb.core.InternalDataException.class,
                bergdb.storage.VersioningStreamException.class,
                bergdb.core.InternalDataException.class, bergdb.core.InternalDataException.class};
        for (int i = 0; i < bad.length; i++) {
            MemoryStream copy = stream.copy();
            Database d = start(copy);
            try {
                Db core = db(d);
                core.execute(core.trans().put(bad[i][0], bad[i][1]).build());
                d.sync();
            } finally {
                d.close();
            }
            try {
                Database refused = start(copy.copy());
                refused.close();
                throw new AssertionError("started with bad index data " + i);
            } catch (RuntimeException e) {
                Assert.assertTrue(e.toString(), refusals[i].isInstance(e));
            }
        }
    }

    /**
     * A start resumes a build that a stop ended (BUILDING: join() and join(millis) return
     * it) from the first key of its directory, and a cleanup whose marker is left; indexJob()
     * gives the build's job.
     */
    @Nano
    public static void testStartResumesBuildsAndCleanups() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        long gen = 0;
        try {
            Connection c = db.newConnection();
            for (int i = 0; i < 30; i++) {
                c.put("/items/" + (100 + i), new Item(i, i));
            }
            db.indexBuilder("old").dir("/items/").type("long").field("amount").start().join();
            gen = manager(db).definition("old").gen();
            Gate cleanup = new Gate();
            Gate build = new Gate();
            manager(db).testHook = p -> {
                cleanup.at(p, IndexManager.CLEANUP_STEP);
                build.at(p, IndexManager.BUILD_STEP);
            };
            db.deleteIndex("old");
            cleanup.awaitReached();
            Job job = db.indexBuilder("by-field").dir("/items/").type("long").field("other")
                    .start();
            build.awaitReached();
            Assert.assertEquals(JobStatus.State.BUILDING, job.getStatus().state());
            db.sync();
            db.close();
            cleanup.open();
            build.open();
            Assert.assertEquals(JobStatus.State.BUILDING, job.join().state());
            Assert.assertEquals(JobStatus.State.BUILDING, job.join(1000).state());
        } finally {
            db.close();
        }
        db = start(stream.copy());
        try {
            Assert.assertEquals(JobStatus.State.ACTIVE, db.indexJob("by-field").join().state());
            Assert.assertEquals(30, db.indexJob("by-field").getStatus().count());
            PubTesterIndexRaces.awaitCleanups(manager(db));
            Assert.assertEquals(0, manager(db).entries("old", gen, Long.MAX_VALUE).size());
            Assert.assertEquals(30, entries(db, "by-field"));
        } finally {
            db.close();
        }
    }

    // ======== Helpers ========

    /** The raw entries of the live index's generation at the latest time. */
    private static int entries(Database db, String name) {
        IndexDefinition def = manager(db).definition(name);
        return manager(db).entries(name, def.gen(), Long.MAX_VALUE).size();
    }

    private static int count(Iterable<?> it) {
        int n = 0;
        for (Object o : it) {
            n++;
        }
        return n;
    }

    private static void assertState(Runnable r) {
        try {
            r.run();
        } catch (IllegalStateException e) {
            return;
        }
        throw new AssertionError("no IllegalStateException");
    }

    private static void assertArgument(Runnable r) {
        try {
            r.run();
        } catch (IllegalArgumentException e) {
            return;
        }
        throw new AssertionError("no IllegalArgumentException");
    }

    static Db db(Database database) {
        return ((DatabaseImp) database).getDb();
    }
}
