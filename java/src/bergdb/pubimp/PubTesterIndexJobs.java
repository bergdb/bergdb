package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import bergdb.core.Db;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Connection;
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

    private static void assertDeleted(JobStatus status) {
        Assert.assertEquals(status.note(), JobStatus.State.FAILED, status.state());
        Assert.assertEquals("deleted", status.reason());
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
            assertDeleted(old.join());
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
            JobStatus status = db.indexBuilder("by-field").dir("/items/").type("long")
                    .field("amount").start().join();
            manager(db).testHook = null;
            assertDeleted(status);
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
     * Error. A RuntimeException ends the build FAILED, with its class and message as the
     * reason, and the database goes on (bergdb 019-42); the definition stays building, so
     * the next start takes the build again and ends ACTIVE.
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
                JobStatus status = db.indexBuilder("by-field").dir("/items/").type("long")
                        .field("amount").start().join();
                if (thrown instanceof Error) {
                    try {
                        putNew(db);
                        throw new AssertionError("the database went on after an Error");
                    } catch (DbFailedException e) {
                        Assert.assertTrue(e.getCause() == thrown);
                    }
                    continue;
                }
                Assert.assertEquals(JobStatus.State.FAILED, status.state());
                Assert.assertTrue(status.reason(), status.reason().contains(
                        "IllegalStateException") && status.reason().contains("by the test"));
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
     * reason that names the key and the format, and the database goes on. A start takes the
     * build again, which fails again; the index can be deleted, and the next start has no
     * index. A null String, which failed the build until format 2, is absent: the object
     * gives no entry, as one without the field, and the build ends ACTIVE with the entries of
     * the other two (020-04, N11); after a restart its job is ACTIVE with count 0.
     */
    @Nano
    public static void testBuildOverAnObjectItCannotIndex() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        try {
            db.newConnection().w().put("/named/1", new Named("a"))
                    .put("/named/2", PubTester.format1Payment())
                    .put("/named/3", new Named("c")).execute();
            checkFailed(db.indexBuilder("by-name").dir("/named/").type("string").field("name")
                    .start().join());
            putNew(db);         // DbFailedException if the build failed the database.
        } finally {
            db.close();
        }
        
        MemoryStream restarted = stream.copy();
        db = start(restarted);
        try {
            checkFailed(db.indexJob("by-name").join());
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
    
    /** FAILED, with a reason that names the format-1 object's key and its format. */
    private static void checkFailed(JobStatus status) {
        Assert.assertEquals(status.note(), JobStatus.State.FAILED, status.state());
        Assert.assertTrue(status.reason(), status.reason().contains("/dnamed/-2")
                && status.reason().contains("format 1"));
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
     * N7: a value whose levels take more than 4,096 bytes has no entry, so no step can be
     * too large to commit; the build ends ACTIVE.
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
            c.put("/named/big2", new Named(IndexKeysTester.repeat("y", 5000)));
            Assert.assertEquals(1, entries(db, "n"));
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

    // ======== The start (020-10, section 4.5) ========

    /**
     * A start reads the definitions and the markers: a key under /#i/dii/ (a definition of
     * format 1, 2026.3's) refuses the database with VersioningStreamException (020-08,
     * section 5); a definition that breaks 4.2 and a marker of a live generation are
     * InternalDataExceptions; each refused start closes its database.
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
        };
        Class<?>[] refusals = {bergdb.storage.VersioningStreamException.class,
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
     * A start resumes a build that a stop ended (BUILDING) from the first key of its
     * directory, and a cleanup whose marker is left; indexJob() gives the build's job.
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
