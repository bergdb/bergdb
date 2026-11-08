package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.common.EventToWaitFor;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.util.DbException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.pub.util.LookupTimeNotAvailableException;
import bergdb.stream.MemoryStream;

/**
 * Tests of the index jobs, builds and deletions, that meet a later index of the same name:
 * a job belongs to its own index, not to the name (bergdb 015-21, 015-22).
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

    /** An object with an indexed String field, which may be null (bergdb 019-42). */
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

    /** The field 'other' of the objects that the index 'by-field' gives, in its order. */
    private static String others(Database db) {
        List<Long> result = new ArrayList<Long>();
        for (Item item : db.newConnection().useIndex("by-field", Item.class).objects()) {
            result.add(item.other);
        }
        return result.toString();
    }

    /**
     * Deletes the index 'by-field' and waits for the deletion, creates the index again on the
     * field 'other', and puts an object (amount 50, other 100): the new index gives [100].
     */
    private static void deleteAndReplace(Database db) {
        Assert.assertEquals(100, db.deleteIndex("by-field").join().progress());
        db.indexBuilder("by-field").dir("/items/").type("long").field("other").createFast();
        db.newConnection().w().put("/items/new", new Item(50, 100)).execute();
        Assert.assertEquals("[100]", others(db));
    }

    /** The old build has ended, without activating its index, and says so. */
    private static void checkStopped(JobStatus status) {
        Assert.assertEquals(100, status.progress());
        Assert.assertTrue(status.note(), status.note().startsWith("Stopped"));
    }

    /** After a restart, the new index still gives [100] and nothing of the old build. */
    private static void checkAfterRestart(MemoryStream stream) {
        Database db = start(stream.copy());
        try {
            Assert.assertEquals("[100]", others(db));
        } finally {
            db.close();
        }
    }

    /**
     * bergdb 015-22 (review R3-F2): a build waits before its first step while its index is
     * deleted and created again on another field. The old build writes nothing into the new
     * index, does not activate it, and says that it stopped; also after a restart.
     */
    @Nano
    public static void testBuildDeletedBeforeItsStep() {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        try {
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            EventToWaitFor wait = new EventToWaitFor();
            IndexBuilderImp builder = (IndexBuilderImp) db.indexBuilder("by-field");
            builder.createInThreadWaitEvent(wait);
            Job build = builder.dir("/items/").type("long").field("amount").start();
            deleteAndReplace(db);
            wait.happened();
            JobStatus status = build.join();
            Assert.assertEquals("[100]", others(db));
            checkStopped(status);
        } finally {
            db.close();
        }
        checkAfterRestart(stream);
    }

    /**
     * bergdb 015-22: the deletion and the new index come in the build's step, after its read
     * and before its transaction (the hook "action"): the transaction runs again and the
     * build stops, as in testBuildDeletedBeforeItsStep.
     */
    @Nano
    public static void testBuildDeletedInItsStep() {
        buildDeletedAt("action");
    }

    /**
     * bergdb 015-22: the deletion and the new index come after the build's last step, before
     * its activation (the hook "step"): the build does not activate, and says that it stopped.
     */
    @Nano
    public static void testBuildDeletedBeforeActivation() {
        buildDeletedAt("step");
    }

    private static void buildDeletedAt(final String point) {
        MemoryStream stream = new MemoryStream();
        final Database db = start(stream);
        try {
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            final AtomicBoolean once = new AtomicBoolean(true);
            final AtomicReference<Throwable> failure = new AtomicReference<Throwable>();
            IndexBuilderImp builder = (IndexBuilderImp) db.indexBuilder("by-field");
            builder.testHook(p -> {
                if (p.equals(point) && once.compareAndSet(true, false)) {
                    try {
                        deleteAndReplace(db);
                    } catch (RuntimeException | Error e) {
                        failure.set(e);
                    }
                }
            });
            JobStatus status = builder.dir("/items/").type("long").field("amount").start().join();
            if (failure.get() != null) {
                throw new AssertionError("in the hook: " + failure.get(), failure.get());
            }
            Assert.assertFalse(once.get());
            Assert.assertEquals("[100]", others(db));
            checkStopped(status);
        } finally {
            db.close();
        }
        checkAfterRestart(stream);
    }
    
    /**
     * bergdb 019-10: an Error in an index build, in its step's Action (the hook "action") or
     * after its transaction (the hook "step"), fails the database, as on BergDB's other
     * threads, and the build's thread ends: every later call is refused with a
     * DbFailedException whose cause is the Error. Before, the thread ended, and the database
     * went on without the build. A RuntimeException ends the build as failed, and the database
     * goes on (bergdb 019-42); from 019-38 to 019-42 it failed the database too.
     */
    @Nano
    public static void testErrorInBuildFailsTheDatabase() {
        for (final String point : new String[] {"action", "step"}) {
            for (final Throwable thrown : new Throwable[] {new Error("an Error in the build"),
                    new IllegalStateException("a bug in the build")}) {
                final Database db = start(new MemoryStream());
                try {
                    db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
                    IndexBuilderImp builder = (IndexBuilderImp) db.indexBuilder("by-field");
                    builder.testHook(p -> {
                        if (p.equals(point)) {
                            throwIt(thrown);
                        }
                    });
                    JobStatus status = builder.dir("/items/").type("long").field("amount")
                            .start().join();
                    if (!(thrown instanceof Error)) {
                        putNew(db);     // DbFailedException if the build failed the database.
                        checkFailed(status);
                        continue;
                    }
                    DbFailedException refused = null;
                    try {
                        putNew(db);
                    } catch (DbFailedException e) {
                        refused = e;
                    }
                    Assert.assertTrue(point + ", " + thrown + ", the database failed: " + refused,
                            refused != null && refused.getCause() == thrown);
                } finally {
                    db.close();
                }
            }
        }
    }
    
    /** The build has ended as failed, without activating its index (bergdb 019-42). */
    private static void checkFailed(JobStatus status) {
        Assert.assertEquals(100, status.progress());
        Assert.assertTrue(status.note(), status.note().startsWith("Failed"));
    }
    
    /**
     * bergdb 019-42 (020-01, N1, its probe V1Probe): a build over an object that its index
     * cannot read, since 2026.4 an object of format 1 (020-08, step 3), ends as failed, and
     * the database goes on. A start takes the build again, which ends as failed again; the
     * index can be deleted, and the next start has no job. Since 019-10 the database failed,
     * at every start. A null String, which failed the build until format 2, is absent: the
     * object gives no entry, as one without the field, and the build ends done with the
     * entries of the other two (020-04, N11).
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
            Job[] jobs = db.getStartupInfo().getStartupJobs();
            Assert.assertEquals(1, jobs.length);
            checkFailed(jobs[0].join());
            putNew(db);
            Assert.assertEquals(100, db.deleteIndex("by-name").join().progress());
        } finally {
            db.close();
        }
        
        db = start(restarted.copy());
        try {
            Assert.assertEquals(0, db.getStartupInfo().getStartupJobs().length);
            putNew(db);
        } finally {
            db.close();
        }
        
        db = start(new MemoryStream());
        try {
            db.newConnection().w().put("/named/1", new Named("a")).put("/named/2", new Named(null))
                    .put("/named/3", new Named("c")).execute();
            JobStatus status = db.indexBuilder("by-name").dir("/named/").type("string")
                    .field("name").start().join();
            Assert.assertTrue(status.note(), status.note().startsWith("Done"));
            StringBuilder names = new StringBuilder();
            for (Named n : db.newConnection().useIndex("by-name", Named.class).objects()) {
                names.append(n.name);
            }
            Assert.assertEquals("ac", names.toString());
        } finally {
            db.close();
        }
    }
    
    /** Throws 'thrown', an Error or a RuntimeException. */
    private static void throwIt(Throwable thrown) {
        if (thrown instanceof Error) {
            throw (Error) thrown;
        }
        throw (RuntimeException) thrown;
    }
    
    /**
     * bergdb 019-38 (review R6 of 006-13, B1, its probe): an interrupt of an index build's
     * thread while its step waits to run again after a conflict. The hook "action" writes the
     * object that the step read, then interrupts the thread; the step's transaction conflicts,
     * and its wait to run again ends with a refusal (DbException). The build takes the step
     * again and ends done, and the database goes on (bergdb 005-46). Since 019-10 the database
     * failed, and every later call threw DbFailedException.
     */
    @Nano
    public static void testInterruptInBuildIsNotAFailure() {
        final Database db = start(new MemoryStream());
        try {
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            final AtomicBoolean once = new AtomicBoolean(true);
            IndexBuilderImp builder = (IndexBuilderImp) db.indexBuilder("by-field");
            builder.testHook(p -> {
                if (p.equals("action") && once.compareAndSet(true, false)) {
                    db.newConnection().w().put("/items/old", new Item(2, 300)).execute();
                    Thread.currentThread().interrupt();
                }
            });
            checkBuildDone(db, builder, once, "[300, 100]");
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 019-38: an expired read (LookupTimeNotAvailableException, as when a cut overtakes
     * the step's getMany) and a refusal of the step's transaction (a DbException), each thrown
     * once in an index build's step by the hook "action". The build takes the step again and
     * ends done, and the database goes on. Since 019-10 the database failed.
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
                IndexBuilderImp builder = (IndexBuilderImp) db.indexBuilder("by-field");
                builder.testHook(p -> {
                    if (p.equals("action") && once.compareAndSet(true, false)) {
                        throw thrown;
                    }
                });
                checkBuildDone(db, builder, once, "[200, 100]");
            } finally {
                db.close();
            }
        }
    }
    
    /**
     * Runs the build of the index 'by-field' on the field 'amount' to its end: the hook has
     * thrown, the database takes a put, the build is done, and the index gives 'expected'.
     */
    private static void checkBuildDone(Database db, IndexBuilderImp builder,
            AtomicBoolean once, String expected) {
        JobStatus status = builder.dir("/items/").type("long").field("amount").start().join();
        Assert.assertFalse(once.get());
        putNew(db);         // DbFailedException if the build failed the database.
        Assert.assertEquals(100, status.progress());
        Assert.assertTrue(status.note(), status.note().startsWith("Done"));
        Assert.assertEquals(expected, others(db));
    }
    
    private static void putNew(Database db) {
        db.newConnection().w().put("/items/new", new Item(50, 100)).execute();
    }
    
    /** Creates the index 'by-field' on the field 'other', if no index has the name. */
    private static boolean createIfFree(Database db) {
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("other").createFast();
            return true;
        } catch (IndexAlreadyExistsException e) {
            return false;
        }
    }
    
    /**
     * bergdb 019-38: an expired read in an index deletion's job, thrown once by its hook
     * "start": the job takes its work again and ends, the index's name is free, and the
     * database goes on. Since 019-10 the database failed; before, the job ended and left the
     * index deleting.
     */
    @Nano
    public static void testExpiryInDeletionIsNotAFailure() {
        final Database db = start(new MemoryStream());
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").createFast();
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            final AtomicInteger starts = new AtomicInteger();
            ((DatabaseImp) db).testHookDelete = p -> {
                if (p.equals("start") && starts.incrementAndGet() == 1) {
                    throw new LookupTimeNotAvailableException("an expired read, by the test");
                }
            };
            Assert.assertEquals(100, db.deleteIndex("by-field").join().progress());
            Assert.assertEquals(2, starts.get());
            Assert.assertTrue(createIfFree(db));
            putNew(db);
            Assert.assertEquals("[100]", others(db));
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 019-38: an unexpected RuntimeException, a bug, in an index deletion's job (its
     * hook "start") fails the database (bergdb 019-10); the job says "Stopped", not "Done!"
     * (bergdb 019-40).
     */
    @Nano
    public static void testBugInDeletionFailsTheDatabase() {
        final Database db = start(new MemoryStream());
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").createFast();
            final RuntimeException bug = new IllegalStateException("a bug in the deletion");
            ((DatabaseImp) db).testHookDelete = p -> {
                if (p.equals("start")) {
                    throw bug;
                }
            };
            checkStopped(db.deleteIndex("by-field").join());
            DbFailedException refused = null;
            try {
                putNew(db);
            } catch (DbFailedException e) {
                refused = e;
            }
            Assert.assertTrue("the database failed: " + refused,
                    refused != null && refused.getCause() == bug);
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 019-40, 015-61 (review R8 of 016-06, R8-F6): a deletion job that a close ends
     * early says "Stopped", as a build does; it said "Done! Deleted".
     */
    @Nano
    public static void testDeletionEndedByCloseIsStopped() {
        final Database db = start(new MemoryStream());
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").createFast();
            ((DatabaseImp) db).testHookDelete = p -> {
                if (p.equals("start")) {
                    db.close();
                }
            };
            checkStopped(db.deleteIndex("by-field").join());
        } finally {
            db.close();
        }
    }
    
    /**
     * bergdb 015-21 (review R3-F1): deleteIndex() twice on one name, and the index created
     * again on another field as soon as the name is free. The first deletion's job waits at
     * its start (the hook "start"); if the second call has started a job of its own, that one
     * finishes first, and the new index is made and gets its entry before the first job goes
     * on, as in R3-F1's probe. The first job must not delete the new index, its definition or
     * its entries; also after a restart.
     */
    @Nano
    public static void testDeleteTwice() throws InterruptedException {
        MemoryStream stream = new MemoryStream();
        Database db = start(stream);
        final CountDownLatch entered = new CountDownLatch(1);
        final CountDownLatch release = new CountDownLatch(1);
        final AtomicBoolean once = new AtomicBoolean(true);
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").createFast();
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            ((DatabaseImp) db).testHookDelete = p -> {
                if (p.equals("start") && once.compareAndSet(true, false)) {
                    entered.countDown();
                    try {
                        release.await(10, TimeUnit.SECONDS);    // A guard, not a timing.
                    } catch (InterruptedException e) {
                        throw new AssertionError(e);
                    }
                }
            };
            
            Job first = db.deleteIndex("by-field");
            Assert.assertTrue(entered.await(10, TimeUnit.SECONDS));
            Job second = db.deleteIndex("by-field");
            if (second != first) {
                Assert.assertEquals(100, second.join().progress());
            }
            boolean created = createIfFree(db);
            if (created) {
                putNew(db);         // The new index has its entry before the first job goes on.
            }
            release.countDown();
            Assert.assertEquals(100, first.join().progress());
            Assert.assertEquals(100, second.join().progress());
            if (!created) {
                Assert.assertTrue(createIfFree(db));
                putNew(db);
            }
            
            try {
                Assert.assertEquals("[100]", others(db));
            } catch (NoSuchIndexException e) {
                throw new AssertionError("The new index was deleted: " + e.getMessage());
            }
        } finally {
            release.countDown();
            db.close();
        }
        checkAfterRestart(stream);
    }
    
    /**
     * bergdb 015-21: a second deleteIndex() finds the index deleting; then, before it starts
     * or finds a job (its hook "call"), the first job, which waited at its start, finishes,
     * and the index is created again and gets its entry. The second call must not start a job
     * for the deleted index: the new index and its entry stay; also after a restart.
     */
    @Nano
    public static void testDeleteAgainAsTheFirstEnds() {
        MemoryStream stream = new MemoryStream();
        final Database db = start(stream);
        final CountDownLatch release = new CountDownLatch(1);
        final AtomicInteger starts = new AtomicInteger();
        final AtomicInteger calls = new AtomicInteger();
        final AtomicReference<Job> first = new AtomicReference<Job>();
        final AtomicReference<Throwable> failure = new AtomicReference<Throwable>();
        try {
            db.indexBuilder("by-field").dir("/items/").type("long").field("amount").createFast();
            db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
            ((DatabaseImp) db).testHookDelete = p -> {
                if (p.equals("start") && starts.incrementAndGet() == 1) {
                    try {
                        release.await(10, TimeUnit.SECONDS);    // A guard, not a timing.
                    } catch (InterruptedException e) {
                        throw new AssertionError(e);
                    }
                } else if (p.equals("call") && calls.incrementAndGet() == 2) {
                    try {
                        release.countDown();
                        Assert.assertEquals(100, first.get().join().progress());
                        Assert.assertTrue(createIfFree(db));
                        putNew(db);
                    } catch (RuntimeException | Error e) {
                        failure.set(e);
                    }
                }
            };
            
            first.set(db.deleteIndex("by-field"));
            Job second = db.deleteIndex("by-field");
            if (failure.get() != null) {
                throw new AssertionError("in the hook: " + failure.get(), failure.get());
            }
            Assert.assertEquals(2, calls.get());
            Assert.assertEquals(100, second.join().progress());
            try {
                Assert.assertEquals("[100]", others(db));
            } catch (NoSuchIndexException e) {
                throw new AssertionError("The new index was deleted: " + e.getMessage());
            }
        } finally {
            release.countDown();
            db.close();
        }
        checkAfterRestart(stream);
    }
}
