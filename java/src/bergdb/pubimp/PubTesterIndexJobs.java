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
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
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
     * went on without the build.
     */
    @Nano
    public static void testErrorInBuildFailsTheDatabase() {
        for (final String point : new String[] {"action", "step"}) {
            final Database db = start(new MemoryStream());
            try {
                db.newConnection().w().put("/items/old", new Item(1, 200)).execute();
                final Error error = new Error("an Error in the build, at " + point);
                IndexBuilderImp builder = (IndexBuilderImp) db.indexBuilder("by-field");
                builder.testHook(p -> {
                    if (p.equals(point)) {
                        throw error;
                    }
                });
                builder.dir("/items/").type("long").field("amount").start().join();
                DbFailedException refused = null;
                try {
                    putNew(db);
                } catch (DbFailedException e) {
                    refused = e;
                }
                Assert.assertTrue(point + ", the database failed: " + refused,
                        refused != null && refused.getCause() == error);
            } finally {
                db.close();
            }
        }
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
