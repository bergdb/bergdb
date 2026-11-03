package bergdb.pubimp;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

import bergdb.common.EventToWaitFor;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.Database;
import bergdb.pub.DatabaseBuilder;
import bergdb.pub.Factory;
import bergdb.pub.util.Job;
import bergdb.pub.util.JobStatus;
import bergdb.stream.MemoryStream;

/**
 * Tests of the index jobs, builds and deletions, that meet a later index of the same name:
 * a job belongs to its own index, not to the name (bergdb 015-22).
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
}
