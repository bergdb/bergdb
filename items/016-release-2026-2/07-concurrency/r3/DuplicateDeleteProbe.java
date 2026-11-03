package bergdb.core;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import bergdb.dag.GetMany;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.NoSuchIndexException;
import bergdb.pub.util.Job;
import bergdb.pubimp.DatabaseImp;
import bergdb.stream.MemoryStream;

/** A latch at a real reader entry forces two delete jobs to overlap. */
public final class DuplicateDeleteProbe {
    public static final class Item {
        public long amount;
        public Item() {}
        Item(long amount) { this.amount = amount; }
    }

    private static final class PausedDb extends Db {
        final AtomicBoolean pauseNextDelete = new AtomicBoolean();
        final CountDownLatch entered = new CountDownLatch(1);
        final CountDownLatch release = new CountDownLatch(1);
        PausedDb(DbBuilder builder) { super(builder); }
        @Override public void getMany(GetMany g) {
            if (Thread.currentThread().getName().startsWith("DatabaseImp-delete-")
                    && pauseNextDelete.compareAndSet(true, false)) {
                entered.countDown();
                try {
                    if (!release.await(5, TimeUnit.SECONDS))
                        throw new AssertionError("probe release timed out");
                } catch (InterruptedException e) { throw new AssertionError(e); }
            }
            super.getMany(g);
        }
    }

    static int indexed(Connection c) {
        int n = 0;
        for (Item item : c.useIndex("amount", Item.class).objects()) n++;
        return n;
    }

    public static void main(String[] args) throws Exception {
        MemoryStream stream = new MemoryStream();
        PausedDb core = new PausedDb(Db.builder().testSetup(stream));
        Database db = DatabaseImp.createAndStart(core);
        Job first = null, second = null;
        try {
            Connection c = db.newConnection();
            db.indexBuilder("amount").dir("/items/").type("long").field("amount").createFast();
            c.w().put("/items/old", new Item(1)).execute();
            core.pauseNextDelete.set(true);
            first = db.deleteIndex("amount");
            if (!core.entered.await(2, TimeUnit.SECONDS)) throw new AssertionError("first job not paused");
            second = db.deleteIndex("amount");
            if (second.join(2000).progress() != 100) throw new AssertionError("second job did not finish");
            db.indexBuilder("amount").dir("/items/").type("long").field("amount").createFast();
            c.w().put("/items/new", new Item(2)).execute();
            System.out.println("new index before old job resumes: " + indexed(c) + " entry");
            core.release.countDown();
            if (first.join(2000).progress() != 100) throw new AssertionError("first job did not finish");
            try {
                System.out.println("new index after old job resumes: " + indexed(c) + " entries");
            } catch (NoSuchIndexException e) {
                System.out.println("FAULT: old delete job removed newly created index: " + e.getClass().getSimpleName());
            }
            System.out.println("primary object survives: " + c.get("/items/new", Item.class).amount);
        } finally {
            core.release.countDown();
            if (first != null) first.join(2000);
            if (second != null) second.join(2000);
            db.close();
        }
        Database reopened = DatabaseImp.createAndStart(Db.builder().testSetup(stream.copy()).build());
        try {
            try {
                indexed(reopened.newConnection());
                System.out.println("index exists after reopen");
            } catch (NoSuchIndexException e) {
                System.out.println("FAULT persists after reopen: NoSuchIndexException");
            }
        } finally { reopened.close(); }
    }
}
