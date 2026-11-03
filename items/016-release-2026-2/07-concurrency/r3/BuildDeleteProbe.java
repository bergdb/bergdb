package bergdb.core;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import bergdb.dag.GetMany;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.util.Job;
import bergdb.pubimp.DatabaseImp;

/** Delete a paused build, replace its name, then let the old build resume. */
public final class BuildDeleteProbe {
    public static final class Item {
        public long amount, other;
        public Item() {}
        Item(long amount, long other) { this.amount = amount; this.other = other; }
    }
    private static final class PausedDb extends Db {
        final AtomicBoolean pause = new AtomicBoolean(true);
        final CountDownLatch entered = new CountDownLatch(1), release = new CountDownLatch(1);
        volatile Thread worker;
        volatile Throwable workerFailure;
        PausedDb(DbBuilder builder) { super(builder); }
        @Override public void getMany(GetMany g) {
            if (Thread.currentThread().getName().startsWith("IndexBuilderImp-CreateIndex-")
                    && pause.compareAndSet(true, false)) {
                worker = Thread.currentThread();
                worker.setUncaughtExceptionHandler((t, e) -> workerFailure = e);
                entered.countDown();
                try {
                    if (!release.await(5, TimeUnit.SECONDS)) throw new AssertionError("release timed out");
                } catch (InterruptedException e) { throw new AssertionError(e); }
            }
            super.getMany(g);
        }
    }
    private static List<Long> values(Connection c) {
        List<Long> result = new ArrayList<>();
        for (Item i : c.useIndex("by-field", Item.class).objects()) result.add(i.other);
        return result;
    }
    public static void main(String[] args) throws Exception {
        PausedDb core = new PausedDb(Db.builder().testSetup());
        Database db = DatabaseImp.createAndStart(core);
        Job build = null;
        try {
            Connection c = db.newConnection();
            c.w().put("/items/old", new Item(1, 200)).execute();
            build = db.indexBuilder("by-field").dir("/items/").type("long").field("amount").start();
            if (!core.entered.await(2, TimeUnit.SECONDS)) throw new AssertionError("build not paused");
            if (db.deleteIndex("by-field").join(2000).progress() != 100)
                throw new AssertionError("delete did not finish");
            db.indexBuilder("by-field").dir("/items/").type("long").field("other").createFast();
            c.w().put("/items/new", new Item(50, 100)).execute();
            System.out.println("replacement index before old build resumes: " + values(c));
            core.release.countDown();
            core.worker.join(2000);
            if (core.worker.isAlive()) throw new AssertionError("old build did not end");
            System.out.println("replacement index after old build resumes: " + values(c));
            System.out.println("old build failure: " + core.workerFailure);
            System.out.println("old build reports progress: " + build.getStatus().progress());
            System.out.println("database active: " + core.internal().isActive());
        } finally {
            core.release.countDown();
            if (core.worker != null) core.worker.join(2000);
            db.close();
        }
    }
}
