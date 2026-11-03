package bergdb.core;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import bergdb.dag.GetMany;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.util.Job;
import bergdb.pubimp.DatabaseImp;

/** Force a normal STM conflict while the build worker's interrupt flag is set. */
public final class BuildInterruptProbe {
    public static final class Item {
        public long amount;
        public Item() {}
        Item(long amount) { this.amount = amount; }
    }
    private static final class PausedDb extends Db {
        final AtomicBoolean pause = new AtomicBoolean(true);
        final CountDownLatch read = new CountDownLatch(1), release = new CountDownLatch(1);
        volatile Thread worker;
        volatile Throwable workerFailure;
        PausedDb(DbBuilder b) { super(b); }
        @Override public void getMany(GetMany g) {
            super.getMany(g);
            if (Thread.currentThread().getName().startsWith("IndexBuilderImp-CreateIndex-")
                    && pause.compareAndSet(true, false)) {
                worker = Thread.currentThread();
                worker.setUncaughtExceptionHandler((t, e) -> workerFailure = e);
                read.countDown();
                try {
                    if (!release.await(5, TimeUnit.SECONDS)) throw new AssertionError("release timed out");
                } catch (InterruptedException e) { throw new AssertionError(e); }
                // The same interrupt that ThreadGroup.interrupt() can deliver here.
                Thread.currentThread().interrupt();
            }
        }
    }
    public static void main(String[] args) throws Exception {
        PausedDb core = new PausedDb(Db.builder().testSetup());
        Database db = DatabaseImp.createAndStart(core);
        try {
            Connection c = db.newConnection();
            c.w().put("/items/a", new Item(1)).put("/items/b", new Item(2)).execute();
            Job job = db.indexBuilder("amount").dir("/items/").type("long").field("amount").start();
            if (!core.read.await(2, TimeUnit.SECONDS)) throw new AssertionError("build did not scan");
            c.w().put("/items/a", new Item(3)).execute();
            core.release.countDown();
            core.worker.join(2000);
            if (core.worker.isAlive()) throw new AssertionError("worker still running");
            System.out.println("build worker terminated: " + !core.worker.isAlive());
            System.out.println("uncaught failure: " + core.workerFailure);
            System.out.println("job progress after join: " + job.join().progress());
            System.out.println("database active: " + core.internal().isActive());
        } finally {
            core.release.countDown();
            if (core.worker != null) core.worker.join(2000);
            db.close();
        }
    }
}
