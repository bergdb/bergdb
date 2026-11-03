package bergdb.core;

import java.io.IOException;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import bergdb.pub.Database;
import bergdb.pub.IndexAlreadyExistsException;
import bergdb.pub.util.SyncLevel;
import bergdb.pubimp.DatabaseImp;
import bergdb.storage.StreamIoException;
import bergdb.stream.MemoryStream;

/** deleteIndex is not an interruptible public wait, but its internal sync aborts admission. */
public final class DeleteCallerInterruptProbe {
    static final class HeldStream extends MemoryStream {
        volatile boolean hold;
        final CountDownLatch release = new CountDownLatch(1);
        @Override public void append(byte[] bytes, int offset, int length) throws IOException {
            if (hold) {
                try {
                    if (!release.await(5, TimeUnit.SECONDS)) throw new IOException("probe timeout");
                } catch (InterruptedException e) { throw new IOException(e); }
            }
            super.append(bytes, offset, length);
        }
    }
    public static void main(String[] args) {
        HeldStream stream = new HeldStream();
        Db core = Db.builder().testSetup(stream).stream("main", stream, 100000, 60000).build();
        Database db = DatabaseImp.createAndStart(core);
        try {
            db.indexBuilder("amount").dir("/items/").type("long").field("amount").createFast();
            db.sync(SyncLevel.ORDINARY);
            stream.hold = true;
            Thread.currentThread().interrupt();
            try {
                db.deleteIndex("amount");
                throw new AssertionError("delete unexpectedly returned a job");
            } catch (StreamIoException e) {
                System.out.println("deleteIndex threw: " + e.getCause().getClass().getSimpleName());
                System.out.println("caller interrupt retained: " + Thread.currentThread().isInterrupted());
            } finally { Thread.interrupted(); }
            System.out.println("database still active: " + core.internal().isActive());
            long jobs = Thread.getAllStackTraces().keySet().stream()
                    .filter(t -> t.getName().startsWith("DatabaseImp-delete-amount-")).count();
            System.out.println("delete workers started: " + jobs);
            try {
                db.indexBuilder("amount");
                throw new AssertionError("name unexpectedly free");
            } catch (IndexAlreadyExistsException expected) {
                System.out.println("index name still occupied after interrupted deletion: true");
            }
        } finally {
            Thread.interrupted();
            stream.release.countDown();
            db.close();
        }
        Database reopened = DatabaseImp.createAndStart(Db.builder().testSetup(stream.copy()).build());
        try {
            System.out.println("restart resumes delete jobs: " + reopened.getStartupInfo().getStartupJobs().length);
            for (bergdb.pub.util.Job job : reopened.getStartupInfo().getStartupJobs()) job.join(1000);
        } finally { reopened.close(); }
    }
}
