package bergdb.core;

import java.io.IOException;
import java.util.Set;
import java.util.concurrent.atomic.AtomicReference;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StreamIoException;

/** A failed append whose cleanup throws must still release durability waiters. */
public class R5CloseErrorProbe {
    private static final class BrokenClose extends DbTesterFailure.FaultStream {
        volatile boolean breakClose;
        @Override public void close() throws IOException {
            if (breakClose) throw new IllegalStateException("R5: unchecked close failure");
            super.close();
        }
    }

    private static void require(boolean yes, String message) {
        if (!yes) throw new AssertionError(message);
    }

    public static void main(String[] args) throws Exception {
        Set<Thread> before = DbTesterFailure.storageThreads();
        BrokenClose s = new BrokenClose();
        Db db = Db.builder().testSetup(s).start();
        Thread syncer = null;
        AtomicReference<Throwable> uncaught = new AtomicReference<>();
        AtomicReference<Throwable> syncFailure = new AtomicReference<>();
        try {
            Set<Thread> added = DbTesterFailure.storageThreads();
            added.removeAll(before);
            require(added.size() == 1, "expected one consumer");
            Thread consumer = added.iterator().next();
            consumer.setUncaughtExceptionHandler((t, e) -> uncaught.set(e));
            db.sync(SyncLevel.ORDINARY);
            long beforeLength = db.getDurableLength();
            s.failAppends = true;
            s.breakClose = true;
            db.execute(db.trans().put("/r5-close-error", "unwritten"));
            consumer.join(500);
            require(!consumer.isAlive(), "consumer did not terminate");
            require(uncaught.get() instanceof IllegalStateException,
                    "wrong failure: " + uncaught.get());
            syncer = new Thread(() -> {
                try { db.sync(SyncLevel.ORDINARY); }
                catch (Throwable e) { syncFailure.set(e); }
            }, "R5-close-error-sync");
            syncer.setDaemon(true);
            syncer.start();
            syncer.join(600); // Includes StorageManager's 500 ms error poll.
            System.out.println("consumerAlive=" + consumer.isAlive()
                    + "; uncaught=" + uncaught.get());
            System.out.println("dbActive=" + db.internal().isActive()
                    + "; durableUnchanged=" + (db.getDurableLength() == beforeLength)
                    + "; syncAlive=" + syncer.isAlive()
                    + "; syncFailure=" + syncFailure.get());
            require(syncer.isAlive() && syncFailure.get() == null,
                    "expected the BASE hang was not reproduced");
        } finally {
            s.breakClose = false;
            s.failAppends = false;
            if (syncer != null && syncer.isAlive()) {
                syncer.interrupt();
                syncer.join(500);
                require(!syncer.isAlive(), "cleanup did not end syncer");
            }
            try { db.close(); } catch (StreamIoException expected) { }
            System.out.println("cleanup: sync waiter ended; database closed");
        }
    }
}
