package bergdb.core;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;
import bergdb.dag.ValueNode;
import bergdb.pub.util.DbFailedException;
import bergdb.stream.MemoryStream;

/** Forces the transfer of the write lock between a failed batch and setFailed. */
public final class R4FailureWindow {
    private static void await(CountDownLatch latch, String what) {
        try {
            if (!latch.await(5, TimeUnit.SECONDS)) throw new AssertionError("timeout: " + what);
        } catch (InterruptedException x) {
            Thread.currentThread().interrupt();
            throw new AssertionError(x);
        }
    }

    private static void waitFor(java.util.function.BooleanSupplier condition, String what) {
        long end = System.nanoTime() + TimeUnit.SECONDS.toNanos(5);
        while (!condition.getAsBoolean()) {
            if (System.nanoTime() >= end) throw new AssertionError("timeout: " + what);
            Thread.yield();
        }
    }

    public static void main(String[] args) throws Exception {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).testId()
                .cacheSizeIndicator(1000000).evictionSchedule(Eviction.Schedule.BUDGET, 1)
                .audit(0).start();
        Eviction eviction = db.internal().eviction();
        CountDownLatch batchReady = new CountDownLatch(1);
        CountDownLatch throwNow = new CountDownLatch(1);
        CountDownLatch writerInside = new CountDownLatch(1);
        CountDownLatch finishWriter = new CountDownLatch(1);
        AtomicReference<Throwable> writerFailure = new AtomicReference<>();
        AtomicReference<Thread> evictionThread = new AtomicReference<>();
        Error injected = new AssertionError("batch failure before write-lock transfer");
        Thread writer = null;
        try {
            clock.setTime(1000000);
            db.execute(db.trans().put("k", "before").build());
            long before = db.internal().getMainStream().getLength();
            clock.setTime(2000000);
            Trans transaction = db.trans().put("k", "after").build();
            transaction.listener = new Trans.Listener() {
                public void valueNodeCreated(ValueNode node, long[] key) {
                    writerInside.countDown();
                    await(finishWriter, "release the writer after FAILED");
                }
                public void transExecuted(Db.ExecuteData x) {}
            };
            writer = new Thread(() -> {
                try { db.execute(transaction); }
                catch (Throwable x) { writerFailure.set(x); }
            }, "probe-writer");
            final Thread writerToStart = writer;
            eviction.testBeforeTrigger = () -> {
                if (!Thread.currentThread().getName().equals("bergdb-evictor")) return;
                evictionThread.set(Thread.currentThread());
                writerToStart.start();
                waitFor(() -> db.internal().writersWaiting() > 0, "writer waiting for batch");
                batchReady.countDown();
                await(throwNow, "controller holds readSync");
                throw injected;
            };
            db.setCacheSizeIndicator(1);
            await(batchReady, "batch has a waiting writer");
            synchronized (db.internal().getReadSynch()) {
                throwNow.countDown();
                await(writerInside, "writer entered after the batch threw");
                waitFor(() -> evictionThread.get().getState() == Thread.State.BLOCKED,
                        "failed evictor waiting to set FAILED under readSync");
                System.out.println("batch threw; next writer passed its go point; database active="
                        + db.internal().isActive());
            }
            waitFor(() -> !db.internal().isActive(), "evictor publishes FAILED");
            System.out.println("database FAILED before next writer appends; stream="
                    + db.internal().getMainStream().getLength());
            finishWriter.countDown();
            writer.join(5000);
            if (writer.isAlive()) throw new AssertionError("writer did not finish");
            long after = db.internal().getMainStream().getLength();
            System.out.println("next writer returned=" + (writerFailure.get() == null)
                    + "; appended after FAILED=" + (after > before)
                    + "; stream=" + before + " -> " + after);
            try {
                DbUtil.get(db, "k");
                throw new AssertionError("read did not see FAILED");
            } catch (DbFailedException x) {
                System.out.println("later read refused; cause is batch failure="
                        + (x.getCause() == injected));
            }
            if (writerFailure.get() != null || after <= before)
                throw new AssertionError("interleaving did not reproduce", writerFailure.get());
        } finally {
            eviction.testBeforeTrigger = null;
            throwNow.countDown();
            finishWriter.countDown();
            if (writer != null && writer.getState() != Thread.State.NEW) writer.join(5000);
            db.close();
        }
    }
}
