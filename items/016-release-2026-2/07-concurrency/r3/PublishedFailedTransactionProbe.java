package bergdb.core;

import java.io.IOException;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;
import bergdb.dag.Keys;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.MemoryStream;

/** Pause the first flush of an oversized record, then fail it before writing a byte. */
public final class PublishedFailedTransactionProbe {
    static final class HeldStream extends MemoryStream {
        final CountDownLatch entered = new CountDownLatch(1);
        final CountDownLatch release = new CountDownLatch(1);
        volatile boolean armed;
        @Override public void append(byte[] bytes, int offset, int length) throws IOException {
            if (armed) {
                entered.countDown();
                try {
                    if (!release.await(5, TimeUnit.SECONDS)) throw new IOException("probe timeout");
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    throw new IOException(e);
                }
                throw new IOException("injected write failure before new record bytes");
            }
            super.append(bytes, offset, length);
        }
    }

    public static void main(String[] args) throws Exception {
        HeldStream stream = new HeldStream();
        Db db = Db.builder().testSetup(stream).stream("main", stream, 1024, 10).start();
        AtomicReference<Throwable> failure = new AtomicReference<>();
        Trans trans = db.trans().put("/key", new byte[8192]).build();
        Thread writer = new Thread(() -> {
            try { db.execute(trans); } catch (Throwable e) { failure.set(e); }
        }, "probe-writer");
        try {
            db.execute(db.trans().put("/key", new byte[] {7}).build());
            db.sync(SyncLevel.ORDINARY);
            long before = stream.getLength();
            stream.armed = true;
            writer.start();
            if (!stream.entered.await(2, TimeUnit.SECONDS)) throw new AssertionError("no held flush");
            byte[] read = db.getOne(Long.MAX_VALUE, Keys.toSegments("/key"), db.newGetData());
            System.out.println("writer still executing: " + writer.isAlive());
            System.out.println("reader saw new value: " + (read.length == 8192));
            System.out.println("transaction time already a lookup time: "
                    + (db.lookupTime(Long.MAX_VALUE) == trans.tt));
            System.out.println("new record bytes written: " + (stream.getLength() - before));
            stream.release.countDown();
            writer.join(2000);
            if (writer.isAlive()) throw new AssertionError("writer did not end");
            System.out.println("writer result: " + failure.get());
            System.out.println("database active after failure: " + db.internal().isActive());
        } finally {
            stream.release.countDown();
            writer.join(2000);
            db.close();
        }
        Db reopened = Db.builder().testSetup(stream.copy()).start();
        try {
            byte[] restored = DbUtil.get(reopened, "/key");
            System.out.println("value length after reopen: " + restored.length);
            if (restored.length != 1 || restored[0] != 7) throw new AssertionError("old state missing");
        } finally { reopened.close(); }
    }
}
