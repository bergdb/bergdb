package bergdb.core;

import java.io.IOException;
import java.lang.reflect.Field;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.BufferedStream;
import bergdb.stream.MemoryStream;

/** The consumer reports failure to StorageManager, but no notification reaches Db. */
public final class BackgroundFlushFailureProbe {
    static final class FailingStream extends MemoryStream {
        volatile boolean fail;
        @Override public void append(byte[] bytes, int offset, int length) throws IOException {
            if (fail) throw new IOException("injected background write failure");
            super.append(bytes, offset, length);
        }
    }
    public static void main(String[] args) throws Exception {
        FailingStream stream = new FailingStream();
        Db db = Db.builder().testSetup(stream).start();
        try {
            db.execute(db.trans().put("/key", "old").build());
            db.sync(SyncLevel.ORDINARY);
            BufferedStream buffered = (BufferedStream) db.internal().getMainStream();
            Field f = BufferedStream.class.getDeclaredField("consumer");
            f.setAccessible(true);
            Thread consumer = (Thread) f.get(buffered);
            stream.fail = true;
            db.execute(db.trans().put("/key", "new").build());
            buffered.flushSoon(buffered.getLength());
            consumer.join(2000);
            if (consumer.isAlive()) throw new AssertionError("consumer did not fail/end");
            System.out.println("failed consumer terminated: true");
            System.out.println("database active after consumer join: " + db.internal().isActive());
            System.out.println("cached read accepted after storage failure: " + DbUtil.getString(db, "/key"));
            try {
                db.execute(db.trans().put("/later", "value").build());
                throw new AssertionError("later append accepted");
            } catch (DbFailedException expected) {
                System.out.println("database fails only on next append: " + !db.internal().isActive());
            }
        } finally { db.close(); }
    }
}
