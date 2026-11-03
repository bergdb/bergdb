package bergdb.core;

import java.io.IOException;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * 016-06/R7, D1: a transaction's warmup reads before the write lock, at the latest time when
 * it starts. If one of its stream reads is held while other commits make a cut that overtakes
 * that time, execute() throws LookupTimeNotAvailableException, which its Javadoc does not list.
 * The hold is a test stream that makes one thread's reads wait (before the MemoryStream's
 * monitor), so it forces the interleaving.
 */
public class R7WarmupExpiryProbe {
    static final class HoldStream implements AppendOnlyStream {
        final MemoryStream s;
        volatile Thread holdThread;
        volatile boolean released;
        volatile long heldPos = -1;
        final Object lock = new Object();
        HoldStream(MemoryStream s) { this.s = s; }
        public long getLength() { return s.getLength(); }
        public long getFirstPos() { return s.getFirstPos(); }
        public void read(long position, byte[] dest, int off, int len) throws IOException {
            if (Thread.currentThread() == holdThread && !released) {
                synchronized (lock) {
                    heldPos = position;
                    lock.notifyAll();
                    while (!released) {
                        try { lock.wait(); } catch (InterruptedException e) { }
                    }
                }
            }
            s.read(position, dest, off, len);
        }
        public void append(byte[] src, int off, int len) throws IOException { s.append(src, off, len); }
        public void pretruncate(long position) throws IOException { s.pretruncate(position); }
        public void seekFirstPos(long position) throws IOException { s.seekFirstPos(position); }
        public void close() throws IOException { s.close(); }
    }

    public static void main(String[] args) throws Exception {
        long[] time = {Clock.UNITS_PER_SEC};
        CoreTestClock c1 = new CoreTestClock();
        c1.setTime(time[0]);
        MemoryStream ms = new MemoryStream();
        Db d1 = Db.builder().testSetup(ms).clock(c1).startupDistance(2000).start();
        d1.execute(d1.trans().put("/old/x", new byte[100]).build());
        java.util.Random r = new java.util.Random(1);
        for (int i = 0; i < 300; i++) {
            time[0] += Clock.UNITS_PER_SEC / 20; c1.setTime(time[0]);
            d1.execute(d1.trans().put("/k/" + r.nextInt(50), new byte[1 + r.nextInt(60)]).build());
        }
        d1.sync(SyncLevel.STRONG);
        d1.close();

        final HoldStream hs = new HoldStream(ms.copy());
        final CoreTestClock c2 = new CoreTestClock();
        c2.setTime(time[0]);
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        final Db db = b.stream("main", hs, 100 * 1000, 10).clock(c2).startupDistance(2000).start();
        db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
        final Throwable[] result = new Throwable[1];
        final boolean[] done = new boolean[1];
        Thread w = new Thread(new Runnable() {
            public void run() {
                try {
                    db.execute(db.trans().put("/old/x", "new").build());
                } catch (Throwable e) {
                    result[0] = e;
                }
                done[0] = true;
            }
        });
        hs.holdThread = w;
        long readTime = db.lookupTime(Long.MAX_VALUE);
        w.start();
        synchronized (hs.lock) {
            long until = System.currentTimeMillis() + 5000;
            while (hs.heldPos == -1 && System.currentTimeMillis() < until && w.isAlive()) {
                hs.lock.wait(100);
            }
        }
        if (hs.heldPos == -1) {
            System.out.println("the warmup read nothing from the stream (done " + done[0] + ", "
                    + result[0] + ")");
            hs.released = true;
            w.join();
            db.close();
            return;
        }
        System.out.println("warmup held at stream pos " + hs.heldPos + ", its time " + readTime);
        int i = 0;
        for (; i < 6000 && !(hs.getFirstPos() > hs.heldPos
                && db.getFirstAvailableLookupTime() > readTime); i++) {
            time[0] += Clock.UNITS_PER_SEC / 20; c2.setTime(time[0]);
            db.execute(db.trans().put("/k/" + r.nextInt(50), new byte[1 + r.nextInt(60)]).build());
        }
        System.out.println("after " + i + " puts: first pos " + hs.getFirstPos()
                + ", first available time " + db.getFirstAvailableLookupTime());
        synchronized (hs.lock) {
            hs.released = true;
            hs.lock.notifyAll();
        }
        w.join(10000);
        System.out.println("the held transaction: " + (result[0] == null ? "committed" : result[0]));
        System.out.println("database active: " + db.internal().isActive());
        db.close();
    }
}
