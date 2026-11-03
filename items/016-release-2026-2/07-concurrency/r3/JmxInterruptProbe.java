package bergdb.core;

import java.lang.reflect.Field;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

/** Exercise both the monitor's own interrupt and an interrupted stop caller. */
public final class JmxInterruptProbe {
    static Thread worker(Jmx.Speed speed) throws Exception {
        Field f = Jmx.Speed.class.getDeclaredField("thread");
        f.setAccessible(true);
        return (Thread) f.get(speed);
    }
    private static final class PausedDb extends Db {
        final CountDownLatch entered = new CountDownLatch(1), release = new CountDownLatch(1);
        PausedDb(DbBuilder b) { super(b); }
        @Override public long getTransactionCount() {
            if (Thread.currentThread().getName().equals("DBMonitor.MThread")) {
                entered.countDown();
                try {
                    if (!release.await(5, TimeUnit.SECONDS)) throw new AssertionError("release timed out");
                } catch (InterruptedException e) { throw new AssertionError(e); }
            }
            return super.getTransactionCount();
        }
    }
    public static void main(String[] args) throws Exception {
        try (Db db = Db.builder().testSetup().start()) {
            Jmx.Speed speed = new Jmx.Speed(db);
            speed.registerAndStart();
            try {
                Thread t = worker(speed);
                long end = System.nanoTime() + TimeUnit.SECONDS.toNanos(2);
                while (t.getState() != Thread.State.TIMED_WAITING && System.nanoTime() < end)
                    Thread.sleep(1);
                if (t.getState() != Thread.State.TIMED_WAITING) throw new AssertionError("no sleep");
                t.interrupt();
                t.join(1000);
                System.out.println("monitor died on interrupt while stop=false: " + !t.isAlive());
                speed.registerAndStart();
                System.out.println("registerAndStart retained dead thread: " + (worker(speed) == t));
            } finally { speed.stop(); }
        }
        PausedDb db = new PausedDb(Db.builder().testSetup());
        db.start();
        Jmx.Speed speed = new Jmx.Speed(db);
        Thread t = null;
        try {
            speed.registerAndStart();
            t = worker(speed);
            if (!db.entered.await(2, TimeUnit.SECONDS)) throw new AssertionError("monitor not paused");
            Thread.currentThread().interrupt();
            speed.stop();
            System.out.println("interrupted stop lost caller flag: " + !Thread.currentThread().isInterrupted());
            System.out.println("stop returned with monitor alive: " + t.isAlive());
        } finally {
            Thread.interrupted();
            db.release.countDown();
            if (t != null) t.join(2000);
            db.close();
        }
    }
}
