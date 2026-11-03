package bergdb.core;

import java.lang.reflect.Field;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import bergdb.pub.util.DbFailedException;

/** A batch's simulated JVM failure must reach the database's other threads. */
public final class EvictorFailureProbe {
    private static Object field(Object obj, String name) throws Exception {
        Field f = obj.getClass().getDeclaredField(name);
        f.setAccessible(true);
        return f.get(obj);
    }
    public static void main(String[] args) throws Exception {
        Db db = Db.builder().testSetup().cacheSizeIndicator(1000000)
                .evictionSchedule(Eviction.Schedule.BUDGET, 1).start();
        Eviction e = db.internal().eviction();
        CountDownLatch failed = new CountDownLatch(1);
        final Error injected = new AssertionError("simulated error during eviction");
        try {
            db.execute(db.trans().put("/kept", "value").build());
            // Installation precedes Thread.start(), which publishes the hook to the worker.
            e.testBeforeTrigger = () -> {
                Thread.currentThread().setUncaughtExceptionHandler((t, x) -> failed.countDown());
                throw injected;
            };
            db.setCacheSizeIndicator(1);
            if (!failed.await(2, TimeUnit.SECONDS)) throw new AssertionError("batch did not fail");
            Thread dead = (Thread) field(e, "evictor");
            dead.join(2000);
            e.testBeforeTrigger = null;
            System.out.println("evictor dead: " + !dead.isAlive());
            System.out.println("database active after worker Error: " + db.internal().isActive());
            try {
                System.out.println("cached read after worker Error: " + DbUtil.getString(db, "/kept"));
                System.out.println("FAULT: read was accepted");
            } catch (DbFailedException expected) {
                System.out.println("database rejected read");
            }
            db.setCacheSizeIndicator(1);
            Thread recorded = (Thread) field(e, "evictor");
            System.out.println("request kept on the same dead worker: " + (recorded == dead)
                    + "; wanted=" + field(e, "wanted"));
        } finally {
            e.testBeforeTrigger = null;
            db.close();
        }
    }
}
