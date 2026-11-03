package bergdb.core;

import java.lang.reflect.Method;
import java.util.concurrent.*;

import bergdb.pub.util.SyncLevel;

/**
 * Review 016-06/S1: each operation of Jmx.DbMonitor on a running, a failed and a closed
 * database; each call in a thread of its own with a 2 s limit, to show a hang.
 */
public class JmxProbe {
    public static void main(String[] args) throws Exception {
        DbTesterFailure.FaultStream s = new DbTesterFailure.FaultStream();
        Db db = Db.builder().testSetup(s).start();
        db.execute(db.trans().put("/a", "a0").build());
        db.sync(SyncLevel.STRONG);
        Jmx.DbMonitor m = new Jmx.DbMonitor(db);
        run("running", m);

        s.failAppends = true;
        db.execute(db.trans().put("/a", "a1").build());
        try {
            db.sync(SyncLevel.STRONG);
        } catch (RuntimeException e) {
            System.out.println("sync: " + e.getClass().getSimpleName());
        }
        System.out.println("state: " + db.internal().isActive());
        run("failed", m);
        s.failAppends = false;
        db.close();
        run("closed", m);

        // A storage that stalls (a disk that does not return): appends held, the write
        // buffer fills, and a writer waits in store() with the write lock.
        DbTesterFailure.FaultStream h = new DbTesterFailure.FaultStream();
        final Db db3 = Db.builder().testSetup(h).start();
        h.holdAppends = true;
        Thread w = new Thread(() -> {
            try {
                for (int i = 0; i < 100; i++) {
                    db3.execute(db3.trans().put("/w" + i, new byte[2000]).build());
                }
            } catch (Throwable e) {
                // ends with the database
            }
        });
        w.setDaemon(true);
        w.start();
        Thread.sleep(500);
        System.out.println("writer state: " + w.getState());
        run("stalled storage", new Jmx.DbMonitor(db3));
        h.holdAppends = false;
        w.join(5000);
        db3.close();

        Db db2 = Db.builder().testSetup(new bergdb.stream.MemoryStream()).start();
        Jmx.DbMonitor m2 = new Jmx.DbMonitor(db2);
        db2.stop();
        run("stopped", m2);
        db2.close();
        System.exit(0);
    }

    static void run(String state, final Jmx.DbMonitor m) throws Exception {
        ExecutorService ex = Executors.newCachedThreadPool(r -> {
            Thread t = new Thread(r); t.setDaemon(true); return t; });
        StringBuilder b = new StringBuilder(state + ":");
        for (final Method method : Jmx.DbMonitorMBean.class.getMethods()) {
            final Object[] a;
            Class<?>[] p = method.getParameterTypes();
            if (p.length == 0) a = new Object[0];
            else if (p[0] == int.class) a = new Object[] {
                    method.getName().equals("setStartupDistance") ? 600000 : 2 };
            else if (p[0] == long.class) a = new Object[] {
                    method.getName().startsWith("setRetain") ? 5000000000000L : 10000000L };
            else a = new Object[] {0.25};
            Future<Object> f = ex.submit(() -> method.invoke(m, a));
            String r;
            try {
                Object o = f.get(2, TimeUnit.SECONDS);
                r = o instanceof String[] ? "[..]" : String.valueOf(o);
            } catch (TimeoutException e) {
                r = "HANGS";
            } catch (ExecutionException e) {
                Throwable c = e.getCause().getCause();
                r = c.getClass().getSimpleName();
            }
            b.append(" " + method.getName() + "=" + r + ";");
        }
        System.out.println(b);
        ex.shutdownNow();
    }
}
