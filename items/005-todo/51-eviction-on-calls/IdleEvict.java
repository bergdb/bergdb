import java.io.File;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;

import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.SyncLevel;
import bergdb.storage.StorageManager;
import bergdb.stream.FileStream;

/**
 * 005-51's measurement (2026-10-27, 006-09's W4): what an idle database costs once its
 * eviction thread has run. 005-14's IdleProbe with a small cache: opens a database on a
 * FileStream with a budget of 2 MB and a startup distance of 1 MB (so that index nodes are
 * written, and can be evicted), writes 200,000 transactions of one put (24-byte keys,
 * 100-byte values), reads every key (the loads start the eviction thread), syncs, and then
 * does nothing. Mode jvm opens no database: the JVM's own background work.
 *
 * Usage: java -cp bergdb.jar:CLASSES IdleEvict jvm|db DIR SETTLE_S
 * Prints READY and the threads alive when the work is done. SETTLE_S seconds later it takes
 * one snapshot of the CPU time of every Java thread and prints T0; on SIGTERM it prints each
 * thread's CPU time since T0, in ms. The process counters (wakeups, energy) are read from
 * outside, by 005-14's procstat.
 */
public class IdleEvict {
    static final Map<Long, Long> t0 = new HashMap<Long, Long>();
    static volatile long t0Nanos;

    public static void main(String[] args) throws Exception {
        String mode = args[0];
        File dir = new File(args[1]);
        int settle = Integer.parseInt(args[2]);
        final ThreadMXBean tmx = ManagementFactory.getThreadMXBean();

        Db db = null;
        if (mode.equals("db")) {
            dir.mkdirs();
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) if (f.getName().endsWith(".bergdb")) f.delete();
            db = Db.builder().stream("main", new FileStream(dir), StorageManager.DEFAULT_BUFFER_SIZE,
                    StorageManager.DEFAULT_BUFFER_TIME).cacheSizeIndicator(2 * 1000 * 1000)
                    .startupDistance(1000 * 1000).build();
            db.start();
            StringBuilder v = new StringBuilder();
            while (v.length() < 100) v.append("value ");
            String value = v.substring(0, 100);
            for (int i = 0; i < 200000; i++) {
                db.execute(db.trans().put(String.format(Locale.ROOT, "/idle/key-%017d", i), value));
            }
            for (int i = 0; i < 200000; i++) {
                DbUtil.get(db, String.format(Locale.ROOT, "/idle/key-%017d", i));
            }
            db.sync(SyncLevel.ORDINARY);
        } else if (!mode.equals("jvm")) {
            throw new IllegalArgumentException("mode " + mode);
        }
        StringBuilder names = new StringBuilder();
        for (ThreadInfo ti : tmx.getThreadInfo(tmx.getAllThreadIds())) {
            if (ti != null) names.append(ti.getThreadName()).append(" (").append(ti.getThreadState()).append("); ");
        }
        System.out.println("READY pid=" + ProcessHandle.current().pid() + " mode=" + mode);
        System.out.println("THREADS " + names);
        System.out.flush();

        Runtime.getRuntime().addShutdownHook(new Thread() {
            public void run() {
                long el = System.nanoTime() - t0Nanos;
                StringBuilder sb = new StringBuilder();
                long sum = 0;
                for (ThreadInfo ti : tmx.getThreadInfo(tmx.getAllThreadIds())) {
                    if (ti == null) continue;
                    long c = tmx.getThreadCpuTime(ti.getThreadId());
                    Long a = t0.get(ti.getThreadId());
                    if (c < 0 || a == null) continue;
                    long d = c - a;
                    sum += d;
                    if (d > 0) sb.append(String.format(Locale.ROOT, "THREAD %.3f ms %s%n", d / 1e6, ti.getThreadName()));
                }
                System.out.print(sb);
                System.out.printf(Locale.ROOT, "T1 elapsed_s=%.3f java_threads_cpu_ms=%.3f%n", el / 1e9, sum / 1e6);
                System.out.flush();
            }
        });

        Thread.sleep(settle * 1000L);
        for (long id : tmx.getAllThreadIds()) t0.put(id, tmx.getThreadCpuTime(id));
        t0Nanos = System.nanoTime();
        System.out.println("T0");
        System.out.flush();
        Object forever = new Object();
        synchronized (forever) {
            while (true) forever.wait();
        }
    }
}
