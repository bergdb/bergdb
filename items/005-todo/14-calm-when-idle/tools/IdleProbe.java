import java.io.File;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;

import bergdb.core.Db;
import bergdb.core.SyncLevel;
import bergdb.storage.StorageManager;
import bergdb.stream.FileStream;

/**
 * 005-13, follow-up (2026-10-21): what an idle database costs. Opens a database on a
 * FileStream with the given buffer time, writes 1000 small transactions, syncs, and then
 * does nothing. Mode jvm opens no database: the JVM's own background work.
 *
 * Usage: java -cp bergdb.jar:CLASSES IdleProbe jvm|db BUFFERMS DIR SETTLE_S
 * Prints READY when the writes are done. SETTLE_S seconds later it takes one snapshot of
 * the CPU time of every Java thread (ThreadMXBean) and prints T0; on SIGTERM it prints
 * each thread's CPU time since T0, in ms, and the time since T0. The process counters
 * (wakeups, energy) are read from outside, by procstat.
 */
public class IdleProbe {
    static final Map<Long, Long> t0 = new HashMap<Long, Long>();
    static volatile long t0Nanos;

    public static void main(String[] args) throws Exception {
        String mode = args[0];
        int bufferMs = Integer.parseInt(args[1]);
        File dir = new File(args[2]);
        int settle = Integer.parseInt(args[3]);
        final ThreadMXBean tmx = ManagementFactory.getThreadMXBean();

        Db db = null;
        if (mode.equals("db")) {
            dir.mkdirs();
            File[] fs = dir.listFiles();
            if (fs != null) for (File f : fs) if (f.getName().endsWith(".bergdb")) f.delete();
            db = Db.builder().stream("main", new FileStream(dir), StorageManager.DEFAULT_BUFFER_SIZE, bufferMs).build();
            db.start();
            for (int i = 0; i < 1000; i++) {
                db.execute(db.trans().put("/idle/" + (i % 100), "value " + i));
            }
            db.sync(SyncLevel.ORDINARY);
        } else if (!mode.equals("jvm")) {
            throw new IllegalArgumentException("mode " + mode);
        }
        System.out.println("READY pid=" + ProcessHandle.current().pid() + " mode=" + mode + " bufferMs=" + bufferMs);
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
