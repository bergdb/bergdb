import java.lang.instrument.Instrumentation;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;

/**
 * bergdb 005-64, question 1: the CPU of a Perf run, which Perf does not record. A Java agent
 * (-javaagent:cpu64.jar, given to performance.sh with JFLAGS) that prints, when the JVM ends,
 * one line
 *
 *   CPU64 process_cpu_ms=P consumer_cpu_ms=C consumers=N uptime_ms=U
 *
 * P is the process's CPU time (user and system) over the whole run: load, warm-up, the
 * measured phase and the verification. C is the CPU time of the threads named
 * BufferedStream-consumer-* (the streams' consumers: the flushes and the timer's wakes), from
 * a sample every 50 ms, as a consumer ends when its database closes; up to 50 ms of a
 * consumer's last CPU can be missed. Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
 */
public class CpuAgent {
    static final Map<Long, Long> consumers = new HashMap<Long, Long>();

    public static void premain(String args, Instrumentation inst) {
        final ThreadMXBean tmx = ManagementFactory.getThreadMXBean();
        Thread sampler = new Thread("cpu64-sampler") {
            public void run() {
                while (true) {
                    sample(tmx);
                    try {
                        Thread.sleep(50);
                    } catch (InterruptedException e) {
                        return;
                    }
                }
            }
        };
        sampler.setDaemon(true);
        sampler.start();
        Runtime.getRuntime().addShutdownHook(new Thread("cpu64-report") {
            public void run() {
                sample(tmx);
                long c = 0;
                int n;
                synchronized (consumers) {
                    for (long v : consumers.values()) c += v;
                    n = consumers.size();
                }
                long p = ((com.sun.management.OperatingSystemMXBean) ManagementFactory.getOperatingSystemMXBean())
                        .getProcessCpuTime();
                System.out.printf(Locale.ROOT, "CPU64 process_cpu_ms=%.1f consumer_cpu_ms=%.1f consumers=%d uptime_ms=%d%n",
                        p / 1e6, c / 1e6, n, ManagementFactory.getRuntimeMXBean().getUptime());
                System.out.flush();
            }
        });
    }

    static void sample(ThreadMXBean tmx) {
        long[] ids = tmx.getAllThreadIds();
        ThreadInfo[] infos = tmx.getThreadInfo(ids, 0);
        for (int i = 0; i < ids.length; i++) {
            ThreadInfo ti = infos[i];
            if (ti == null || !ti.getThreadName().startsWith("BufferedStream-consumer")) continue;
            long t = tmx.getThreadCpuTime(ids[i]);
            if (t < 0) continue;
            synchronized (consumers) {
                consumers.put(ids[i], t);
            }
        }
    }
}
