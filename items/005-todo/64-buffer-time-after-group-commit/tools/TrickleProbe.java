import java.io.File;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.util.Locale;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.locks.LockSupport;

import bergdb.core.Db;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StorageManager;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;

/**
 * bergdb 005-64, question 4: a database while data trickles in, and then idle, at a given
 * buffer time. After 005-14's IdleProbe. Written 2026-10-28 by Claude (Opus 5.5, Claude Code).
 *
 * <p>Mode db: a database on a FileStream in DIR, the main stream at BUFFERMS ms (default
 * buffer size); 100 small transactions and a sync; READY; then RATE transactions a second (one
 * put of a 16-byte key and a VALSIZE-byte value each, no sync), on a schedule, for TRICKLE_S
 * seconds; then TRICKLE (the phase's counters) and IDLE; then nothing, until SIGTERM, when
 * IDLESTAT gives the idle phase's counters. Mode jvm opens no database: READY, IDLE at once,
 * and IDLESTAT on SIGTERM; the JVM's own background work. The process's wake-ups and energy
 * are read from outside (procstat, by trickle.sh), in windows inside each phase.
 *
 * <p>Lines:
 * READY pid= mode= buffer_ms=
 * TRICKLE elapsed_s= transactions= forces= process_cpu_ms= consumer_cpu_ms= end_epoch_ms=
 * IDLE epoch_ms=
 * IDLESTAT elapsed_s= forces= process_cpu_ms= consumer_cpu_ms=
 * The forces are the appends that reach the FileStream (each one forced). consumer_cpu_ms is
 * the CPU of the thread BufferedStream-consumer-* in the phase.
 *
 * <p>Usage: java -cp bergdb.jar:CLASSES TrickleProbe db|jvm BUFFERMS DIR TRICKLE_S RATE VALSIZE
 */
public class TrickleProbe {
    static final class CountingStream implements AppendOnlyStream {
        final FileStream s;
        final AtomicLong appends = new AtomicLong();

        CountingStream(FileStream s) { this.s = s; }

        public long getLength() { return s.getLength(); }
        public long getFirstPos() { return s.getFirstPos(); }
        public void read(long position, byte[] dest, int destOffset, int length) throws IOException {
            s.read(position, dest, destOffset, length);
        }
        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            s.append(source, sourceOffset, length);
            appends.incrementAndGet();
        }
        public void pretruncate(long position) throws IOException { s.pretruncate(position); }
        // Kept so that the tool compiles against older jars, whose AppendOnlyStream has it;
        // main's has not (bergdb 019-04). No layer of BergDB calls it.
        public void seekFirstPos(long position) { throw new UnsupportedOperationException(); }
        public void close() throws IOException { s.close(); }
    }

    static final ThreadMXBean tmx = ManagementFactory.getThreadMXBean();

    static long consumerCpu() {
        long sum = 0;
        long[] ids = tmx.getAllThreadIds();
        ThreadInfo[] infos = tmx.getThreadInfo(ids, 0);
        for (int i = 0; i < ids.length; i++) {
            if (infos[i] != null && infos[i].getThreadName().startsWith("BufferedStream-consumer")) {
                long t = tmx.getThreadCpuTime(ids[i]);
                if (t > 0) sum += t;
            }
        }
        return sum;
    }

    static long processCpu() {
        return ((com.sun.management.OperatingSystemMXBean) ManagementFactory.getOperatingSystemMXBean())
                .getProcessCpuTime();
    }

    public static void main(String[] args) throws Exception {
        if (args.length != 6) {
            System.err.println("Usage: TrickleProbe db|jvm BUFFERMS DIR TRICKLE_S RATE VALSIZE");
            System.exit(2);
        }
        String mode = args[0];
        int bufferMs = Integer.parseInt(args[1]);
        File dir = new File(args[2]);
        double trickleS = Double.parseDouble(args[3]);
        int rate = Integer.parseInt(args[4]);
        int valsize = Integer.parseInt(args[5]);

        Db db = null;
        CountingStream counting = null;
        if (mode.equals("db")) {
            if (dir.exists()) throw new IllegalStateException(dir + " exists");
            dir.mkdirs();
            counting = new CountingStream(new FileStream(dir));
            db = Db.builder().stream("main", counting, StorageManager.DEFAULT_BUFFER_SIZE, bufferMs).build();
            db.start();
            for (int i = 0; i < 100; i++) {
                db.execute(db.trans().put("/trickle/" + (i % 100), "warm " + i));
            }
            db.sync(SyncLevel.ORDINARY);
        } else if (!mode.equals("jvm")) {
            throw new IllegalArgumentException("mode " + mode);
        }
        System.out.println("READY pid=" + ProcessHandle.current().pid() + " mode=" + mode + " buffer_ms=" + bufferMs);
        System.out.flush();

        if (db != null) {
            long f0 = counting.appends.get(), p0 = processCpu(), c0 = consumerCpu();
            long start = System.nanoTime();
            long interval = 1000000000L / rate;
            long end = start + (long) (trickleS * 1e9);
            long n = 0;
            byte[] value = new byte[valsize];
            for (long i = 0; ; i++) {
                long intended = start + i * interval;
                if (intended >= end) break;
                long now;
                while ((now = System.nanoTime()) < intended) {
                    LockSupport.parkNanos(intended - now);
                }
                value[0] = (byte) i;
                db.execute(db.trans().put(String.format("/trickle/%08d", i % 1000), value));
                n++;
            }
            long el = System.nanoTime() - start;
            long f1 = counting.appends.get(), p1 = processCpu(), c1 = consumerCpu();
            System.out.printf(Locale.ROOT, "TRICKLE elapsed_s=%.3f transactions=%d forces=%d process_cpu_ms=%.3f "
                    + "consumer_cpu_ms=%.3f end_epoch_ms=%d%n", el / 1e9, n, f1 - f0, (p1 - p0) / 1e6, (c1 - c0) / 1e6,
                    System.currentTimeMillis());
        }

        final CountingStream cs = counting;
        final long f0 = cs == null ? 0 : cs.appends.get(), p0 = processCpu(), c0 = consumerCpu();
        final long t0 = System.nanoTime();
        Runtime.getRuntime().addShutdownHook(new Thread() {
            public void run() {
                long el = System.nanoTime() - t0;
                long f1 = cs == null ? 0 : cs.appends.get();
                System.out.printf(Locale.ROOT, "IDLESTAT elapsed_s=%.3f forces=%d process_cpu_ms=%.3f consumer_cpu_ms=%.3f%n",
                        el / 1e9, f1 - f0, (processCpu() - p0) / 1e6, (consumerCpu() - c0) / 1e6);
                System.out.flush();
            }
        });
        System.out.println("IDLE epoch_ms=" + System.currentTimeMillis());
        System.out.flush();
        Object forever = new Object();
        synchronized (forever) {
            while (true) forever.wait();
        }
    }
}
