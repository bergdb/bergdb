import java.io.File;
import java.io.IOException;
import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.pub.Action;
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.RwEnvironment;
import bergdb.pub.Transaction;
import bergdb.pubimp.DatabaseImp;
import bergdb.pubimp.RwTransaction;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.AppendOnlyStream;

/**
 * bergdb 006-11: public rw actions, optimistic versus serialized application actions.
 * This is an item-local experiment; it changes no production code.
 *
 * Example: RwBench threads=4 mode=optimistic workload=partitioned keys=4096
 * reads=1 work=0 seconds=3 warmupSeconds=2 storage=memory durable=false
 *
 * Each action reads distinct counters at one snapshot, computes dependent arithmetic,
 * and increments its first counter. A fixed-size stored value retains the computation's
 * seed and result. Every value read has its guard checked; after both phases all stored
 * computations are recomputed and the sum of counters must equal every successful action,
 * including warm-up and post-deadline drainage. No shared per-operation statistics.
 */
public final class RwBench {
    static final long GUARD = 0x6a09e667f3bcc909L;
    static final ThreadMXBean THREAD = ManagementFactory.getThreadMXBean();
    static final com.sun.management.ThreadMXBean ALLOC =
            THREAD instanceof com.sun.management.ThreadMXBean
                    ? (com.sun.management.ThreadMXBean) THREAD : null;
    static volatile long calibrationSink;

    final Map<String, String> args = new LinkedHashMap<>();
    final int threads, keys, reads, work, startupBytes;
    final double seconds, warmupSeconds, hotFraction;
    final long seed, cacheBytes;
    final String mode, workload, storage, variant;
    final boolean durable, diagnosticLoads;
    final Object gate = new Object();
    final String[] keyNames;
    final Db core;
    final Database db;
    final ProbeStream probe;

    RwBench(String[] commandLine) throws Exception {
        for (String arg : commandLine) {
            int eq = arg.indexOf('=');
            if (eq < 1) throw new IllegalArgumentException("expected key=value: " + arg);
            if (args.put(arg.substring(0, eq), arg.substring(eq + 1)) != null)
                throw new IllegalArgumentException("duplicate argument: " + arg);
        }
        threads = integer("threads", 1);
        keys = integer("keys", 4096);
        reads = integer("reads", 1);
        work = integer("work", 0);
        startupBytes = integer("startupBytes", 0);
        seconds = decimal("seconds", 3);
        warmupSeconds = decimal("warmupSeconds", 2);
        hotFraction = decimal("hotFraction", 0.9);
        seed = Long.parseLong(value("seed", "1"));
        cacheBytes = Long.parseLong(value("cacheBytes", "0"));
        mode = value("mode", "optimistic");
        workload = value("workload", "partitioned");
        storage = value("storage", "memory");
        variant = System.getProperty("bench.variant", "stock");
        durable = Boolean.parseBoolean(value("durable", "false"));
        diagnosticLoads = Boolean.parseBoolean(value("diagnosticLoads", "false"));
        if (!List.of("optimistic", "serial").contains(mode)) bad("unknown mode");
        if (!variant.equals("stock") && !mode.equals("serial"))
            bad("experimental builds may run only serial actions");
        if (!List.of("partitioned", "uniform", "hot").contains(workload)) bad("unknown workload");
        if (!List.of("memory", "file").contains(storage)) bad("unknown storage");
        if (threads < 1 || threads > 128 || keys < 1 || reads < 1 || reads > keys
                || work < 0 || seconds <= 0 || warmupSeconds < 0 || hotFraction < 0
                || hotFraction > 1 || cacheBytes < 0 || startupBytes < 0) bad("invalid numeric parameter");
        if (workload.equals("partitioned") && (keys % threads != 0 || keys / threads < reads))
            bad("partitioned requires keys divisible by threads and reads <= keys/threads");

        keyNames = new String[keys];
        for (int i = 0; i < keys; i++) keyNames[i] = String.format(Locale.ROOT, "/bench/c/%08d", i);
        DbBuilder builder = Db.builder().retainForever().testId();
        if (startupBytes > 0) builder.startupDistance(startupBytes);
        if (cacheBytes == 0) builder.noEvict();
        else builder.cacheSizeIndicator(cacheBytes);
        AppendOnlyStream stream;
        if (storage.equals("memory")) stream = new MemoryStream();
        else {
            File dir = new File(value("dir", ""));
            if (dir.getPath().isEmpty()) bad("file storage needs dir=PATH");
            if (dir.exists() && dir.list() != null && dir.list().length > 0)
                bad("file benchmark directory must be empty: " + dir);
            stream = new FileStream(dir);
        }
        probe = diagnosticLoads ? new ProbeStream(stream) : null;
        builder.mainStream(probe == null ? stream : probe);
        core = builder.build();
        if (probe != null) probe.writeLock = core.internal().getWriteLock();
        db = DatabaseImp.createAndStart(core);
    }

    /** Counts actual underlying stream reads, without replacing eviction's load listener. */
    static final class ProbeStream implements AppendOnlyStream {
        final AppendOnlyStream delegate;
        final AtomicLong lockedReads = new AtomicLong(), unlockedReads = new AtomicLong();
        final AtomicLong lockedNs = new AtomicLong(), unlockedNs = new AtomicLong();
        volatile Object writeLock;
        ProbeStream(AppendOnlyStream delegate) { this.delegate = delegate; }
        public long getLength() { return delegate.getLength(); }
        public long getFirstPos() { return delegate.getFirstPos(); }
        public void read(long position, byte[] dest, int offset, int length) throws IOException {
            boolean locked = writeLock != null && Thread.holdsLock(writeLock);
            long begin = System.nanoTime();
            try { delegate.read(position, dest, offset, length); }
            finally {
                (locked ? lockedReads : unlockedReads).incrementAndGet();
                (locked ? lockedNs : unlockedNs).addAndGet(System.nanoTime() - begin);
            }
        }
        public void append(byte[] source, int offset, int length) throws IOException { delegate.append(source, offset, length); }
        public void pretruncate(long position) throws IOException { delegate.pretruncate(position); }
        public void seekFirstPos(long position) throws IOException { delegate.seekFirstPos(position); }
        public void close() throws IOException { delegate.close(); }
    }

    String value(String key, String fallback) { return args.getOrDefault(key, fallback); }
    int integer(String key, int fallback) { return Integer.parseInt(value(key, "" + fallback)); }
    double decimal(String key, double fallback) { return Double.parseDouble(value(key, "" + fallback)); }
    static void bad(String message) { throw new IllegalArgumentException(message); }

    static long compute(long seed, int iterations) {
        long x = seed ^ 0x9e3779b97f4a7c15L;
        for (int i = 0; i < iterations; i++) {
            x ^= x >>> 27;
            x *= 0x3c79ac492ba7b653L;
            x ^= x >>> 33;
            x *= 0x1c69b3f74ac4ae35L;
        }
        return x ^ (x >>> 27);
    }

    static long getLong(byte[] bytes, int offset) {
        long result = 0;
        for (int i = 0; i < 8; i++) result |= (bytes[offset + i] & 255L) << (i * 8);
        return result;
    }

    static void putLong(byte[] bytes, int offset, long value) {
        for (int i = 0; i < 8; i++) bytes[offset + i] = (byte) (value >>> (i * 8));
    }

    static byte[] payload(long count, long seed, long result) {
        byte[] out = new byte[32];
        putLong(out, 0, count);
        putLong(out, 8, seed);
        putLong(out, 16, result);
        putLong(out, 24, count ^ Long.rotateLeft(seed, 17) ^ Long.rotateLeft(result, 31) ^ GUARD);
        return out;
    }

    static void check(byte[] value) {
        if (value == null || value.length != 32) throw new AssertionError("bad value size");
        long count = getLong(value, 0), seed = getLong(value, 8), result = getLong(value, 16);
        if (count < 0 || getLong(value, 24)
                != (count ^ Long.rotateLeft(seed, 17) ^ Long.rotateLeft(result, 31) ^ GUARD))
            throw new AssertionError("bad value guard or count");
    }

    void preload() {
        Connection connection = db.connection();
        for (int start = 0; start < keys; start += 100) {
            bergdb.pub.WBuilder builder = connection.w();
            for (int i = start; i < Math.min(keys, start + 100); i++)
                builder.put(keyNames[i], payload(0, i, compute(i, work)));
            builder.execute();
        }
    }

    static final class Hist {
        final long[] bins = new long[1024];
        long count, max;
        double sum;
        static int index(long ns) {
            if (ns <= 0) return 0;
            int exponent = 63 - Long.numberOfLeadingZeros(ns);
            long base = 1L << exponent;
            int fraction = (int) (((ns - base) * 16) / base);
            return Math.min(1023, exponent * 16 + fraction);
        }
        void add(long ns) {
            bins[index(ns)]++;
            count++;
            sum += ns;
            max = Math.max(max, ns);
        }
        void merge(Hist other) {
            for (int i = 0; i < bins.length; i++) bins[i] += other.bins[i];
            count += other.count;
            sum += other.sum;
            max = Math.max(max, other.max);
        }
        long percentile(double p) {
            if (count == 0) return 0;
            long rank = Math.max(1, (long) Math.ceil(count * p)), seen = 0;
            for (int i = 0; i < bins.length; i++) {
                seen += bins[i];
                if (seen >= rank) {
                    int exponent = i / 16, fraction = i % 16;
                    double upper = Math.scalb(1.0 + (fraction + 1) / 16.0, exponent);
                    return Math.min(max, (long) upper);
                }
            }
            return max;
        }
        Map<String, Object> result() {
            Map<String, Object> out = new LinkedHashMap<>();
            out.put("count", count);
            out.put("mean_ns", count == 0 ? 0 : sum / count);
            out.put("p50_ns_upper", percentile(0.5));
            out.put("p95_ns_upper", percentile(0.95));
            out.put("p99_ns_upper", percentile(0.99));
            out.put("max_ns", max);
            return out;
        }
    }

    final class Phase {
        final CountDownLatch ready = new CountDownLatch(threads), go = new CountDownLatch(1);
        final Worker[] workers = new Worker[threads];
        final double duration;
        long start, deadline, end;
        Phase(double duration, int ordinal) {
            this.duration = duration;
            for (int i = 0; i < threads; i++) workers[i] = new Worker(this, i, ordinal);
        }
        Map<String, Object> run() throws Exception {
            long loads0 = core.internal().nodeCollection().loads();
            long locked0 = probe == null ? 0 : probe.lockedReads.get();
            long unlocked0 = probe == null ? 0 : probe.unlockedReads.get();
            long lockedNs0 = probe == null ? 0 : probe.lockedNs.get();
            long unlockedNs0 = probe == null ? 0 : probe.unlockedNs.get();
            long[] gc0 = gc();
            long process0 = processCpu();
            for (Worker worker : workers) worker.start();
            if (!ready.await(20, TimeUnit.SECONDS)) throw new AssertionError("worker startup timeout");
            start = System.nanoTime();
            deadline = start + (long) (duration * 1e9);
            go.countDown();
            long joinDeadline = deadline + TimeUnit.SECONDS.toNanos(45);
            for (Worker worker : workers) {
                long remaining = joinDeadline - System.nanoTime();
                if (remaining > 0) worker.join(Math.max(1, TimeUnit.NANOSECONDS.toMillis(remaining)));
                if (worker.isAlive()) throw new AssertionError("worker failed to drain within 45 s: " + worker.getName());
                if (worker.error != null) throw new AssertionError("worker failed: " + worker.getName(), worker.error);
            }
            end = System.nanoTime();
            long[] gc1 = gc();
            long total = 0, active = 0, attempts = 0, cpu = 0, allocation = 0, maxAttempts = 0;
            long completedEnd = deadline;
            Hist latency = new Hist(), activeLatency = new Hist(), execution = new Hist();
            List<Long> perWorker = new ArrayList<>(), perWorkerActive = new ArrayList<>();
            for (Worker worker : workers) {
                total += worker.commits; active += worker.active; attempts += worker.attempts;
                cpu += worker.cpuNs; allocation += worker.allocatedBytes;
                maxAttempts = Math.max(maxAttempts, worker.maxAttempts);
                completedEnd = Math.max(completedEnd, worker.lastCompletion);
                latency.merge(worker.latency); activeLatency.merge(worker.activeLatency);
                execution.merge(worker.execution);
                perWorker.add(worker.commits); perWorkerActive.add(worker.active);
            }
            Map<String, Object> out = new LinkedHashMap<>();
            double batchSec = (completedEnd - start) * 1e-9;
            out.put("requested_seconds", duration);
            out.put("batch_seconds", batchSec);
            out.put("drain_seconds", Math.max(0, completedEnd - deadline) * 1e-9);
            out.put("commits", total); out.put("active_commits", active);
            out.put("active_commits_per_second", duration == 0 ? 0 : active / duration);
            out.put("batch_commits_per_second", batchSec == 0 ? 0 : total / batchSec);
            out.put("attempts", attempts);
            out.put("attempts_per_commit", total == 0 ? 0 : (double) attempts / total);
            out.put("max_attempts_one_commit", maxAttempts);
            out.put("per_worker_commits", perWorker);
            out.put("per_worker_active_commits", perWorkerActive);
            out.put("latency", latency.result());
            out.put("active_completion_latency", activeLatency.result());
            out.put("rw_execution_latency", execution.result());
            out.put("worker_cpu_ns", cpu);
            out.put("process_cpu_ns", processCpu() - process0);
            out.put("allocated_bytes", allocation);
            out.put("gc_count", gc1[0] - gc0[0]); out.put("gc_ms", gc1[1] - gc0[1]);
            out.put("stream_loads", core.internal().nodeCollection().loads() - loads0);
            if (diagnosticLoads) {
                out.put("storage_read_calls_with_write_lock", probe.lockedReads.get() - locked0);
                out.put("storage_read_calls_without_write_lock", probe.unlockedReads.get() - unlocked0);
                out.put("storage_read_ns_with_write_lock", probe.lockedNs.get() - lockedNs0);
                out.put("storage_read_ns_without_write_lock", probe.unlockedNs.get() - unlockedNs0);
            }
            out.put("stream_bytes", core.getStreamLength());
            out.put("heap_used_bytes", Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory());
            out.put("resident_cache_bytes", core.internal().cache().residents().bytes());
            out.put("eviction_summary", core.internal().eviction().summary());
            return out;
        }
    }

    final class Worker extends Thread implements Action {
        final Phase phase;
        final int id;
        final Random random;
        final int[] picks = new int[reads];
        final Hist latency = new Hist(), activeLatency = new Hist(), execution = new Hist();
        long commits, active, attempts, maxAttempts, cpuNs, allocatedBytes, lastCompletion;
        Throwable error;
        Connection connection;
        Worker(Phase phase, int id, int ordinal) {
            super("rwbench-" + ordinal + "-" + id);
            this.phase = phase; this.id = id;
            random = new Random(seed * 31 + id + ordinal * 10007L);
            setDaemon(true);
        }
        void chooseKeys() {
            int span = workload.equals("partitioned") ? keys / threads : keys;
            for (int j = 0; j < reads; j++) {
                int key;
                boolean duplicate;
                do {
                    if (j == 0 && workload.equals("hot") && random.nextDouble() < hotFraction) key = 0;
                    else {
                        key = random.nextInt(span);
                        if (workload.equals("partitioned")) key = key * threads + id;
                    }
                    duplicate = false;
                    for (int k = 0; k < j; k++) if (picks[k] == key) duplicate = true;
                } while (duplicate);
                picks[j] = key;
            }
        }
        public void run(RwEnvironment env) {
            long firstCount = 0;
            long input = 0x510e527fade682d1L;
            for (int j = 0; j < reads; j++) {
                byte[] value = env.get(keyNames[picks[j]], byte[].class);
                check(value);
                long count = getLong(value, 0);
                if (j == 0) firstCount = count;
                input = Long.rotateLeft(input ^ count ^ getLong(value, 16) ^ picks[j], 13)
                        * 0x9e3779b97f4a7c15L;
            }
            long result = compute(input, work);
            env.put(keyNames[picks[0]], payload(firstCount + 1, input, result));
        }
        public void run() {
            long cpu0 = 0, alloc0 = 0;
            try {
                connection = db.connection();
                phase.ready.countDown();
                phase.go.await();
                cpu0 = THREAD.isCurrentThreadCpuTimeSupported() ? THREAD.getCurrentThreadCpuTime() : 0;
                alloc0 = allocation();
                while (System.nanoTime() < phase.deadline) {
                    chooseKeys();
                    long begin = System.nanoTime();
                    Transaction transaction;
                    long executionBegin;
                    if (mode.equals("serial")) {
                        synchronized (gate) {
                            executionBegin = System.nanoTime();
                            transaction = connection.rw(this);
                        }
                    } else {
                        executionBegin = System.nanoTime();
                        transaction = connection.rw(this);
                    }
                    long rwEnd = System.nanoTime();
                    if (durable) transaction.sync();
                    long end = System.nanoTime();
                    commits++;
                    long runs = ((RwTransaction) transaction).getRunCount();
                    attempts += runs;
                    maxAttempts = Math.max(maxAttempts, runs);
                    latency.add(end - begin);
                    execution.add(rwEnd - executionBegin);
                    if (end <= phase.deadline) { active++; activeLatency.add(end - begin); }
                    lastCompletion = end;
                }
            } catch (Throwable t) {
                error = t;
                phase.ready.countDown();
            } finally {
                cpuNs = THREAD.isCurrentThreadCpuTimeSupported() ? Math.max(0, THREAD.getCurrentThreadCpuTime() - cpu0) : -1;
                allocatedBytes = Math.max(0, allocation() - alloc0);
            }
        }
        long allocation() {
            return ALLOC != null && ALLOC.isThreadAllocatedMemorySupported()
                    ? ALLOC.getThreadAllocatedBytes(Thread.currentThread().getId()) : 0;
        }
    }

    Map<String, Object> verify(long expected) {
        Connection connection = db.connection();
        connection.freezeLookupTime();
        long total = 0, digest = 0;
        for (int i = 0; i < keys; i++) {
            byte[] value = connection.get(keyNames[i], byte[].class);
            check(value);
            long count = getLong(value, 0), input = getLong(value, 8), result = getLong(value, 16);
            if (compute(input, work) != result) throw new AssertionError("bad stored work result at " + keyNames[i]);
            total += count;
            digest = Long.rotateLeft(digest ^ result ^ count ^ i, 7);
        }
        if (total != expected) throw new AssertionError("lost update: expected " + expected + ", got " + total);
        Map<String, Object> out = new LinkedHashMap<>();
        out.put("passed", true); out.put("sum_counters", total);
        out.put("expected_commits", expected); out.put("value_digest", Long.toUnsignedString(digest));
        return out;
    }

    static long processCpu() {
        java.lang.management.OperatingSystemMXBean os = ManagementFactory.getOperatingSystemMXBean();
        return os instanceof com.sun.management.OperatingSystemMXBean
                ? ((com.sun.management.OperatingSystemMXBean) os).getProcessCpuTime() : -1;
    }
    static long[] gc() {
        long count = 0, ms = 0;
        for (GarbageCollectorMXBean gc : ManagementFactory.getGarbageCollectorMXBeans()) {
            count += Math.max(0, gc.getCollectionCount()); ms += Math.max(0, gc.getCollectionTime());
        }
        return new long[] {count, ms};
    }
    static Map<String, Object> calibration(int work) {
        int iterations = work, loops = Math.max(200, Math.min(20000, 20000000 / Math.max(1, iterations)));
        long x = 0x123456789abcdefL;
        for (int i = 0; i < loops * 2; i++) x = compute(x + i, iterations);
        long begin = System.nanoTime();
        for (int i = 0; i < loops; i++) x = compute(x + i, iterations);
        double ns = (double) (System.nanoTime() - begin) / loops;
        calibrationSink = x;
        Map<String, Object> out = new LinkedHashMap<>();
        out.put("iterations", iterations); out.put("ns_per_compute", ns);
        out.put("ns_per_iteration", iterations == 0 ? null : ns / iterations);
        out.put("checksum", Long.toUnsignedString(x));
        return out;
    }

    Map<String, Object> run() throws Exception {
        Map<String, Object> out = new LinkedHashMap<>();
        out.put("schema", "rwbench-1"); out.put("variant", variant);
        out.put("threads", threads); out.put("mode", mode); out.put("workload", workload);
        out.put("keys", keys); out.put("reads", reads); out.put("work", work);
        out.put("seconds", seconds); out.put("warmup_seconds", warmupSeconds);
        out.put("hot_fraction", hotFraction); out.put("seed", seed);
        out.put("storage", storage); out.put("durable", durable); out.put("cache_bytes", cacheBytes);
        out.put("startup_bytes", startupBytes);
        out.put("effective_startup_bytes", core.getStartupDistance());
        out.put("diagnostic_loads", diagnosticLoads);
        out.put("java", System.getProperty("java.runtime.version"));
        out.put("available_processors", Runtime.getRuntime().availableProcessors());
        out.put("max_heap_bytes", Runtime.getRuntime().maxMemory());
        out.put("jvm_flags", ManagementFactory.getRuntimeMXBean().getInputArguments());
        out.put("thread_cpu_time_enabled", THREAD.isCurrentThreadCpuTimeSupported() && THREAD.isThreadCpuTimeEnabled());
        out.put("thread_allocated_memory_enabled", ALLOC != null && ALLOC.isThreadAllocatedMemorySupported() && ALLOC.isThreadAllocatedMemoryEnabled());
        out.put("calibration", calibration(work));
        preload();
        Map<String, Object> warmup = new Phase(warmupSeconds, 0).run();
        Map<String, Object> measured = new Phase(seconds, 1).run();
        out.put("warmup", warmup); out.put("measured", measured);
        long expected = ((Number) warmup.get("commits")).longValue() + ((Number) measured.get("commits")).longValue();
        out.put("verification", verify(expected));
        System.err.printf(Locale.ROOT, "%s %s %s t%d r%d work%d: %.0f active/s, %.0f drained/s, %.4f attempts/commit, p99 %.3f ms, drain %.3f s%n",
                variant, mode, workload, threads, reads, work,
                measured.get("active_commits_per_second"), measured.get("batch_commits_per_second"),
                measured.get("attempts_per_commit"),
                ((Number) ((Map<?, ?>) measured.get("latency")).get("p99_ns_upper")).doubleValue() / 1e6,
                measured.get("drain_seconds"));
        return out;
    }

    static String json(Object value) {
        if (value == null) return "null";
        if (value instanceof String) return "\"" + ((String) value).replace("\\", "\\\\").replace("\"", "\\\"").replace("\n", "\\n").replace("\r", "\\r").replace("\t", "\\t") + "\"";
        if (value instanceof Number || value instanceof Boolean) return value.toString();
        if (value instanceof Map<?, ?>) {
            List<String> parts = new ArrayList<>();
            for (Map.Entry<?, ?> entry : ((Map<?, ?>) value).entrySet()) parts.add(json(entry.getKey().toString()) + ":" + json(entry.getValue()));
            return "{" + String.join(",", parts) + "}";
        }
        if (value instanceof Iterable<?>) {
            List<String> parts = new ArrayList<>();
            for (Object item : (Iterable<?>) value) parts.add(json(item));
            return "[" + String.join(",", parts) + "]";
        }
        throw new IllegalArgumentException("cannot encode " + value.getClass());
    }

    public static void main(String[] args) throws Exception {
        if (List.of(args).contains("calibrate=true")) {
            int work = 1000;
            for (String arg : args) if (arg.startsWith("work=")) work = Integer.parseInt(arg.substring(5));
            if (work < 0) bad("work must be nonnegative");
            Map<String, Object> result = new LinkedHashMap<>();
            result.put("schema", "rwbench-calibrate-1");
            result.put("java", System.getProperty("java.runtime.version"));
            result.put("calibration", calibration(work));
            System.out.println("RESULT " + json(result));
            return;
        }
        RwBench bench = null;
        try {
            bench = new RwBench(args);
            Map<String, Object> result = bench.run();
            bench.db.close();
            bench = null;
            System.out.println("RESULT " + json(result));
        } finally {
            if (bench != null) bench.db.close();
        }
    }
}
