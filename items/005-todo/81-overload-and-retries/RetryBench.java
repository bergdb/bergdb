import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
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
 * bergdb 005-81, section 7: the retry diagnostic, an extension of 006-11's RwBench
 * (006-11, section 10). Item-local; it changes no production code.
 *
 * Example: RetryBench threads=2 workload=hot reads=8 work=3000 seconds=10 out=DIR
 * With longActionMs=N, worker 0 sleeps N ms inside its action after the reads: the history
 * case, where a long action outlives KeyModSet's history under the other workers' writes.
 *
 * The workload, the checks and the timing are RwBench's. Added: per request, the number of
 * attempts (the action's invocations, checked against getRunCount()), the time between
 * attempts seen from the action (from the end of one invocation to the start of the next:
 * the refused commit, the rerun reset and the sleep), each worker's longest gap between
 * completions, and a CSV row for every request that took more than one attempt. On a jar
 * made by make-probe.py, RwTransaction.retryProbe also gives each retry's requested sleep,
 * its measured Thread.sleep() and the refused Db.execute() call; on a stock jar the hook is
 * absent and the harness runs without it (variant "stock"). On a jar also patched by
 * make-probe-db.py (variant "probe2"), Db's hooks give each attempt's wait for Db.writeLock
 * and the reason of each refusal: a changed key or history exhaustion.
 */
public final class RetryBench {
    static final java.util.function.Consumer<long[]> HOOK = RetryBench::probeEvent;
    static final java.util.function.LongConsumer LOCK_HOOK = RetryBench::lockWaitEvent;
    static final java.util.function.IntConsumer REASON_HOOK = RetryBench::reasonEvent;
    static final boolean PROBE = installProbe();
    /** The Db probes of make-probe-db.py: the lock wait and the reason of each refusal. */
    static final boolean DB_PROBE = installDbProbe();

    static boolean installDbProbe() {
        try {
            Db.class.getField("lockWaitProbe").set(null, LOCK_HOOK);
            Db.class.getField("rerunReasonProbe").set(null, REASON_HOOK);
            return true;
        } catch (NoSuchFieldException e) {
            return false;
        } catch (IllegalAccessException e) {
            throw new AssertionError(e);
        }
    }

    static void lockWaitEvent(long ns) {
        Thread t = Thread.currentThread();
        if (t instanceof RetryBench.Worker) ((RetryBench.Worker) t).lockWaited(ns);
    }

    static void reasonEvent(int reason) {
        Thread t = Thread.currentThread();
        if (t instanceof RetryBench.Worker) ((RetryBench.Worker) t).refusedFor(reason);
    }

    static boolean installProbe() {
        try {
            RwTransaction.class.getField("retryProbe").set(null, HOOK);
            return true;
        } catch (NoSuchFieldException e) {
            return false;
        } catch (IllegalAccessException e) {
            throw new AssertionError(e);
        }
    }

    /** Called by the probe build on the retrying caller's own thread. */
    static void probeEvent(long[] event) {
        Thread t = Thread.currentThread();
        if (t instanceof RetryBench.Worker) ((RetryBench.Worker) t).retried(event);
    }

    static final long GUARD = 0x6a09e667f3bcc909L;
    static final ThreadMXBean THREAD = ManagementFactory.getThreadMXBean();
    static final com.sun.management.ThreadMXBean ALLOC =
            THREAD instanceof com.sun.management.ThreadMXBean
                    ? (com.sun.management.ThreadMXBean) THREAD : null;
    static volatile long calibrationSink;

    final Map<String, String> args = new LinkedHashMap<>();
    final int threads, keys, reads, work, startupBytes, longActionMs;
    final double seconds, warmupSeconds, hotFraction, drainSeconds;
    final long seed, cacheBytes;
    final String mode, workload, storage, variant, outDir;
    final boolean durable, diagnosticLoads;
    final Object gate = new Object();
    final String[] keyNames;
    final Db core;
    final Database db;
    final ProbeStream probe;

    RetryBench(String[] commandLine) throws Exception {
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
        variant = DB_PROBE ? "probe2" : PROBE ? "probe" : "stock";
        drainSeconds = decimal("drainSeconds", 180);
        longActionMs = integer("longActionMs", 0);
        outDir = value("out", "");
        durable = Boolean.parseBoolean(value("durable", "false"));
        diagnosticLoads = Boolean.parseBoolean(value("diagnosticLoads", "false"));
        if (!List.of("optimistic", "serial").contains(mode)) bad("unknown mode");
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
        final boolean record;
        long start, deadline, end;
        Phase(double duration, int ordinal) {
            this.duration = duration;
            this.record = ordinal == 1;
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
            long joinDeadline = deadline + (long) (drainSeconds * 1e9);
            for (Worker worker : workers) {
                long remaining = joinDeadline - System.nanoTime();
                if (remaining > 0) worker.join(Math.max(1, TimeUnit.NANOSECONDS.toMillis(remaining)));
                if (worker.isAlive()) throw new AssertionError("worker failed to drain within " + drainSeconds + " s: " + worker.getName());
                if (worker.error != null) throw new AssertionError("worker failed: " + worker.getName(), worker.error);
            }
            end = System.nanoTime();
            long[] gc1 = gc();
            long total = 0, active = 0, attempts = 0, cpu = 0, allocation = 0, maxAttempts = 0;
            long completedEnd = deadline;
            Hist latency = new Hist(), activeLatency = new Hist(), execution = new Hist();
            List<Long> perWorker = new ArrayList<>(), perWorkerActive = new ArrayList<>();
            List<Long> perWorkerRetried = new ArrayList<>(), perWorkerGapMs = new ArrayList<>();
            List<Long> perWorkerMaxLatencyMs = new ArrayList<>(), perWorkerSleptMs = new ArrayList<>();
            Hist firstTry = new Hist(), retried = new Hist();
            long[] attemptCounts = new long[64];
            long retriedRequests = 0, invocations = 0, gapNs = 0, requestedMs = 0, sleptNs = 0;
            long refusedNs = 0, probeRetries = 0, maxCompletionGap = 0, maxSleptNs = 0;
            long lockWaits = 0, lockWaitNs = 0, refusedLockWaitNs = 0, maxLockWaitNs = 0, conflicts = 0, histories = 0;
            for (Worker worker : workers) {
                firstTry.merge(worker.firstTry); retried.merge(worker.retriedLatency);
                for (int i = 0; i < 64; i++) attemptCounts[i] += worker.attemptCounts[i];
                retriedRequests += worker.retriedRequests; invocations += worker.invocations;
                gapNs += worker.gapNs; requestedMs += worker.requestedMs; sleptNs += worker.sleptNs;
                refusedNs += worker.refusedNs; probeRetries += worker.probeRetries;
                maxCompletionGap = Math.max(maxCompletionGap, worker.maxCompletionGap);
                maxSleptNs = Math.max(maxSleptNs, worker.maxSleptNs);
                lockWaits += worker.lockWaits; lockWaitNs += worker.lockWaitNs;
                refusedLockWaitNs += worker.refusedLockWaitNs; maxLockWaitNs = Math.max(maxLockWaitNs, worker.maxLockWaitNs);
                conflicts += worker.conflicts; histories += worker.histories;
                perWorkerRetried.add(worker.retriedRequests);
                perWorkerGapMs.add(worker.maxCompletionGap / 1000000);
                perWorkerMaxLatencyMs.add(worker.latency.max / 1000000);
                perWorkerSleptMs.add((PROBE ? worker.sleptNs : worker.gapNs) / 1000000);
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
            if (attempts != invocations) throw new AssertionError("attempts " + attempts + " != action invocations " + invocations);
            if (PROBE && probeRetries != attempts - total) throw new AssertionError("probe retries " + probeRetries + " != " + (attempts - total));
            if (DB_PROBE && conflicts + histories != attempts - total)
                throw new AssertionError("refusal reasons " + (conflicts + histories) + " != " + (attempts - total));
            if (DB_PROBE && lockWaits != attempts) throw new AssertionError("lock waits " + lockWaits + " != attempts " + attempts);
            out.put("probe_lock_waits", lockWaits);
            out.put("probe_lock_wait_ns", lockWaitNs);
            out.put("probe_lock_wait_ns_refused", refusedLockWaitNs);
            out.put("probe_max_lock_wait_ns", maxLockWaitNs);
            out.put("probe_refused_conflict", conflicts);
            out.put("probe_refused_history", histories);
            List<Long> attemptDistribution = new ArrayList<>();
            int top = 63;
            while (top > 1 && attemptCounts[top] == 0) top--;
            for (int i = 1; i <= top; i++) attemptDistribution.add(attemptCounts[i]);
            out.put("requests_by_attempts", attemptDistribution);
            out.put("retried_requests", retriedRequests);
            out.put("first_try_latency", firstTry.result());
            out.put("retried_latency", retried.result());
            out.put("between_attempts_ns", gapNs);
            out.put("probe_retries", probeRetries);
            out.put("probe_requested_sleep_ms", requestedMs);
            out.put("probe_slept_ns", sleptNs);
            out.put("probe_refused_execute_ns", refusedNs);
            out.put("probe_max_one_sleep_ns", maxSleptNs);
            out.put("max_completion_gap_ns", maxCompletionGap);
            out.put("between_attempts_share_of_worker_time", gapNs / (threads * (completedEnd - start) * 1.0));
            out.put("per_worker_retried_requests", perWorkerRetried);
            out.put("per_worker_max_completion_gap_ms", perWorkerGapMs);
            out.put("per_worker_max_latency_ms", perWorkerMaxLatencyMs);
            out.put("per_worker_sleep_ms", perWorkerSleptMs);
            if (record && !outDir.isEmpty()) {
                try (PrintWriter w = new PrintWriter(new File(outDir, "retried-requests.csv"), "UTF-8")) {
                    w.println("worker,begin_ms,latency_ms,attempts,between_attempts_ms,requested_sleep_ms,"
                            + "slept_ms,refused_execute_ms,max_one_sleep_ms,in_window,history_refusals");
                    for (Worker worker : workers)
                        for (long[] r : worker.rows)
                            w.printf(Locale.ROOT, "%d,%.3f,%.3f,%d,%.3f,%d,%.3f,%.3f,%.3f,%d,%d%n",
                                    r[0], (r[1] - start) / 1e6, r[2] / 1e6, r[3], r[4] / 1e6, r[5],
                                    r[6] / 1e6, r[7] / 1e6, r[8] / 1e6, r[9], r[10]);
                }
            }
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
        // bergdb 005-81: per request (req*) and per worker (the rest), on this thread only.
        final Hist firstTry = new Hist(), retriedLatency = new Hist();
        final long[] attemptCounts = new long[64];
        final List<long[]> rows = new ArrayList<>();
        int reqInvocations;
        long reqActionEnd, reqGapNs, reqRequestedMs, reqSleptNs, reqRefusedNs, reqProbeRetries, reqMaxSleptNs;
        long invocations, retriedRequests, gapNs, requestedMs, sleptNs, refusedNs, probeRetries;
        long maxSleptNs, maxCompletionGap;
        long lastLockWait, lockWaits, lockWaitNs, refusedLockWaitNs, maxLockWaitNs, conflicts, histories;
        long reqHistories;
        void lockWaited(long ns) {
            lastLockWait = ns; lockWaits++; lockWaitNs += ns; maxLockWaitNs = Math.max(maxLockWaitNs, ns);
        }
        void refusedFor(int reason) {
            refusedLockWaitNs += lastLockWait;
            if (reason == 2) { histories++; reqHistories++; } else conflicts++;
        }
        /** The probe build's event, {runCount, requestedMs, sleptNs, failedExecuteNs}. */
        void retried(long[] e) {
            if (e[0] != reqInvocations) throw new AssertionError("probe runCount " + e[0] + " != " + reqInvocations);
            reqProbeRetries++;
            reqRequestedMs += e[1];
            reqSleptNs += e[2];
            reqRefusedNs += e[3];
            reqMaxSleptNs = Math.max(reqMaxSleptNs, e[2]);
        }
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
            long now = System.nanoTime();
            if (reqInvocations > 0) reqGapNs += now - reqActionEnd;
            reqInvocations++;
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
            if (id == 0 && longActionMs > 0) {
                // The history case (005-81, section 5.1): worker 0's action lasts longActionMs
                // after its reads, while the other workers write.
                try { Thread.sleep(longActionMs); }
                catch (InterruptedException e) { throw new IllegalStateException(e); }
            }
            env.put(keyNames[picks[0]], payload(firstCount + 1, input, result));
            reqActionEnd = System.nanoTime();
        }
        public void run() {
            long cpu0 = 0, alloc0 = 0;
            try {
                connection = db.connection();
                phase.ready.countDown();
                phase.go.await();
                cpu0 = THREAD.isCurrentThreadCpuTimeSupported() ? THREAD.getCurrentThreadCpuTime() : 0;
                alloc0 = allocation();
                long previousEnd = phase.start;
                while (System.nanoTime() < phase.deadline) {
                    chooseKeys();
                    reqInvocations = 0; reqGapNs = 0; reqRequestedMs = 0; reqSleptNs = 0;
                    reqRefusedNs = 0; reqProbeRetries = 0; reqMaxSleptNs = 0; reqHistories = 0;
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
                    if (runs != reqInvocations) throw new AssertionError("getRunCount " + runs + " != invocations " + reqInvocations);
                    if (PROBE && reqProbeRetries != runs - 1) throw new AssertionError("probe retries " + reqProbeRetries + " != " + (runs - 1));
                    invocations += reqInvocations;
                    attemptCounts[(int) Math.min(63, runs)]++;
                    maxCompletionGap = Math.max(maxCompletionGap, end - previousEnd);
                    previousEnd = end;
                    gapNs += reqGapNs; requestedMs += reqRequestedMs; sleptNs += reqSleptNs;
                    refusedNs += reqRefusedNs; probeRetries += reqProbeRetries;
                    maxSleptNs = Math.max(maxSleptNs, reqMaxSleptNs);
                    if (runs == 1) firstTry.add(end - begin);
                    else {
                        retriedRequests++;
                        retriedLatency.add(end - begin);
                        if (phase.record) rows.add(new long[] {id, begin, end - begin, runs, reqGapNs, reqRequestedMs,
                                reqSleptNs, reqRefusedNs, reqMaxSleptNs, end <= phase.deadline ? 1 : 0, reqHistories});
                    }
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

    Map<String, Object> verify(long expected) { return verify(db, expected); }

    Map<String, Object> verify(Database database, long expected) {
        Connection connection = database.connection();
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
        out.put("schema", "retrybench-1"); out.put("variant", variant);
        out.put("threads", threads); out.put("mode", mode); out.put("workload", workload);
        out.put("keys", keys); out.put("reads", reads); out.put("work", work);
        out.put("seconds", seconds); out.put("warmup_seconds", warmupSeconds);
        out.put("hot_fraction", hotFraction); out.put("seed", seed);
        out.put("storage", storage); out.put("durable", durable); out.put("cache_bytes", cacheBytes);
        out.put("startup_bytes", startupBytes); out.put("drain_seconds_limit", drainSeconds);
        out.put("long_action_ms", longActionMs);
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
        System.err.printf(Locale.ROOT, "  retried %d of %d, attempts %s, max latency %.1f ms, max completion gap %.1f ms,"
                + " between attempts %.1f%% of worker time, worker sleep ms %s, worker max gap ms %s%n",
                measured.get("retried_requests"), measured.get("commits"), measured.get("requests_by_attempts"),
                ((Number) ((Map<?, ?>) measured.get("latency")).get("max_ns")).doubleValue() / 1e6,
                ((Number) measured.get("max_completion_gap_ns")).doubleValue() / 1e6,
                100 * ((Number) measured.get("between_attempts_share_of_worker_time")).doubleValue(),
                measured.get("per_worker_sleep_ms"), measured.get("per_worker_max_completion_gap_ms"));
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
        RetryBench bench = null;
        try {
            bench = new RetryBench(args);
            Map<String, Object> result = bench.run();
            bench.db.close();
            if (bench.storage.equals("file") && Boolean.parseBoolean(bench.value("reopen", "false"))) {
                // bergdb 005-81, section 5.4: the reopen subset; the same checks on the database
                // started again from its files after close().
                long expected = (Long) ((Map<?, ?>) result.get("verification")).get("expected_commits");
                long begin = System.nanoTime();
                DbBuilder builder = Db.builder().retainForever().testId();
                if (bench.startupBytes > 0) builder.startupDistance(bench.startupBytes);
                if (bench.cacheBytes == 0) builder.noEvict();
                else builder.cacheSizeIndicator(bench.cacheBytes);
                Db core = builder.mainStream(new FileStream(new File(bench.value("dir", "")))).build();
                Database reopened = DatabaseImp.createAndStart(core);
                try {
                    Map<String, Object> check = bench.verify(reopened, expected);
                    check.put("reopen_ms", (System.nanoTime() - begin) / 1e6);
                    result.put("reopen_verification", check);
                } finally {
                    reopened.close();
                }
            }
            bench = null;
            System.out.println("RESULT " + json(result));
        } finally {
            if (bench != null) bench.db.close();
        }
    }
}
