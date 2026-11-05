package bergdb.core;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.Locale;
import java.util.Random;
import java.util.SplittableRandom;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;

import bergdb.dag.GetData;
import bergdb.dag.Klong;
import bergdb.stream.FileStream;

/**
 * The cache's budget lowered while the database runs, for bergdb 005-52 (question 2, the
 * first step). By Claude (Opus 5.5, Claude Code), 2026-10-27. A tool of the entry, not part
 * of BergDB: it uses bergdb.jar as it is.
 *
 * One JVM: a load, as ScaleBench's (004-02): bb.keys key24 keys in random order, 1,000 puts
 * a transaction, 8-byte values, node size 30, infinite retention, the capacity controller
 * with budget bb.high. Then readers (bb.readers threads, uniform gets) and one writer
 * (bb.commits commits a second, bb.puts updates each) run through five phases:
 *
 *   warm      until the cache is full (a sweep, or the resident bytes at 90 percent of
 *             bb.high) or steady (less than 2 percent more in 10 s), at most bb.warmmax
 *             seconds; the load leaves the latest tree resident, about 16 bytes a key;
 *   base      bb.base seconds at bb.high;
 *   converge  Eviction.setBudget(low), low = bb.lowfrac times the resident bytes then,
 *             until the resident bytes are at most low (at most bb.convmax seconds);
 *   after     bb.after seconds at low;
 *   raise     setBudget(bb.high) again, bb.raise seconds.
 *
 * Every bb.sample ms a line of bb.out's CSV: the time since the budget was lowered, the
 * resident bytes, the budget, the eviction thread's CPU time (ThreadMXBean, thread
 * "bergdb-evictor"), the controller's sweeps, objects released, sweep time and longest
 * sweep (Eviction.figures, the writer's sweeps and the thread's), the gets and commits in the
 * interval and the longest of each. At the end, per phase: gets and commits a second, the
 * longest, and counts above 1, 2, 5, 10, 20, 50 and 100 ms; the 15 slowest gets and commits
 * of the run with their times; and "BUDGETBENCH OK".
 */
public class BudgetBench {
    static String prop(String name, String def) {
        return System.getProperty("bb." + name, def);
    }

    final File dir = new File(prop("dir", "bbdata"));
    final int keys = Integer.parseInt(prop("keys", "10000000"));
    final long high = Long.parseLong(prop("high", "665000000"));
    final double lowFrac = Double.parseDouble(prop("lowfrac", "0.2"));
    long low;           // lowFrac times the resident bytes at the drop
    final int readers = Integer.parseInt(prop("readers", "2"));
    final int commitsPerSec = Integer.parseInt(prop("commits", "200"));
    final int puts = Integer.parseInt(prop("puts", "10"));
    final double warmMaxSec = Double.parseDouble(prop("warmmax", "300"));
    final double baseSec = Double.parseDouble(prop("base", "60"));
    final double convMaxSec = Double.parseDouble(prop("convmax", "300"));
    final double afterSec = Double.parseDouble(prop("after", "60"));
    final double raiseSec = Double.parseDouble(prop("raise", "30"));
    final long sampleMs = Long.parseLong(prop("sample", "100"));
    final String out = prop("out", "budget.csv");

    static final byte[] PREFIX = "/scale/key/".getBytes();
    static final String[] PHASES = {"warm", "base", "converge", "after", "raise"};
    static final int N = PHASES.length;
    static final long[] LIMITS_MS = {1, 2, 5, 10, 20, 50, 100};

    Db db;
    volatile boolean running = true;
    volatile int phase = 0;
    volatile long dropNanos = 0;        // when the budget was lowered; 0 before

    final AtomicLong maxGet = new AtomicLong(), maxCommit = new AtomicLong();
    final LongAdder gets = new LongAdder(), commits = new LongAdder();
    final Phase[] getPhases = new Phase[N], commitPhases = new Phase[N];
    final Slowest slowGets = new Slowest(), slowCommits = new Slowest();

    /** A phase's counts for one kind of call. */
    static final class Phase {
        final LongAdder n = new LongAdder();
        final LongAdder[] over = new LongAdder[LIMITS_MS.length];
        final AtomicLong max = new AtomicLong();
        long startNanos, endNanos;

        Phase() {
            for (int i = 0; i < over.length; i++) over[i] = new LongAdder();
        }

        void add(long ns) {
            n.increment();
            if (ns > max.get()) max.accumulateAndGet(ns, Math::max);
            for (int i = 0; i < LIMITS_MS.length && ns > LIMITS_MS[i] * 1000000L; i++) {
                over[i].increment();
            }
        }
    }

    /** The 15 slowest calls: duration and end time (nanoTime). */
    static final class Slowest {
        final long[][] rows = new long[15][2];
        volatile long floor = 0;

        void offer(long ns, long end) {
            if (ns <= floor) return;
            synchronized (this) {
                int min = 0;
                for (int i = 1; i < rows.length; i++) if (rows[i][0] < rows[min][0]) min = i;
                if (ns > rows[min][0]) {
                    rows[min][0] = ns;
                    rows[min][1] = end;
                }
                long f = Long.MAX_VALUE;
                for (long[] r : rows) f = Math.min(f, r[0]);
                floor = f;
            }
        }
    }

    static void say(String s) {
        System.out.println(s);
        System.out.flush();
    }

    static void fillKey(int k, byte[] b) {
        long v = k;
        for (int i = 23; i >= PREFIX.length; i--) {
            b[i] = (byte) ('0' + v % 10);
            v /= 10;
        }
    }

    static byte[] newKey() {
        byte[] b = new byte[24];
        System.arraycopy(PREFIX, 0, b, 0, PREFIX.length);
        return b;
    }

    static void toSegments(byte[] key, long[] segs) {
        int offset = 0;
        for (int i = 0; i < segs.length; i++) {
            int length = Math.min(Klong.MAX_SIZE, key.length - offset);
            segs[i] = Klong.createCompareValue(key, offset, length);
            offset += Klong.MAX_SIZE;
        }
    }

    static byte[] value(int k, int version) {
        byte[] b = new byte[8];
        b[0] = (byte) (k >>> 24); b[1] = (byte) (k >>> 16); b[2] = (byte) (k >>> 8); b[3] = (byte) k;
        b[4] = (byte) (version >>> 24); b[5] = (byte) (version >>> 16);
        b[6] = (byte) (version >>> 8); b[7] = (byte) version;
        return b;
    }

    static void check(int k, byte[] v) {
        if (v == null || v.length != 8 || v[0] != (byte) (k >>> 24) || v[1] != (byte) (k >>> 16)
                || v[2] != (byte) (k >>> 8) || v[3] != (byte) k) {
            throw new AssertionError("wrong value for key " + k);
        }
    }

    long resident() {
        return db.internal().cache().residents().bytes();
    }

    void open() throws IOException {
        if (dir.exists()) throw new IllegalStateException(dir + " exists; the load needs a new directory");
        dir.mkdirs();
        DbBuilder b = Db.builder().stream("main", new FileStream(dir)).testId()
                .maxNodeSize30().cacheSizeIndicator(high)
                .evictionSchedule(Eviction.Schedule.BUDGET, 1);
        db = b.build();
        db.start();
    }

    void load() {
        int[] order = new int[keys];
        for (int i = 0; i < keys; i++) order[i] = i;
        Random rnd = new Random(1);
        for (int i = keys - 1; i > 0; i--) {
            int j = rnd.nextInt(i + 1);
            int x = order[i]; order[i] = order[j]; order[j] = x;
        }
        long t0 = System.nanoTime();
        long next = t0 + 10_000_000_000L;
        for (int i = 0; i < keys; i += 1000) {
            Trans.Builder tb = db.trans();
            int e = Math.min(keys, i + 1000);
            for (int j = i; j < e; j++) {
                byte[] key = newKey();
                fillKey(order[j], key);
                tb.put(key, value(order[j], 0));
            }
            db.execute(tb.build());
            if (System.nanoTime() > next) {
                next += 10_000_000_000L;
                say(String.format(Locale.ROOT, "  load: %d puts, resident %d MB", e, resident() / 1000000));
            }
        }
        double sec = (System.nanoTime() - t0) / 1e9;
        say(String.format(Locale.ROOT, "load done: %d keys in %.1f s, %.0f puts a second; resident %d MB, budget %d MB",
                keys, sec, keys / sec, resident() / 1000000, high / 1000000));
    }

    final class Reader extends Thread {
        final int id;

        Reader(int id) {
            super("bb-reader-" + id);
            this.id = id;
        }

        public void run() {
            SplittableRandom rnd = new SplittableRandom(100 + id);
            byte[] key = newKey();
            long[] segs = new long[(key.length + Klong.MAX_SIZE) / Klong.MAX_SIZE];
            GetData gd = db.newGetData();
            while (running) {
                int k = rnd.nextInt(keys);
                fillKey(k, key);
                toSegments(key, segs);
                long t0 = System.nanoTime();
                byte[] v = db.getOne(Long.MAX_VALUE, segs, gd);
                long t1 = System.nanoTime();
                check(k, v);
                record(t1 - t0, t1, maxGet, gets, getPhases, slowGets);
            }
        }
    }

    final class Writer extends Thread {
        Writer() {
            super("bb-writer");
        }

        public void run() {
            SplittableRandom rnd = new SplittableRandom(7);
            long period = 1_000_000_000L / commitsPerSec;
            long next = System.nanoTime();
            int version = 1;
            while (running) {
                Trans.Builder tb = db.trans();
                for (int i = 0; i < puts; i++) {
                    int k = rnd.nextInt(keys);
                    byte[] key = newKey();
                    fillKey(k, key);
                    tb.put(key, value(k, version));
                }
                version++;
                Trans t = tb.build();
                long t0 = System.nanoTime();
                db.execute(t);
                long t1 = System.nanoTime();
                record(t1 - t0, t1, maxCommit, commits, commitPhases, slowCommits);
                next += period;
                long wait = next - System.nanoTime();
                if (wait > 0) java.util.concurrent.locks.LockSupport.parkNanos(wait);
                else if (wait < -1_000_000_000L) next = System.nanoTime();  // behind: no burst
            }
        }
    }

    void record(long ns, long end, AtomicLong max, LongAdder count, Phase[] phases, Slowest slow) {
        count.increment();
        if (ns > max.get()) max.accumulateAndGet(ns, Math::max);
        int p = phase;
        if (p < N) phases[p].add(ns);
        slow.offer(ns, end);
    }

    long evictorId = -1;

    long evictorCpu(ThreadMXBean mx) {
        if (evictorId == -1) {
            for (Thread t : Thread.getAllStackTraces().keySet()) {
                if (t.getName().equals("bergdb-evictor")) evictorId = t.threadId();
            }
        }
        if (evictorId == -1) return 0;
        long c = mx.getThreadCpuTime(evictorId);
        return c < 0 ? 0 : c;
    }

    double rel(long nanos) {
        return dropNanos == 0 ? (nanos - getPhases[1].startNanos) / 1e9 - baseSec
                : (nanos - dropNanos) / 1e9;
    }

    void run() throws IOException, InterruptedException {
        say("BudgetBench: " + keys + " keys, budget " + high + " bytes, lowered to " + lowFrac
                + " of the resident bytes, " + readers
                + " readers, " + commitsPerSec + " commits a second of " + puts + " puts; dir " + dir
                + "; " + System.getProperty("java.vm.name") + " " + System.getProperty("java.version")
                + ", " + ManagementFactory.getRuntimeMXBean().getInputArguments());
        open();
        load();
        for (int i = 0; i < N; i++) {
            getPhases[i] = new Phase();
            commitPhases[i] = new Phase();
        }
        ThreadMXBean mx = ManagementFactory.getThreadMXBean();
        Eviction ev = db.internal().eviction();
        PrintWriter csv = new PrintWriter(new FileWriter(out));
        csv.println("phase,sec,residentBytes,budget,evictorCpuMs,sweeps,released,sweepMs,maxSweepMs,"
                + "gets,maxGetMs,commits,maxCommitMs");
        ArrayList<Thread> threads = new ArrayList<Thread>();
        for (int i = 0; i < readers; i++) threads.add(new Reader(i));
        threads.add(new Writer());
        long start = System.nanoTime();
        getPhases[0].startNanos = commitPhases[0].startNanos = start;
        for (Thread t : threads) t.start();
        getPhases[1].startNanos = start + (long) (warmMaxSec * 1e9);    // for rel() while warming
        long phaseEnd = start + (long) (warmMaxSec * 1e9);
        double reachedSec = -1;
        long cpuAtDrop = 0;
        long[] figAtDrop = null;
        String dropState = "";
        long warmMark = start, warmRes = resident();
        boolean steady = false;
        while (phase < N) {
            Thread.sleep(sampleMs);
            long now = System.nanoTime();
            long res = resident();
            long[] f = ev.figures();
            long cpu = evictorCpu(mx);
            csv.println(String.format(Locale.ROOT, "%s,%.2f,%d,%d,%.1f,%d,%d,%.1f,%.2f,%d,%.2f,%d,%.2f",
                    PHASES[phase], rel(now), res, ev.budget(), cpu / 1e6, f[0], f[1], f[2] / 1e6,
                    f[3] / 1e6, gets.sumThenReset(), maxGet.getAndSet(0) / 1e6,
                    commits.sumThenReset(), maxCommit.getAndSet(0) / 1e6));
            boolean next = false;
            if (phase == 0) {
                // Warm: until the cache is full (a sweep, or the resident bytes at 90 percent
                // of the budget) or steady (less than 2 percent more in 10 s), at most
                // bb.warmmax seconds.
                if (now - warmMark >= 10_000_000_000L) {
                    steady = res < 1.02 * warmRes;
                    warmMark = now;
                    warmRes = res;
                }
                next = f[0] > 0 || res >= 0.9 * high || steady || now >= phaseEnd;
                if (next) say(String.format(Locale.ROOT, "warm: %.1f s, resident %d MB, %d sweeps",
                        (now - start) / 1e9, res / 1000000, f[0]));
            } else if (phase == 2) {
                if (res <= low) {
                    reachedSec = rel(now);
                    next = true;
                } else if (now >= phaseEnd) {
                    next = true;
                }
            } else {
                next = now >= phaseEnd;
            }
            if (!next) continue;
            getPhases[phase].endNanos = commitPhases[phase].endNanos = now;
            if (phase == 2) {
                long[] f1 = ev.figures();
                say(String.format(Locale.ROOT, "converge: %s; %s after %.2f s; the eviction thread's CPU %.0f ms; "
                        + "%d sweeps, %d objects released, %.0f ms of sweeps (the longest of the run %.2f ms)",
                        dropState, reachedSec >= 0 ? "reached the budget" : "NOT reached the budget",
                        rel(now), (cpu - cpuAtDrop) / 1e6, f1[0] - figAtDrop[0], f1[1] - figAtDrop[1],
                        (f1[2] - figAtDrop[2]) / 1e6, f1[3] / 1e6));
            }
            phase++;
            if (phase == N) break;
            getPhases[phase].startNanos = commitPhases[phase].startNanos = now;
            if (phase == 1) {
                phaseEnd = now + (long) (baseSec * 1e9);
            } else if (phase == 2) {
                low = Math.max(1, (long) (lowFrac * res));
                cpuAtDrop = cpu;
                figAtDrop = f;
                dropState = String.format(Locale.ROOT, "resident %d MB at the drop, budget %d MB",
                        res / 1000000, low / 1000000);
                dropNanos = System.nanoTime();
                ev.setBudget(low);
                phaseEnd = now + (long) (convMaxSec * 1e9);
            } else if (phase == 3) {
                phaseEnd = now + (long) (afterSec * 1e9);
            } else if (phase == 4) {
                ev.setBudget(high);
                phaseEnd = now + (long) (raiseSec * 1e9);
            }
        }
        running = false;
        for (Thread t : threads) t.join();
        csv.close();
        say("resident at the end " + resident() / 1000000 + " MB; " + ev.summary());
        for (int k = 0; k < 2; k++) {
            Phase[] ps = k == 0 ? getPhases : commitPhases;
            String kind = k == 0 ? "gets" : "commits";
            for (int i = 0; i < N; i++) {
                Phase p = ps[i];
                double sec = (p.endNanos - p.startNanos) / 1e9;
                StringBuilder sb = new StringBuilder();
                for (int j = 0; j < LIMITS_MS.length; j++) {
                    sb.append(j == 0 ? "" : ", ").append(">").append(LIMITS_MS[j]).append(" ms ")
                            .append(p.over[j].sum());
                }
                say(String.format(Locale.ROOT, "%s, %s: %.1f s, %.0f a second, the longest %.2f ms; %s",
                        kind, PHASES[i], sec, sec > 0 ? p.n.sum() / sec : 0.0, p.max.get() / 1e6, sb));
            }
            Slowest s = k == 0 ? slowGets : slowCommits;
            long[][] rows = s.rows.clone();
            java.util.Arrays.sort(rows, (a, b) -> Long.compare(b[0], a[0]));
            StringBuilder sb = new StringBuilder("slowest " + kind + " (ms at s from the drop):");
            for (long[] r : rows) {
                if (r[0] > 0) sb.append(String.format(Locale.ROOT, " %.1f@%.2f", r[0] / 1e6, rel(r[1])));
            }
            say(sb.toString());
        }
        db.close();
        say(reachedSec >= 0 ? "BUDGETBENCH OK" : "BUDGETBENCH FAILED: the budget was not reached");
    }

    public static void main(String[] args) throws Exception {
        new BudgetBench().run();
    }
}
