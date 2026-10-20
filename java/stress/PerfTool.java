package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.regex.Pattern;

import bergdb.core.PerfUtil.GcLog;
import bergdb.core.PerfUtil.Json;

/**
 * The tool around the performance harness (Perf.java), written 2026-10-14. Run by
 * java/stress/performance.sh; it does not touch the database.
 *
 *   finish RUNDIR MODE            add what the GC log says to RUNDIR/MODE.result.json
 *   session OUT.json k=v ...      write a session description (dotted keys make nested objects)
 *   summary SESSION [--md]        one table per scenario: median, range, variation, sample count
 *   compare REF CAND [CAND2] [--thresholds FILE]
 *                                 compare sessions; refuses incompatible workloads and environments
 *   calibrate SESSION SESSION ... [--out FILE] [--freeze]
 *                                 propose alert thresholds from the repeatability of equal sessions
 *
 * A session is a directory: session.json and SCENARIO/runK/MODE.result.json. Exit codes:
 * 0 fine, 1 a performance alert (not yet a conclusion: repeat in a matched run), 2 usage,
 * 3 incompatible sessions, 4 a failed or missing run.
 */
public class PerfTool {

    // ---- Metric classes ----

    static final class Rule {
        final Pattern p;
        final String cls;
        final boolean higherIsBetter;
        final boolean primary;
        Rule(String regex, String cls, boolean higherIsBetter, boolean primary) {
            this.p = Pattern.compile(regex);
            this.cls = cls;
            this.higherIsBetter = higherIsBetter;
            this.primary = primary;
        }
    }

    /** The first matching rule classifies a metric. Primary metrics can raise alerts. */
    static final Rule[] RULES = {
        new Rule("^(get_latest|get_historical|get_longkey)\\.ops_per_s$", "warm_read_throughput", true, true),
        new Rule("^get_[a-z0-9_]*\\.ops_per_s$", "throughput", true, true),
        new Rule("^scan_[a-z_]*\\.(kvs|scans)_per_s$", "throughput", true, true),
        new Rule("^(mix\\.)?(commits|puts|gets)_per_s$|^mix\\.(commits|puts|gets)_per_s$|^user_mb_per_s$", "throughput", true, true),
        new Rule("^(prepare\\.)?commit\\.(append|durable)\\.(p50|mean)_us$|^mix\\.commit\\.(append|durable)\\.(p50|mean)_us$|^delay\\.(p50|mean)_us$", "latency_p50", false, true),
        new Rule("^[a-z0-9_.]*get\\.(p50|mean)_us$|^(first|second)_gets\\.(p50|mean)_us$|^mix\\.get\\.(p50|mean)_us$|^scan_[a-z_]*\\.(p50|mean)_us$", "latency_p50", false, true),
        new Rule("^[a-z0-9_.]*\\.(p95|p99)_us$", "latency_p99", false, true),
        new Rule("^[a-z0-9_.]*\\.p999_us$", "latency_p999", false, true),
        new Rule("^[a-z0-9_.]*\\.max_us$|^slowest_commit_ms$", "latency_max", false, true),
        new Rule("^startup\\.sec$|^restart\\.startup_sec$", "startup", false, true),
        new Rule("^(bytes_appended_per_user_byte|bytes_appended_per_put)$|^rec\\.[a-z_]*$", "size", false, true),
        new Rule("^(we|se|se_offered)$", "size", true, true),
        new Rule("^(heap\\.after_gc_mb_max|rss_mb_max|storage\\.disk_mb_max|kept_mb_max|kept_mb_mean|disk_over_kept_[a-z]*)$", "size", false, true),
        new Rule("^gclog\\.(pause|safepoint)\\.(total_ms)$", "gc", false, true),
        new Rule("^gclog\\.(pause|safepoint)\\.(max_ms)$", "latency_max", false, true),
        new Rule("^[a-z0-9_.]*\\.(count|window_cv)$", "info", false, false),
    };

    static Rule rule(String metric) {
        for (Rule r : RULES) if (r.p.matcher(metric).find()) return r;
        return null;
    }

    // ---- Main ----

    public static void main(String[] args) throws Exception {
        if (args.length == 0) usage();
        String cmd = args[0];
        if (cmd.equals("finish") && args.length == 3) finish(new File(args[1]), args[2]);
        else if (cmd.equals("session") && args.length >= 2) session(args);
        else if (cmd.equals("summary") && args.length >= 2) System.exit(summary(args));
        else if (cmd.equals("compare") && args.length >= 3) System.exit(compare(args));
        else if (cmd.equals("calibrate") && args.length >= 3) System.exit(calibrate(args));
        else if (cmd.equals("selftest")) System.exit(selftest());
        else usage();
    }

    /** Checks of the pieces the results depend on: histogram, JSON, GC log, statistics. */
    static int selftest() throws IOException {
        int bad = 0;
        // Histogram: percentiles within 1% of the exact ones, exact count, sum, min, max; merge.
        Random r = new Random(5);
        PerfUtil.Hist h = new PerfUtil.Hist(), h1 = new PerfUtil.Hist(), h2 = new PerfUtil.Hist();
        long[] v = new long[200000];
        for (int i = 0; i < v.length; i++) {
            v[i] = (long) (Math.exp(r.nextDouble() * 18) * (1 + r.nextInt(3)));      // 1 ns to seconds
            h.record(v[i]);
            (i % 2 == 0 ? h1 : h2).record(v[i]);
        }
        h1.add(h2);
        long[] sorted = v.clone();
        Arrays.sort(sorted);
        for (double p : new double[] {50, 90, 99, 99.9}) {
            long exact = sorted[(int) Math.ceil(p / 100 * sorted.length) - 1];
            long got = h.percentile(p), got2 = h1.percentile(p);
            if (got < exact || got > exact * 1.01 + 1 || got2 != got) {
                System.out.println("SELFTEST FAIL histogram p" + p + ": exact " + exact + ", got " + got + ", merged " + got2);
                bad++;
            }
        }
        if (h.count() != v.length || h.max() != sorted[sorted.length - 1] || h.min() != sorted[0]) {
            System.out.println("SELFTEST FAIL histogram count, min or max");
            bad++;
        }
        for (int i = 0; i < PerfUtil.Hist.SIZE; i++) {
            if (i > 0 && PerfUtil.Hist.upper(i) <= PerfUtil.Hist.upper(i - 1)) { System.out.println("SELFTEST FAIL bucket edges at " + i); bad++; break; }
            if (PerfUtil.Hist.index(PerfUtil.Hist.upper(i)) != i) { System.out.println("SELFTEST FAIL bucket index at " + i); bad++; break; }
        }
        if (PerfUtil.Hist.index(Long.MAX_VALUE) >= PerfUtil.Hist.SIZE) { System.out.println("SELFTEST FAIL index of Long.MAX_VALUE"); bad++; }
        // JSON round trip.
        Map<String, Object> m = new LinkedHashMap<String, Object>();
        m.put("a", 1L); m.put("b", 2.5); m.put("c", "x\"y\\z\n"); m.put("d", Arrays.<Object>asList(1L, 2L, "s")); m.put("e", null);
        Map<String, Object> inner = new LinkedHashMap<String, Object>();
        inner.put("t", Boolean.TRUE);
        m.put("f", inner);
        Map<String, Object> back = Json.parseObject(Json.write(m));
        if (!Json.writeCompact(back).equals(Json.writeCompact(m))) { System.out.println("SELFTEST FAIL json round trip: " + Json.writeCompact(back)); bad++; }
        // GC log lines of G1, ZGC and a safepoint.
        File f = File.createTempFile("gclog", ".txt");
        PerfUtil.writeFile(f, "[0.900s][info][gc,start    ] GC(0) Pause Young (Normal) (G1 Evacuation Pause)\n"
                + "[1.000s][info][gc          ] GC(0) Pause Young (Normal) (G1 Evacuation Pause) 125M->64M(2048M) 13.082ms\n"
                + "[2.000s][info][gc          ] GC(1) Pause Full (G1 Compaction Pause) 900M->300M(1024M) 250.5ms\n"
                + "[3.000s][info][gc,phases   ] GC(2) y: Pause Mark Start 0.012ms\n"
                + "[3.100s][info][gc          ] GC(2) Concurrent Mark Cycle 400.000ms\n"
                + "[1.000s][info][safepoint   ] Safepoint \"G1CollectForAllocation\", Time since last: 876713250 ns, Reaching safepoint: 3584 ns, At safepoint: 13225458 ns, Leaving safepoint: 7375 ns, Total: 13236417 ns, Threads: 0 runnable, 14 total\n");
        GcLog g = GcLog.read(f);
        f.delete();
        if (g.pauses.size() != 3 || g.fullGcs != 1 || g.safepoints.size() != 1 || g.concurrentCycles != 1
                || Math.abs(g.pauses.get(0).ms - 13.082) > 1e-9 || Math.abs(g.safepoints.get(0).ms - 13.229042) > 1e-6) {
            System.out.println("SELFTEST FAIL gc log: " + g.pauses.size() + " pauses, " + g.fullGcs + " full, " + g.safepoints.size()
                    + " safepoints, " + g.concurrentCycles + " concurrent");
            bad++;
        }
        // Statistics.
        double[] a = {1, 2, 3, 4, 100};
        if (median(a) != 3 || Math.abs(mean(a) - 22) > 1e-9 || Math.abs(cv(new double[] {2, 2, 2})) > 1e-12) { System.out.println("SELFTEST FAIL statistics"); bad++; }
        // Classification of the metric names the harness writes.
        String[][] expect = {{"get_latest.ops_per_s", "warm_read_throughput"}, {"get_latest_mt4.ops_per_s", "throughput"},
                {"scan_fwd.kvs_per_s", "throughput"}, {"commits_per_s", "throughput"}, {"commit.append.p50_us", "latency_p50"},
                {"commit.durable.p99_us", "latency_p99"}, {"delay.p999_us", "latency_p999"}, {"commit.append.max_us", "latency_max"},
                {"get_latest.get.p50_us", "latency_p50"}, {"scan_back.p50_us", "latency_p50"}, {"startup.sec", "startup"},
                {"we", "size"}, {"rec.user_bytes_per_put", "size"}, {"gclog.pause.total_ms", "gc"}, {"gclog.pause.max_ms", "latency_max"},
                {"mix.get.p99_us", "latency_p99"}, {"first_gets.mean_us", "latency_p50"}};
        for (String[] e : expect) {
            Rule rl = rule(e[0]);
            if (rl == null || !rl.cls.equals(e[1])) { System.out.println("SELFTEST FAIL classification of " + e[0] + ": " + (rl == null ? "none" : rl.cls) + ", wanted " + e[1]); bad++; }
        }
        System.out.println(bad == 0 ? "SELFTEST OK" : "SELFTEST FAILED: " + bad);
        return bad == 0 ? 0 : 1;
    }

    static void usage() {
        System.err.println("usage: PerfTool finish RUNDIR MODE | session OUT.json k=v... | summary SESSION [--md]\n"
                + "       | compare REF CAND [CAND2] [--thresholds FILE] | calibrate SESSION SESSION... [--out FILE] [--freeze]");
        System.exit(2);
    }

    // ---- finish ----

    @SuppressWarnings("unchecked")
    static void finish(File runDir, String mode) throws IOException {
        File rf = new File(runDir, mode + ".result.json");
        if (!rf.exists()) throw new IOException("no " + rf);
        Map<String, Object> r = Json.parseObject(PerfUtil.readFile(rf));
        Map<String, Object> metrics = (Map<String, Object>) r.get("metrics");
        List<Object> up = (List<Object>) r.get("uptimeMs");
        double from = up == null ? 0 : ((Number) up.get(0)).doubleValue() / 1000.0;
        double to = up == null ? 1e12 : ((Number) up.get(1)).doubleValue() / 1000.0;
        if (to <= from) to = 1e12;
        GcLog g = GcLog.read(new File(runDir, mode + ".gc.log"));
        Map<String, Object> window = g.summary(from, to);
        Map<String, Object> whole = g.summary(0, 1e12);
        Map<String, Object> gc = new LinkedHashMap<String, Object>();
        gc.put("measuredWindowSec", Arrays.<Object>asList(from, to));
        gc.put("measured", window);
        gc.put("wholeRun", whole);
        r.put("gcLog", gc);
        putGc(metrics, "gclog.pause", Json.map(window, "pauses"));
        putGc(metrics, "gclog.safepoint", Json.map(window, "safepoints"));
        metrics.put("gclog.full_gcs", window.get("fullGcs"));
        metrics.put("gclog.heap_after_gc_max_mb", window.get("heapAfterGcMaxMB"));

        // The slowest commits next to the GC pauses and safepoints that overlap them.
        File raw = new File(runDir, mode + ".raw.json");
        if (raw.exists()) {
            Map<String, Object> rm = Json.parseObject(PerfUtil.readFile(raw));
            Object slow = rm.get("slowest");
            if (slow instanceof List) {
                List<Object> out = new ArrayList<Object>();
                int c = 0;
                for (Object o : (List<Object>) slow) {
                    if (c++ >= 5) break;
                    Map<String, Object> s = new LinkedHashMap<String, Object>((Map<String, Object>) o);
                    double ms = ((Number) s.get("ms")).doubleValue();
                    double end = ((Number) s.get("uptimeMs")).doubleValue() / 1000.0;
                    s.put("overlap", overlap(g, end - ms / 1000.0, end));
                    out.add(s);
                }
                r.put("slowestCommits", out);
            }
        }
        PerfUtil.writeFile(rf, Json.write(r));
    }

    static void putGc(Map<String, Object> metrics, String prefix, Map<String, Object> m) {
        if (m == null) return;
        metrics.put(prefix + ".count", m.get("count"));
        metrics.put(prefix + ".total_ms", m.get("totalMs"));
        metrics.put(prefix + ".max_ms", m.get("maxMs"));
        metrics.put(prefix + ".p99_ms", m.get("p99Ms"));
    }

    static String overlap(GcLog g, double from, double to) {
        StringBuilder sb = new StringBuilder();
        for (GcLog.Event e : g.pauses) {
            if (e.uptimeSec >= from - 0.002 && e.uptimeSec - e.ms / 1000.0 <= to + 0.002) {
                sb.append(String.format(Locale.ROOT, "GC pause %s %.1f ms; ", e.what, e.ms));
            }
        }
        for (GcLog.Event e : g.safepoints) {
            if (e.ms < 1) continue;
            if (e.uptimeSec >= from - 0.002 && e.uptimeSec - e.ms / 1000.0 <= to + 0.002) {
                sb.append(String.format(Locale.ROOT, "safepoint %s %.1f ms; ", e.what, e.ms));
            }
        }
        return sb.length() == 0 ? "none" : sb.toString().trim();
    }

    // ---- session ----

    @SuppressWarnings("unchecked")
    static void session(String[] args) throws IOException {
        Map<String, Object> root = new LinkedHashMap<String, Object>();
        for (int i = 2; i < args.length; i++) {
            int eq = args[i].indexOf('=');
            if (eq < 0) throw new IllegalArgumentException("not key=value: " + args[i]);
            String[] path = args[i].substring(0, eq).split("\\.");
            Map<String, Object> m = root;
            for (int j = 0; j < path.length - 1; j++) {
                Object o = m.get(path[j]);
                if (!(o instanceof Map)) { o = new LinkedHashMap<String, Object>(); m.put(path[j], o); }
                m = (Map<String, Object>) o;
            }
            String v = args[i].substring(eq + 1);
            Object val = v;
            if (v.matches("-?\\d{1,15}")) val = Long.parseLong(v);
            else if (v.equals("true") || v.equals("false")) val = Boolean.valueOf(v);
            m.put(path[path.length - 1], val);
        }
        PerfUtil.writeFile(new File(args[1]), Json.write(root));
    }

    // ---- Sessions ----

    static final class Run {
        File dir;
        Map<String, Double> metrics = new LinkedHashMap<String, Double>();
        Map<String, Object> jvm, runInfo, firstResult;
        String workloadId, status = "ok", failure;
        List<Object> slowest;
        String mode;
    }

    static final class Scenario {
        String name, kind;
        List<Run> runs = new ArrayList<Run>();
        String workloadId;
    }

    static final class Session {
        File dir;
        Map<String, Object> info;
        Map<String, Scenario> scenarios = new TreeMap<String, Scenario>();
        String id() { return dir.getName(); }
    }

    @SuppressWarnings("unchecked")
    static Session load(File dir) throws IOException {
        Session s = new Session();
        s.dir = dir;
        File sj = new File(dir, "session.json");
        if (!sj.exists()) throw new IOException("not a session (no session.json): " + dir);
        s.info = Json.parseObject(PerfUtil.readFile(sj));
        File[] scs = dir.listFiles();
        Arrays.sort(scs);
        for (File sd : scs) {
            if (!sd.isDirectory()) continue;
            File[] runs = sd.listFiles();
            Arrays.sort(runs);
            Scenario sc = new Scenario();
            sc.name = sd.getName();
            for (File rd : runs) {
                if (!rd.isDirectory() || !rd.getName().startsWith("run")) continue;
                Run run = loadRun(rd);
                if (run == null) continue;
                sc.kind = run.mode;
                sc.workloadId = run.workloadId;
                sc.runs.add(run);
            }
            if (!sc.runs.isEmpty()) s.scenarios.put(sc.name, sc);
        }
        return s;
    }

    @SuppressWarnings("unchecked")
    static Run loadRun(File rd) throws IOException {
        File restart = new File(rd, "restart.result.json");
        File read = new File(rd, "read.result.json");
        File write = new File(rd, "write.result.json");
        File primary = restart.exists() ? restart : read.exists() ? read : write.exists() ? write : null;
        if (primary == null) return null;
        Run run = new Run();
        run.dir = rd;
        run.mode = primary.getName().replace(".result.json", "");
        Map<String, Object> r = Json.parseObject(PerfUtil.readFile(primary));
        run.status = String.valueOf(r.get("status"));
        run.workloadId = String.valueOf(r.get("workloadId"));
        run.jvm = (Map<String, Object>) r.get("jvm");
        run.runInfo = (Map<String, Object>) r.get("run");
        run.firstResult = r;
        addMetrics(run, (Map<String, Object>) r.get("metrics"), "");
        if (r.get("slowestCommits") instanceof List) run.slowest = (List<Object>) r.get("slowestCommits");
        if (primary == restart && write.exists()) {
            Map<String, Object> w = Json.parseObject(PerfUtil.readFile(write));
            addMetrics(run, (Map<String, Object>) w.get("metrics"), "prepare.");
            if (!"ok".equals(String.valueOf(w.get("status")))) run.status = "failed";
            run.workloadId += "+" + w.get("workloadId");
        }
        return run;
    }

    static void addMetrics(Run run, Map<String, Object> m, String prefix) {
        for (Map.Entry<String, Object> e : m.entrySet()) {
            if (e.getValue() instanceof Number) run.metrics.put(prefix + e.getKey(), ((Number) e.getValue()).doubleValue());
            else if (e.getKey().equals("failure")) run.failure = String.valueOf(e.getValue());
        }
    }

    // ---- Statistics ----

    static double[] values(List<Run> runs, String metric) {
        List<Double> l = new ArrayList<Double>();
        for (Run r : runs) {
            Double v = r.metrics.get(metric);
            if (v != null && !v.isNaN()) l.add(v);
        }
        double[] a = new double[l.size()];
        for (int i = 0; i < a.length; i++) a[i] = l.get(i);
        return a;
    }

    static double median(double[] a) {
        if (a.length == 0) return Double.NaN;
        double[] s = a.clone();
        Arrays.sort(s);
        return s.length % 2 == 1 ? s[s.length / 2] : (s[s.length / 2 - 1] + s[s.length / 2]) / 2;
    }

    static double mean(double[] a) {
        double s = 0;
        for (double x : a) s += x;
        return a.length == 0 ? Double.NaN : s / a.length;
    }

    static double cv(double[] a) {
        if (a.length < 2) return Double.NaN;
        double m = mean(a), s = 0;
        for (double x : a) s += (x - m) * (x - m);
        return m == 0 ? Double.NaN : Math.sqrt(s / (a.length - 1)) / Math.abs(m);
    }

    static double min(double[] a) { double m = Double.POSITIVE_INFINITY; for (double x : a) m = Math.min(m, x); return m; }
    static double max(double[] a) { double m = Double.NEGATIVE_INFINITY; for (double x : a) m = Math.max(m, x); return m; }

    static String fmt(double v) {
        if (Double.isNaN(v)) return "-";
        double a = Math.abs(v);
        if (a >= 1e6) return String.format(Locale.ROOT, "%,.0f", v);
        if (a >= 1000) return String.format(Locale.ROOT, "%,.1f", v);
        if (a >= 100) return String.format(Locale.ROOT, "%.1f", v);
        if (a >= 1) return String.format(Locale.ROOT, "%.3f", v);
        return String.format(Locale.ROOT, "%.4f", v);
    }

    static String pct(double v) {
        return Double.isNaN(v) ? "-" : String.format(Locale.ROOT, "%+.1f%%", 100 * v);
    }

    // ---- summary ----

    static int summary(String[] args) throws IOException {
        Session s = load(new File(args[1]));
        boolean md = Arrays.asList(args).contains("--md");
        System.out.println((md ? "### " : "") + "Session " + s.id() + "  (" + Json.str(Json.map(s.info, "source"), "commit")
                + (Boolean.TRUE.equals(Json.map(s.info, "source") == null ? null : Json.map(s.info, "source").get("dirty")) ? " + working-tree diff" : "")
                + ")");
        int failed = 0;
        for (Scenario sc : s.scenarios.values()) {
            System.out.println();
            System.out.println((md ? "#### " : "") + sc.name + "  [" + sc.kind + ", " + sc.runs.size() + " runs, workload " + sc.workloadId + "]");
            for (Run r : sc.runs) {
                if (!r.status.equals("ok")) { failed++; System.out.println("  FAILED run " + r.dir.getName() + ": " + r.failure); }
            }
            Set<String> names = new TreeSet<String>();
            for (Run r : sc.runs) names.addAll(r.metrics.keySet());
            if (md) {
                System.out.println("| metric | n | median | min | max | CV |");
                System.out.println("|---|---|---|---|---|---|");
            } else {
                System.out.println(String.format(Locale.ROOT, "  %-44s %3s %16s %16s %16s %7s", "metric", "n", "median", "min", "max", "CV"));
            }
            for (String name : names) {
                Rule rl = rule(name);
                if (rl == null || !rl.primary) continue;
                double[] v = values(sc.runs, name);
                String row = md
                        ? String.format(Locale.ROOT, "| %s | %d | %s | %s | %s | %s |", name, v.length, fmt(median(v)), fmt(min(v)), fmt(max(v)), Double.isNaN(cv(v)) ? "-" : String.format(Locale.ROOT, "%.1f%%", 100 * cv(v)))
                        : String.format(Locale.ROOT, "  %-44s %3d %16s %16s %16s %7s", name, v.length, fmt(median(v)), fmt(min(v)), fmt(max(v)), Double.isNaN(cv(v)) ? "-" : String.format(Locale.ROOT, "%.1f%%", 100 * cv(v)));
                System.out.println(row);
            }
            // The longest GC pauses of the first run's measured window.
            Run run0 = sc.runs.get(0);
            Map<String, Object> gcm = Json.map(Json.map(run0.firstResult, "gcLog"), "measured");
            Map<String, Object> pz = gcm == null ? null : Json.map(gcm, "pauses");
            if (pz != null && pz.get("longest") instanceof List && !((List<?>) pz.get("longest")).isEmpty()) {
                StringBuilder sb = new StringBuilder("  longest GC pauses of " + run0.dir.getName() + " (" + pz.get("count") + " in the window, total "
                        + fmt(((Number) pz.get("totalMs")).doubleValue()) + " ms):");
                for (Object o : (List<?>) pz.get("longest")) {
                    @SuppressWarnings("unchecked") Map<String, Object> e = (Map<String, Object>) o;
                    sb.append(String.format(Locale.ROOT, " %.1f ms (%s at uptime %.1f s);", ((Number) e.get("ms")).doubleValue(), e.get("what"), ((Number) e.get("uptimeSec")).doubleValue()));
                }
                System.out.println(sb);
            }
            // The worst commits of the first run: what coincided.
            Run first = sc.runs.get(0);
            if (first.slowest != null && !first.slowest.isEmpty()) {
                System.out.println("  slowest commits of " + first.dir.getName() + ":");
                for (Object o : first.slowest) {
                    @SuppressWarnings("unchecked") Map<String, Object> m = (Map<String, Object>) o;
                    System.out.println(String.format(Locale.ROOT, "    %.2f ms at %d ms into the phase, %s index nodes written; overlapping: %s",
                            ((Number) m.get("ms")).doubleValue(), ((Number) m.get("atMs")).longValue(), m.get("indexNodes"), m.get("overlap")));
                }
            }
        }
        return failed > 0 ? 4 : 0;
    }

    // ---- compare ----

    static final String[] JVM_KEYS = {"javaRuntimeVersion", "javaVmName", "javaVmVersion", "javaVendor", "osName", "osVersion",
            "osArch", "availableProcessors", "maxHeapBytes", "physicalMemoryBytes", "collector", "vmFlags"};

    /** The reasons why two sessions cannot be compared, empty if they can. */
    static List<String> incompatibilities(Session a, Session b, Scenario sa, Scenario sb) {
        List<String> why = new ArrayList<String>();
        if (!sa.kind.equals(sb.kind)) why.add("mode " + sa.kind + " vs " + sb.kind);
        if (!sa.workloadId.equals(sb.workloadId)) {
            why.add("workload ids differ: " + sa.workloadId + " vs " + sb.workloadId
                    + " (parameters or trace version changed; compare WORKLOAD lines in the result files)");
        }
        Run ra = sa.runs.get(0), rb = sb.runs.get(0);
        for (String k : JVM_KEYS) {
            Object x = ra.jvm == null ? null : ra.jvm.get(k), y = rb.jvm == null ? null : rb.jvm.get(k);
            if (!String.valueOf(x).equals(String.valueOf(y))) why.add("JVM " + k + ": " + x + " vs " + y);
        }
        if (!String.valueOf(ra.runInfo.get("oscache")).equals(String.valueOf(rb.runInfo.get("oscache")))) {
            why.add("OS file cache state: " + ra.runInfo.get("oscache") + " vs " + rb.runInfo.get("oscache"));
        }
        for (String k : new String[] {"machine.model", "machine.cpu", "machine.cores", "machine.memBytes", "machine.osBuild",
                "machine.fsType", "harness.sha256", "harness.traceVersion"}) {
            String x = nested(a.info, k), y = nested(b.info, k);
            if (!x.equals(y)) why.add("session " + k + ": " + x + " vs " + y);
        }
        return why;
    }

    @SuppressWarnings("unchecked")
    static String nested(Map<String, Object> m, String dotted) {
        Object o = m;
        for (String p : dotted.split("\\.")) {
            if (!(o instanceof Map)) return "?";
            o = ((Map<String, Object>) o).get(p);
        }
        return String.valueOf(o);
    }

    static final class Thresholds {
        Map<String, Double> rel = new HashMap<String, Double>();
        boolean frozen;
        String source = "none";
    }

    @SuppressWarnings("unchecked")
    static Thresholds loadThresholds(String path) throws IOException {
        Thresholds t = new Thresholds();
        // The provisional target of docs/level3-plan.md, task 3: investigate a consistent warm-read loss above 5%.
        t.rel.put("warm_read_throughput", 0.05);
        if (path == null) return t;
        File f = new File(path);
        if (!f.exists()) { t.source = path + " (missing)"; return t; }
        Map<String, Object> m = Json.parseObject(PerfUtil.readFile(f));
        t.frozen = Boolean.TRUE.equals(m.get("frozen"));
        t.source = path + (t.frozen ? " (frozen)" : " (proposal, not frozen)");
        Map<String, Object> cls = Json.map(m, "classes");
        if (cls != null) {
            for (Map.Entry<String, Object> e : cls.entrySet()) {
                Double v = Json.num((Map<String, Object>) e.getValue(), "relative");
                if (v != null) t.rel.put(e.getKey(), v);
            }
        }
        return t;
    }

    /** An alert for one metric: the candidate is worse than the reference by more than the threshold, in every run. */
    static final class Alert {
        String scenario, metric, cls;
        double refMedian, candMedian, change, threshold;
        int refN, candN;
        double refCv, candCv;
    }

    static Pattern only;
    static boolean showAll;

    static int compare(String[] args) throws IOException {
        only = null;
        showAll = false;
        List<String> dirs = new ArrayList<String>();
        String thr = null;
        for (int i = 1; i < args.length; i++) {
            if (args[i].equals("--thresholds")) thr = args[++i];
            else if (args[i].equals("--only")) only = Pattern.compile(args[++i]);
            else if (args[i].equals("--all")) showAll = true;
            else dirs.add(args[i]);
        }
        if (dirs.size() < 2 || dirs.size() > 3) usage();
        Session ref = load(new File(dirs.get(0)));
        List<Session> cands = new ArrayList<Session>();
        for (int i = 1; i < dirs.size(); i++) cands.add(load(new File(dirs.get(i))));
        Thresholds t = loadThresholds(thr);

        System.out.println("COMPARE reference " + ref.id() + " [" + describe(ref) + "]");
        for (Session c : cands) System.out.println("        candidate " + c.id() + " [" + describe(c) + "]");
        System.out.println("thresholds: " + t.source + ": " + new TreeMap<String, Double>(t.rel)
                + (t.frozen ? "" : "  (NOT FROZEN: only the provisional warm-read target raises alerts)"));
        int exit = 0;
        int compared = 0;
        List<List<Alert>> alertsPerCand = new ArrayList<List<Alert>>();
        for (Session c : cands) alertsPerCand.add(new ArrayList<Alert>());
        Set<String> names = new TreeSet<String>(ref.scenarios.keySet());
        for (Session c : cands) names.addAll(c.scenarios.keySet());
        for (String name : names) {
            if (only != null && !only.matcher(name).find()) continue;
            Scenario sr = ref.scenarios.get(name);
            System.out.println();
            if (sr == null) { System.out.println("SCENARIO " + name + ": only in a candidate"); exit = Math.max(exit, 4); continue; }
            for (int ci = 0; ci < cands.size(); ci++) {
                Session c = cands.get(ci);
                Scenario sc = c.scenarios.get(name);
                if (sc == null) { System.out.println("SCENARIO " + name + ": missing in " + c.id()); exit = Math.max(exit, 4); continue; }
                for (Run r : sc.runs) if (!r.status.equals("ok")) { System.out.println("SCENARIO " + name + ": FAILED run " + r.dir + ": " + r.failure); exit = Math.max(exit, 4); }
                List<String> why = incompatibilities(ref, c, sr, sc);
                if (!why.isEmpty()) {
                    System.out.println("SCENARIO " + name + " vs " + c.id() + ": INCOMPATIBLE, no comparison made");
                    for (String w : why) System.out.println("    - " + w);
                    exit = 3;
                    continue;
                }
                compared++;
                exit = Math.max(exit, compareScenario(name, sr, sc, c, t, alertsPerCand.get(ci)));
            }
        }
        System.out.println();
        int alerts = 0;
        for (int ci = 0; ci < cands.size(); ci++) alerts += alertsPerCand.get(ci).size();
        if (cands.size() == 2) {
            System.out.println("REPEATED MATCHED RUN: " + cands.get(0).id() + " and " + cands.get(1).id());
            for (Alert a : alertsPerCand.get(0)) {
                boolean again = false;
                for (Alert b : alertsPerCand.get(1)) if (b.scenario.equals(a.scenario) && b.metric.equals(a.metric)) again = true;
                System.out.println("  " + (again ? "CONFIRMED (alerts in both candidate sessions): " : "NOT REPEATED (second session does not alert): ") + a.scenario + " " + a.metric);
            }
            for (Alert b : alertsPerCand.get(1)) {
                boolean first = false;
                for (Alert a : alertsPerCand.get(0)) if (b.scenario.equals(a.scenario) && b.metric.equals(a.metric)) first = true;
                if (!first) System.out.println("  NOT REPEATED (only the second session alerts): " + b.scenario + " " + b.metric);
            }
        } else if (alerts > 0) {
            System.out.println(alerts + " ALERT(S), UNCONFIRMED. An alert is not a regression conclusion: repeat in a matched run "
                    + "(performance.sh ab ...) and compare with both candidate sessions.");
        }
        if (compared == 0) {
            System.out.println("NOTHING COMPARED: the sessions have no scenario in common that could be compared.");
            return Math.max(exit, 4);
        }
        if (exit == 0 && alerts > 0) exit = 1;
        if (alerts == 0 && exit == 0) System.out.println("NO ALERTS");
        return exit;
    }

    @SuppressWarnings("unchecked")
    static String describe(Session s) {
        Map<String, Object> src = Json.map(s.info, "source");
        if (src == null) return "no source info";
        String diff = String.valueOf(src.get("diffSha256")), jar = String.valueOf(src.get("jarSha256"));
        return src.get("commit") + (Boolean.TRUE.equals(src.get("dirty")) ? "+diff " + diff.substring(0, Math.min(8, diff.length())) : "")
                + ", build " + src.get("buildLabel") + ", jar " + jar.substring(0, Math.min(8, jar.length()));
    }

    static int compareScenario(String name, Scenario sr, Scenario sc, Session c, Thresholds t, List<Alert> alerts) {
        System.out.println("SCENARIO " + name + " [" + sr.kind + "] reference " + sr.runs.size() + " runs, candidate " + c.id() + " " + sc.runs.size() + " runs");
        System.out.println(String.format(Locale.ROOT, "  %-40s %14s %7s   %14s %7s %9s  %s", "metric", "ref median", "ref CV", "cand median", "cand CV", "change", "status"));
        Set<String> metrics = new TreeSet<String>(sr.runs.get(0).metrics.keySet());
        int hidden = 0;
        for (String m : metrics) {
            Rule rl = rule(m);
            if (rl == null || !rl.primary) continue;
            double[] rv = values(sr.runs, m), cvals = values(sc.runs, m);
            if (rv.length == 0 || cvals.length == 0) continue;
            double rm = median(rv), cm = median(cvals);
            double change = rm == 0 ? Double.NaN : (cm - rm) / Math.abs(rm);
            double bad = rl.higherIsBetter ? -change : change;           // positive: the candidate is worse
            Double th = t.rel.get(rl.cls);
            String status = "";
            boolean explain = rl.cls.equals("latency_max");
            if (th != null && !Double.isNaN(bad) && bad > th && !explain) {
                boolean consistent = rl.higherIsBetter ? max(cvals) < rm : min(cvals) > rm;
                if (cvals.length < 3 || rv.length < 3) status = "worse by more than " + pct(th).replace("+", "") + " but fewer than 3 runs: no conclusion";
                else if (!consistent) status = "median worse by more than " + pct(th).replace("+", "") + ", not in every run: noise?";
                else {
                    status = "ALERT (worse by more than " + pct(th).replace("+", "") + " in every candidate run; unconfirmed)";
                    Alert a = new Alert();
                    a.scenario = name; a.metric = m; a.cls = rl.cls; a.refMedian = rm; a.candMedian = cm; a.change = change;
                    a.threshold = th; a.refN = rv.length; a.candN = cvals.length; a.refCv = cv(rv); a.candCv = cv(cvals);
                    alerts.add(a);
                }
            } else if (explain && !Double.isNaN(bad) && bad > 0.5 && max(cvals) > 2 * median(rv)) {
                status = "EXPLAIN (maximum much larger than the reference's)";
            } else if (th == null && !Double.isNaN(bad) && bad > 0.05) {
                status = "(no threshold for " + rl.cls + ")";
            }
            // The headline metrics are always shown; the others only when something is to be said.
            boolean headline = rl.cls.equals("warm_read_throughput") || rl.cls.equals("throughput") || rl.cls.equals("startup");
            boolean said = !status.isEmpty() && !status.startsWith("(no threshold");
            if (showAll || headline || said) {
                System.out.println(String.format(Locale.ROOT, "  %-40s %14s %7s   %14s %7s %9s  %s", m, fmt(rm), cvs(rv), fmt(cm), cvs(cvals), pct(change), status));
            } else {
                hidden++;
            }
        }
        if (hidden > 0) System.out.println("  (" + hidden + " more metrics compared, nothing to report; --all shows them)");
        return 0;
    }

    static String cvs(double[] a) {
        double c = cv(a);
        return (Double.isNaN(c) ? "-" : String.format(Locale.ROOT, "%.1f%%", 100 * c)) + " n" + a.length;
    }

    // ---- calibrate ----

    static int calibrate(String[] args) throws IOException {
        List<Session> ss = new ArrayList<Session>();
        String out = null;
        boolean freeze = false;
        for (int i = 1; i < args.length; i++) {
            if (args[i].equals("--out")) out = args[++i];
            else if (args[i].equals("--freeze")) freeze = true;
            else ss.add(load(new File(args[i])));
        }
        if (ss.size() < 2) { System.err.println("calibrate needs at least two sessions of the same build"); return 2; }
        // For every scenario and primary metric: the medians of the sessions; the deviation between the sessions
        // is (max - min) / mean. Per class: the 90th percentile of the deviations and the median run-to-run CV.
        Map<String, List<Double>> dev = new TreeMap<String, List<Double>>(), cvs = new TreeMap<String, List<Double>>();
        Scenario base0 = null;
        for (String name : ss.get(0).scenarios.keySet()) {
            Scenario s0 = ss.get(0).scenarios.get(name);
            List<Scenario> all = new ArrayList<Scenario>();
            boolean all_ok = true;
            for (Session s : ss) {
                Scenario sx = s.scenarios.get(name);
                if (sx == null) { all_ok = false; break; }
                if (!sx.workloadId.equals(s0.workloadId)) { System.out.println("scenario " + name + ": workload differs between sessions, skipped"); all_ok = false; break; }
                all.add(sx);
            }
            if (!all_ok) continue;
            for (String m : s0.runs.get(0).metrics.keySet()) {
                Rule rl = rule(m);
                if (rl == null || !rl.primary || rl.cls.equals("info") || rl.cls.equals("latency_max")) continue;   // maxima do not alert
                double[] meds = new double[all.size()];
                for (int i = 0; i < meds.length; i++) {
                    meds[i] = median(values(all.get(i).runs, m));
                    double c = cv(values(all.get(i).runs, m));
                    if (!Double.isNaN(c)) add(cvs, rl.cls, c);
                }
                double mean = mean(meds);
                if (mean != 0 && !Double.isNaN(mean)) add(dev, rl.cls, (max(meds) - min(meds)) / Math.abs(mean));
            }
        }
        Map<String, Object> root = new LinkedHashMap<String, Object>();
        root.put("frozen", freeze);
        List<Object> from = new ArrayList<Object>();
        for (Session s : ss) from.add(s.id());
        root.put("sessions", from);
        root.put("rule", "relative threshold = max(2 x the 90th percentile of the deviation between the medians of equal sessions, "
                + "3 x the median run-to-run CV), rounded up to 0.5%; warm_read_throughput never below the plan's 5%");
        Map<String, Object> classes = new LinkedHashMap<String, Object>();
        for (String cls : dev.keySet()) {
            double p90 = percentile(dev.get(cls), 0.9);
            double mcv = cvs.containsKey(cls) ? percentile(cvs.get(cls), 0.5) : 0;
            double prop = Math.max(2 * p90, 3 * mcv);
            prop = Math.ceil(prop * 200) / 200;
            if (cls.equals("warm_read_throughput")) {
                if (prop > 0.05) System.out.println("WARNING: the repeatability of warm reads (" + pct(prop) + ") is worse than the 5% target: the target cannot be checked reliably");
                prop = Math.max(prop, 0.05);
            }
            Map<String, Object> c = new LinkedHashMap<String, Object>();
            c.put("relative", prop);
            c.put("metricsSampled", (long) dev.get(cls).size());
            c.put("p90SessionDeviation", p90);
            c.put("medianRunCv", mcv);
            classes.put(cls, c);
            System.out.println(String.format(Locale.ROOT, "%-24s threshold %5.1f%%   (p90 deviation between sessions %.2f%%, median run CV %.2f%%, %d metrics)",
                    cls, 100 * prop, 100 * p90, 100 * mcv, dev.get(cls).size()));
        }
        root.put("classes", classes);
        if (out != null) {
            PerfUtil.writeFile(new File(out), Json.write(root));
            System.out.println("wrote " + out + (freeze ? " (frozen)" : " (a proposal; freeze it with --freeze, in a commit, before Level 4 work)"));
        }
        return 0;
    }

    static void add(Map<String, List<Double>> m, String k, double v) {
        List<Double> l = m.get(k);
        if (l == null) { l = new ArrayList<Double>(); m.put(k, l); }
        l.add(v);
    }

    static double percentile(List<Double> l, double p) {
        if (l.isEmpty()) return 0;
        List<Double> s = new ArrayList<Double>(l);
        Collections.sort(s);
        int i = (int) Math.ceil(p * s.size()) - 1;
        return s.get(Math.max(0, Math.min(s.size() - 1, i)));
    }
}
