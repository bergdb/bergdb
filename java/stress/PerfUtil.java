package bergdb.core;

import java.io.*;
import java.lang.management.*;
import java.nio.charset.Charset;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Support for the performance harness (Perf.java, PerfTool.java), written 2026-10-14:
 * a bounded streaming histogram, a small JSON reader and writer, the GC log reader and
 * the description of the JVM and machine. Nothing here touches the database; the soak of
 * docs/level3-plan.md, task 2, can use the same classes.
 *
 * Compiled with --release 17 like the rest of java/stress/.
 */
public final class PerfUtil {
    private PerfUtil() {}

    static final Charset UTF8 = Charset.forName("UTF-8");

    // ---- Histogram ----

    /**
     * A bounded histogram of non-negative longs (nanoseconds). Values below 256 are exact;
     * above, a power of two is split into 128 buckets, so that a percentile is within 0.8%
     * of the true value (the upper edge of its bucket is reported, so never too low).
     * The count, sum, minimum and maximum are exact. Memory is fixed (7,296 longs) however
     * many values are recorded. Not thread safe: one per thread, merge afterwards.
     */
    public static final class Hist {
        static final int EXACT_BITS = 8;
        static final int EXACT = 1 << EXACT_BITS;                // 256
        static final int HALF = EXACT >>> 1;                     // 128 buckets per power of two
        static final int SIZE = EXACT + (63 - EXACT_BITS) * HALF;     // non-negative longs have at most 63 bits

        final long[] counts = new long[SIZE];
        long count, sum, min = Long.MAX_VALUE, max;

        static int index(long v) {
            if (v < EXACT) return (int) v;
            int bits = 64 - Long.numberOfLeadingZeros(v);        // >= 9
            int shift = bits - EXACT_BITS;
            int top = (int) (v >>> shift);                       // HALF .. EXACT-1
            return EXACT + (shift - 1) * HALF + (top - HALF);
        }

        /** The largest value that falls in bucket 'idx'. */
        static long upper(int idx) {
            if (idx < EXACT) return idx;
            int k = idx - EXACT;
            int shift = k / HALF + 1;
            long top = HALF + k % HALF;
            return ((top + 1) << shift) - 1;
        }

        public void record(long v) {
            if (v < 0) v = 0;
            counts[index(v)]++;
            count++;
            sum += v;
            if (v < min) min = v;
            if (v > max) max = v;
        }

        public void add(Hist o) {
            for (int i = 0; i < SIZE; i++) counts[i] += o.counts[i];
            count += o.count;
            sum += o.sum;
            if (o.min < min) min = o.min;
            if (o.max > max) max = o.max;
        }

        public long count() { return count; }
        public long max() { return count == 0 ? 0 : max; }
        public long min() { return count == 0 ? 0 : min; }
        public double mean() { return count == 0 ? 0 : (double) sum / count; }

        /** The value at percentile p (0 to 100), at most the maximum. */
        public long percentile(double p) {
            if (count == 0) return 0;
            long rank = Math.max(1, (long) Math.ceil(p / 100.0 * count));
            long seen = 0;
            for (int i = 0; i < SIZE; i++) {
                seen += counts[i];
                if (seen >= rank) return Math.min(upper(i), max);
            }
            return max;
        }

        /** Count, mean, p50, p95, p99, p99.9 and maximum, in the unit of the recorded values. */
        public Map<String, Object> summary() {
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            m.put("count", count);
            m.put("mean", mean());
            m.put("p50", percentile(50));
            m.put("p95", percentile(95));
            m.put("p99", percentile(99));
            m.put("p999", percentile(99.9));
            m.put("max", max());
            return m;
        }

        /** The non-empty buckets as [upper edge, count] pairs, for the raw record. */
        public List<Object> sparse() {
            List<Object> l = new ArrayList<Object>();
            for (int i = 0; i < SIZE; i++) {
                if (counts[i] != 0) l.add(Arrays.<Object>asList(upper(i), counts[i]));
            }
            return l;
        }
    }

    // ---- JSON ----

    /**
     * JSON writing and reading for plain data: Map (insertion order kept), List, String,
     * Long, Double, Boolean and null. NaN and infinities are written as null.
     */
    public static final class Json {
        private Json() {}

        public static String write(Object o) {
            StringBuilder sb = new StringBuilder();
            write(sb, o, 0);
            sb.append('\n');
            return sb.toString();
        }

        /** One line, no indentation. */
        public static String writeCompact(Object o) {
            StringBuilder sb = new StringBuilder();
            write(sb, o, -1);
            return sb.toString();
        }

        private static void indent(StringBuilder sb, int level) {
            sb.append('\n');
            for (int i = 0; i < level; i++) sb.append("  ");
        }

        private static boolean simple(Collection<?> c) {
            if (c.size() > 24) return false;
            for (Object x : c) {
                if (x instanceof Map || x instanceof List) return false;
            }
            return true;
        }

        @SuppressWarnings("unchecked")
        private static void write(StringBuilder sb, Object o, int level) {
            if (o == null) {
                sb.append("null");
            } else if (o instanceof String) {
                string(sb, (String) o);
            } else if (o instanceof Boolean) {
                sb.append(o.toString());
            } else if (o instanceof Double || o instanceof Float) {
                double d = ((Number) o).doubleValue();
                if (Double.isNaN(d) || Double.isInfinite(d)) sb.append("null");
                else if (d == Math.rint(d) && Math.abs(d) < 1e15) sb.append((long) d);
                else sb.append(String.format(Locale.ROOT, "%.6g", d));
            } else if (o instanceof Number) {
                sb.append(((Number) o).longValue());
            } else if (o instanceof Map) {
                Map<String, Object> m = (Map<String, Object>) o;
                if (m.isEmpty()) { sb.append("{}"); return; }
                sb.append('{');
                boolean first = true;
                for (Map.Entry<String, Object> e : m.entrySet()) {
                    if (!first) sb.append(',');
                    first = false;
                    if (level >= 0) indent(sb, level + 1);
                    string(sb, e.getKey());
                    sb.append(level >= 0 ? ": " : ":");
                    write(sb, e.getValue(), level < 0 ? -1 : level + 1);
                }
                if (level >= 0) indent(sb, level);
                sb.append('}');
            } else if (o instanceof List) {
                List<Object> l = (List<Object>) o;
                if (l.isEmpty()) { sb.append("[]"); return; }
                boolean flat = level < 0 || simple(l);
                sb.append('[');
                boolean first = true;
                for (Object x : l) {
                    if (!first) sb.append(flat ? "," : ",");
                    first = false;
                    if (!flat) indent(sb, level + 1);
                    write(sb, x, flat ? -1 : level + 1);
                }
                if (!flat) indent(sb, level);
                sb.append(']');
            } else if (o instanceof long[]) {
                List<Object> l = new ArrayList<Object>();
                for (long x : (long[]) o) l.add(x);
                write(sb, l, -1);
            } else if (o instanceof double[]) {
                List<Object> l = new ArrayList<Object>();
                for (double x : (double[]) o) l.add(x);
                write(sb, l, -1);
            } else {
                throw new IllegalArgumentException("cannot write " + o.getClass());
            }
        }

        private static void string(StringBuilder sb, String s) {
            sb.append('"');
            for (int i = 0; i < s.length(); i++) {
                char c = s.charAt(i);
                switch (c) {
                case '"': sb.append("\\\""); break;
                case '\\': sb.append("\\\\"); break;
                case '\n': sb.append("\\n"); break;
                case '\r': sb.append("\\r"); break;
                case '\t': sb.append("\\t"); break;
                default:
                    if (c < 0x20) sb.append(String.format("\\u%04x", (int) c));
                    else sb.append(c);
                }
            }
            sb.append('"');
        }

        public static Object parse(String s) {
            int[] pos = {0};
            Object o = value(s, pos);
            skip(s, pos);
            if (pos[0] != s.length()) throw new IllegalArgumentException("JSON: trailing text at " + pos[0]);
            return o;
        }

        @SuppressWarnings("unchecked")
        public static Map<String, Object> parseObject(String s) {
            return (Map<String, Object>) parse(s);
        }

        private static void skip(String s, int[] p) {
            while (p[0] < s.length() && Character.isWhitespace(s.charAt(p[0]))) p[0]++;
        }

        private static Object value(String s, int[] p) {
            skip(s, p);
            if (p[0] >= s.length()) throw new IllegalArgumentException("JSON: unexpected end");
            char c = s.charAt(p[0]);
            if (c == '{') {
                p[0]++;
                Map<String, Object> m = new LinkedHashMap<String, Object>();
                skip(s, p);
                if (s.charAt(p[0]) == '}') { p[0]++; return m; }
                while (true) {
                    skip(s, p);
                    String k = str(s, p);
                    skip(s, p);
                    expect(s, p, ':');
                    m.put(k, value(s, p));
                    skip(s, p);
                    if (s.charAt(p[0]) == ',') { p[0]++; continue; }
                    expect(s, p, '}');
                    return m;
                }
            } else if (c == '[') {
                p[0]++;
                List<Object> l = new ArrayList<Object>();
                skip(s, p);
                if (s.charAt(p[0]) == ']') { p[0]++; return l; }
                while (true) {
                    l.add(value(s, p));
                    skip(s, p);
                    if (s.charAt(p[0]) == ',') { p[0]++; continue; }
                    expect(s, p, ']');
                    return l;
                }
            } else if (c == '"') {
                return str(s, p);
            } else if (s.startsWith("true", p[0])) {
                p[0] += 4; return Boolean.TRUE;
            } else if (s.startsWith("false", p[0])) {
                p[0] += 5; return Boolean.FALSE;
            } else if (s.startsWith("null", p[0])) {
                p[0] += 4; return null;
            } else {
                int st = p[0];
                while (p[0] < s.length() && "+-0123456789.eE".indexOf(s.charAt(p[0])) >= 0) p[0]++;
                String num = s.substring(st, p[0]);
                if (num.isEmpty()) throw new IllegalArgumentException("JSON: bad value at " + st);
                if (num.indexOf('.') < 0 && num.indexOf('e') < 0 && num.indexOf('E') < 0) {
                    try { return Long.parseLong(num); } catch (NumberFormatException e) { /* fall through */ }
                }
                return Double.parseDouble(num);
            }
        }

        private static void expect(String s, int[] p, char c) {
            if (p[0] >= s.length() || s.charAt(p[0]) != c) {
                throw new IllegalArgumentException("JSON: expected '" + c + "' at " + p[0]);
            }
            p[0]++;
        }

        private static String str(String s, int[] p) {
            expect(s, p, '"');
            StringBuilder sb = new StringBuilder();
            while (true) {
                char c = s.charAt(p[0]++);
                if (c == '"') return sb.toString();
                if (c == '\\') {
                    char d = s.charAt(p[0]++);
                    switch (d) {
                    case 'n': sb.append('\n'); break;
                    case 'r': sb.append('\r'); break;
                    case 't': sb.append('\t'); break;
                    case 'b': sb.append('\b'); break;
                    case 'f': sb.append('\f'); break;
                    case 'u': sb.append((char) Integer.parseInt(s.substring(p[0], p[0] + 4), 16)); p[0] += 4; break;
                    default: sb.append(d);
                    }
                } else {
                    sb.append(c);
                }
            }
        }

        // Access helpers for the nested maps of the records.

        @SuppressWarnings("unchecked")
        public static Map<String, Object> map(Object o, String key) {
            Object v = ((Map<String, Object>) o).get(key);
            return v instanceof Map ? (Map<String, Object>) v : null;
        }

        public static Double num(Map<String, Object> m, String key) {
            if (m == null) return null;
            Object v = m.get(key);
            return v instanceof Number ? ((Number) v).doubleValue() : null;
        }

        public static String str(Map<String, Object> m, String key) {
            if (m == null) return null;
            Object v = m.get(key);
            return v == null ? null : v.toString();
        }
    }

    public static String readFile(File f) throws IOException {
        InputStream in = new FileInputStream(f);
        try {
            ByteArrayOutputStream out = new ByteArrayOutputStream();
            byte[] buf = new byte[1 << 16];
            int n;
            while ((n = in.read(buf)) > 0) out.write(buf, 0, n);
            return new String(out.toByteArray(), UTF8);
        } finally {
            in.close();
        }
    }

    public static void writeFile(File f, String s) throws IOException {
        File parent = f.getAbsoluteFile().getParentFile();
        if (parent != null) parent.mkdirs();
        OutputStream out = new FileOutputStream(f);
        try {
            out.write(s.getBytes(UTF8));
        } finally {
            out.close();
        }
    }

    public static String sha256(String s) {
        try {
            java.security.MessageDigest md = java.security.MessageDigest.getInstance("SHA-256");
            byte[] d = md.digest(s.getBytes(UTF8));
            StringBuilder sb = new StringBuilder();
            for (byte b : d) sb.append(String.format("%02x", b & 0xff));
            return sb.toString();
        } catch (java.security.NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
    }

    // ---- GC log ----

    /**
     * The pauses of a JVM run, read from its unified-logging file. The JVM is started with
     * -Xlog:gc*,safepoint:file=...:uptime,level,tags (performance.sh). A pause is a line
     * "Pause ..." of tag [gc] (G1, Parallel, Serial) or a "Pause Mark Start" etc. line of
     * [gc,phases] (ZGC); concurrent work is not a pause. A safepoint is any stop of the Java
     * threads, also those that are not collections, with the time to reach it and the time at it.
     */
    public static final class GcLog {
        public static final class Event {
            public final double uptimeSec;
            public final String what;
            public final double ms;
            Event(double uptimeSec, String what, double ms) {
                this.uptimeSec = uptimeSec; this.what = what; this.ms = ms;
            }
        }

        public final List<Event> pauses = new ArrayList<Event>();
        public final List<Event> safepoints = new ArrayList<Event>();      // ms = reach + at
        public final List<double[]> heapAfter = new ArrayList<double[]>(); // {uptime, MB after, MB total}
        public int fullGcs;
        public int concurrentCycles;

        private static final Pattern UP = Pattern.compile("^\\[(\\d+\\.\\d+)s\\]\\[(\\w+)\\]\\[([\\w,]+)\\s*\\]\\s*(.*)$");
        private static final Pattern PAUSE_MS = Pattern.compile("(?:GC\\(\\d+\\)\\s+)?(Pause .*?)\\s+(\\d+\\.\\d+)ms$");
        private static final Pattern ZPAUSE = Pattern.compile("(?:GC\\(\\d+\\)\\s+)?(?:[yYoO]: )?(Pause (?:Mark Start|Mark End|Relocate Start))\\s+(\\d+\\.\\d+)ms");
        private static final Pattern HEAP = Pattern.compile("(\\d+)([KMG])->(\\d+)([KMG])\\((\\d+)([KMG])\\)");
        private static final Pattern SAFEPOINT = Pattern.compile("Safepoint \"([^\"]+)\".*Reaching safepoint: (\\d+) ns.*At safepoint: (\\d+) ns");
        private static final Pattern CONC = Pattern.compile("Concurrent (?:Mark )?Cycle|Concurrent Undo Cycle");

        static double mb(String n, String u) {
            double v = Double.parseDouble(n);
            return u.equals("K") ? v / 1024 : u.equals("G") ? v * 1024 : v;
        }

        public static GcLog read(File f) throws IOException {
            GcLog g = new GcLog();
            if (!f.exists()) return g;
            BufferedReader r = new BufferedReader(new InputStreamReader(new FileInputStream(f), UTF8));
            try {
                String line;
                while ((line = r.readLine()) != null) {
                    Matcher m = UP.matcher(line);
                    if (!m.matches()) continue;
                    double up = Double.parseDouble(m.group(1));
                    String tags = m.group(3).trim();
                    String msg = m.group(4);
                    if (tags.equals("gc")) {
                        Matcher p = PAUSE_MS.matcher(msg);
                        if (p.find()) {
                            String what = p.group(1).replaceAll("\\s*\\d+[KMG]->.*$", "");
                            g.pauses.add(new Event(up, what, Double.parseDouble(p.group(2))));
                            if (what.startsWith("Pause Full")) g.fullGcs++;
                            Matcher h = HEAP.matcher(msg);
                            if (h.find()) {
                                g.heapAfter.add(new double[] {up, mb(h.group(3), h.group(4)), mb(h.group(5), h.group(6))});
                            }
                        } else if (CONC.matcher(msg).find()) {
                            g.concurrentCycles++;
                        }
                    } else if (tags.equals("gc,phases")) {
                        Matcher z = ZPAUSE.matcher(msg);
                        if (z.find()) g.pauses.add(new Event(up, z.group(1), Double.parseDouble(z.group(2))));
                    } else if (tags.equals("safepoint")) {
                        Matcher s = SAFEPOINT.matcher(msg);
                        if (s.find()) {
                            double ms = (Double.parseDouble(s.group(2)) + Double.parseDouble(s.group(3))) / 1e6;
                            g.safepoints.add(new Event(up, s.group(1), ms));
                        }
                    }
                }
            } finally {
                r.close();
            }
            return g;
        }

        /** Counts, total, distribution and the longest events of 'events' within [from, to] (uptime, s). */
        public static Map<String, Object> summarize(List<Event> events, double from, double to) {
            Hist h = new Hist();
            double total = 0;
            List<Event> in = new ArrayList<Event>();
            for (Event e : events) {
                if (e.uptimeSec < from || e.uptimeSec > to) continue;
                in.add(e);
                total += e.ms;
                h.record(Math.round(e.ms * 1000));            // microseconds
            }
            Collections.sort(in, new Comparator<Event>() {
                public int compare(Event a, Event b) { return Double.compare(b.ms, a.ms); }
            });
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            m.put("count", (long) in.size());
            m.put("totalMs", total);
            m.put("maxMs", in.isEmpty() ? 0.0 : in.get(0).ms);
            m.put("p50Ms", h.percentile(50) / 1000.0);
            m.put("p99Ms", h.percentile(99) / 1000.0);
            m.put("p999Ms", h.percentile(99.9) / 1000.0);
            List<Object> top = new ArrayList<Object>();
            for (int i = 0; i < Math.min(5, in.size()); i++) {
                Map<String, Object> e = new LinkedHashMap<String, Object>();
                e.put("uptimeSec", in.get(i).uptimeSec);
                e.put("what", in.get(i).what);
                e.put("ms", in.get(i).ms);
                top.add(e);
            }
            m.put("longest", top);
            return m;
        }

        public Map<String, Object> summary(double from, double to) {
            Map<String, Object> m = new LinkedHashMap<String, Object>();
            m.put("pauses", summarize(pauses, from, to));
            m.put("safepoints", summarize(safepoints, from, to));
            double maxAfter = 0, maxTotal = 0;
            for (double[] h : heapAfter) {
                if (h[0] < from || h[0] > to) continue;
                maxAfter = Math.max(maxAfter, h[1]);
                maxTotal = Math.max(maxTotal, h[2]);
            }
            m.put("heapAfterGcMaxMB", maxAfter);
            m.put("heapCommittedMaxMB", maxTotal);
            m.put("fullGcs", (long) fullGcs);
            m.put("concurrentCycles", (long) concurrentCycles);
            return m;
        }
    }

    // ---- JVM and machine ----

    /** The JVM as the program sees it. The machine and the source are described by performance.sh. */
    public static Map<String, Object> jvmInfo() {
        Map<String, Object> m = new LinkedHashMap<String, Object>();
        m.put("javaRuntimeVersion", System.getProperty("java.runtime.version"));
        m.put("javaVmName", System.getProperty("java.vm.name"));
        m.put("javaVmVersion", System.getProperty("java.vm.version"));
        m.put("javaVendor", System.getProperty("java.vendor"));
        m.put("osName", System.getProperty("os.name"));
        m.put("osVersion", System.getProperty("os.version"));
        m.put("osArch", System.getProperty("os.arch"));
        m.put("availableProcessors", (long) Runtime.getRuntime().availableProcessors());
        m.put("maxHeapBytes", Runtime.getRuntime().maxMemory());
        m.put("physicalMemoryBytes", physicalMemory());
        m.put("collector", collector());
        List<String> gcBeans = new ArrayList<String>();
        for (GarbageCollectorMXBean b : ManagementFactory.getGarbageCollectorMXBeans()) gcBeans.add(b.getName());
        m.put("gcBeans", gcBeans);
        m.put("vmFlags", vmFlags());
        m.put("pid", pid());
        return m;
    }

    /** The JVM arguments with the run-specific parts (log file paths, -Dperf.*) removed. */
    public static List<Object> vmFlags() {
        List<Object> l = new ArrayList<Object>();
        for (String a : ManagementFactory.getRuntimeMXBean().getInputArguments()) {
            if (a.startsWith("-Dperf.")) continue;
            if (a.startsWith("-Xlog:")) {
                a = a.replaceAll("file=[^:]*", "file=<run>");
            }
            if (a.startsWith("-javaagent") || a.startsWith("-agentlib")) {
                // Kept: an agent changes the measurement.
            }
            l.add(a);
        }
        return l;
    }

    public static String collector() {
        StringBuilder sb = new StringBuilder();
        for (GarbageCollectorMXBean b : ManagementFactory.getGarbageCollectorMXBeans()) {
            String n = b.getName();
            String c = n.startsWith("G1") ? "G1" : n.startsWith("ZGC") ? "ZGC"
                    : n.startsWith("PS ") ? "Parallel" : n.equals("Copy") || n.equals("MarkSweepCompact") ? "Serial"
                    : n.startsWith("Shenandoah") ? "Shenandoah" : n;
            if (sb.indexOf(c) < 0) {
                if (sb.length() > 0) sb.append('+');
                sb.append(c);
            }
        }
        return sb.toString();
    }

    public static long physicalMemory() {
        try {
            Object os = ManagementFactory.getOperatingSystemMXBean();
            for (String name : new String[] {"getTotalMemorySize", "getTotalPhysicalMemorySize"}) {
                try {
                    java.lang.reflect.Method m = os.getClass().getMethod(name);
                    m.setAccessible(true);
                    return ((Number) m.invoke(os)).longValue();
                } catch (Exception e) {
                    // Try the next name.
                }
            }
        } catch (Throwable t) {
            // Not available.
        }
        return -1;
    }

    public static long pid() {
        String n = ManagementFactory.getRuntimeMXBean().getName();     // pid@host
        try {
            return Long.parseLong(n.substring(0, n.indexOf('@')));
        } catch (Exception e) {
            return -1;
        }
    }

    /** The resident set size of this process in bytes, or -1 if it cannot be read. */
    public static long rssBytes() {
        try {
            File status = new File("/proc/self/status");
            if (status.exists()) {
                for (String line : readFile(status).split("\n")) {
                    if (line.startsWith("VmRSS:")) {
                        return Long.parseLong(line.replaceAll("[^0-9]", "")) * 1024;
                    }
                }
                return -1;
            }
            Process p = new ProcessBuilder("ps", "-o", "rss=", "-p", Long.toString(pid()))
                    .redirectErrorStream(true).start();
            BufferedReader r = new BufferedReader(new InputStreamReader(p.getInputStream(), UTF8));
            String line = r.readLine();
            p.waitFor();
            return line == null ? -1 : Long.parseLong(line.trim()) * 1024;
        } catch (Exception e) {
            return -1;
        }
    }

    /** Total collections (count) and collection time (ms) of all collectors since the JVM started. */
    public static long[] gcTotals() {
        long c = 0, t = 0;
        for (GarbageCollectorMXBean b : ManagementFactory.getGarbageCollectorMXBeans()) {
            if (b.getCollectionCount() > 0) c += b.getCollectionCount();
            if (b.getCollectionTime() > 0) t += b.getCollectionTime();
        }
        return new long[] {c, t};
    }

    /** Heap in use right after the last collection of each pool, summed (MB): what the program keeps. */
    public static double heapAfterLastGcMB() {
        long used = 0;
        for (MemoryPoolMXBean p : ManagementFactory.getMemoryPoolMXBeans()) {
            if (p.getType() != MemoryType.HEAP) continue;
            MemoryUsage u = p.getCollectionUsage();
            if (u != null) used += u.getUsed();
        }
        return used / 1e6;
    }

    public static double heapUsedMB() {
        return ManagementFactory.getMemoryMXBean().getHeapMemoryUsage().getUsed() / 1e6;
    }
}
