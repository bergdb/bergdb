import java.io.*;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.time.LocalTime;
import java.util.*;

/**
 * ZeroTailProbe (bergdb 035-01; extended from 031-02's apps/ZeroTailProbe.java). Without
 * BergDB: after a SIGKILL of a process that appends to a file, does the file hold zeros within
 * its length, and how do the file's length and the zeros lie against the write that the kill
 * cut?
 *
 * A child process appends writes to a file, each filled with one byte value that is never 0
 * and that differs from the last write's (1 + seq % 255). Before each write it appends a line
 * "W seq start size" to a side log, "w seq" after the write returns, and "f seq" after its
 * force, if forced. Each log line is one write() system call that has returned before the next
 * step begins, so after the kill the log names the write that was in progress, if any. At a cap
 * (32 MiB by default) the child opens the next file ("O n"), then closes and deletes the last.
 *
 * The parent starts the child, waits for its "ready" line (the file is open), sleeps a random
 * delay and kills it (Process.destroyForcibly(), SIGKILL). It then reads the last file and
 * compares it with the log: every write's bytes within the file's length must be its fill byte.
 * Each trial is one line of LABEL.tsv in DIR; the summary is printed and written to
 * LABEL.summary. The first files of another class than complete, none or prefix (at most
 * keep=N) are copied to DIR/keep/ with the end of their logs.
 *
 * Classes of a trial: complete (the file ends at the last write's end), none (it ends at the
 * last write's start), prefix (between them, no zeros), zeros (a byte 0 within the length),
 * garbage (another wrong byte), short (shorter than the last write's start), long (longer than
 * its end).
 *
 * Usage: java ZeroTailProbe.java parent DIR TRIALS [key=value ...]
 *   label=NAME       name of the run (default run)
 *   api=raf|fc|fcd   RandomAccessFile.write(byte[], off, len) as BergDB's FileStream does
 *                    (default); FileChannel.write of a heap ByteBuffer; of a direct ByteBuffer
 *   force=1|2|0      1: FileChannel.force(true) after each write (default, as FileStream's
 *                    hard sync; on macOS it reaches F_FULLFSYNC); 2: FileDescriptor.sync()
 *                    (fsync(2) on macOS); 0: no force
 *   size=SPEC        r:MIN:MAX uniform sizes; f:N one size; l:N1,N2,... one of a list
 *                    (default r:65536:2065535, 031-02's sizes)
 *   delay=MIN:MAX    ms between the child's "ready" and the kill (default 20:400)
 *   cap=BYTES        file size at which the child starts a new file (default 33554432)
 *   keep=N           files kept of the classes zeros, garbage, short, long (default 2)
 *   seed=N           seed of the parent's delays and the children's sizes (default 1)
 *   until=HH:MM      stop starting trials at this local time
 *   stop=PATH        stop starting trials when this file exists
 *
 * The parent compiles this file once into DIR/classes (it runs in the JDK's source-file
 * mode) and starts each child from there. 2026-11-26.
 */
public class ZeroTailProbe {
    static final String HEADER = "label\ttrial\tdelay_ms\tlast_ev\tseq\tstart\tsize\tend\tlength\tclass"
            + "\tfirst_bad\tbad_byte\tzero_run\tzero_to_end\tbad_write_from_last\tlen_mod_4k\tlen_mod_16k"
            + "\tbad_mod_4k\tbad_mod_16k\tlen_minus_start\tbad_minus_start\tend_minus_len";

    public static void main(String[] args) throws Exception {
        if (args.length > 0 && args[0].equals("child")) {
            child(args);
        } else if (args.length >= 3 && args[0].equals("parent")) {
            parent(args);
        } else {
            System.err.println("Usage: java ZeroTailProbe.java parent DIR TRIALS [key=value ...]");
            System.exit(2);
        }
    }

    static byte fill(long seq) {
        return (byte) (1 + seq % 255);
    }

    static String fileName(int n) {
        return "f-" + n + ".bin";
    }

    // ---- sizes ----

    static final class Sizes {
        final char kind;
        final int[] v;

        Sizes(char kind, int[] v) {
            this.kind = kind;
            this.v = v;
        }

        static Sizes parse(String s) {
            String[] p = s.split(":");
            switch (p[0]) {
                case "r": return new Sizes('r', new int[] {Integer.parseInt(p[1]), Integer.parseInt(p[2])});
                case "f": return new Sizes('f', new int[] {Integer.parseInt(p[1])});
                case "l": return new Sizes('l', Arrays.stream(p[1].split(",")).mapToInt(Integer::parseInt).toArray());
                default: throw new IllegalArgumentException("size: " + s);
            }
        }

        int next(Random r) {
            switch (kind) {
                case 'r': return v[0] + r.nextInt(v[1] - v[0] + 1);
                case 'f': return v[0];
                default: return v[r.nextInt(v.length)];
            }
        }

        int max() {
            return Arrays.stream(v).max().getAsInt();
        }
    }

    // ---- child ----

    static void logLine(FileOutputStream log, String s) throws IOException {
        log.write((s + "\n").getBytes(StandardCharsets.US_ASCII));
    }

    static void child(String[] a) throws Exception {
        File dir = new File(a[1]);
        String api = a[2];
        String force = a[3];
        Sizes sizes = Sizes.parse(a[4]);
        long cap = Long.parseLong(a[5]);
        Random r = new Random(Long.parseLong(a[6]));
        byte[] buf = new byte[sizes.max()];
        ByteBuffer direct = api.equals("fcd") ? ByteBuffer.allocateDirect(sizes.max()) : null;
        try (FileOutputStream log = new FileOutputStream(new File(dir, "log.txt"), true)) {
            int fileNo = 0;
            RandomAccessFile f = new RandomAccessFile(new File(dir, fileName(fileNo)), "rw");
            FileChannel ch = f.getChannel();
            logLine(log, "O " + fileNo);
            System.out.println("ready");
            System.out.flush();
            long pos = 0;
            for (long seq = 0; ; seq++) {
                int n = sizes.next(r);
                if (pos + n > cap) {
                    // The next file is opened and logged before the last is deleted, so that
                    // the file the log names last exists after a kill.
                    RandomAccessFile old = f;
                    fileNo++;
                    f = new RandomAccessFile(new File(dir, fileName(fileNo)), "rw");
                    ch = f.getChannel();
                    logLine(log, "O " + fileNo);
                    old.close();
                    new File(dir, fileName(fileNo - 1)).delete();
                    pos = 0;
                }
                byte b = fill(seq);
                Arrays.fill(buf, 0, n, b);
                if (direct != null) {
                    direct.clear();
                    direct.put(buf, 0, n);
                    direct.flip();
                }
                logLine(log, "W " + seq + " " + pos + " " + n);
                switch (api) {
                    case "raf":
                        f.write(buf, 0, n);
                        break;
                    case "fc": {
                        ByteBuffer bb = ByteBuffer.wrap(buf, 0, n);
                        while (bb.hasRemaining()) ch.write(bb);
                        break;
                    }
                    case "fcd":
                        while (direct.hasRemaining()) ch.write(direct);
                        break;
                    default:
                        throw new IllegalArgumentException("api: " + api);
                }
                logLine(log, "w " + seq);
                if (force.equals("1")) {
                    ch.force(true);
                    logLine(log, "f " + seq);
                } else if (force.equals("2")) {
                    f.getFD().sync();
                    logLine(log, "f " + seq);
                }
                pos += n;
            }
        }
    }

    // ---- parent ----

    static Map<String, String> options(String[] a, int from) {
        Map<String, String> m = new LinkedHashMap<>();
        for (int i = from; i < a.length; i++) {
            int eq = a[i].indexOf('=');
            if (eq <= 0) throw new IllegalArgumentException("option: " + a[i]);
            m.put(a[i].substring(0, eq), a[i].substring(eq + 1));
        }
        return m;
    }

    static File compile(File dir) throws Exception {
        File classes = new File(dir, "classes");
        String src = System.getProperty("jdk.launcher.sourcefile");
        if (src == null) return new File(System.getProperty("java.class.path"));
        classes.mkdirs();
        int rc = javax.tools.ToolProvider.getSystemJavaCompiler().run(null, null, null, "-d", classes.getPath(), src);
        if (rc != 0) throw new IllegalStateException("javac failed: " + rc);
        return classes;
    }

    static void deleteTree(File f) {
        File[] fs = f.listFiles();
        if (fs != null) for (File c : fs) deleteTree(c);
        f.delete();
    }

    static void parent(String[] a) throws Exception {
        File dir = new File(a[1]);
        int trials = Integer.parseInt(a[2]);
        Map<String, String> o = options(a, 3);
        String label = o.getOrDefault("label", "run");
        String api = o.getOrDefault("api", "raf");
        String force = o.getOrDefault("force", "1");
        String size = o.getOrDefault("size", "r:65536:2065535");
        String[] dl = o.getOrDefault("delay", "20:400").split(":");
        int dmin = Integer.parseInt(dl[0]), dmax = Integer.parseInt(dl[1]);
        long cap = Long.parseLong(o.getOrDefault("cap", "33554432"));
        int keep = Integer.parseInt(o.getOrDefault("keep", "2"));
        long seed = Long.parseLong(o.getOrDefault("seed", "1"));
        LocalTime until = o.containsKey("until") ? LocalTime.parse(o.get("until")) : null;
        File stop = o.containsKey("stop") ? new File(o.get("stop")) : null;
        Sizes.parse(size);

        dir.mkdirs();
        File classes = compile(dir);
        String java = ProcessHandle.current().info().command().orElse("java");
        File tsv = new File(dir, label + ".tsv");
        boolean fresh = !tsv.exists();
        Random r = new Random(seed);
        Map<String, Integer> classes2 = new TreeMap<>();
        Map<String, Integer> lastEvs = new TreeMap<>();
        List<String> notable = new ArrayList<>();
        int prefixAligned16 = 0, prefixAligned4 = 0, done = 0, kept = 0;
        long t0 = System.nanoTime();
        String why = "all trials run";
        try (PrintWriter out = new PrintWriter(new FileWriter(tsv, true))) {
            if (fresh) out.println(HEADER);
            for (int t = 0; t < trials; t++) {
                if (stop != null && stop.exists()) { why = "stop file " + stop; break; }
                if (until != null && LocalTime.now().isAfter(until)) { why = "time " + until; break; }
                File td = new File(dir, "cur-" + label);
                deleteTree(td);
                td.mkdirs();
                Process p = new ProcessBuilder(java, "-Xmx256m", "-cp", classes.getPath(), "ZeroTailProbe", "child",
                        td.getPath(), api, force, size, Long.toString(cap), Long.toString(seed * 1_000_003L + t))
                        .redirectErrorStream(true).start();
                BufferedReader rd = new BufferedReader(new InputStreamReader(p.getInputStream()));
                String line = rd.readLine();
                if (!"ready".equals(line)) {
                    StringBuilder sb = new StringBuilder(String.valueOf(line));
                    for (String l; (l = rd.readLine()) != null; ) sb.append('\n').append(l);
                    p.destroyForcibly();
                    throw new IllegalStateException("child did not start: " + sb);
                }
                int d = dmin + r.nextInt(dmax - dmin + 1);
                Thread.sleep(d);
                p.destroyForcibly();
                p.waitFor();
                Result res = analyse(td);
                done++;
                classes2.merge(res.cls, 1, Integer::sum);
                lastEvs.merge(res.lastEv + "/" + res.cls, 1, Integer::sum);
                if (res.cls.equals("prefix")) {
                    if (res.length % 16384 == 0) prefixAligned16++;
                    if (res.length % 4096 == 0) prefixAligned4++;
                }
                String row = label + "\t" + t + "\t" + d + "\t" + res.row();
                out.println(row);
                out.flush();
                if (!res.cls.equals("complete") && !res.cls.equals("none") && !res.cls.equals("prefix")) {
                    notable.add(row);
                    System.out.println(row);
                    if (kept < keep && res.file != null) {
                        File kd = new File(dir, "keep");
                        kd.mkdirs();
                        Files.copy(res.file.toPath(), new File(kd, label + "-t" + t + ".bin").toPath(),
                                StandardCopyOption.REPLACE_EXISTING);
                        List<String> log = Files.readAllLines(new File(td, "log.txt").toPath());
                        Files.write(new File(kd, label + "-t" + t + ".log-tail.txt").toPath(),
                                log.subList(Math.max(0, log.size() - 40), log.size()));
                        kept++;
                    }
                }
            }
        }
        deleteTree(new File(dir, "cur-" + label));
        StringBuilder s = new StringBuilder();
        s.append("label ").append(label).append(": api=").append(api).append(" force=").append(force)
                .append(" size=").append(size).append(" delay=").append(dmin).append(':').append(dmax)
                .append(" cap=").append(cap).append(" seed=").append(seed).append('\n');
        s.append("trials ").append(done).append(" (").append(why).append("), ")
                .append((System.nanoTime() - t0) / 1_000_000_000L).append(" s\n");
        s.append("classes ").append(classes2).append('\n');
        s.append("last event/class ").append(lastEvs).append('\n');
        s.append("prefix lengths on a 16 KiB boundary ").append(prefixAligned16).append(", on 4 KiB ")
                .append(prefixAligned4).append('\n');
        for (String n : notable) s.append(n).append('\n');
        System.out.print(s);
        Files.writeString(new File(dir, label + ".summary").toPath(), s.toString());
    }

    static final class Result {
        String lastEv = "-", cls;
        long seq = -1, start = -1, size = -1, end = -1, length = -1, firstBad = -1, zeroRun = 0;
        int badByte = -1, badFromLast = -1;
        boolean zeroToEnd;
        File file;

        String row() {
            return lastEv + "\t" + seq + "\t" + start + "\t" + size + "\t" + end + "\t" + length + "\t" + cls + "\t"
                    + firstBad + "\t" + badByte + "\t" + zeroRun + "\t" + (zeroToEnd ? 1 : 0) + "\t" + badFromLast
                    + "\t" + (length % 4096) + "\t" + (length % 16384) + "\t"
                    + (firstBad < 0 ? -1 : firstBad % 4096) + "\t" + (firstBad < 0 ? -1 : firstBad % 16384) + "\t"
                    + (length - start) + "\t" + (firstBad < 0 ? -1 : firstBad - start) + "\t" + (end - length);
        }
    }

    static Result analyse(File td) throws IOException {
        Result res = new Result();
        byte[] logBytes = Files.readAllBytes(new File(td, "log.txt").toPath());
        String logText = new String(logBytes, StandardCharsets.US_ASCII);
        int lastNl = logText.lastIndexOf('\n');
        String[] lines = lastNl < 0 ? new String[0] : logText.substring(0, lastNl).split("\n");
        int open = -1;
        for (int i = lines.length - 1; i >= 0; i--) {
            if (lines[i].startsWith("O ")) { open = i; break; }
        }
        if (open < 0) { res.cls = "nolog"; return res; }
        int fileNo = Integer.parseInt(lines[open].substring(2).trim());
        List<long[]> recs = new ArrayList<>();
        for (int i = open + 1; i < lines.length; i++) {
            if (lines[i].startsWith("W ")) {
                String[] p = lines[i].split(" ");
                recs.add(new long[] {Long.parseLong(p[1]), Long.parseLong(p[2]), Long.parseLong(p[3])});
            }
        }
        res.lastEv = lines[lines.length - 1].substring(0, 1);
        File f = new File(td, fileName(fileNo));
        res.file = f;
        if (!f.exists()) { res.cls = "nofile"; res.file = null; return res; }
        byte[] data = Files.readAllBytes(f.toPath());
        long len = data.length;
        res.length = len;
        if (recs.isEmpty()) {
            res.start = 0;
            res.size = 0;
            res.end = 0;
            res.cls = len == 0 ? "none" : "long";
            return res;
        }
        long[] last = recs.get(recs.size() - 1);
        res.seq = last[0];
        res.start = last[1];
        res.size = last[2];
        res.end = last[1] + last[2];
        outer:
        for (int k = 0; k < recs.size(); k++) {
            long[] rec = recs.get(k);
            byte b = fill(rec[0]);
            long e = Math.min(rec[1] + rec[2], len);
            for (long i = rec[1]; i < e; i++) {
                if (data[(int) i] != b) {
                    res.firstBad = i;
                    res.badByte = data[(int) i] & 0xff;
                    res.badFromLast = recs.size() - 1 - k;
                    break outer;
                }
            }
        }
        if (res.firstBad >= 0) {
            long z = res.firstBad;
            while (z < len && data[(int) z] == 0) z++;
            res.zeroRun = z - res.firstBad;
            res.zeroToEnd = z == len;
            res.cls = res.badByte == 0 ? "zeros" : "garbage";
        } else if (len == res.end) {
            res.cls = "complete";
        } else if (len == res.start) {
            res.cls = "none";
        } else if (len > res.start && len < res.end) {
            res.cls = "prefix";
        } else if (len < res.start) {
            res.cls = "short";
        } else {
            res.cls = "long";
        }
        return res;
    }
}
