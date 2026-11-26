import java.io.*;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.time.LocalTime;
import java.util.*;

/**
 * StaleBytesProbe (bergdb 035-02; from 035-01's ZeroTailProbe). Without BergDB: after a SIGKILL
 * of a process that appends to a file, does the file hold within its length bytes of a file
 * deleted before (stale bytes), and whose?
 *
 * Every 4 KiB block of every file the child writes begins with a tag of 32 bytes: the marker
 * "STALE035", the run's nonce, the trial, the file's id and the block's offset in its file, and
 * a check of these. The other bytes of a write are its fill byte, 1 + seq % 255. So every byte of
 * every file is a function of (run, trial, file, offset, write), and a block read from another
 * file names that file and offset.
 *
 * The child first writes prepared files (prep=N:BYTES, ids 1000 + i), forces each with
 * FileChannel.force(true) and deletes them; then it opens file 0, prints "ready", and appends
 * writes as 035-01's child: "W seq start size" in a side log before each write, "w seq nanos"
 * after it returns, "f seq" after its force. At a cap the child opens the next file ("O n"),
 * closes and deletes the last. Before each write it prints "S seq start file" to stdout.
 *
 * The parent starts the child and kills it (Process.destroyForcibly(), SIGKILL): with
 * target=any after a random delay from "ready" (delay=MIN:MAX ms); with target=first:A:B during
 * the first write of file k, k uniform in A..B; with target=seq:A:B during write seq s, s uniform
 * in A..B: a random delay (kdelay=MIN:MAX microseconds, a busy wait) after the child's line "S"
 * of that write. It then reads the last file and compares it with
 * the log. When a byte within the length is wrong, every 4 KiB block from the first wrong byte
 * to the length is classified: zero (all zero), tagged (a valid tag of another block: own, of a
 * file of this trial, prepared or the child's; earlier, of an earlier trial of this run; other,
 * of another run), single (one repeated byte, not 0, such as 035-01's fill), or other bytes
 * (their entropy in bits per byte is kept, their bytes not).
 *
 * Classes of a trial: complete, none, prefix, short, long as in 035-01; for a wrong byte,
 * stale (a tagged block), single, other, or zeros (every wrong block zero), the first that
 * applies. One line per trial in LABEL.tsv in DIR, the summary in LABEL.summary; the first
 * files of the classes stale and single (at most keep=N) are copied to DIR/keep/ with the end
 * of their logs; of the class other only the counts. For every cut file (a wrong byte, or a
 * prefix) the bytes allocated to it (stat(1)'s st_blocks times 512) are kept: whether the
 * wrong bytes lie in blocks of the file or in a hole.
 *
 * Usage: java StaleBytesProbe.java parent DIR TRIALS [key=value ...]
 *   label=NAME        name of the run (default run)
 *   force=1|2|0       1: FileChannel.force(true) after each write (default; on macOS
 *                     F_FULLFSYNC, FileStream's hard sync); 2: FileDescriptor.sync() (fsync); 0: none
 *   size=SPEC         r:MIN:MAX uniform sizes; f:N one size; l:N1,N2,... (default r:65536:8388608)
 *   cap=BYTES         file size at which the child starts a new file (default 16777216)
 *   prep=N:BYTES      prepared files written, forced and deleted first (default 2:16777216; 0: none)
 *   pause=MS          sleep after the prepared files' deletes, before file 0 (default 0)
 *   spin=N            N threads of the child that spin, so that other threads than the writer
 *                     run when the kill comes (default 0)
 *   phys=PATH         a helper that prints a file's extents on its device (phys.c, macOS,
 *                     F_LOG2PHYS_EXT): for a cut file, the bytes of its wrong range that lie in
 *                     blocks that a deleted prepared file, or a file of the last 500 trials, held
 *   fdel=0|1          1: the parent forces each file of the trial before (FileChannel.force(true))
 *                     before it records its extents and deletes it, so that the device holds
 *                     the file's tagged bytes when its blocks are freed (default 0)
 *   lag=0|1           1: the last file is deleted after the next file's first write returns, not
 *                     before that write (default 0)
 *   target=SPEC       any, first:A:B or seq:A:B: when to kill (default first:1:3)
 *   delay=MIN:MAX     ms after "ready", for target=any (default 20:400)
 *   kdelay=MIN:MAX    microseconds after "S", for first and seq (default 0:2000)
 *   page=BYTES        page size for the positions in pages (default 16384)
 *   keep=N            files kept of the classes stale and single (default 3)
 *   seed=N            seed of the parent's choices and the children's sizes (default 1)
 *   until=HH:MM       stop starting trials at this local time
 *   stop=PATH         stop starting trials when this file exists
 *
 * The parent compiles this file once into DIR/classes (it runs in the JDK's source-file mode)
 * and starts each child from there. 2026-11-26.
 */
public class StaleBytesProbe {
    static final int BLOCK = 4096, TAG = 32;
    static final byte[] MARK = "STALE035".getBytes(StandardCharsets.US_ASCII);
    static final String HEADER = "label\ttrial\tdelay\tlast_ev\tfile\tseq\tstart\tsize\tend\tlength\tclass"
            + "\tfirst_write\tfirst_bad\tbad_from_last\tbad_pages\tlen_pages\tend_pages\tblocks_bad\tzero"
            + "\ttag_own_prep\ttag_own_child\ttag_earlier\ttag_other\tsingle\tother\tother_entropy"
            + "\tfirst_tag\twrite_us\talloc\twrong_dev";

    public static void main(String[] args) throws Exception {
        if (args.length > 0 && args[0].equals("child")) {
            child(args);
        } else if (args.length >= 3 && args[0].equals("parent")) {
            parent(args);
        } else {
            System.err.println("Usage: java StaleBytesProbe.java parent DIR TRIALS [key=value ...]");
            System.exit(2);
        }
    }

    static byte fill(long seq) {
        return (byte) (1 + seq % 255);
    }

    static String fileName(int n) {
        return "f-" + n + ".bin";
    }

    static int check(int nonce, int trial, int fileId, long offset) {
        long h = 0x9E3779B97F4A7C15L;
        h = (h ^ nonce) * 0xBF58476D1CE4E5B9L;
        h = (h ^ trial) * 0x94D049BB133111EBL;
        h = (h ^ fileId) * 0xBF58476D1CE4E5B9L;
        h = (h ^ offset) * 0x94D049BB133111EBL;
        return (int) (h ^ (h >>> 31));
    }

    /** A child's seed: adjacent trials' seeds would give java.util.Random correlated first sizes. */
    static long mix(long z) {
        z = (z ^ (z >>> 30)) * 0xBF58476D1CE4E5B9L;
        z = (z ^ (z >>> 27)) * 0x94D049BB133111EBL;
        return z ^ (z >>> 31);
    }

    static void putTag(byte[] t, int nonce, int trial, int fileId, long offset) {
        ByteBuffer b = ByteBuffer.wrap(t);
        b.put(MARK).putInt(nonce).putInt(trial).putInt(fileId).putLong(offset).putInt(check(nonce, trial, fileId, offset));
    }

    /** Fills buf[0, n) with the bytes of a write at file offset pos: tags at 4 KiB blocks, fill elsewhere. */
    static void content(byte[] buf, int n, long pos, long seq, int nonce, int trial, int fileId) {
        Arrays.fill(buf, 0, n, fill(seq));
        byte[] t = new byte[TAG];
        long b0 = pos - pos % BLOCK;
        for (long b = b0; b < pos + n; b += BLOCK) {
            putTag(t, nonce, trial, fileId, b);
            for (int k = 0; k < TAG; k++) {
                long y = b + k;
                if (y >= pos && y < pos + n) buf[(int) (y - pos)] = t[k];
            }
        }
    }

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

    static void force(RandomAccessFile f, String force) throws IOException {
        if (force.equals("1")) f.getChannel().force(true);
        else if (force.equals("2")) f.getFD().sync();
    }

    static void child(String[] a) throws Exception {
        File dir = new File(a[1]);
        String force = a[2];
        Sizes sizes = Sizes.parse(a[3]);
        long cap = Long.parseLong(a[4]);
        Random r = new Random(Long.parseLong(a[5]));
        String[] prep = a[6].split(":");
        int nonce = Integer.parseInt(a[7]);
        int trial = Integer.parseInt(a[8]);
        int pause = Integer.parseInt(a[9]);
        boolean lag = a[10].equals("1");
        int spin = Integer.parseInt(a[11]);
        String phys = a.length > 12 ? a[12] : "-";
        for (int i = 0; i < spin; i++) {
            Thread th = new Thread(() -> {
                long x = 0;
                while (true) {
                    x += System.nanoTime();
                    if (x == 42) System.out.print("");
                }
            });
            th.setDaemon(true);
            th.start();
        }
        int prepN = Integer.parseInt(prep[0]);
        long prepBytes = prepN > 0 ? Long.parseLong(prep[1]) : 0;
        byte[] buf = new byte[Math.max(sizes.max(), 1 << 20)];
        try (FileOutputStream log = new FileOutputStream(new File(dir, "log.txt"), true)) {
            for (int i = 0; i < prepN; i++) {
                File pf = new File(dir, "p-" + i + ".bin");
                try (RandomAccessFile f = new RandomAccessFile(pf, "rw")) {
                    for (long pos = 0; pos < prepBytes; pos += 1 << 20) {
                        int n = (int) Math.min(1 << 20, prepBytes - pos);
                        content(buf, n, pos, 1000 + i, nonce, trial, 1000 + i);
                        f.write(buf, 0, n);
                    }
                    f.getChannel().force(true);
                }
                logLine(log, "P " + i + " " + prepBytes);
            }
            for (int i = 0; i < prepN; i++) {
                File pf = new File(dir, "p-" + i + ".bin");
                if (!phys.equals("-")) for (long[] e : extents(phys, pf)) logLine(log, "X " + (1000 + i) + " " + e[0] + " " + e[1] + " " + e[2]);
                pf.delete();
            }
            if (pause > 0) Thread.sleep(pause);
            int fileNo = 0;
            int toDelete = -1;
            RandomAccessFile f = new RandomAccessFile(new File(dir, fileName(fileNo)), "rw");
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
                    logLine(log, "O " + fileNo);
                    old.close();
                    if (lag) toDelete = fileNo - 1;
                    else new File(dir, fileName(fileNo - 1)).delete();
                    pos = 0;
                }
                content(buf, n, pos, seq, nonce, trial, fileNo);
                logLine(log, "W " + seq + " " + pos + " " + n);
                System.out.println("S " + seq + " " + pos + " " + fileNo);
                System.out.flush();
                long t0 = System.nanoTime();
                f.write(buf, 0, n);
                logLine(log, "w " + seq + " " + (System.nanoTime() - t0));
                if (toDelete >= 0) {
                    new File(dir, fileName(toDelete)).delete();
                    toDelete = -1;
                }
                if (!force.equals("0")) {
                    force(f, force);
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
        String force = o.getOrDefault("force", "1");
        String size = o.getOrDefault("size", "r:65536:8388608");
        long cap = Long.parseLong(o.getOrDefault("cap", "16777216"));
        String prep = o.getOrDefault("prep", "2:16777216");
        String pause = o.getOrDefault("pause", "0");
        String lag = o.getOrDefault("lag", "0");
        String spin = o.getOrDefault("spin", "0");
        String phys = o.getOrDefault("phys", "-");
        boolean fdel = o.getOrDefault("fdel", "0").equals("1");
        // The extents of the files of the last 500 trials, deleted by the parent: {trial, device, length}.
        ArrayDeque<long[]> recent = new ArrayDeque<>();
        String target = o.getOrDefault("target", "first:1:3");
        String[] dl = o.getOrDefault("delay", "20:400").split(":");
        String[] kl = o.getOrDefault("kdelay", "0:2000").split(":");
        int dmin = Integer.parseInt(dl[0]), dmax = Integer.parseInt(dl[1]);
        int kmin = Integer.parseInt(kl[0]), kmax = Integer.parseInt(kl[1]);
        int page = Integer.parseInt(o.getOrDefault("page", "16384"));
        int keep = Integer.parseInt(o.getOrDefault("keep", "3"));
        long seed = Long.parseLong(o.getOrDefault("seed", "1"));
        LocalTime until = o.containsKey("until") ? LocalTime.parse(o.get("until")) : null;
        File stop = o.containsKey("stop") ? new File(o.get("stop")) : null;
        Sizes.parse(size);
        String[] tg = target.split(":");
        boolean timed = tg[0].equals("any");
        if (!timed && !(tg.length == 3 && (tg[0].equals("first") || tg[0].equals("seq"))))
            throw new IllegalArgumentException("target: " + target);
        int ta = timed ? 0 : Integer.parseInt(tg[1]), tb = timed ? 0 : Integer.parseInt(tg[2]);

        dir.mkdirs();
        File classes = compile(dir);
        String java = ProcessHandle.current().info().command().orElse("java");
        File tsv = new File(dir, label + ".tsv");
        boolean fresh = !tsv.exists();
        Random r = new Random(seed);
        int nonce = new Random(seed * 7919 + label.hashCode()).nextInt() & 0x7fffffff;
        Map<String, Integer> classCount = new TreeMap<>();
        Map<String, Integer> byWrite = new TreeMap<>();
        Map<String, Integer> origins = new TreeMap<>();
        List<String> notable = new ArrayList<>();
        int done = 0, kept = 0;
        long firstWriteNs = 0, firstWrites = 0;
        long t0 = System.nanoTime();
        String why = "all trials run";
        String env = "os " + System.getProperty("os.name") + " " + System.getProperty("os.version") + " "
                + System.getProperty("os.arch") + "; java " + System.getProperty("java.vm.vendor") + " "
                + System.getProperty("java.runtime.version") + "; store " + Files.getFileStore(dir.toPath()).type()
                + " " + Files.getFileStore(dir.toPath()).name();
        try (PrintWriter out = new PrintWriter(new FileWriter(tsv, true))) {
            if (fresh) out.println(HEADER);
            for (int t = 0; t < trials; t++) {
                if (stop != null && stop.exists()) { why = "stop file " + stop; break; }
                if (until != null && LocalTime.now().isAfter(until)) { why = "time " + until; break; }
                File td = new File(dir, "cur-" + label);
                if (!phys.equals("-") && td.isDirectory()) {
                    for (File c : td.listFiles()) {
                        if (!c.getName().endsWith(".bin")) continue;
                        if (fdel) {
                            try (FileChannel fc = FileChannel.open(c.toPath(), StandardOpenOption.READ, StandardOpenOption.WRITE)) {
                                fc.force(true);
                            }
                        }
                        for (long[] e : extents(phys, c)) recent.addLast(new long[] {t - 1, e[1], e[2]});
                    }
                    while (!recent.isEmpty() && recent.peekFirst()[0] < t - 500) recent.removeFirst();
                }
                deleteTree(td);
                td.mkdirs();
                Process p = new ProcessBuilder(java, "-Xmx256m", "-cp", classes.getPath(), "StaleBytesProbe", "child",
                        td.getPath(), force, size, Long.toString(cap), Long.toString(mix(seed * 1_000_003L + t)), prep,
                        Integer.toString(nonce), Integer.toString(t), pause, lag, spin, phys)
                        .redirectErrorStream(true).start();
                BufferedReader rd = new BufferedReader(new InputStreamReader(p.getInputStream()));
                String line = rd.readLine();
                if (!"ready".equals(line)) {
                    StringBuilder sb = new StringBuilder(String.valueOf(line));
                    for (String l; (l = rd.readLine()) != null; ) sb.append('\n').append(l);
                    p.destroyForcibly();
                    throw new IllegalStateException("child did not start: " + sb);
                }
                String delay;
                if (timed) {
                    int d = dmin + r.nextInt(dmax - dmin + 1);
                    Thread.sleep(d);
                    delay = d + "ms";
                } else {
                    int k = ta + r.nextInt(tb - ta + 1);
                    int us = kmin + r.nextInt(kmax - kmin + 1);
                    for (String l; (l = rd.readLine()) != null; ) {
                        String[] q = l.split(" ");
                        if (q.length == 4 && q[0].equals("S") && (tg[0].equals("seq") ? Long.parseLong(q[1]) == k
                                : q[2].equals("0") && Integer.parseInt(q[3]) == k)) break;
                    }
                    long until2 = System.nanoTime() + us * 1000L;
                    while (System.nanoTime() < until2) Thread.onSpinWait();
                    delay = tg[0] + k + "+" + us + "us";
                }
                p.destroyForcibly();
                p.waitFor();
                Result res = analyse(td, nonce, t, page);
                if (!phys.equals("-") && res.file != null && res.firstBad >= 0) devices(phys, res, td, recent, t);
                done++;
                if (res.firstWriteNs > 0) { firstWriteNs += res.firstWriteNs; firstWrites++; }
                classCount.merge(res.cls, 1, Integer::sum);
                String w = res.start == 0 ? "first" : "later";
                byWrite.merge(res.lastEv + "/" + w + "/" + res.cls, 1, Integer::sum);
                for (Map.Entry<String, Integer> e : res.origins.entrySet()) origins.merge(e.getKey(), e.getValue(), Integer::sum);
                String row = label + "\t" + t + "\t" + delay + "\t" + res.row();
                out.println(row);
                out.flush();
                boolean bad = res.firstBad >= 0 || res.cls.equals("short") || res.cls.equals("long");
                if (bad) {
                    notable.add(row);
                    System.out.println(row);
                    boolean keepIt = res.cls.equals("stale") || res.cls.equals("single");
                    if (keepIt && kept < keep && res.file != null) {
                        File kd = new File(dir, "keep");
                        kd.mkdirs();
                        Files.copy(res.file.toPath(), new File(kd, label + "-t" + t + ".bin").toPath(),
                                StandardCopyOption.REPLACE_EXISTING);
                        List<String> log = Files.readAllLines(new File(td, "log.txt").toPath());
                        Files.write(new File(kd, label + "-t" + t + ".log-tail.txt").toPath(),
                                log.subList(Math.max(0, log.size() - 40), log.size()));
                        Files.writeString(new File(kd, label + "-t" + t + ".blocks.txt").toPath(), res.blockList);
                        kept++;
                    }
                }
            }
        }
        deleteTree(new File(dir, "cur-" + label));
        StringBuilder s = new StringBuilder();
        s.append("label ").append(label).append(": force=").append(force).append(" size=").append(size)
                .append(" cap=").append(cap).append(" prep=").append(prep).append(" pause=").append(pause)
                .append(" lag=").append(lag).append(" spin=").append(spin).append(" target=").append(target)
                .append(timed ? " delay=" + dmin + ":" + dmax : " kdelay=" + kmin + ":" + kmax)
                .append(" seed=").append(seed).append(" nonce=").append(nonce).append('\n');
        s.append(env).append('\n');
        s.append("trials ").append(done).append(" (").append(why).append("), ")
                .append((System.nanoTime() - t0) / 1_000_000_000L).append(" s\n");
        s.append("classes ").append(classCount).append('\n');
        s.append("last event/write/class ").append(byWrite).append('\n');
        s.append("tagged blocks by origin ").append(origins).append('\n');
        s.append("first writes that returned: ").append(firstWrites).append(", mean ")
                .append(firstWrites == 0 ? 0 : firstWriteNs / firstWrites / 1000).append(" us\n");
        for (String n : notable) s.append(n).append('\n');
        System.out.print(s);
        Files.writeString(new File(dir, label + ".summary").toPath(), s.toString());
    }

    static final class Result {
        String lastEv = "-", cls, firstTag = "-", blockList = "";
        int fileNo = -1;
        long seq = -1, start = -1, size = -1, end = -1, length = -1, firstBad = -1, firstWriteNs = -1;
        int badFromLast = -1, page;
        int blocksBad, zero, tagOwnPrep, tagOwnChild, tagEarlier, tagOther, single, other;
        double otherEntropy;
        long writeNs = -1, alloc = -1;
        String dev = "-";
        Map<String, Integer> origins = new TreeMap<>();
        File file;

        String pages(long x) {
            if (x < 0 || start < 0) return "-";
            long p0 = start - start % page;
            return Long.toString((x - p0) / page) + (((x - p0) % page) == 0 ? "" : "+");
        }

        String row() {
            return lastEv + "\t" + fileNo + "\t" + seq + "\t" + start + "\t" + size + "\t" + end + "\t" + length + "\t"
                    + cls + "\t" + (start == 0 ? 1 : 0) + "\t" + firstBad + "\t" + badFromLast + "\t" + pages(firstBad)
                    + "\t" + pages(length) + "\t" + pages(end) + "\t" + blocksBad + "\t" + zero + "\t" + tagOwnPrep
                    + "\t" + tagOwnChild + "\t" + tagEarlier + "\t" + tagOther + "\t" + single + "\t" + other + "\t"
                    + String.format(Locale.ROOT, "%.2f", other == 0 ? 0.0 : otherEntropy / other) + "\t" + firstTag
                    + "\t" + (writeNs < 0 ? "-" : Long.toString(writeNs / 1000)) + "\t" + alloc + "\t" + dev;
        }
    }

    static byte expected(int nonce, int trial, int fileNo, long y, long seq, byte[] tag, long[] tagFor) {
        int k = (int) (y % BLOCK);
        if (k >= TAG) return fill(seq);
        long b = y - k;
        if (tagFor[0] != b) {
            putTag(tag, nonce, trial, fileNo, b);
            tagFor[0] = b;
        }
        return tag[k];
    }

    /** The file's extents on its device, {file offset, device offset, length}, by the helper 'phys' (macOS). */
    static List<long[]> extents(String phys, File f) {
        List<long[]> r = new ArrayList<>();
        try {
            Process p = new ProcessBuilder(phys, f.getPath()).redirectErrorStream(true).start();
            for (String l : new String(p.getInputStream().readAllBytes(), StandardCharsets.US_ASCII).split("\n")) {
                String[] q = l.trim().split(" ");
                if (q.length == 3) r.add(new long[] {Long.parseLong(q[0]), Long.parseLong(q[1]), Long.parseLong(q[2])});
            }
            p.waitFor();
        } catch (Exception e) {
            // none known
        }
        return r;
    }

    /**
     * For a cut file: how many bytes of its wrong range lie, on the device, in blocks that a
     * prepared file of this trial, or a file of the last 500 trials, held before it was deleted,
     * and how many trials ago the newest of those was.
     */
    static void devices(String phys, Result res, File td, ArrayDeque<long[]> recent, int t) throws IOException {
        List<long[]> prep = new ArrayList<>();
        for (String l : Files.readAllLines(new File(td, "log.txt").toPath(), StandardCharsets.US_ASCII)) {
            String[] q = l.split(" ");
            if (q.length == 5 && q[0].equals("X")) prep.add(new long[] {Long.parseLong(q[2]), Long.parseLong(q[3]), Long.parseLong(q[4])});
        }
        long inPrep = 0, inRecent = 0, mapped = 0, newest = -1;
        for (long[] e : extents(phys, res.file)) {
            long from = Math.max(e[0], res.firstBad), to = Math.min(e[0] + e[2], res.length);
            if (from >= to) continue;
            long d0 = e[1] + (from - e[0]), d1 = d0 + (to - from);
            mapped += to - from;
            inPrep += overlap(d0, d1, prep);
            for (long[] r : recent) {
                long n = Math.max(0, Math.min(d1, r[1] + r[2]) - Math.max(d0, r[1]));
                if (n > 0) { inRecent += n; newest = Math.max(newest, r[0]); }
            }
        }
        res.dev = "mapped" + mapped + ":prep" + inPrep + ":recent" + inRecent + (newest >= 0 ? ":ago" + (t - newest) : "");
    }

    static long overlap(long d0, long d1, List<long[]> ext) {
        long n = 0;
        for (long[] e : ext) n += Math.max(0, Math.min(d1, e[1] + e[2]) - Math.max(d0, e[1]));
        return n;
    }

    /**
     * The bytes allocated to the file (st_blocks times 512), by stat(1), after a force of the
     * file, so that the pages the child copied are written and allocated; -1 if unknown.
     */
    static long allocated(File f) {
        try {
            try (FileChannel fc = FileChannel.open(f.toPath(), StandardOpenOption.READ, StandardOpenOption.WRITE)) {
                fc.force(true);
            }
            boolean mac = System.getProperty("os.name").startsWith("Mac");
            Process p = new ProcessBuilder("stat", mac ? "-f" : "-c", mac ? "%b" : "%b", f.getPath())
                    .redirectErrorStream(true).start();
            String out = new String(p.getInputStream().readAllBytes(), StandardCharsets.US_ASCII).trim();
            p.waitFor();
            return Long.parseLong(out) * 512;
        } catch (Exception e) {
            return -1;
        }
    }

    static double entropy(byte[] d, int from, int to) {
        int[] c = new int[256];
        for (int i = from; i < to; i++) c[d[i] & 0xff]++;
        double h = 0, n = to - from;
        for (int x : c) if (x > 0) h -= x / n * Math.log(x / n) / Math.log(2);
        return h;
    }

    static Result analyse(File td, int nonce, int trial, int page) throws IOException {
        Result res = new Result();
        res.page = page;
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
        res.fileNo = fileNo;
        List<long[]> recs = new ArrayList<>();
        Map<Long, Long> durations = new HashMap<>();
        Set<Long> firsts = new HashSet<>();
        for (int i = 0; i < lines.length; i++) {
            String[] p = lines[i].split(" ");
            if (lines[i].startsWith("W ")) {
                if (i > open) recs.add(new long[] {Long.parseLong(p[1]), Long.parseLong(p[2]), Long.parseLong(p[3])});
                if (Long.parseLong(p[2]) == 0) firsts.add(Long.parseLong(p[1]));
            } else if (lines[i].startsWith("w ") && p.length > 2) {
                durations.put(Long.parseLong(p[1]), Long.parseLong(p[2]));
            }
        }
        for (long s : firsts) {
            Long d = durations.get(s);
            if (d != null) { res.firstWriteNs = d; }
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
        Long wd = durations.get(res.seq);
        res.writeNs = wd == null ? -1 : wd;
        byte[] tag = new byte[TAG];
        long[] tagFor = {-1};
        outer:
        for (int k = 0; k < recs.size(); k++) {
            long[] rec = recs.get(k);
            long e = Math.min(rec[1] + rec[2], len);
            for (long i = rec[1]; i < e; i++) {
                if (data[(int) i] != expected(nonce, trial, fileNo, i, rec[0], tag, tagFor)) {
                    res.firstBad = i;
                    res.badFromLast = recs.size() - 1 - k;
                    break outer;
                }
            }
        }
        // A block of another file begins with the same marker, and with the same nonce in this
        // run: a wrong byte inside a tag makes the whole block wrong, from its start.
        if (res.firstBad >= 0 && res.firstBad % BLOCK < TAG) res.firstBad -= res.firstBad % BLOCK;
        if (res.firstBad < 0) {
            if (len == res.end) res.cls = "complete";
            else if (len == res.start) res.cls = "none";
            else if (len > res.start && len < res.end) res.cls = "prefix";
            else if (len < res.start) res.cls = "short";
            else res.cls = "long";
            if (res.cls.equals("prefix")) res.alloc = allocated(f);
            return res;
        }
        res.alloc = allocated(f);
        StringBuilder bl = new StringBuilder();
        ByteBuffer bb = ByteBuffer.wrap(data);
        for (long b = res.firstBad - res.firstBad % BLOCK; b < len; b += BLOCK) {
            int from = (int) Math.max(b, res.firstBad), to = (int) Math.min(b + BLOCK, len);
            res.blocksBad++;
            boolean allZero = true;
            for (int i = from; i < to; i++) if (data[i] != 0) { allZero = false; break; }
            String kind;
            if (allZero) {
                res.zero++;
                kind = "zero";
            } else {
                String tagged = null;
                if (from == b && to - from >= TAG && Arrays.equals(data, from, from + 8, MARK, 0, 8)) {
                    int tn = bb.getInt(from + 8), tt = bb.getInt(from + 12), tf = bb.getInt(from + 16);
                    long to2 = bb.getLong(from + 20);
                    int tc = bb.getInt(from + 28);
                    if (tc == check(tn, tt, tf, to2)) {
                        String origin;
                        if (tn == nonce && tt == trial) {
                            if (tf >= 1000) { res.tagOwnPrep++; origin = "own-prep"; }
                            else { res.tagOwnChild++; origin = "own-child"; }
                        } else if (tn == nonce) { res.tagEarlier++; origin = "earlier-trial"; }
                        else { res.tagOther++; origin = "other-run"; }
                        res.origins.merge(origin, 1, Integer::sum);
                        tagged = origin + ":t" + tt + ":file" + tf + ":off" + to2 + ":delta" + (to2 - b)
                                + ":fill" + (to - from > TAG ? (data[from + TAG] & 0xff) : -1);
                        if (res.firstTag.equals("-")) res.firstTag = tagged + ":at" + b;
                    }
                }
                if (tagged != null) {
                    kind = tagged;
                } else {
                    boolean one = true;
                    for (int i = from + 1; i < to; i++) if (data[i] != data[from]) { one = false; break; }
                    if (one) { res.single++; kind = "single:" + (data[from] & 0xff); }
                    else {
                        res.other++;
                        double h = entropy(data, from, to);
                        res.otherEntropy += h;
                        kind = String.format(Locale.ROOT, "other:entropy%.2f", h);
                    }
                }
            }
            bl.append(b).append('\t').append(kind).append('\n');
        }
        res.blockList = bl.toString();
        if (res.tagOwnPrep + res.tagOwnChild + res.tagEarlier + res.tagOther > 0) res.cls = "stale";
        else if (res.single > 0) res.cls = "single";
        else if (res.other > 0) res.cls = "other";
        else res.cls = "zeros";
        return res;
    }
}
