import bergdb.pub.*;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.TimeUnit;

/** Functional crash recovery checks. Usage: D4CrashBatches DIR SEED [kills]. */
public final class D4CrashBatches {
    static final long BASE = Time.utc("2020-01-01").units();
    static final String MARKER = "/progress/sequence.txt";
    static final String[] DIRS = {"/state/", "/audit/", "/progress/"};
    static void check(boolean ok, String m) { if (!ok) throw new IllegalStateException(m); }
    static byte[] utf8(String text) { return text.getBytes(StandardCharsets.UTF_8); }
    static Map<String, byte[]> batch(long seed, int seq) {
        Random r = new Random(seed ^ seq * 0x9e3779b97f4a7c15L);
        Map<String, byte[]> ops = new LinkedHashMap<>();
        for (int n = 0; n < 7; n++) {
            String key = "/state/k" + r.nextInt(83) + ".bin";
            if (n % 3 == 0) ops.put(key, null);
            else { byte[] value = new byte[8192 + r.nextInt(24577)]; r.nextBytes(value); ops.put(key, value); }
        }
        ops.put("/state/mirror-a.txt", utf8("batch:" + seq));
        ops.put("/state/mirror-b.txt", utf8("batch:" + seq));
        ops.put("/audit/" + String.format(Locale.ROOT, "%08d", seq) + ".txt", utf8("accepted:" + seed + ":" + seq));
        ops.put(MARKER, utf8(Integer.toString(seq))); return ops;
    }
    static void write(Connection c, Map<String, byte[]> ops) {
        WBuilder w = c.w(); for (var e : ops.entrySet()) { if (e.getValue() == null) w.delete(e.getKey()); else w.put(e.getKey(), e.getValue()); } w.execute();
    }
    static String readCommand(BufferedReader in) throws IOException {
        String s = in.readLine(); if (s == null) throw new EOFException("parent ended"); return s;
    }
    static void child(String path, long seed, int start) throws Exception {
        TestClock clock = new TestClock(); clock.setTime(Time.units(BASE + start * 1000000L));
        try (Database db = Factory.database().open(path).clock(clock).cacheSizeInMb(32).start()) {
            Connection c = db.connection(); BufferedReader in = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
            for (int seq = start + 1; ; seq++) {
                Map<String, byte[]> ops = batch(seed, seq);
                System.out.println("PREPARED " + seq); System.out.flush();
                if (!readCommand(in).equals("write")) throw new IllegalStateException("bad write command");
                clock.setTime(Time.units(BASE + seq * 1000000L));
                write(c, ops);
                System.out.println("COMMITTED " + seq); System.out.flush();
                String command = readCommand(in);
                if (command.equals("sync")) {
                    c.sync(); System.out.println("SYNCED " + seq); System.out.flush(); command = readCommand(in);
                }
                if (!command.equals("next")) throw new IllegalStateException("bad next command");
            }
        }
    }
    static int verify(String path, long seed, int lower, int upper) {
        TestClock clock = new TestClock(); clock.setTime(Time.units(BASE + upper * 1000000L));
        try (Database db = Factory.database().open(path).clock(clock).cacheSizeInMb(32).start()) {
            Connection c = db.connection(); int seq = Integer.parseInt(c.get(MARKER, String.class));
            check(seq >= lower, "lost synced batch: synced=" + lower + " recovered=" + seq);
            check(seq <= upper, "phantom batch: attempted=" + upper + " recovered=" + seq);
            Map<String, byte[]> want = new HashMap<>(); want.put(MARKER, utf8("0"));
            for (int n = 1; n <= seq; n++) for (var e : batch(seed, n).entrySet()) {
                if (e.getValue() == null) want.remove(e.getKey()); else want.put(e.getKey(), e.getValue());
            }
            Map<String, byte[]> got = new HashMap<>();
            for (String dir : DIRS) for (Kv<byte[]> e : c.usePrimary(byte[].class).dir(dir).kvs()) {
                check(got.put(e.key(), e.value()) == null, "duplicate scan key");
            }
            check(got.keySet().equals(want.keySet()), "partial batch or prefix gap: expected=" + want.keySet() + " got=" + got.keySet());
            for (var e : want.entrySet()) {
                check(Arrays.equals(e.getValue(), got.get(e.getKey())), "changed/reordered value " + e.getKey() + " at batch " + seq);
                check(Arrays.equals(e.getValue(), c.get(e.getKey(), byte[].class)), "get disagrees with scan " + e.getKey());
                check(c.exists(e.getKey()), "exists disagrees");
            }
            // The marker, both mirrors and every journal entry must describe one whole prefix.
            check(seq == 0 || Objects.equals(c.get("/state/mirror-a.txt", String.class), "batch:" + seq), "mirror A torn");
            check(seq == 0 || Objects.equals(c.get("/state/mirror-b.txt", String.class), "batch:" + seq), "mirror B torn");
            System.out.println("recovery synced=" + lower + " attempted=" + upper + " present=" + seq
                    + " checked=" + want.size() + " first=" + db.getFirstAvailableLookupTime().units());
            return seq;
        }
    }
    static void send(BufferedWriter out, String s) throws IOException { out.write(s); out.newLine(); out.flush(); }
    public static void main(String[] args) throws Exception {
        if (args[0].equals("child")) { child(args[1], Long.parseLong(args[2]), Integer.parseInt(args[3])); return; }
        String path = args[0]; long seed = Long.parseLong(args[1]); int kills = args.length > 2 ? Integer.parseInt(args[2]) : 30;
        check(!Files.exists(Path.of(path)), "use a fresh directory");
        System.out.println("Kind: functional; D4CrashBatches seed=" + seed + " kills=" + kills);
        TestClock clock = new TestClock(); clock.setTime(Time.units(BASE));
        try (Database db = Factory.database().create(path).clock(clock).cacheSizeInMb(32).start()) {
            db.setStartupDistanceInMb(5); db.setRetainDuration(Duration.seconds(2)); db.connection().put(MARKER, "0"); db.sync();
        }
        Random random = new Random(seed); int recovered = 0, synced = 0, highest = 0;
        for (int round = 0; round < kills; round++) {
            int target = recovered + 15 + random.nextInt(46), mode = round % 5;
            String java = Path.of(System.getProperty("java.home"), "bin", "java").toString();
            Process p = new ProcessBuilder(java, "-ea", "-Xmx256m", "-XX:+ExitOnOutOfMemoryError", "-cp", System.getProperty("java.class.path"),
                    "D4CrashBatches", "child", path, Long.toString(seed), Integer.toString(recovered))
                    .redirectError(Path.of(path).resolveSibling(Path.of(path).getFileName() + "-child-" + round + ".stderr.log").toFile()).start();
            try (BufferedReader in = new BufferedReader(new InputStreamReader(p.getInputStream(), StandardCharsets.UTF_8));
                 BufferedWriter out = new BufferedWriter(new OutputStreamWriter(p.getOutputStream(), StandardCharsets.UTF_8))) {
                while (true) {
                    String line = in.readLine(); if (line == null) throw new IllegalStateException("child exited unexpectedly: " + p.waitFor());
                    String[] words = line.split(" "); check(words.length == 2, "unexpected child output " + line);
                    int seq = Integer.parseInt(words[1]); boolean atTarget = seq == target;
                    if (words[0].equals("PREPARED")) {
                        if (atTarget && mode == 0) break;
                        highest = Math.max(highest, seq); send(out, "write");
                        if (atTarget && mode == 1) { Thread.sleep(random.nextInt(5)); break; }
                    } else if (words[0].equals("COMMITTED")) {
                        if (atTarget && mode == 2) break;
                        if (seq % 7 == 0 || atTarget && (mode == 3 || mode == 4)) {
                            send(out, "sync");
                            if (atTarget && mode == 3) { Thread.sleep(random.nextInt(3)); break; }
                        } else send(out, "next");
                    } else if (words[0].equals("SYNCED")) {
                        synced = Math.max(synced, seq);
                        if (atTarget && mode == 4) break;
                        send(out, "next");
                    } else throw new IllegalStateException("unexpected child stage " + line);
                }
                p.destroyForcibly(); check(p.waitFor(10, TimeUnit.SECONDS), "child did not end after forced stop");
            } finally { if (p.isAlive()) { p.destroyForcibly(); p.waitFor(10, TimeUnit.SECONDS); } }
            recovered = verify(path, seed, synced, highest);
            System.out.println("kill=" + round + " mode=" + mode + " target=" + target + " recovered=" + recovered);
        }
        verify(path, seed, synced, highest);
        System.out.println("OK D4CrashBatches kills=" + kills + " synced=" + synced + " recovered=" + recovered);
    }
}
