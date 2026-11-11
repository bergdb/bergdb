package bergdb.core;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.pub.util.Clock;

/**
 * The exporters of the cross workloads (bergdb 012-05, section 3, step 4): StreamDigest's
 * configurations in its four modes, through its own class (same package: its
 * constructor's lists of keys, values and times, and its lookups, draw for draw);
 * CoreSame's draws (bergdb 006-08); and Gen's random workloads. One JVM writes a whole
 * set's workloads.
 *
 * <pre>
 * Usage: java -cp CLASSES bergdb.core.Export OUTDIR SPEC...
 *   sd:NAME:MODE[:n=N]   StreamDigest's configuration NAME in MODE (plain, reads,
 *                        restarts, restarts-once: the retain duration set after the
 *                        first start only, which a restart keeps, bergdb 015-87; 022-01,
 *                        D3), with n transactions if given (a smaller run of the
 *                        same draws); writes OUTDIR/sd-NAME-MODE[-nN].wl and, beside it,
 *                        .digest: StreamDigest's own DIGEST line for the same run, which
 *                        the stream that Run makes must match from the decided cut
 *   coresame[:n=N][:plain]  CoreSame's workload, N transactions (6000); OUTDIR/coresame[-nN].wl;
 *                        with plain, without its retain duration and its restarts (its
 *                        syncs kept), for a writer that neither reclaims nor restarts
 *                        (012-09): OUTDIR/coresame-plain[-nN].wl
 *   gen:SEED[:K=V,...]   Gen's workload; OUTDIR/gen-SEED[-K-V...].wl
 *   del:SEED[:K=V,...]   GenDel's workload, the delete path of release 2026.4 (bergdb
 *                        022-07); OUTDIR/del-SEED[-K-V...].wl
 *   scale:KEYS           the scale workload: KEYS keys; OUTDIR/scale-KEYS.wl
 *   scaledel:KEYS        the scale workload of deletes (bergdb 022-07): KEYS keys put,
 *                        deleted but for one in a thousand, then those too, then one in
 *                        a hundred put again; OUTDIR/scaledel-KEYS.wl
 * Prints the path of each workload written.
 * </pre>
 */
public final class Export {
    public static void main(String[] args) throws IOException {
        File dir = new File(args[0]);
        dir.mkdirs();
        for (int i = 1; i < args.length; i++) {
            String[] parts = args[i].split(":");
            File f;
            switch (parts[0]) {
            case "sd":
                f = streamDigest(dir, parts[1], parts[2], parts.length > 3 ? parts[3] : null);
                break;
            case "coresame": {
                int n = 6000;
                boolean plain = false;
                for (int k = 1; k < parts.length; k++) {
                    if (parts[k].equals("plain")) {
                        plain = true;
                    } else {
                        n = Integer.parseInt(parts[k].substring(2));
                    }
                }
                f = coreSame(dir, n, plain);
                break;
            }
            case "scale":
                f = scale(dir, Long.parseLong(parts[1]));
                break;
            case "scaledel":
                f = scaleDel(dir, Long.parseLong(parts[1]));
                break;
            case "gen":
                f = gen(dir, Long.parseLong(parts[1]), parts.length > 2 ? parts[2] : null);
                break;
            case "del":
                f = del(dir, Long.parseLong(parts[1]), parts.length > 2 ? parts[2] : null);
                break;
            default:
                throw new IllegalArgumentException("unknown spec " + args[i]);
            }
            System.out.println(f.getPath());
        }
    }

    static PrintStream open(File f) throws IOException {
        return new PrintStream(new BufferedOutputStream(new FileOutputStream(f), 1 << 16),
                false, "UTF-8");
    }

    // ======== StreamDigest ========

    static File streamDigest(File dir, String name, String mode, String nOption)
            throws IOException {
        String[] config = null;
        for (String[] c : StreamDigest.CONFIGS) {
            if (c[0].equals(name)) config = c;
        }
        if (config == null) {
            throw new IllegalArgumentException("no StreamDigest configuration " + name);
        }
        if (!mode.equals("plain") && !mode.equals("reads") && !mode.equals("restarts")
                && !mode.equals("restarts-once")) {
            throw new IllegalArgumentException("mode " + mode);
        }
        String props = config[2];
        String suffix = "";
        if (nOption != null) {
            props += " " + nOption;         // the later n wins (StreamDigest's HashMap)
            suffix = "-n" + nOption.substring(2);
        }
        StreamDigest w = new StreamDigest(name, Long.parseLong(config[1]), props);
        File f = new File(dir, "sd-" + name + "-" + mode + suffix + ".wl");
        PrintStream out = open(f);
        out.println("bergdb-workload 1");
        out.println("# StreamDigest " + name + " seed=" + config[1] + " " + props + "; mode "
                + mode + " (bergdb 012-05)");
        out.println("set maxnode " + (w.maxNode == 0 ? 30 : w.maxNode));
        if (w.startupDistance > 0) {
            out.println("set sd " + w.startupDistance);
        }
        final boolean reads = !mode.equals("plain");
        final boolean restarts = mode.startsWith("restarts");
        final boolean setRetainAtRestart = !mode.equals("restarts-once");
        final String setRetain = w.retain > 0
                ? "setretain " + w.retain * Clock.UNITS_PER_SEC : null;
        if (setRetain != null) out.println(setRetain);
        StringBuilder line = new StringBuilder();
        for (int i = 0; i < w.n; i++) {
            line.setLength(0);
            line.append("t ").append(w.times[i]);
            String[] ks = w.keys.get(i);
            byte[][] vs = w.values.get(i);
            for (int j = 0; j < ks.length; j++) {
                if (vs[j] == StreamDigest.DELETED) {
                    line.append(" d ").append(keyWord(ks[j]));
                } else {
                    line.append(" p ").append(keyWord(ks[j])).append(" x:");
                    hex(line, vs[j]);
                }
            }
            out.println(line);
            boolean checkpoint = (i + 1) % w.every == 0 || i == w.n - 1;
            if (restarts && (i + 1) % w.every == 0 && i + 1 < w.n) {
                out.println("sync");
                out.println("restart");
                if (setRetain != null && setRetainAtRestart) out.println(setRetain);
            }
            if (reads && checkpoint) {
                lookups(w, i, out);
            }
        }
        out.println("sync");                // StreamDigest syncs after its last transaction
        out.close();

        // StreamDigest's own DIGEST line for the same run: the stream Run makes must match it.
        PrintStream digest = open(new File(dir, f.getName().replace(".wl", ".digest")));
        PrintStream sysout = System.out;
        System.setOut(new PrintStream(new java.io.ByteArrayOutputStream()));
        try {
            digest.println(w.run(mode));
        } finally {
            System.setOut(sysout);
        }
        digest.close();
        return f;
    }

    /**
     * StreamDigest.lookups after trans i, draw for draw: DbUtil.checksum's read of the latest
     * state (a check line), the latest value of every key /k/j (one get line), and the 300
     * random lookups (a get line each; one before the first available time prints
     * "unavailable", where StreamDigest skips it).
     */
    static void lookups(StreamDigest w, int i, PrintStream out) {
        out.println("check latest");
        StringBuilder all = new StringBuilder("get latest");
        Random rnd = new Random(w.seed * 31 + i);
        StringBuilder random = new StringBuilder();
        for (int j = 0; j < w.keyCount + 300; j++) {
            String k = "/k/" + (j < w.keyCount ? j : rnd.nextInt(w.keyCount));
            long t = j < w.keyCount ? Long.MAX_VALUE : w.times[rnd.nextInt(i + 1)] - rnd.nextInt(2);
            if (t == Long.MAX_VALUE) {
                all.append(' ').append(k);
            } else {
                random.append("get ").append(t).append(' ').append(k).append('\n');
            }
        }
        out.println(all);
        out.print(random);
    }

    /** A key as a workload word: '%', '#' and bytes outside 0x21 to 0x7e escaped. */
    static String keyWord(String ikey) {
        StringBuilder b = new StringBuilder();
        for (byte x : ikey.getBytes(java.nio.charset.StandardCharsets.UTF_8)) {
            int c = x & 0xff;
            if (c >= 0x21 && c <= 0x7e && c != '%' && c != '#') {
                b.append((char) c);
            } else {
                b.append('%').append(String.format("%02X", c));
            }
        }
        return b.toString();
    }

    static void hex(StringBuilder b, byte[] bytes) {
        for (byte x : bytes) {
            b.append(Character.forDigit((x >> 4) & 15, 16)).append(Character.forDigit(x & 15, 16));
        }
    }

    // ======== CoreSame (bergdb 006-08) ========

    /**
     * CoreSame's workload, draw for draw: a test clock 10 ms a transaction, the test id, a
     * startup distance of 20,000, a cache budget of 64,000, a retain duration of 5 s, a
     * restart (sync, close, start) after every 1,000 transactions, and its read of the
     * latest state at the end. With plain (bergdb 012-09), the same draws without the retain
     * duration and the restarts: no reclaim, one segment.
     */
    static File coreSame(File dir, int n, boolean plain) throws IOException {
        String name = "coresame" + (plain ? "-plain" : "");
        File f = new File(dir, n == 6000 ? name + ".wl" : name + "-n" + n + ".wl");
        PrintStream out = open(f);
        out.println("bergdb-workload 1");
        out.println("# CoreSame (bergdb 006-08), " + n + " transactions (bergdb 012-05)"
                + (plain ? ", without its retain duration and restarts (bergdb 012-09)" : ""));
        out.println("set maxnode 30");
        out.println("set sd 20000");
        out.println("set budget 64000");
        if (!plain) {
            out.println("set retain 50000000");
        }
        final long step = 100 * 1000;
        Random random = new Random(17);
        long time = 0;
        StringBuilder line = new StringBuilder();
        for (int i = 1; i <= n; i++) {
            time += step;
            line.setLength(0);
            line.append("t ").append(time);
            int ops = 1 + random.nextInt(4);
            for (int j = 0; j < ops; j++) {
                String key = "/k/" + random.nextInt(3000);
                if (random.nextInt(10) == 0) {
                    line.append(" d ").append(key);
                } else {
                    line.append(" p ").append(key).append(" s:v").append(i).append('-').append(j)
                            .append('-').append("x".repeat(random.nextInt(40)));
                }
            }
            out.println(line);
            if (i % 1000 == 0) {
                out.println("sync");
                if (!plain) {
                    out.println("restart");
                }
            }
        }
        out.println("check latest");
        out.close();
        return f;
    }

    // ======== Scale ========

    /**
     * The scale workload (bergdb 012-01, done item 7): KEYS keys /k/0 to /k/KEYS-1 put in
     * transactions of 100 consecutive keys, values of 40 bytes (r:KEY:40), the default node
     * size 30 and a startup distance of 50 MB; a restart halfway; then a second pass that
     * puts or deletes every 97th key, a check of the latest state, and gets.
     */
    static File scale(File dir, long keys) throws IOException {
        File f = new File(dir, "scale-" + keys + ".wl");
        PrintStream out = open(f);
        out.println("bergdb-workload 1");
        out.println("# The scale workload, " + keys + " keys (bergdb 012-05)");
        out.println("set maxnode 30");
        out.println("set sd 50000000");
        long time = 1000;
        StringBuilder line = new StringBuilder();
        for (long k = 0; k < keys; k += 100) {
            time += 10;
            line.setLength(0);
            line.append("t ").append(time);
            for (long j = k; j < Math.min(keys, k + 100); j++) {
                line.append(" p /k/").append(j).append(" r:").append(j).append(":40");
            }
            out.println(line);
            if (k / 100 == keys / 200) {
                out.println("sync");
                out.println("restart");
            }
        }
        for (long k = 0; k < keys; k += 97 * 50) {
            time += 10;
            line.setLength(0);
            line.append("t ").append(time);
            for (long j = k; j < Math.min(keys, k + 97 * 50); j += 97) {
                if (j % 2 == 0) {
                    line.append(" d /k/").append(j);
                } else {
                    line.append(" p /k/").append(j).append(" r:").append(j + keys).append(":40");
                }
            }
            out.println(line);
        }
        out.println("check latest");
        out.println("get latest /k/0 /k/1 /k/97 /k/" + (keys / 2) + " /k/" + (keys - 1));
        out.println("sync");
        out.close();
        return f;
    }

    /**
     * The scale workload of deletes (bergdb 022-07; the delete path of release 2026.4 on a
     * large database, 023-07, section 5): KEYS keys /k/000000000 to /k/(KEYS-1), nine
     * digits, put in transactions of 100 consecutive keys with values of 40 bytes, the
     * default node size 30 and a startup distance of 50 MB; a restart; a mass delete in
     * key order, 999 keys a transaction, every key but those whose number ends in 500;
     * a check, a restart (whose rerun has deletes); the kept keys deleted, 1,000 a
     * transaction, so that the database is empty and its root a segment leaf again; a
     * check; then every hundredth key put again, 100 a transaction; a check of the latest
     * state, and gets.
     */
    static File scaleDel(File dir, long keys) throws IOException {
        File f = new File(dir, "scaledel-" + keys + ".wl");
        PrintStream out = open(f);
        out.println("bergdb-workload 1");
        out.println("# The scale workload of deletes, " + keys + " keys (bergdb 022-07)");
        out.println("set maxnode 30");
        out.println("set sd 50000000");
        long time = 1000;
        StringBuilder line = new StringBuilder();
        for (long k = 0; k < keys; k += 100) {
            time += 10;
            line.setLength(0);
            line.append("t ").append(time);
            for (long j = k; j < Math.min(keys, k + 100); j++) {
                line.append(" p /k/").append(String.format("%09d", j)).append(" r:").append(j)
                        .append(":40");
            }
            out.println(line);
        }
        out.println("sync");
        out.println("restart");
        for (long k = 0; k < keys; k += 1000) {
            time += 10;
            line.setLength(0);
            line.append("t ").append(time);
            for (long j = k; j < Math.min(keys, k + 1000); j++) {
                if (j % 1000 != 500) {
                    line.append(" d /k/").append(String.format("%09d", j));
                }
            }
            out.println(line);
        }
        out.println("check latest");
        out.println("sync");
        out.println("restart");
        for (long k = 0; k < keys; k += 1000000) {
            time += 10;
            line.setLength(0);
            line.append("t ").append(time);
            for (long j = k + 500; j < Math.min(keys, k + 1000000); j += 1000) {
                line.append(" d /k/").append(String.format("%09d", j));
            }
            out.println(line);
        }
        out.println("check latest");
        for (long k = 0; k < keys; k += 10000) {
            time += 10;
            line.setLength(0);
            line.append("t ").append(time);
            for (long j = k; j < Math.min(keys, k + 10000); j += 100) {
                line.append(" p /k/").append(String.format("%09d", j)).append(" r:")
                        .append(j + keys).append(":40");
            }
            out.println(line);
        }
        out.println("check latest");
        out.println("get latest /k/000000000 /k/000000001 /k/000000100 /k/"
                + String.format("%09d", keys / 2) + " /k/" + String.format("%09d", keys - 1));
        out.println("sync");
        out.close();
        return f;
    }

    // ======== Gen ========

    static File gen(File dir, long seed, String options) throws IOException {
        Map<String, String> p = new TreeMap<String, String>();
        String name = "gen-" + seed;
        if (options != null) {
            for (String kv : options.split(",")) {
                int eq = kv.indexOf('=');
                p.put(kv.substring(0, eq), kv.substring(eq + 1));
                name += "-" + kv.substring(0, eq) + kv.substring(eq + 1);
            }
        }
        File f = new File(dir, name + ".wl");
        PrintStream out = open(f);
        bergdb.cross.Gen.generate(seed, p, out);
        out.close();
        return f;
    }

    static File del(File dir, long seed, String options) throws IOException {
        Map<String, String> p = new TreeMap<String, String>();
        String name = "del-" + seed;
        if (options != null) {
            for (String kv : options.split(",")) {
                int eq = kv.indexOf('=');
                p.put(kv.substring(0, eq), kv.substring(eq + 1));
                name += "-" + kv.substring(0, eq) + kv.substring(eq + 1);
            }
        }
        File f = new File(dir, name + ".wl");
        PrintStream out = open(f);
        bergdb.cross.GenDel.generate(seed, p, out);
        out.close();
        return f;
    }
}
