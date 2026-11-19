package bergdb.core;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.*;

import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.RecoverableStream;
import bergdb.stream.MemoryStream;

/**
 * The byte comparison of bergdb item 001 (items/001-lean-model-levels-3-4,
 * 01-plan.md, section 8.9), written 2026-10-16. Runs the deterministic
 * workloads of RestartInvariance's configurations in level2.sh (step 4) and
 * level3.sh (step 3, reclaim on) and prints the SHA-256 of each stream:
 * sha256all from its first position, sha256 from the cut that reclaim
 * decided (getFirstAvailablePos; 0 without reclaim).
 *
 * A change that must not change the records gives the same digests as the
 * build before it. Compare with a preserved build (performance.sh build
 * LABEL) by running one compiled copy of this class, the preserved build's,
 * against both jars:
 *
 *   B=java/build/perf/builds/l34-base/java/build
 *   java -cp $B/bergdb.jar:$B/stress bergdb.core.StreamDigest all > base.txt
 *   java -cp java/build/bergdb.jar:$B/stress bergdb.core.StreamDigest all > cur.txt
 *   java -cp java/build/bergdb.jar:$B/stress bergdb.core.StreamDigest compare base.txt cur.txt
 *
 * So it uses only API that the item does not change: DbBuilder.testSetup,
 * Db, Trans, MemoryStream, CoreTestClock and DbUtil. It must not use
 * RestartInvariance, which reaches internals that change.
 *
 * Each configuration runs in four modes, which must give the same stream
 * from the decided cut (sha256). The physical cut may differ between them:
 * it waits for durability, and a restart syncs (bergdb 011-04, Level 3):
 *   plain     the transactions only;
 *   reads     as RestartInvariance's run A: at every checkpoint (after every
 *             'every' transactions, and at the end) a checksum of the latest
 *             state and the lookups of RestartInvariance.lookupViolations;
 *   restarts  as its run B: the same, with a restart (sync, stop, copy the
 *             stream, start) before each checkpoint but the last.
 *   restarts-once  as restarts, but the retain duration is set after the first
 *             start only: a restart must keep it, as it is kept in the stream
 *             (bergdb 015-87). Before 015-87 a start forgot it, and the l3-*
 *             configurations differed from plain in this mode.
 * The workloads are those of RestartInvariance, draw for draw, so the stream
 * lengths equal those it prints ("stream length A=... B=...").
 *
 * Usage: java -cp ... bergdb.core.StreamDigest all|quick|NAME...
 *        java -cp ... bergdb.core.StreamDigest compare FILE FILE
 *   all        every configuration below; quick: all but l2-default-100MB.
 *   NAME       configurations by name, as printed.
 *   compare    compares the DIGEST lines of two outputs on the fields that reclaim
 *              decides: length, firstAvailablePos, firstAvailableTime and sha256; prints
 *              DIGESTS IDENTICAL or the differences, and exits with 1 if they differ.
 *              The physical cut's fields, firstPos and sha256all, wait for durability
 *              and differ between runs of the same jar (in l3-node62: firstPos 8000000
 *              or 9000000, bergdb 005-79); where the decided fields are the same, a
 *              PHYSICAL CUT line shows them, as information (bergdb 015-08).
 * Properties:
 *   modes=M,M  the modes to run (default plain,reads,restarts,restarts-once).
 *   metamask=O:N  the digests take bytes O to O+N-1 of every meta block as zero: for a
 *              change that writes a field there and nothing else, compared with the build
 *              before it (bergdb 005-50: metamask=44:2, the node size).
 */
public class StreamDigest {
    static final byte[] DELETED = null;

    /**
     * The configurations: name, seed, RestartInvariance's properties. The n of the full
     * gates (INV_N=2000), as in level2.sh step 4 and level3.sh step 3.
     */
    static final String[][] CONFIGS = {
        {"l2-sd100", "1", "del=1 n=2000 sd=100 keys=500 every=100 long=1 bigtrans=20"},
        {"l2-sd1000-node8", "1", "del=1 n=2000 sd=1000 keys=500 every=100 maxnode=8 long=1 bigtrans=10"},
        {"l2-sd10000-node14", "1", "del=1 n=2000 sd=10000 keys=500 every=200 maxnode=14 long=1"},
        {"l2-sd100000-node62", "1",
            "del=1 n=2000 sd=100000 keys=1000 every=200 maxnode=62 bigtrans=40 valsize=400"},
        {"l2-every1", "1", "del=1 n=400 sd=500 keys=100 every=1 long=1"},
        {"l2-idle-1", "1", "del=1 n=400 sd=100 keys=100 every=1 long=1 empty=30 nodel=20"},
        {"l2-idle-2", "2", "del=1 n=400 sd=100 keys=100 every=1 long=1 empty=30 nodel=20"},
        {"l2-default-100MB", "1", "sd=0 n=12000 keys=3000 valsize=8000 every=4000 del=1"},
        {"l3-every1", "1", "del=1 retain=1 n=1000 sd=500 keys=100 every=1 long=1"},
        {"l3-node8", "1", "del=1 retain=1 n=2000 sd=1000 keys=500 every=50 maxnode=8 long=1 bigtrans=10"},
        {"l3-node14", "1", "del=1 retain=1 n=2000 sd=3000 keys=50 every=37 maxnode=14"},
        {"l3-node62", "1",
            "del=1 retain=1 n=2000 sd=10000 keys=1000 every=100 maxnode=62 bigtrans=40 valsize=400"},
    };

    final String name;
    final long seed;
    final int n, keyCount, startupDistance, maxNode, every, valsize, bigTrans, empty, nodel, retain;
    final boolean del, longKeys;
    final long timeScale;

    final List<String[]> keys = new ArrayList<String[]>();      // per transaction
    final List<byte[][]> values = new ArrayList<byte[][]>();    // per transaction, null = delete
    final long[] times;

    /** The workload of RestartInvariance's constructor, draw for draw. */
    StreamDigest(String name, long seed, String props) {
        this.name = name;
        this.seed = seed;
        Map<String, String> p = new HashMap<String, String>();
        for (String kv : props.trim().split("\\s+")) {
            int eq = kv.indexOf('=');
            p.put(kv.substring(0, eq), kv.substring(eq + 1));
        }
        n = intProp(p, "n", 3000);
        keyCount = intProp(p, "keys", 500);
        startupDistance = intProp(p, "sd", 10000);
        maxNode = intProp(p, "maxnode", 0);
        every = intProp(p, "every", 250);
        valsize = intProp(p, "valsize", 40);
        del = "1".equals(p.get("del"));
        longKeys = "1".equals(p.get("long"));
        bigTrans = intProp(p, "bigtrans", 0);
        empty = intProp(p, "empty", 0);
        nodel = intProp(p, "nodel", 0);
        retain = intProp(p, "retain", 0);
        timeScale = retain > 0 ? Clock.UNITS_PER_SEC / 100 : 1;

        Random rnd = new Random(seed);
        times = new long[n];
        long time = 10;
        for (int i = 0; i < n; i++) {
            time += (1 + rnd.nextInt(20)) * timeScale;
            times[i] = time;
            int idle = empty + nodel > 0 ? rnd.nextInt(100) : 100;
            if (idle < empty + nodel) {
                int c = idle < empty ? 0 : 1 + rnd.nextInt(3);
                String[] ks = new String[c];
                for (int j = 0; j < c; j++) ks[j] = "/missing/" + i + "/" + j;
                keys.add(ks);
                values.add(new byte[c][]);      // DELETED
                continue;
            }
            int opCount = 1 + rnd.nextInt(3);
            if (bigTrans > 0 && rnd.nextInt(10) == 0) {
                opCount = 1 + rnd.nextInt(bigTrans);
            }
            LinkedHashMap<String, byte[]> ops = new LinkedHashMap<String, byte[]>();
            for (int o = 0; o < opCount; o++) {
                String prefix = longKeys && rnd.nextBoolean() ? "/long/" : "/k/";
                String k = prefix + rnd.nextInt(keyCount);
                if (del && rnd.nextInt(5) == 0) {
                    ops.put(k, DELETED);
                } else {
                    byte[] v = new byte[1 + rnd.nextInt(valsize)];
                    rnd.nextBytes(v);
                    ops.put(k, v);
                }
            }
            keys.add(ops.keySet().toArray(new String[0]));
            values.add(ops.values().toArray(new byte[0][]));
        }
    }

    static int intProp(Map<String, String> p, String key, int def) {
        String v = p.get(key);
        return v == null ? def : Integer.parseInt(v);
    }

    Db start(MemoryStream stream, CoreTestClock clock) {
        return start(stream, clock, true);
    }

    /** Starts the database; sets the retain duration of the configuration if 'setRetain'. */
    Db start(MemoryStream stream, CoreTestClock clock, boolean setRetain) {
        DbBuilder b = Db.builder().testSetup(stream).clock(clock);
        if (maxNode == 8) b.maxNodeSize8();
        if (maxNode == 14) b.maxNodeSize14();
        if (maxNode == 30) b.maxNodeSize30();
        if (maxNode == 62) b.maxNodeSize62();
        Db db = b.start();
        // Nothing written if in force (bergdb 028-13).
        if (startupDistance > 0) db.setStartupDistance(startupDistance);
        if (setRetain && retain > 0) db.setRetainDuration(retain * Clock.UNITS_PER_SEC);
        return db;
    }

    /** One run in the given mode; returns its DIGEST line. */
    String run(String mode) {
        boolean reads = !mode.equals("plain");
        boolean restarts = mode.startsWith("restarts");
        boolean setRetainAtRestart = !mode.equals("restarts-once");
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = start(stream, clock);
        int lookups = 0;
        for (int i = 0; i < n; i++) {
            clock.setTime(times[i]);
            Trans.Builder b = db.trans();
            String[] ks = keys.get(i);
            byte[][] vs = values.get(i);
            for (int j = 0; j < ks.length; j++) {
                if (vs[j] == DELETED) b.delete(ks[j]);
                else b.put(ks[j], vs[j]);
            }
            db.execute(b.build());

            boolean checkpoint = (i + 1) % every == 0 || i == n - 1;
            if (restarts && (i + 1) % every == 0 && i + 1 < n) {
                db.sync(SyncLevel.ORDINARY);
                db.stop();
                stream = stream.copy();
                db = start(stream, clock, setRetainAtRestart);
            }
            if (reads && checkpoint) {
                DbUtil.checksum(db);
                lookups += lookups(db, i);
            }
        }
        db.sync(SyncLevel.ORDINARY);
        long cut = Math.max(stream.getFirstPos(), db.getFirstAvailablePos());
        String line = "DIGEST " + name + " " + mode + " length=" + stream.getLength()
                + " firstPos=" + stream.getFirstPos()
                + " firstAvailablePos=" + db.getFirstAvailablePos()
                + " firstAvailableTime=" + db.getFirstAvailableLookupTime()
                + " sha256all=" + digest(stream, stream.getFirstPos())
                + " sha256=" + digest(stream, cut);
        db.stop();
        System.out.println("  " + name + " " + mode + ": " + lookups + " lookups");
        return line;
    }

    /**
     * The lookups of RestartInvariance.lookupViolations after trans i, draw for draw: the
     * latest value of every key /k/j, and 300 lookups at random historical times. Results
     * are not checked here; RestartInvariance does that.
     */
    int lookups(Db db, int i) {
        Random rnd = new Random(seed * 31 + i);
        int count = 0;
        for (int j = 0; j < keyCount + 300; j++) {
            String k = "/k/" + (j < keyCount ? j : rnd.nextInt(keyCount));
            long t = j < keyCount ? Long.MAX_VALUE : times[rnd.nextInt(i + 1)] - rnd.nextInt(2);
            if (t < db.getFirstAvailableLookupTime()) continue;
            DbUtil.get(db, t, k);
            count++;
        }
        return count;
    }

    /** The bytes of every meta block that the digests take as zero: offset and count, or null. */
    static final int[] MASK = parseMask(System.getProperty("metamask"));

    static int[] parseMask(String prop) {
        if (prop == null) return null;
        String[] on = prop.split(":");
        return new int[] {Integer.parseInt(on[0]), Integer.parseInt(on[1])};
    }

    /** Zeroes the bytes of MASK in the meta blocks that buf holds: chunk bytes from pos. */
    static void mask(byte[] buf, long pos, int chunk) {
        if (MASK == null) return;
        final long d = RecoverableStream.META_BLOCK_DISTANCE;
        for (long block = pos / d * d; block < pos + chunk; block += d) {
            long from = Math.max(pos, block + MASK[0]);
            long to = Math.min(pos + chunk, block + MASK[0] + MASK[1]);
            for (long p = from; p < to; p++) {
                buf[(int) (p - pos)] = 0;
            }
        }
    }

    /** SHA-256 of the stream from position 'from' to its end, in hex; see MASK. */
    static String digest(MemoryStream s, long from) {
        MessageDigest md;
        try {
            md = MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException e) {
            throw new RuntimeException(e);
        }
        byte[] buf = new byte[65536];
        long len = s.getLength();
        try {
            for (long pos = from; pos < len; pos += buf.length) {
                int chunk = (int) Math.min(buf.length, len - pos);
                s.read(pos, buf, 0, chunk);
                mask(buf, pos, chunk);
                md.update(buf, 0, chunk);
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        StringBuilder b = new StringBuilder();
        for (byte x : md.digest()) b.append(String.format("%02x", x & 0xff));
        return b.toString();
    }

    /** The DIGEST lines of an output, by configuration and mode. */
    static Map<String, String> readDigests(String file) throws IOException {
        Map<String, String> result = new TreeMap<String, String>();
        BufferedReader r = new BufferedReader(new FileReader(file));
        try {
            for (String line; (line = r.readLine()) != null; ) {
                if (!line.startsWith("DIGEST ")) continue;
                String[] parts = line.split(" ");
                result.put(parts[1] + " " + parts[2], line);
            }
        } finally {
            r.close();
        }
        return result;
    }

    /** The fields of a DIGEST line that compare checks: those reclaim decides. */
    static final String[] DECIDED = {"length", "firstAvailablePos", "firstAvailableTime", "sha256"};

    /** The physical cut's fields: they depend on timing, so compare only shows them. */
    static final String[] PHYSICAL = {"firstPos", "sha256all"};

    /** The name=value fields of a DIGEST line. */
    static Map<String, String> fields(String line) {
        Map<String, String> result = new HashMap<String, String>();
        String[] parts = line.split(" ");
        for (int i = 3; i < parts.length; i++) {
            int eq = parts[i].indexOf('=');
            if (eq > 0) result.put(parts[i].substring(0, eq), parts[i].substring(eq + 1));
        }
        return result;
    }

    /** "name x -> y" for each of the fields 'names' that differ, joined by ", "; "" if none. */
    static String differences(Map<String, String> x, Map<String, String> y, String[] names) {
        StringBuilder b = new StringBuilder();
        for (String name : names) {
            if (Objects.equals(x.get(name), y.get(name))) continue;
            if (b.length() > 0) b.append(", ");
            b.append(name + " " + x.get(name) + " -> " + y.get(name));
        }
        return b.toString();
    }

    static int compare(String file1, String file2) throws IOException {
        Map<String, String> a = readDigests(file1), b = readDigests(file2);
        Set<String> all = new TreeSet<String>(a.keySet());
        all.addAll(b.keySet());
        int same = 0, differ = 0, physical = 0;
        for (String key : all) {
            String x = a.get(key), y = b.get(key);
            if (x == null || y == null) {
                differ++;
                System.out.println("MISSING " + key + " in " + (x == null ? file1 : file2));
                continue;
            }
            Map<String, String> fx = fields(x), fy = fields(y);
            String decided = differences(fx, fy, DECIDED);
            if (!decided.isEmpty()) {
                differ++;
                System.out.println("DIFFERENT " + key + ": " + decided);
                System.out.println("  " + file1 + ": " + x);
                System.out.println("  " + file2 + ": " + y);
                continue;
            }
            same++;
            String cut = differences(fx, fy, PHYSICAL);
            if (!cut.isEmpty()) {
                physical++;
                System.out.println("PHYSICAL CUT " + key + " (timing, not compared): " + cut);
            }
        }
        String info = "; of the identical, the physical cut differs in " + physical + ")";
        if (differ == 0 && same > 0) {
            System.out.println("DIGESTS IDENTICAL (" + same + " of " + same + info);
            return 0;
        }
        System.out.println("DIGESTS DIFFER (" + differ + " of " + all.size() + info);
        return 1;
    }

    public static void main(String[] args) throws IOException {
        if (args.length == 3 && args[0].equals("compare")) {
            System.exit(compare(args[1], args[2]));
        }
        if (args.length == 0) {
            System.out.println("Usage: StreamDigest all|quick|NAME... | compare FILE FILE");
            System.exit(2);
        }
        Set<String> wanted = new LinkedHashSet<String>(Arrays.asList(args));
        String[] modes = System.getProperty("modes", "plain,reads,restarts,restarts-once").split(",");
        if (MASK != null) {
            System.out.println("METAMASK " + MASK[0] + ":" + MASK[1]);
        }
        int configs = 0, modeDiffs = 0;
        for (String[] c : CONFIGS) {
            boolean take = wanted.contains("all") || wanted.contains(c[0])
                    || (wanted.contains("quick") && !c[0].equals("l2-default-100MB"));
            if (!take) continue;
            configs++;
            StreamDigest w = new StreamDigest(c[0], Long.parseLong(c[1]), c[2]);
            System.out.println("CONFIG " + c[0] + " seed=" + c[1] + " " + c[2]);
            String first = null;
            for (String mode : modes) {
                long t0 = System.nanoTime();
                String line = w.run(mode);
                System.out.println(line);
                System.out.println("  " + c[0] + " " + mode + ": "
                        + (System.nanoTime() - t0) / 1000000 + " ms");
                String sha = line.substring(line.indexOf(" sha256=") + 8);
                if (first == null) {
                    first = sha;
                } else if (!first.equals(sha)) {
                    modeDiffs++;
                    System.out.println("MODES DIFFER: " + c[0] + " " + mode
                            + " differs from " + modes[0] + " after the decided cut");
                }
            }
        }
        System.out.println("Done: " + configs + " configurations, " + modes.length + " modes; "
                + (modeDiffs == 0 ? "the modes give the same stream" : modeDiffs + " mode differences"));
    }
}
