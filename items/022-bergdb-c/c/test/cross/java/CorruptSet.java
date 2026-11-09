package bergdb.core;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import bergdb.common.Bytes;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.Spos;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.RecoverableStream;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;
import bergdb.stream.MemoryStream;

/**
 * The corrupt-stream set of C's harness (bergdb 022-01, step 4, D4; 012-18, section 3.2,
 * "The new harnesses for C", and section 4, point 5): damaged copies of streams that the
 * release's Java writes, each as a database directory, which test/stress/corruptset.sh
 * starts with Java's Dump and C's bergdb-dump and compares. The streams and the damage are
 * the release's own, made by its classes; nothing of Java is changed. Two families:
 *
 * <ul>
 * <li><b>Harness 6.1's</b>, CorruptStreamTester (bergdb 018-02 to 018-08): its originals,
 * the configurations all, take and meta, and its copies by class, made by its own methods
 * with the random choices of its sample run (CorruptStreamTester.run(seed, false, ...)), so
 * that seed 1 gives testSample's copies: truncation (a cut at a length), flip (a byte xor
 * 0x01, 0x80 or 0xff), header (a record's size, time, startupPos, topPos, got-dirty entry or
 * count set), node (a node's byte or 4-byte field changed, its checksum made right), cut out
 * (a range of bytes removed). And the ten copies of testFound019_32, the damage that found
 * 019-32 (bases "found-..."), and the three of testFound021_11 (bergdb 021-11, release
 * 2026.4: a pointer that a start links by node id set to a version of a node of another
 * type; base "found-long-1", the configuration LONG's original of seed 1).</li>
 * <li><b>The cases of the release's refusal tests</b> (bases "case-..."), on the streams
 * that those tests write, with the tests' changes: DbTesterRestart's
 * testEnlargedRecordSizeRefused (015-72), testCorruptStartupPosRefused,
 * testCorruptGotDirtyIdRefused and testOlderTopPosRefused (015-75),
 * testMetaBlockLastTransPosRefused (019-34) and testVersionHighBytesRefused (019-01); and
 * StoredKeyNode.testRefusesBadKlongs's and StoredValueNode.testRefusesBadKey's changes
 * (019-32), made to every key node and every value or delete node of a stream of keys of
 * one to four segments, its checksum made right, the stream written with a startup
 * distance of 1,000,000 (no take) and of 300 (the take moves the startup position and
 * writes index nodes in later records).</li>
 * </ul>
 *
 * <p>Each copy of harness 6.1 is also checked by CorruptStreamTester.check, the tester's
 * own start of it, whose outcome the list shows ("tester: refused (StreamFormatException)",
 * "tester: holds all", ...; "tester: FAILED: ..." is a fault of Java that the tester finds).
 * A copy whose start makes recovery's zero fill pass the tester's 1 MB (014-01, a damaged
 * size that recovery fills up to, as much as 2 GB) is left out and counted, as the tester
 * counts it: both dumpers would write it, and Java's start then throws an
 * OutOfMemoryError for a record of 2 GB.</p>
 *
 * <pre>
 * Usage: java -ea -cp CLASSES bergdb.core.CorruptSet [-quick] OUT [SEED ...]
 *   -quick  the gate's set, about 60 copies: the refusal tests' cases and testFound019_32's
 *           and testFound021_11's copies only, the node tests' changes on the first and the
 *           last node that takes each
 *   SEED    the sample runs' seeds, 1 (testSample's) by default
 * Writes, for each original NAME, OUT/base/NAME/db (the stream as written), and for each
 * copy OUT/v/NAME/N/src, its damaged directory, with a and b, two copies of it for the two
 * dumpers; OUT/list.txt, one line a copy: "NAME/N KIND WHAT", with " known=ENTRY" where
 * CorruptStreamTester says that the damage may pass undetected by Frans's decision, and
 * " | tester: OUTCOME". Every original has the default node size, 30. The directories are
 * written without forces: they are test data.
 * Exit: 0; 1 if the tester failed a copy.
 *
 * Or: java -ea -cp CLASSES bergdb.core.CorruptSet -dump THREADS JOBFILE
 *   Java's dumps of the copies, on THREADS threads of one JVM: Batch's dump jobs ("dump OUT
 *   ARGS..." a line), each job's text to OUT, its standard error to OUT.err (a failed
 *   start's message, Dump's line), with the stack trace of an exception that leaves Dump
 *   (status 3, as Batch's), and its status to OUT.exit.
 * </pre>
 */
public final class CorruptSet {
    private final File out;
    private final PrintStream list;
    private final Map<String, Integer> counts = new TreeMap<String, Integer>();
    private int copies, fills, testerFailures;
    private boolean quick;
    private final ExecutorService pool = Executors.newFixedThreadPool(4, r -> {
        Thread t = new Thread(r, "CorruptSet");
        t.setDaemon(true);
        return t;
    });

    private CorruptSet(File out, PrintStream list) {
        this.out = out;
        this.list = list;
    }

    public static void main(String[] args) throws Exception {
        if (args.length == 3 && args[0].equals("-dump")) {
            dumps(Integer.parseInt(args[1]), new File(args[2]));
            return;
        }
        int i = 0;
        boolean quick = false;
        if (i < args.length && args[i].equals("-quick")) {
            quick = true;
            i++;
        }
        if (i >= args.length) {
            System.err.println("Usage: CorruptSet [-quick] OUT [SEED ...]");
            System.exit(2);
        }
        File out = new File(args[i++]);
        List<Long> seeds = new ArrayList<Long>();
        for (; i < args.length; i++) {
            seeds.add(Long.parseLong(args[i]));
        }
        if (seeds.isEmpty()) {
            seeds.add(1L);
        }
        out.mkdirs();
        long t0 = System.nanoTime();
        try (PrintStream list = new PrintStream(new BufferedOutputStream(
                new FileOutputStream(new File(out, "list.txt"))), false, "UTF-8")) {
            CorruptSet set = new CorruptSet(out, list);
            set.quick = quick;
            set.cases();
            set.found019_32();
            set.found021_11();
            if (!quick) {
                for (long seed : seeds) {
                    set.sample(seed);
                }
            }
            list.flush();
            for (Map.Entry<String, Integer> e : set.counts.entrySet()) {
                System.out.println("  " + e.getValue() + "\t" + e.getKey());
            }
            System.out.println("CorruptSet: " + set.copies + " copies; " + set.fills
                    + " left out, recovery's zero fill over 1 MB (014-01); the tester failed "
                    + set.testerFailures + "; " + (System.nanoTime() - t0) / 1000000 + " ms");
            set.pool.shutdownNow();
            System.exit(set.testerFailures == 0 ? 0 : 1);
        }
    }

    // ======== Java's dumps ========

    static void dumps(int threads, File jobs) throws Exception {
        long t0 = System.nanoTime();
        List<Future<Integer>> futures = new ArrayList<Future<Integer>>();
        ExecutorService pool = Executors.newFixedThreadPool(threads, r -> {
            Thread t = new Thread(r, "CorruptSet-dump");
            t.setDaemon(true);
            return t;
        });
        for (String line : Files.readAllLines(jobs.toPath(), StandardCharsets.UTF_8)) {
            line = line.trim();
            if (line.isEmpty() || line.startsWith("#")) continue;
            String[] w = line.split(" +");
            if (!w[0].equals("dump")) {
                throw new IllegalArgumentException("not a dump job: " + line);
            }
            futures.add(pool.submit(() -> dumpJob(w)));
        }
        int failed = 0;
        for (Future<Integer> f : futures) {
            if (f.get() != 0) failed++;
        }
        pool.shutdownNow();
        System.out.println("CorruptSet: " + futures.size() + " dumps, " + failed
                + " with a status other than 0, " + (System.nanoTime() - t0) / 1000000 + " ms");
    }

    private static int dumpJob(String[] w) throws IOException {
        String[] rest = Arrays.copyOfRange(w, 2, w.length);
        int status;
        try (PrintStream out = new PrintStream(new BufferedOutputStream(
                new FileOutputStream(w[1]), 1 << 16), false, "UTF-8");
                PrintStream err = new PrintStream(new FileOutputStream(w[1] + ".err"), true,
                        "UTF-8")) {
            try {
                status = bergdb.cross.Dump.main(rest, out, err);
            } catch (Throwable e) {
                e.printStackTrace(err);
                status = 3;
            }
        }
        Files.write(new File(w[1] + ".exit").toPath(),
                (status + "\n").getBytes(StandardCharsets.UTF_8));
        return status;
    }

    // ======== Writing ========

    /** Writes the original's stream as OUT/base/NAME/db. */
    private void base(String name, byte[] bytes) throws IOException {
        writeDir(new File(out, "base/" + name + "/db"), bytes, bytes.length);
    }

    /** Writes a copy as OUT/v/NAME/N/src, a and b, and its line of the list. */
    private void copy(String name, int n, CorruptStreamTester.Copy c, String tester)
            throws IOException {
        byte[] bytes = c.bytes.get();
        int length = c.length < 0 ? bytes.length : c.length;
        File d = new File(out, "v/" + name + "/" + n);
        File src = new File(d, "src");
        writeDir(src, bytes, length);
        copyDir(src, new File(d, "a"));
        copyDir(src, new File(d, "b"));
        list.println(name + "/" + n + " " + c.kind.replace(' ', '-') + " " + c.what
                + (c.known == null ? "" : " known=" + c.known)
                + (tester == null ? "" : " | tester: " + tester));
        Integer k = counts.get(c.kind);
        counts.put(c.kind, (k == null ? 0 : k) + 1);
        copies++;
    }

    /** The copies of one original, numbered from 0; without the tester's check. */
    private void copies(String name, List<CorruptStreamTester.Copy> list) throws IOException {
        int n = 0;
        for (CorruptStreamTester.Copy c : list) {
            copy(name, n++, c, null);
        }
    }

    /**
     * The copies of one of harness 6.1's originals, numbered from 0, each checked by the
     * tester first (on four threads, at most 60 s each, as its checkAll); a copy whose zero
     * fill passed 1 MB is left out.
     */
    private void checked(String name, CorruptStreamTester.Original o,
            List<CorruptStreamTester.Copy> list) throws IOException {
        List<Future<CorruptStreamTester.Outcome>> futures =
                new ArrayList<Future<CorruptStreamTester.Outcome>>();
        for (CorruptStreamTester.Copy c : list) {
            futures.add(pool.submit(() -> CorruptStreamTester.check(o, c)));
        }
        int n = 0;
        for (int i = 0; i < list.size(); i++) {
            CorruptStreamTester.Copy c = list.get(i);
            String tester;
            try {
                CorruptStreamTester.Outcome out = futures.get(i).get(60, TimeUnit.SECONDS);
                tester = out.failure == null ? out.kind : "FAILED: " + out.failure;
            } catch (Exception e) {
                tester = "FAILED: the check threw or did not end in 60 s, " + e;
            }
            if (tester.startsWith("known 014-01: recovery's zero fill passed")) {
                fills++;
                continue;
            }
            if (tester.startsWith("FAILED")) {
                testerFailures++;
                System.out.println("the tester failed " + name + "/" + n + ", " + c.kind + ", "
                        + c.what + ": " + tester);
            }
            copy(name, n++, c, tester);
        }
    }

    /** No force: the directories are test data, and a force costs milliseconds. */
    static final class NoForceIo extends FileStreamIo {
        protected void forceFile(File file, java.io.RandomAccessFile handle, Force why) {}

        protected void forceFile(File file, java.io.RandomAccessFile handle) {}

        protected void forceDirectory(File directory) {}
    }

    /** The first 'length' bytes of 'bytes' as a stream directory, through FileStream. */
    static void writeDir(File dir, byte[] bytes, int length) throws IOException {
        dir.mkdirs();
        FileStream s = new FileStream(dir, new NoForceIo(), false);
        try {
            if (length > 0) {
                s.append(bytes, 0, length);
            }
        } finally {
            s.close();
        }
    }

    static void copyDir(File from, File to) throws IOException {
        to.mkdirs();
        String[] names = from.list();
        Arrays.sort(names);
        for (String name : names) {
            Files.copy(new File(from, name).toPath(), new File(to, name).toPath());
        }
    }

    // ======== Harness 6.1's copies ========

    /**
     * CorruptStreamTester.run(seed, false, ...)'s copies, with its random choices in its
     * order: per configuration the truncations, the flips, the header fields and the node
     * fields of the last record and of a random one (every 7th node copy, from a random one),
     * and the cuts.
     */
    private void sample(long seed) throws IOException {
        Random r = new Random(seed);
        for (CorruptStreamTester.Config c : CorruptStreamTester.CONFIGS) {
            CorruptStreamTester.Original o = CorruptStreamTester.write(c,
                    seed * 31 + c.name.hashCode());
            String name = c.name + "-" + seed;
            base(name, o.bytes);
            List<CorruptStreamTester.Copy> all = new ArrayList<CorruptStreamTester.Copy>();
            CorruptStreamTester.truncations(o, CorruptStreamTester.sampleLengths(o, r, 60), all);
            List<Integer> positions = CorruptStreamTester.samplePositions(o, r, 60);
            int[] masks = CorruptStreamTester.MASKS;
            CorruptStreamTester.flips(o, positions, new int[] {masks[r.nextInt(masks.length)]},
                    all);
            List<CorruptStreamTester.Record> recs = new ArrayList<CorruptStreamTester.Record>();
            recs.add(o.records.get(o.records.size() - 1));
            recs.add(o.records.get(r.nextInt(o.records.size())));
            for (CorruptStreamTester.Record rec : recs) {
                CorruptStreamTester.headerFields(o, rec, all);
            }
            List<CorruptStreamTester.Copy> nodes = new ArrayList<CorruptStreamTester.Copy>();
            for (CorruptStreamTester.Record rec : recs) {
                CorruptStreamTester.nodeFields(o, rec, 40, new int[] {0x80},
                        new int[] {-8, 0x7ffffff8, 0x10000}, nodes);
            }
            for (int i = r.nextInt(7); i < nodes.size(); i += 7) {
                all.add(nodes.get(i));
            }
            CorruptStreamTester.cuts(o, r, 30, 30, all);
            checked(name, o, all);
        }
    }

    /** testFound019_32's rows, one copy each, as the test makes them. */
    private void found019_32() throws IOException {
        Object[][] rows = {
            {CorruptStreamTester.META, 3348004L, 365024, 104, 39, 0x80},
            {CorruptStreamTester.TAKE, 3552484L, 31880, 156, 37, 0x80},
            {CorruptStreamTester.TAKE, 4184729L, 2808, 72, 17, 0x01},
            {CorruptStreamTester.TAKE, 4184729L, 2808, 72, 24, 0x01},
            {CorruptStreamTester.TAKE, 4184729L, 2808, 32, 16, 0x01},
            {CorruptStreamTester.ALL, 729011L, 4528, 72, 16, 0x01},
            {CorruptStreamTester.ALL, 729042L, 128, 72, 16, 0x01},
            {CorruptStreamTester.META, 3980311L, 180568, 88, 56, 0x80},
            {CorruptStreamTester.TAKE, 4184729L, 2808, -1, 3151, 0xff},
            {CorruptStreamTester.TAKE, 4184729L, 2808, -1, 3336, 0xff},
        };
        Map<String, CorruptStreamTester.Original> originals =
                new TreeMap<String, CorruptStreamTester.Original>();
        Map<String, Integer> next = new TreeMap<String, Integer>();
        for (Object[] row : rows) {
            CorruptStreamTester.Config config = (CorruptStreamTester.Config) row[0];
            long seed = (Long) row[1];
            String name = "found-" + config.name + "-" + seed;
            CorruptStreamTester.Original o = originals.get(name);
            if (o == null) {
                o = CorruptStreamTester.write(config, seed);
                originals.put(name, o);
                base(name, o.bytes);
            }
            int offset = (Integer) row[3], at = (Integer) row[4], mask = (Integer) row[5];
            CorruptStreamTester.Copy c;
            if (offset < 0) {
                List<CorruptStreamTester.Copy> list = new ArrayList<CorruptStreamTester.Copy>();
                CorruptStreamTester.flips(o, Arrays.asList(at), new int[] {mask}, list);
                c = list.get(0);
            } else {
                CorruptStreamTester.Record rec = o.recordAt((Integer) row[2]);
                int[] node = null;
                for (int[] n : rec.nodes) {
                    if (n[0] == offset) node = n;
                }
                byte[] nb = Arrays.copyOfRange(rec.bytes, node[0], node[0] + node[1]);
                nb[at] ^= (byte) mask;
                c = nodeCopy(o, "found", rec, node, nb, "xor " + mask + " at its byte " + at);
            }
            Integer n = next.get(name);
            n = n == null ? 0 : n;
            next.put(name, n + 1);
            CorruptStreamTester.Outcome out = CorruptStreamTester.check(o, c);
            String tester = out.failure == null ? out.kind : "FAILED: " + out.failure;
            if (out.failure != null) {
                testerFailures++;
                System.out.println("the tester failed " + name + "/" + n + ": " + tester);
            }
            copy(name, n, c, tester);
        }
    }

    /**
     * testFound021_11's rows (bergdb 021-11, as Java's since release 2026.4), one copy each, as
     * the test makes them: in LONG's original of seed 1 (keys of three segments, so that key
     * nodes point to key nodes), a pointer that a start links by node id
     * (NodeCollection.linkToCanonical) set to a version of a node of another type, its node's
     * checksum made right. A row: the record, the node's offset in it, the pointer's byte in
     * the node, the position it is set to. Each refused at the start, the third by the check
     * of 005-57, which Java's Dump runs under -ea and C's bergdb-dump with -check.
     */
    private void found021_11() throws IOException {
        long[][] rows = {
            {32760, 880, 112, 35936},   // a key node's pointer 1 to the newest top node
            {35904, 32, 40, 7080},      // a top node's skip pointer 0 to a key node
            {32760, 880, 112, 27560},   // to an older top node version: 005-57's check (-ea)
        };
        CorruptStreamTester.Original o = CorruptStreamTester.write(CorruptStreamTester.LONG, 1);
        String name = "found-" + CorruptStreamTester.LONG.name + "-1";
        base(name, o.bytes);
        int n = 0;
        for (long[] row : rows) {
            CorruptStreamTester.Record rec = o.recordAt(row[0]);
            int[] node = null;
            for (int[] x : rec.nodes) {
                if (x[0] == row[1]) node = x;
            }
            byte[] nb = Arrays.copyOfRange(rec.bytes, node[0], node[0] + node[1]);
            Bytes.longToBytesLE(row[3], nb, (int) row[2]);
            CorruptStreamTester.Copy c = nodeCopy(o, "found", rec, node, nb,
                    "its byte " + row[2] + " set to " + row[3]);
            CorruptStreamTester.Outcome out = CorruptStreamTester.check(o, c);
            String tester = out.failure == null ? out.kind : "FAILED: " + out.failure;
            if (out.failure != null) {
                testerFailures++;
                System.out.println("the tester failed " + name + "/" + n + ": " + tester);
            }
            copy(name, n++, c, tester);
        }
    }

    /** As CorruptStreamTester.nodeCopy (private there): the checksum made right. */
    static CorruptStreamTester.Copy nodeCopy(CorruptStreamTester.Original o, String kind,
            CorruptStreamTester.Record rec, int[] node, byte[] nb, String what) {
        Bytes.ushortToBytesLE(NodeChecksum.sumWithZeroReplace(nb, 0, nb.length, 6), nb, 6);
        return CorruptStreamTester.patched(o, kind, what
                + ", checksum right, of the node at offset " + node[0] + " (size " + node[1]
                + ", type " + nb[4] + ") of the record at " + rec.tpos, rec, node[0], nb, null);
    }

    // ======== The refusal tests' cases ========

    /**
     * An original of a stream that a test wrote: its records walked. The Config's keys, a
     * seventh argument since bergdb 021-11, are KEYS, the tester's keys of 2026.3: such an
     * original is walked and patched, which use none of them, and never checked.
     */
    static CorruptStreamTester.Original original(String name, MemoryStream s) throws IOException {
        CorruptStreamTester.Original o = new CorruptStreamTester.Original(
                new CorruptStreamTester.Config(name, 1000000, 0, 0, 0, 0,
                        CorruptStreamTester.KEYS), 0);
        o.bytes = new byte[(int) s.getLength()];
        s.read(0, o.bytes, 0, o.bytes.length);
        CorruptStreamTester.walk(o);
        return o;
    }

    /** A copy with 'data' at the stream's position 'pos' (meta blocks counted). */
    static CorruptStreamTester.Copy at(CorruptStreamTester.Original o, String kind, String what,
            long pos, byte[] data) {
        return new CorruptStreamTester.Copy(kind, what, () -> {
            byte[] b = o.bytes.clone();
            System.arraycopy(data, 0, b, (int) pos, data.length);
            return b;
        }, -1, -1, null);
    }

    static byte[] le8(long x) {
        byte[] b = new byte[8];
        Bytes.longToBytesLE(x, b, 0);
        return b;
    }

    static byte[] le4(int x) {
        byte[] b = new byte[4];
        Bytes.intToBytesLE(x, b, 0);
        return b;
    }

    /** The tests' streams: /a, /b and /c at 10, 20 and 30 (the first n), distance 1,000,000. */
    static MemoryStream abc(int n, long[] tpos) {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(s).clock(clock).startupDistance(1000000).start()) {
            String[] keys = {"/a", "/b", "/c"};
            for (int i = 0; i < n; i++) {
                clock.setTime(10 * (i + 1));
                Trans t = db.trans().put(keys[i], "" + (i + 1)).build();
                db.execute(t);
                tpos[i] = t.tpos;
            }
        }
        return s;
    }

    private void cases() throws IOException {
        // DbTesterRestart.testEnlargedRecordSizeRefused (015-72): A's size over B's last byte.
        long[] tp = new long[3];
        CorruptStreamTester.Original o = original("enlarged", abc(3, tp));
        base("case-enlarged", o.bytes);
        List<CorruptStreamTester.Copy> list = new ArrayList<CorruptStreamTester.Copy>();
        list.add(at(o, "case", "testEnlargedRecordSizeRefused: size " + (tp[2] - tp[0])
                + " of the record at " + tp[0], tp[0], le4((int) (tp[2] - tp[0]))));
        copies("case-enlarged", list);

        // testCorruptStartupPosRefused (015-75): the last record's startupPos.
        tp = new long[2];
        o = original("startuppos", abc(2, tp));
        base("case-startuppos", o.bytes);
        list.clear();
        long c = tp[1];
        for (long sp : new long[] {-8, Long.MIN_VALUE, 4, 8, 120, c + 4, c + 8, c | (1L << 40)}) {
            list.add(at(o, "case", "testCorruptStartupPosRefused: startupPos " + sp
                    + " of the record at " + c, c + 16, le8(sp)));
        }
        copies("case-startuppos", list);

        // testCorruptGotDirtyIdRefused (015-75): an entry with a stream position, id 123456789;
        // every such entry of every record.
        tp = new long[3];
        o = original("gotdirty", abc(3, tp));
        base("case-gotdirty", o.bytes);
        list.clear();
        for (CorruptStreamTester.Record rec : o.records) {
            for (int e = 0; e < rec.gotDirtyCount; e++) {
                int off = rec.endMarker + 8 + 16 * e;
                long spos = Bytes.bytesToLongLE(rec.bytes, off + 8);
                if (Spos.isValid(spos) && !Spos.isVpos(spos)) {
                    list.add(CorruptStreamTester.patched(o, "case",
                            "testCorruptGotDirtyIdRefused: got-dirty id 123456789 (entry " + e
                            + ") of the record at " + rec.tpos, rec, off, le8(123456789L), null));
                }
            }
        }
        copies("case-gotdirty", list);

        // testOlderTopPosRefused (015-75): six transactions, distance 100; the last record's
        // topPos set to each older version of its top node.
        olderTopPos();

        // testMetaBlockLastTransPosRefused (019-34): the first meta block's byte 23 xor 0x80
        // and 0xff; a second meta block naming a position in the first, or after itself.
        tp = new long[2];
        MemoryStream s = abc(2, tp);
        o = original("metalast", s);
        base("case-metalast", o.bytes);
        list.clear();
        for (int mask : new int[] {0x80, 0xff}) {
            list.add(at(o, "case", "testMetaBlockLastTransPosRefused: byte 23 xor " + mask,
                    23, new byte[] {(byte) (o.bytes[23] ^ mask)}));
        }
        copies("case-metalast", list);
        MemoryStream large = s.copy();
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(large).clock(clock).startupDistance(1000000)
                .start()) {
            clock.setTime(30);
            db.execute(db.trans().put("/c", new byte[RecoverableStream.META_BLOCK_DISTANCE]));
        }
        o = original("metalast2", large);
        base("case-metalast2", o.bytes);
        list.clear();
        long block = RecoverableStream.META_BLOCK_DISTANCE;
        for (long spos : new long[] {10, block + RecoverableStream.META_BLOCK_SIZE}) {
            list.add(at(o, "case", "testMetaBlockLastTransPosRefused: the second meta block's "
                    + "last transaction at " + spos, block + 16, le8(spos)));
        }
        copies("case-metalast2", list);

        // testVersionHighBytesRefused (019-01): byte 6 or 7 of the meta block set to 1.
        s = new MemoryStream();
        clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("key1", "value1"));
        db.sync(SyncLevel.ORDINARY);
        db.close();
        o = original("version", s);
        base("case-version", o.bytes);
        list.clear();
        for (int offset : new int[] {6, 7}) {
            list.add(at(o, "case", "testVersionHighBytesRefused: byte " + offset
                    + " of the meta block set to 1", offset, new byte[] {1}));
        }
        copies("case-version", list);

        // StoredKeyNode.testRefusesBadKlongs and StoredValueNode.testRefusesBadKey (019-32),
        // on every node of a stream, written with startup distances of 1,000,000 and 300.
        for (int distance : new int[] {1000000, 300}) {
            nodeCases("case-nodes-" + distance, distance);
        }
    }

    private void olderTopPos() throws IOException {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(s).clock(clock).startupDistance(100).start()) {
            for (int i = 1; i <= 6; i++) {
                clock.setTime(10 * i);
                db.execute(db.trans().put("/k" + i, "" + i));
            }
        }
        CorruptStreamTester.Original o = original("oldertop", s);
        base("case-oldertop", o.bytes);
        CorruptStreamTester.Record last = o.records.get(o.records.size() - 1);
        long topPos = last.topPos();
        long id = -1;
        List<long[]> tops = new ArrayList<long[]>();     // {id, spos} of each top node
        for (CorruptStreamTester.Record rec : o.records) {
            for (int[] node : rec.nodes) {
                if (rec.bytes[node[0] + 4] == Node.TYPE_TOP_NODE) {
                    long spos = RecoverableStream.getSpos(rec.tpos, node[0]);
                    long nid = Bytes.bytesToLongLE(rec.bytes, node[0] + StoredTopNode.ID_OFFSET);
                    tops.add(new long[] {nid, spos});
                    if (spos == topPos) id = nid;
                }
            }
        }
        List<CorruptStreamTester.Copy> list = new ArrayList<CorruptStreamTester.Copy>();
        for (long[] t : tops) {
            if (t[0] == id && t[1] < topPos) {
                list.add(CorruptStreamTester.patched(o, "case", "testOlderTopPosRefused: topPos "
                        + t[1] + " (was " + topPos + ", top node " + id + ") of the record at "
                        + last.tpos, last, 24, le8(t[1]), null));
            }
        }
        if (list.isEmpty()) {
            throw new AssertionError("no older version of top node " + id);
        }
        copies("case-oldertop", list);
    }

    /** Keys of one to four segments (seven key bytes a segment), and deletes. */
    static final String[] NODE_KEYS = {"/a", "/-mykey.txt", "/d/g/h", "/x/-longer-key.txt",
            "/d/-a-key-of-four-segments", "/k1", "/k2"};

    /**
     * testRefusesBadKlongs's changes to every key node (each klong of type 2; each key
     * klong's pointer -8; the count one less and one more) and testRefusesBadKey's to every
     * value and delete node (the last segment's bit 63 or bit 0 set, or its length 7; the
     * first segment's length 6 when there are more), each with its checksum made right.
     * Quick: each change on the first and the last node that takes it.
     */
    private void nodeCases(String name, int distance) throws IOException {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Random r = new Random(17);
        try (Db db = Db.builder().testSetup(s).clock(clock).startupDistance(distance).start()) {
            for (int i = 1; i <= 12; i++) {
                clock.setTime(10 * i);
                Trans.Builder b = db.trans();
                b.put("/n", "" + i);
                for (int k = 0; k < 2; k++) {
                    String key = NODE_KEYS[(i + 3 * k) % NODE_KEYS.length];
                    if (i > 6 && k == 1) {
                        b.delete(key);
                    } else {
                        byte[] v = new byte[1 + r.nextInt(40)];
                        r.nextBytes(v);
                        b.put(key, v);
                    }
                }
                db.execute(b.build());
            }
        }
        CorruptStreamTester.Original o = original(name, s);
        base(name, o.bytes);
        List<CorruptStreamTester.Copy> list = new ArrayList<CorruptStreamTester.Copy>();
        List<String> tags = new ArrayList<String>();      // each copy's change
        for (CorruptStreamTester.Record rec : o.records) {
            for (int[] node : rec.nodes) {
                byte[] orig = Arrays.copyOfRange(rec.bytes, node[0], node[0] + node[1]);
                byte type = orig[4];
                if (type == Node.TYPE_KEY_NODE) {
                    int count = Bytes.bytesToShortLE(orig, 17);
                    for (int i = 0; i < count; i++) {
                        byte[] nb = orig.clone();
                        long k = Bytes.bytesToLongLE(nb, 32 + 8 * i);
                        Bytes.longToBytesLE((k & ~0xc000000000000000L) | (2L << 62), nb,
                                32 + 8 * i);
                        list.add(nodeCopy(o, "case", rec, node, nb,
                                "testRefusesBadKlongs: klong " + i + " of type 2"));
                        tags.add("type");
                        if (Klong.getIntType(k) == Klong.INT_TYPE_KEY) {
                            nb = orig.clone();
                            Bytes.longToBytesLE(-8L, nb, 32 + 8 * count + 8 * i);
                            list.add(nodeCopy(o, "case", rec, node, nb,
                                    "testRefusesBadKlongs: the pointer of klong " + i + " -8"));
                            tags.add("pointer");
                        }
                    }
                    for (int d : new int[] {-1, 1}) {
                        byte[] nb = orig.clone();
                        nb[17] = (byte) (count + d);
                        nb[18] = (byte) ((count + d) >>> 8);
                        list.add(nodeCopy(o, "case", rec, node, nb,
                                "testRefusesBadKlongs: the count " + (count + d) + ", not "
                                + count));
                        tags.add("count" + d);
                    }
                } else if (type == Node.TYPE_VALUE || type == Node.TYPE_DELETE) {
                    int keyAt = type == Node.TYPE_VALUE
                            ? 28 + Bytes.bytesToIntLE(orig, 20) : 24;
                    int segments = Bytes.bytesToIntLE(orig, keyAt - 4) / 8;
                    int lastAt = keyAt + 8 * (segments - 1);
                    long lastSeg = Bytes.bytesToLongLE(orig, lastAt);
                    long[][] changes = {
                        {lastAt, lastSeg ^ (1L << 63)},
                        {lastAt, lastSeg | 1},
                        {lastAt, lastSeg | (7 << 3)},
                        {keyAt, Bytes.bytesToLongLE(orig, keyAt) & ~(1L << 3)},
                    };
                    String[] whats = {"the last segment's bit 63", "the last segment's bit 0",
                            "the last segment's length 7", "the first segment's length 6"};
                    for (int j = 0; j < changes.length; j++) {
                        if (j == 3 && segments < 2) continue;
                        int pos = (int) changes[j][0];
                        if (Bytes.bytesToLongLE(orig, pos) == changes[j][1]) continue;
                        byte[] nb = orig.clone();
                        Bytes.longToBytesLE(changes[j][1], nb, pos);
                        list.add(nodeCopy(o, "case", rec, node, nb, "testRefusesBadKey: "
                                + whats[j] + " (a key of " + segments + " segments)"));
                        tags.add("key" + j);
                    }
                }
            }
        }
        if (quick) {
            List<CorruptStreamTester.Copy> some = new ArrayList<CorruptStreamTester.Copy>();
            for (int i = 0; i < list.size(); i++) {
                String tag = tags.get(i);
                if (tags.indexOf(tag) == i || tags.lastIndexOf(tag) == i) {
                    some.add(list.get(i));
                }
            }
            list = some;
        }
        copies(name, list);
    }
}
