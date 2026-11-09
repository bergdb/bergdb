package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.Random;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * Test streams for StreamScan and the format document (bergdb 012-02): small workloads
 * on Db in directories, each with the test id and a test clock (10 ms a transaction), so
 * that two runs give the same bytes. Not a cross workload of 012-05; only streams that
 * show the format's cases.
 *
 * Usage: java -ea -cp CLASSES bergdb.core.MakeStreams OUTDIR [NAME...]
 * Makes OUTDIR/NAME for each NAME (all if none): fresh, n8, n30, restarts, big, setsd,
 * reclaim, deadline, crash (copies of n8 cut at chosen positions, cut-*), recovered (cut-*
 * opened and closed by Java). OUTDIR/NAME must not exist.
 */
public class MakeStreams {
    static final long STEP = 100 * 1000;            // 10 ms in clock units (100 ns)
    static final long T0 = 1000L * 1000 * 1000 * 1000 * 10;    // 2001-09-09 in clock units

    public static void main(String[] args) throws Exception {
        File out = new File(args[0]);
        out.mkdirs();
        String[] names = args.length > 1 ? java.util.Arrays.copyOfRange(args, 1, args.length)
                : new String[] {"fresh", "n8", "n30", "restarts", "big", "setsd", "reclaim",
                        "deadline", "crash"};
        for (String name : names) {
            File dir = new File(out, name);
            switch (name) {
            case "fresh": fresh(dir); break;
            case "n8": workload(dir, 8, 2000, 400, 200, 17); break;
            case "n30": workload(dir, 30, 5000, 400, 200, 18); break;
            case "restarts": workload(dir, 8, 3000, 300, 7, 19); break;
            case "big": big(dir); break;
            case "setsd": setsd(dir); break;
            case "reclaim": reclaim(dir); break;
            case "deadline": deadline(dir); break;
            case "crash": crash(out); break;
            default: throw new IllegalArgumentException(name);
            }
            System.out.println("made " + dir);
        }
    }

    static class Run {
        final File dir;
        final int nodeSize;
        final int sd;
        final TestClock clock = new TestClock();
        long time = T0;
        long retain = -1;
        boolean started = false;
        Db db;

        Run(File dir, int nodeSize, int sd) {
            this.dir = dir;
            this.nodeSize = nodeSize;
            this.sd = sd;
        }

        void start() throws IOException {
            if (clock.getTime() < time) clock.setTime(time);
            DbBuilder b = Db.builder().mainStream(new FileStream(dir)).clock(clock).testId()
                    .startupDistance(sd);
            if (nodeSize == 8) b.maxNodeSize8();
            else if (nodeSize == 14) b.maxNodeSize14();
            else if (nodeSize == 30) b.maxNodeSize30();
            else b.maxNodeSize62();
            db = b.start();
            // The retain duration once, after the first start, the creation's (OUTDIR/NAME
            // is new): the stream keeps it (bergdb 015-87; 022-01, D3). Forever by default.
            if (!started && retain > 0) db.setRetainDuration(retain);
            started = true;
        }

        void tick() {
            time += STEP;
            clock.setTime(time);
        }

        void close() {
            db.sync(SyncLevel.ORDINARY);
            db.close();
            db = null;
        }

        void restart() throws IOException {
            close();
            start();
        }
    }

    static void fresh(File dir) throws IOException {
        Run r = new Run(dir, 30, 20 * 1000 * 1000);
        r.start();
        r.close();
    }

    /** Puts and deletes on 300 keys, 1 to 4 a transaction; restarts every 'every'. */
    static void workload(File dir, int nodeSize, int sd, int count, int every, long seed)
            throws IOException {
        Run r = new Run(dir, nodeSize, sd);
        r.start();
        Random random = new Random(seed);
        for (int i = 1; i <= count; i++) {
            r.tick();
            r.db.execute(randomTrans(r.db, random, i, 300));
            if (i % every == 0 && i < count) {
                r.restart();
            }
        }
        r.close();
    }

    static Trans randomTrans(Db db, Random random, int i, int keys) {
        Trans.Builder b = db.trans();
        int n = 1 + random.nextInt(4);
        for (int j = 0; j < n; j++) {
            String key = "/k/" + random.nextInt(keys);
            if (random.nextInt(10) == 0) {
                b.delete(key);
            } else {
                b.put(key, "v" + i + "-" + j + "-" + "x".repeat(random.nextInt(40)));
            }
        }
        return b.build();
    }

    /** A value of 250 kB, so that its record crosses a meta block; an empty value; long keys. */
    static void big(File dir) throws IOException {
        Run r = new Run(dir, 30, 4000);
        r.start();
        r.tick();
        r.db.execute(r.db.trans().put("/a", "first").build());
        r.tick();
        byte[] large = new byte[250 * 1000];
        new Random(5).nextBytes(large);
        r.db.execute(r.db.trans().put("/large", large).build());
        r.tick();
        r.db.execute(r.db.trans().put("/empty", new byte[0]).put("/1234567", "seven")
                .put("/a/very/long/key/of/many/segments/ä", "utf-8").build());
        r.tick();
        r.db.execute(r.db.trans().delete("/a").build());
        r.close();
    }

    /** setStartupDistance: a dummy transaction, and nothing for the value in force. */
    static void setsd(File dir) throws IOException {
        Run r = new Run(dir, 30, 5000);
        r.start();
        Random random = new Random(21);
        for (int i = 1; i <= 50; i++) {
            r.tick();
            r.db.execute(randomTrans(r.db, random, i, 100));
        }
        r.tick();
        r.db.setStartupDistance(500 * 1000);
        r.tick();
        r.db.setStartupDistance(500 * 1000);        // In force: writes nothing.
        for (int i = 51; i <= 100; i++) {
            r.tick();
            r.db.execute(randomTrans(r.db, random, i, 100));
        }
        r.restart();
        for (int i = 101; i <= 120; i++) {
            r.tick();
            r.db.execute(randomTrans(r.db, random, i, 100));
        }
        r.close();
    }

    /** Reclaim: a retain duration of 2 s, 4,000 transactions of about 600 bytes. */
    static void reclaim(File dir) throws IOException {
        Run r = new Run(dir, 30, 10 * 1000);
        r.retain = 2 * 10 * 1000 * 1000L;
        r.start();
        Random random = new Random(23);
        for (int i = 1; i <= 4000; i++) {
            r.tick();
            Trans.Builder b = r.db.trans();
            b.put("/r/" + random.nextInt(500), "v" + i + "x".repeat(500 + random.nextInt(100)));
            r.db.execute(b.build());
            if (i % 1000 == 0) {
                r.restart();
            }
        }
        System.out.println("reclaim: first available pos " + r.db.getFirstAvailablePos()
                + ", iterations " + r.db.getReclaimIterationCount());
        r.close();
    }

    /**
     * The take's deadline (bergdb 012-02, 8.7), which the other streams never reach. A value
     * of 1.5 MB with a startup distance of 600,000: the share of the small records after it
     * is tiny, and the transactions that begin twice the startup distance before the end are
     * taken by the deadline. Then the startup distance up to 2,000,000, 2.4 MB of 3,000-byte
     * values, and down to 400,000, and the same with 5,000,000 and 12 MB of 30,000-byte
     * values: while the section's span is longer than twice the new setting, the deadline is
     * the span (007-07), and the take stops at transactions that twice the setting alone
     * would take. Also an empty transaction, which writes a record of its own.
     */
    static void deadline(File dir) throws IOException {
        Run r = new Run(dir, 8, 600 * 1000);
        r.start();
        Random random = new Random(29);
        r.tick();
        r.db.execute(r.db.trans().build());         // No key-value pairs.
        for (int i = 1; i <= 100; i++) {
            r.tick();
            r.db.execute(randomTrans(r.db, random, i, 300));
        }
        r.tick();
        byte[] large = new byte[1500 * 1000];
        new Random(31).nextBytes(large);
        r.db.execute(r.db.trans().put("/large", large).build());
        for (int i = 101; i <= 150; i++) {
            r.tick();
            r.db.execute(randomTrans(r.db, random, i, 300));
        }
        r.tick();
        r.db.setStartupDistance(2000 * 1000);
        for (int i = 151; i <= 950; i++) {
            r.tick();
            byte[] value = new byte[3000];
            random.nextBytes(value);
            r.db.execute(r.db.trans().put("/m/" + random.nextInt(300), value).build());
        }
        r.tick();
        r.db.setStartupDistance(400 * 1000);
        for (int i = 951; i <= 1250; i++) {
            r.tick();
            byte[] value = new byte[3000];
            random.nextBytes(value);
            r.db.execute(r.db.trans().put("/m/" + random.nextInt(300), value).build());
        }
        r.tick();
        r.db.setStartupDistance(5000 * 1000);
        for (int i = 1251; i <= 1650; i++) {
            r.tick();
            byte[] value = new byte[30 * 1000];
            random.nextBytes(value);
            r.db.execute(r.db.trans().put("/n/" + random.nextInt(300), value).build());
        }
        r.tick();
        r.db.setStartupDistance(400 * 1000);
        for (int i = 1651; i <= 1800; i++) {
            r.tick();
            byte[] value = new byte[30 * 1000];
            random.nextBytes(value);
            r.db.execute(r.db.trans().put("/n/" + random.nextInt(300), value).build());
        }
        r.close();
    }

    /**
     * Copies of n8 (made first if missing) cut at chosen positions of its stream: in the
     * first meta block, in a record's size, in a record's header, in a node, at the last
     * byte, at the meta block at 200,000 and in it; and the same copies after Java opened
     * and closed them (recovery's fill and nothing else).
     */
    static void crash(File out) throws Exception {
        File n8 = new File(out, "n8");
        if (!n8.exists()) {
            workload(n8, 8, 2000, 400, 200, 17);
        }
        File file = new File(n8, "00000000000000.bergdb");
        long length = file.length();
        long[] cuts = {60, 128 + 2, 128 + 20, 128 + 300, length - 1, length - 7};
        java.util.List<Long> all = new java.util.ArrayList<Long>();
        for (long c : cuts) all.add(c);
        File second = new File(n8, "00000000000002.bergdb");
        if (second.exists()) {
            all.add(200000L);
            all.add(200000L + 50);
            all.add(200000L + 128 + 3);
        }
        for (long cut : all) {
            File dir = new File(out, "cut-" + cut);
            copyCut(n8, dir, cut);
            File rec = new File(out, "recovered-" + cut);
            copyCut(n8, rec, cut);
            try {
                Run r = new Run(rec, 8, 2000);
                r.time = T0 + 1000 * STEP;
                r.start();
                r.close();
            } catch (RuntimeException e) {
                System.out.println("recovered-" + cut + ": start refused, " + e);
            }
        }
    }

    /** Copies the .bergdb files of 'from' to 'to', the stream cut at position 'cut'. */
    static void copyCut(File from, File to, long cut) throws IOException {
        to.mkdirs();
        File[] files = from.listFiles((d, n) -> n.endsWith(".bergdb"));
        java.util.Arrays.sort(files);
        for (File f : files) {
            long start = Long.parseLong(f.getName().substring(0, 14)) * 100000;
            if (start >= cut && start > 0) {
                continue;
            }
            File g = new File(to, f.getName());
            Files.copy(f.toPath(), g.toPath());
            if (start + f.length() > cut) {
                try (RandomAccessFile x = new RandomAccessFile(g, "rw")) {
                    x.setLength(cut - start);
                }
            }
        }
    }
}
