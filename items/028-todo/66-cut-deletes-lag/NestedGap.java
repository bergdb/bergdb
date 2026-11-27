package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;

/**
 * bergdb 028-66's review (2026-11-27): every subset of a cut's deletes, and every subset of
 * the deletes of the start that follows (the files before the gap and the stream's files
 * before the cut, one batch), checked at the level of a database start, exhaustively.
 *
 * A database (Core, FileStream with per-append forces) is written while the cut's thread is
 * held at its first delete, so that the cuts take several files off the list and none is
 * deleted; then, with the writer idle after a sync, the directory's stream files are copied:
 * the image of a power loss right after the cut's thread issued none of its deletes. For
 * every subset of the files that the cuts took off, the image without them is started
 * (plain FileStream), every key read against the model, and the start must leave no gap
 * (level 1). For some of those images, the files that the start deletes (its batch) are
 * found from a start on a copy; then every subset of that batch is removed from the level-1
 * image and the result started and checked the same way (level 2, a power loss in the
 * start's own batch). Prints NESTED GAP OK and the counts, or NESTED GAP FAILED.
 *
 * Usage, from java/ after build.sh (a probe in bergdb.core goes before the jar):
 *   javac -d CLASSES -cp build/bergdb.jar ../items/028-todo/66-cut-deletes-lag/NestedGap.java
 *   java -ea -cp CLASSES:build/bergdb.jar bergdb.core.NestedGap [LEVEL2_SAMPLES [off]]
 * With "off", the database is written with per-append forcing off (the images are of what
 * was written, as after a kill, not of what was forced).
 */
public class NestedGap {
    static final long SEC = FileStreamPowerLossTester.SEC;

    /** Holds the cut's thread at its deletes while 'held' is set. */
    static class GateIo extends FileStreamIo {
        final Object gate = new Object();
        boolean held;

        void hold() { synchronized (gate) { held = true; } }
        void release() { synchronized (gate) { held = false; gate.notifyAll(); } }

        protected boolean delete(File file) throws IOException {
            synchronized (gate) {
                while (held) {
                    try {
                        gate.wait();
                    } catch (InterruptedException e) {
                        throw new IOException(e);
                    }
                }
            }
            return super.delete(file);
        }
    }

    static int started = 0, gapImages = 0, refused = 0;

    public static void main(String[] args) throws Exception {
        int samples = args.length > 0 ? Integer.parseInt(args[0]) : 6;
        boolean forceAppends = args.length < 2 || !"off".equals(args[1]);
        File dir = Files.createTempDirectory("nested-gap-").toFile();
        Map<String, byte[]> model = new TreeMap<String, byte[]>();
        Map<String, byte[]> snapshot;
        long firstPos;
        long lastTime;
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(SEC);
        GateIo io = new GateIo();
        FileStream stream = new FileStream(dir, io, forceAppends);
        Db db = FileStreamPowerLossTester.start(stream, clock);
        io.hold();
        Random random = new Random(28066);
        long time = SEC;
        try {
            for (int i = 0; i < 20000 && stream.getFirstPos() < 1400000; i++) {
                time += SEC / 10; clock.setTime(time);
                byte[] value = new byte[1000 + random.nextInt(1000)]; random.nextBytes(value);
                String key = FileStreamPowerLossTester.key(i % 12);
                db.execute(db.trans().put(key, value).build());
                model.put(key, value);
            }
            db.sync(SyncLevel.ORDINARY);
            firstPos = stream.getFirstPos();
            snapshot = FileStreamPowerLossTester.streamFiles(dir);
            lastTime = time;
        } finally {
            io.release();
            db.close();
            FileStreamPowerLossTester.remove(dir);
        }
        List<String> taken = new ArrayList<String>();
        for (String name : snapshot.keySet()) {
            if (Long.parseLong(name.substring(0, 14)) * 100000 < firstPos) taken.add(name);
        }
        System.out.println("per-append forces " + (forceAppends ? "on" : "off") + "; snapshot: "
                + snapshot.size() + " files, first position " + firstPos
                + ", taken off and not deleted: " + taken);
        if (taken.size() < 3) {
            System.out.println("NESTED GAP FAILED: fewer than 3 files taken off");
            System.exit(1);
        }

        int n = taken.size();
        Random pick = new Random(66);
        List<Integer> level2 = new ArrayList<Integer>();
        for (int mask = 1; mask < (1 << n); mask++) level2.add(mask);
        java.util.Collections.shuffle(level2, pick);
        level2 = level2.subList(0, Math.min(samples, level2.size()));
        int level1 = 0, level2Images = 0;
        for (int mask = 0; mask < (1 << n); mask++) {
            Map<String, byte[]> files = new TreeMap<String, byte[]>(snapshot);
            for (int i = 0; i < n; i++) if ((mask & (1 << i)) != 0) files.remove(taken.get(i));
            String what = "level 1, deleted " + names(taken, mask);
            Map<String, byte[]> after = check(files, model, lastTime, what);
            level1++;
            if (!level2.contains(mask)) continue;
            // The start's batch: the files of 'files' that its start deleted.
            List<String> batch = new ArrayList<String>();
            for (String name : files.keySet()) if (!after.containsKey(name)) batch.add(name);
            if (batch.size() > 12) batch = batch.subList(0, 12);
            for (int m2 = 1; m2 < (1 << batch.size()); m2++) {
                Map<String, byte[]> f2 = new TreeMap<String, byte[]>(files);
                for (int i = 0; i < batch.size(); i++) {
                    if ((m2 & (1 << i)) != 0) f2.remove(batch.get(i));
                }
                check(f2, model, lastTime, what + "; level 2, the start's batch " + batch
                        + ", deleted " + names(batch, m2));
                level2Images++;
            }
        }
        System.out.println("level 1 images " + level1 + ", level 2 images " + level2Images
                + "; started " + started + ", with a gap " + gapImages + ", refused " + refused);
        System.out.println("NESTED GAP OK");
    }

    static String names(List<String> list, int mask) {
        List<String> out = new ArrayList<String>();
        for (int i = 0; i < list.size(); i++) if ((mask & (1 << i)) != 0) out.add(list.get(i));
        return out.toString();
    }

    /** Starts 'files', checks every key, closes; returns the files after the start. */
    static Map<String, byte[]> check(Map<String, byte[]> files, Map<String, byte[]> model,
            long lastTime, String what) throws Exception {
        File d = Files.createTempDirectory("nested-gap-image-").toFile();
        try {
            for (Map.Entry<String, byte[]> e : files.entrySet()) {
                Files.write(new File(d, e.getKey()).toPath(), e.getValue());
            }
            boolean gap = FileStreamPowerLossTester.hasGap(d);
            if (gap) gapImages++;
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(lastTime + SEC);
            Db db;
            try {
                db = FileStreamPowerLossTester.start(new FileStream(d), clock);
            } catch (RuntimeException e) {
                refused++;
                System.out.println("NESTED GAP FAILED: " + what + ": refused: " + e);
                System.exit(1);
                return null;
            }
            try {
                for (Map.Entry<String, byte[]> e : model.entrySet()) {
                    if (!Arrays.equals(e.getValue(), DbUtil.get(db, Long.MAX_VALUE, e.getKey()))) {
                        System.out.println("NESTED GAP FAILED: " + what + ": key " + e.getKey());
                        System.exit(1);
                    }
                }
                db.checkNodes();
            } finally {
                db.close();
            }
            started++;
            if (FileStreamPowerLossTester.hasGap(d)) {
                System.out.println("NESTED GAP FAILED: " + what + ": a gap after the start");
                System.exit(1);
            }
            return FileStreamPowerLossTester.streamFiles(d);
        } finally {
            FileStreamPowerLossTester.remove(d);
        }
    }
}
