package bergdb.core;

import java.io.File;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;

/**
 * Review probe (bergdb 033, review of the start, 2026-11-28): other bytes at a meta block's
 * position that a start has taken, inside a record that it aborted, as the first block of the
 * stream after a cut. FileStreamPowerLossTester.testStartOnACutStreamThatBeginsAtAnInvalidBlock
 * (028-76) with one change: the kill that ends the stream at a stream file's first block, in
 * a record over it, leaves that file with other bytes in it, as 035-02 found a cut first
 * write of a new file to leave on APFS, where the test has no file.
 *
 * 1. A database on files is written until reclaim has cut once; then a record with a value
 *    of 20,000 random bytes is written over the next file's first meta block, at 'block'.
 * 2. The kill: the files from 'block' on are removed, and the file at 'block' is made with
 *    STALE bytes: "random" (300 random bytes), "older" (the first 300 bytes of an older file
 *    of this stream: a valid block of this database, of another position), "other" (the
 *    first 300 bytes of another database's file at the same position: a valid block with
 *    that position and another ID), "sameid" (as "other", with this database's ID, as a
 *    copy of the database has: F1), "v155" (as "older", with the meta block's version of
 *    release 2026.6), "none" (no file: 028-76's case, the control).
 * 3. Start 1 must take the stream: the record's header, before 'block', holds its check, so
 *    it is completed and aborted, with the other bytes in it.
 * 4. The database is written until reclaim's cut makes the file at 'block' the first, and
 *    stopped.
 * 5. Start 2. Every key must read as written.
 *
 * With WHERE "exact" the last record before the kill ends exactly at 'block' (it is
 * committed, and the kill comes before the block's bytes): the other bytes then follow a
 * whole record (the database is written without a retain duration until then, and has one
 * from start 1 on), start 1 refuses the tail with a BadTailException, and the probe does what
 * its message says, cuts the stream at its P, and starts again. P is 'block' + 128, the
 * position after the block, so the file at 'block' keeps its first 128 bytes, the other
 * bytes at the block's position.
 *
 * The forces are no-ops (StartChain.Io), so that reclaim's cuts come as soon as they are
 * decided and one of them lies in the file at 'block'; if none does, the probe says so.
 *
 * Usage, from java/ after build.sh:
 *   javac -d CLASSES -cp build/bergdb.jar PROBES/StartChain.java PROBES/StaleFirstBlockProbe.java
 *   java -ea -cp CLASSES:build/bergdb.jar bergdb.core.StaleFirstBlockProbe OUT STALE [WHERE]
 */
public class StaleFirstBlockProbe {
    static final long SEC = FileStreamPowerLossTester.SEC;

    public static void main(String[] args) throws Exception {
        File base = new File(args[0]);
        String stale = args[1];
        boolean exact = args.length > 2 && args[2].equals("exact");
        StartChain.rm(base);
        File dir = new File(base, "db");
        dir.mkdirs();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(SEC);
        Map<String, byte[]> model = new TreeMap<String, byte[]>();
        Random random = new Random(2078503);
        long time = SEC;
        long block = -1;
        long lastEnd = 0;       // the end of the last record that is in the model
        byte[] olderFile = null;
        FileStream stream = new FileStream(dir, new StartChain.Io(), true);
        // "exact": no retain duration yet, so no record carries reclaim's work, and a put's
        // record has the size of the put before it but for the value.
        Db db = exact ? Db.builder().testSetup(stream).clock(clock).start()
                : FileStreamPowerLossTester.start(stream, clock);
        if (exact) block = 400000;
        try {
            long end = 0;
            for (int i = 0; ; i++) {
                if (i >= 3000) throw new Error("no record over " + block);
                time += SEC / 10; clock.setTime(time);
                if (olderFile == null && end > 300000) {
                    olderFile = Files.readAllBytes(new File(dir, "00000000000002.bergdb").toPath());
                }
                if (block < 0 && stream.getFirstPos() > 0) block = (end / 200000 + 2) * 200000;
                if (exact && block > 0 && end + 9000 > block) {
                    // Two puts of one key: the first gives the record's size for 1,000 bytes,
                    // the second is sized to end at the block; if it does not, the next block
                    // is tried.
                    String key = FileStreamPowerLossTester.key(0);
                    byte[] v1 = new byte[1000]; random.nextBytes(v1);
                    Trans t1 = db.trans().put(key, v1).build();
                    db.execute(t1);
                    model.put(key, v1);
                    time += SEC / 10; clock.setTime(time);
                    long need = block - t1.nextPos - (t1.nextPos - t1.tpos);
                    if (need > -900 && need < 100000) {
                        byte[] v2 = new byte[1000 + (int) need]; random.nextBytes(v2);
                        Trans t2 = db.trans().put(key, v2).build();
                        db.execute(t2);
                        model.put(key, v2);
                        end = t2.nextPos;
                        lastEnd = t2.lastPos + 1;
                        if (t2.lastPos + 1 == block) break;
                    }
                    block = (end / 200000 + 2) * 200000;
                    continue;
                }
                boolean over = !exact && block > 0 && end + 15000 > block;
                byte[] value = new byte[over ? 20000 : 1000 + random.nextInt(1000)];
                random.nextBytes(value);
                String key = FileStreamPowerLossTester.key(i % 12);
                Trans t = db.trans().put(key, value).build();
                db.execute(t);
                end = t.nextPos;
                if (over) {
                    if (!(t.tpos < block - 8000 && t.lastPos > block + 4000)) throw new Error("not over the block");
                    break;          // Aborted by the kill: not in the model.
                }
                model.put(key, value);
                lastEnd = t.lastPos + 1;
            }
            db.sync(SyncLevel.ORDINARY);
        } finally { db.close(); }
        final String blockFile = String.format("%014d.bergdb", block / 100000);
        byte[] other = stale.equals("other") || stale.equals("sameid")
                ? otherDatabasesFile(base, blockFile, stale.equals("sameid")) : null;
        for (String name : StartChain.files(dir).keySet()) {
            if (name.compareTo(blockFile) >= 0) new File(dir, name).delete();
        }
        byte[] bytes = null;
        if (stale.equals("random")) { bytes = new byte[300]; new Random(1).nextBytes(bytes); }
        if (stale.equals("older")) bytes = Arrays.copyOf(olderFile, 300);
        if (stale.equals("v155")) { bytes = Arrays.copyOf(olderFile, 300); bytes[4] = (byte) 155; }
        if (stale.equals("other") || stale.equals("sameid")) bytes = Arrays.copyOf(other, 300);
        if (bytes != null) Files.write(new File(dir, blockFile).toPath(), bytes);
        System.out.println("stale " + stale + ": the kill ends the stream at " + block + (exact
                ? ", where its last record ends" : " in a record over it") + "; the file " + blockFile + (bytes == null ? " is not there" : " holds 300 other bytes"));

        time += SEC; clock.setTime(time);
        try {
            stream = new FileStream(dir, new StartChain.Io(), true);
            db = FileStreamPowerLossTester.start(stream, clock);
        } catch (RuntimeException e) {
            bergdb.storage.BadTailException bad = StartChain.badTail(e);
            String m = StartChain.messages(e);
            System.out.println("start 1 refused: " + m.substring(0, Math.min(m.length(), 330)));
            if (bad == null) return;
            System.out.println("its P is " + bad.getCutPos() + ": the stream cut there, " + (bad.getCutPos() >= block
                    ? "the file " + blockFile + " to " + (bad.getCutPos() - block) + " bytes"
                    : "before the file " + blockFile) + "; start 1 again");
            StartChain.cutAt(dir, bad.getCutPos());
            stream = new FileStream(dir, new StartChain.Io(), true);
            db = FileStreamPowerLossTester.start(stream, clock);
            try {
                check(db, model, "after the cut at P");
            } catch (Error lost) {
                System.out.println("THE CUT AT P LOST COMMITTED RECORDS: " + lost.getMessage() + "; the last"
                        + " committed record ended at " + lastEnd);
                db.close();
                return;
            }
        }
        System.out.println("start 1 ok");
        try {
            check(db, model, "start 1");
            for (int i = 0; stream.getFirstPos() < block; i++) {
                if (i >= 5000) throw new Error("no cut to " + block);
                time += SEC / 10; clock.setTime(time);
                byte[] value = new byte[1000 + random.nextInt(1000)]; random.nextBytes(value);
                String key = FileStreamPowerLossTester.key(i % 12);
                db.execute(db.trans().put(key, value).build());
                model.put(key, value);
            }
            if (stream.getFirstPos() != block) {
                System.out.println("the cut passed the file at " + block + ": nothing more to show");
                return;
            }
            db.sync(SyncLevel.ORDINARY);
        } finally { db.close(); }
        System.out.println("written on and stopped; reclaim's cut has made " + blockFile
                + " the stream's first file, " + StartChain.files(dir).size() + " files");

        time += SEC; clock.setTime(time);
        Map<String, byte[]> before = StartChain.files(dir);
        try {
            db = FileStreamPowerLossTester.start(new FileStream(dir, new StartChain.Io(), true), clock);
        } catch (RuntimeException e) {
            System.out.println("START 2 REFUSED: " + StartChain.messages(e));
            System.out.println("the files " + (FileStreamPowerLossTester.sameFiles(before, StartChain.files(dir))
                    ? "as before the start" : "changed by the start"));
            return;
        }
        try {
            check(db, model, "start 2");
            System.out.println("start 2 ok, every key as written");
        } finally { db.close(); }
        StartChain.rm(base);
    }

    static void check(Db db, Map<String, byte[]> model, String where) {
        for (Map.Entry<String, byte[]> e : model.entrySet()) {
            if (!Arrays.equals(e.getValue(), DbUtil.get(db, Long.MAX_VALUE, e.getKey()))) {
                throw new Error(where + ": " + e.getKey() + " reads another value");
            }
        }
    }

    /** Another database's file of the name 'blockFile': written with the same sizes until it has one. */
    static byte[] otherDatabasesFile(File base, String blockFile, boolean sameId) throws Exception {
        File dir = new File(base, "other");
        dir.mkdirs();
        CoreTestClock clock = new CoreTestClock();
        long time = SEC;
        clock.setTime(time);
        Random random = new Random(7);
        long need = Long.parseLong(blockFile.substring(0, 14)) * 100000 + 20000;
        // Reclaim off (the default): every file stays.
        // Another ID than the test setup's, which every database of the Core's tests has.
        try (Db db = Db.builder().testSetup(new FileStream(dir, new StartChain.Io(), true))
                .id(sameId ? DatabaseId.TEST_ID : DatabaseId.createRandom()).clock(clock).start()) {
            for (int i = 0; db.getStreamLength() < need; i++) {
                time += SEC / 10; clock.setTime(time);
                byte[] value = new byte[1000 + random.nextInt(1000)]; random.nextBytes(value);
                db.execute(db.trans().put(FileStreamPowerLossTester.key(i % 12), value).build());
            }
            db.sync(SyncLevel.ORDINARY);
        }
        return Files.readAllBytes(new File(dir, blockFile).toPath());
    }
}
