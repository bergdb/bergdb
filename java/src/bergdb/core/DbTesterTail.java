package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.storage.BadTailException;
import bergdb.storage.RecoverableStream;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

/**
 * Bergdb 028-67 (Frans, 2026-11-27: C1 and C3): a start on a stream whose tail, from a
 * position Z on, holds bytes that are not its own records, as a kill of the process during an
 * append can leave them within the last stream file's length on APFS (bergdb 035-02): zeros,
 * an older stream file's bytes at the same offsets and at others, another database's bytes
 * at the same positions and at others, and a record's size from other bytes. Each start
 * either takes the records that end before the first byte that differs from the stream's own
 * (Z'), and none after, or refuses the stream with a BadTailException, which names the cause
 * and P, before anything is written; the stream cut at P then starts with those records. A
 * meta block holds its own position and the database ID, and a record's header a check of
 * the ID, its position and its fields (C3), so another file's blocks and records are not
 * taken: 031-07's probe found two stale tails on main (17c7c7db) that took another database's
 * records whole (028-67's S1), which testS1Refused makes again.
 *
 * @author Frans Lundberg
 */
public class DbTesterTail {

    /** Another database's ID than testSetup()'s (DatabaseId.TEST_ID). */
    static final DatabaseId OTHER_ID = DatabaseId.createFromBytes(new byte[] {
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16});

    /** What a start of a copy gave, for the counts of a test. */
    static final class Counts {
        int started;
        int refused;
        int copies;

        public String toString() {
            return copies + " copies: " + started + " started, " + refused
                    + " refused and started after the cut";
        }
    }

    // ======== MemoryStream: CorruptStreamTester's workloads ========

    /**
     * Stale tails on CorruptStreamTester's sample workloads (all, take, meta), from every
     * page of 4,096 bytes on: zeros; another database's bytes at the same positions and 4,096
     * bytes after; the stream's own bytes from 4,096 and 200,000 bytes before, as an older
     * stream file of the database leaves them at other offsets and at the same ones. Each
     * copy is started (check()).
     */
    @Nano
    private static void testStaleTailsSample() {
        Counts counts = new Counts();
        for (CorruptStreamTester.Config cfg : CorruptStreamTester.CONFIGS) {
            staleTails(cfg, 20261127L, 4096, counts);
        }
        Assert.assertTrue(counts.toString(), counts.refused > 0 && counts.copies > 300);
    }

    /**
     * As testStaleTailsSample(), as 031-07's probe made them: from every 512 bytes, on the
     * full set of workloads (with long), the probe's seed.
     */
    @Nano("f")
    private static void testStaleTailsFull() {
        Counts counts = new Counts();
        for (CorruptStreamTester.Config cfg : CorruptStreamTester.FULL_CONFIGS) {
            staleTails(cfg, 20768, 512, counts);
        }
        Assert.assertTrue(counts.toString(), counts.refused > 0 && counts.copies > 2000);
    }

    private static void staleTails(CorruptStreamTester.Config cfg, long seed, int step,
            Counts counts) {
        CorruptStreamTester.Original o = CorruptStreamTester.write(cfg,
                seed * 31 + cfg.name.hashCode());
        CorruptStreamTester.Original other = CorruptStreamTester.write(cfg,
                seed * 31 + cfg.name.hashCode() + 7777, OTHER_ID);
        final int n = o.bytes.length;
        List<Object[]> sources = new ArrayList<Object[]>();
        sources.add(new Object[] {"zeros", new byte[n]});
        sources.add(new Object[] {"another database, the same positions",
                shifted(other.bytes, 0, n)});
        sources.add(new Object[] {"another database, 4096 after", shifted(other.bytes, 4096, n)});
        for (int d : new int[] {4096, RecoverableStream.META_BLOCK_DISTANCE}) {
            if (d < n) {
                sources.add(new Object[] {"its own bytes from " + d + " before",
                        shifted(o.bytes, -d, n)});
            }
        }
        for (Object[] s : sources) {
            for (int z = step; z < n; z += step) {
                byte[] bytes = o.bytes.clone();
                System.arraycopy((byte[]) s[1], z, bytes, z, n - z);
                check(o, bytes, z, cfg + ", seed " + seed + ", " + s[0] + ", Z " + z, counts);
            }
        }

        // A record's size from other bytes, at the start of each record after the last meta
        // block, which the start's walk reads: a size of 1 GB, which the recovery zero-filled
        // before 028-67 (014-01, 005-83's case), the rest the stream's own. (Before that
        // block, the size is damage in the middle of the stream, not a tail.)
        final long lastBlock = (n - RecoverableStream.META_BLOCK_SIZE)
                / RecoverableStream.META_BLOCK_DISTANCE * RecoverableStream.META_BLOCK_DISTANCE;
        for (CorruptStreamTester.Record rec : o.records) {
            if (rec.tpos < lastBlock + RecoverableStream.META_BLOCK_SIZE || rec.tpos < 4096) {
                continue;       // from the first page on, where a kill's other bytes begin
            }
            byte[] bytes = o.bytes.clone();
            Bytes.intToBytesLE(1 << 30, bytes, (int) rec.tpos);
            check(o, bytes, (int) rec.tpos, cfg + ", a size of 1 GB at " + rec.tpos, counts);
        }
    }

    /** 'n' bytes, byte i of them source[i - d], or 0 outside 'source'. */
    private static byte[] shifted(byte[] source, int d, int n) {
        byte[] b = new byte[n];
        for (int i = 0; i < n; i++) {
            int j = i - d;
            b[i] = j >= 0 && j < source.length ? source[j] : 0;
        }
        return b;
    }

    /**
     * Starts 'bytes', o's stream with other bytes from 'z' on: it must hold o's state after
     * the transactions whose records end before Z', the first position from 'z' at which
     * 'bytes' differ from o's own, or refuse with a BadTailException, the start having
     * appended nothing; the copy cut at its P must then hold that state. A start that takes a
     * record of another place or database, or refuses otherwise, fails.
     */
    private static void check(CorruptStreamTester.Original o, byte[] bytes, int z, String what,
            Counts counts) {
        int zz = z;
        while (zz < bytes.length && bytes[zz] == o.bytes[zz]) {
            zz++;
        }
        final int k = zz == bytes.length ? o.n : o.committed(zz);
        counts.copies++;
        CorruptStreamTester.CopyStream stream = new CorruptStreamTester.CopyStream(bytes,
                bytes.length);
        long cut;
        try {
            Db db = start(o, stream);
            try {
                String diff = CorruptStreamTester.compare(db, o.config, o.states.get(k),
                        Long.MAX_VALUE);
                Assert.assertTrue(what + ": started, " + diff, diff == null);
            } finally {
                db.close();
            }
            counts.started++;
            return;
        } catch (BadTailException e) {
            cut = e.getCutPos();
            Assert.assertEquals(what + ": appended", 0, stream.appended());
            String m = e.getMessage();
            Assert.assertTrue(what + ": " + m, m.contains("A kill of the process during an "
                    + "append") && m.contains("keep a copy of its files, then cut the stream at "
                    + cut + ":") && m.contains("The start has written nothing."));
            Assert.assertTrue(what + ": P " + cut, cut > RecoverableStream.META_BLOCK_SIZE
                    && cut <= bytes.length);
        } catch (RuntimeException e) {
            throw new AssertionError(what + ": the start threw " + e, e);
        }

        CorruptStreamTester.CopyStream cutStream = new CorruptStreamTester.CopyStream(bytes,
                (int) cut);
        Db db = start(o, cutStream);
        try {
            String diff = CorruptStreamTester.compare(db, o.config, o.states.get(k),
                    Long.MAX_VALUE);
            Assert.assertTrue(what + ": cut at " + cut + ", " + diff, diff == null);
        } finally {
            db.close();
        }
        counts.refused++;
    }

    private static Db start(CorruptStreamTester.Original o, CorruptStreamTester.CopyStream s) {
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(CorruptStreamTester.TIME_STEP * (o.n + 5));
        return Db.builder().testSetup(s).clock(clock).audit(0).start();
    }

    /**
     * 028-67's S1 case, as 031-07's probe made it (inventory, section 4.5): another
     * database's stream of the same workload from 512 on, where the record of the first
     * transaction begins in both. Its records have the same sizes and times, and their
     * pointers name the first three records, of the same bytes in both but for their headers'
     * checks; on main before 028-67 such a start took the other database's records and
     * answered its values (workloads all and long). The record at 512 holds the check of the
     * other database's ID: refused at P = 512, nothing written, and the stream cut there
     * holds no transaction of the workload. The probe's two databases had the same ID,
     * testSetup()'s; another ID is what separates two real databases (DatabaseId).
     */
    @Nano
    private static void testS1Refused() {
        for (CorruptStreamTester.Config cfg : new CorruptStreamTester.Config[] {
                CorruptStreamTester.ALL, CorruptStreamTester.LONG}) {
            final long seed = 20768 * 31 + cfg.name.hashCode();
            CorruptStreamTester.Original o = CorruptStreamTester.write(cfg, seed);
            CorruptStreamTester.Original other = CorruptStreamTester.write(cfg, seed + 7777,
                    OTHER_ID);
            Assert.assertEquals(cfg + ": a record at 512", 512L, o.tpos[1]);
            Assert.assertEquals(cfg + ": the other's at 512", 512L, other.tpos[1]);
            byte[] bytes = o.bytes.clone();
            System.arraycopy(other.bytes, 512, bytes, 512,
                    Math.min(bytes.length, other.bytes.length) - 512);
            CorruptStreamTester.CopyStream stream = new CorruptStreamTester.CopyStream(bytes,
                    Math.min(bytes.length, other.bytes.length));
            try {
                start(o, stream).close();
                throw new AssertionError(cfg + ": started with another database's records");
            } catch (BadTailException e) {
                Assert.assertEquals(cfg + ": " + e.getMessage(), 512L, e.getCutPos());
                Assert.assertTrue(e.getMessage(), e.getMessage().startsWith(
                        "The header of the record at 512 is not one of this database's"));
                Assert.assertEquals(cfg + ": appended", 0, stream.appended());
            }
            Db db = start(o, new CorruptStreamTester.CopyStream(bytes, 512));
            try {
                Assert.assertTrue(cfg + ": the counter",
                        DbUtil.get(db, Long.MAX_VALUE, CorruptStreamTester.COUNTER) == null);
            } finally {
                db.close();
            }
        }
    }

    // ======== MemoryStream: torn last records ========

    /**
     * A torn last record is completed with zeros only after its header is found to be one
     * (028-67, C1): the record of a transaction of 100 kB, cut 1,000 bytes after its start,
     * whose size field is set to 1 GB, as other bytes there give it, is refused at its
     * position, nothing written (before 028-67 the recovery appended 1 GB of zeros first);
     * with its own size it is completed and aborted. A header that the end of the stream
     * cuts, 5 to 31 bytes of it, is completed when its size and format byte are one the writer
     * writes, and refused when the format byte is another; 1 to 4 bytes as before.
     */
    @Nano
    private static void testTornRecordHeaderChecked() throws IOException {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long last;
        try (Db db = Db.builder().testSetup(s).clock(clock).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("a", "a-value"));
            clock.setTime(20);
            Trans t = db.trans().put("b", new byte[100 * 1000]).build();
            db.execute(t);
            last = t.tpos;
        }

        // The size of 1 GB.
        MemoryStream m = s.copy();
        m.truncate(last + 1000);
        MemoryStream.TestAccess.write(m, le4(1 << 30), last);
        try {
            Db.builder().testSetup(m).clock(clock).start().close();
            throw new AssertionError("started");
        } catch (BadTailException e) {
            Assert.assertEquals(e.getMessage(), last, e.getCutPos());
            Assert.assertTrue(e.getMessage(), e.getMessage().startsWith("The record at " + last
                    + ", of size " + (1 << 30) + ", which the end of the stream cuts, has a "
                    + "header that is not one"));
        }
        Assert.assertEquals("nothing written", last + 1000, m.getLength());

        // Its own size: completed, aborted, and the database has a only.
        m = s.copy();
        m.truncate(last + 1000);
        try (Db db = Db.builder().testSetup(m).clock(clock).start()) {
            Assert.assertTrue(DbUtil.get(db, Long.MAX_VALUE, "a") != null);
            Assert.assertTrue(DbUtil.get(db, Long.MAX_VALUE, "b") == null);
        }

        // The header cut by the end of the stream.
        for (int cutIn = 1; cutIn < StoredTrans.HEADER_SIZE; cutIn++) {
            m = s.copy();
            m.truncate(last + cutIn);
            try (Db db = Db.builder().testSetup(m).clock(clock).start()) {
                Assert.assertTrue("cut " + cutIn, DbUtil.get(db, Long.MAX_VALUE, "b") == null);
            }
            if (cutIn >= 5) {
                m = s.copy();
                m.truncate(last + cutIn);
                MemoryStream.TestAccess.write(m, new byte[] {7}, last + 4);
                try {
                    Db.builder().testSetup(m).clock(clock).start().close();
                    throw new AssertionError("started with format 7 in a cut header, " + cutIn);
                } catch (BadTailException e) {
                    Assert.assertEquals(e.getMessage(), last, e.getCutPos());
                }
                Assert.assertEquals("nothing written", last + cutIn, m.getLength());
            }
        }
    }

    private static byte[] le4(int v) {
        byte[] b = new byte[4];
        Bytes.intToBytesLE(v, b, 0);
        return b;
    }

    /**
     * A meta block of another database (another ID) or of another place (its own position
     * another, as a block of an older stream file of the same database at the same offset in
     * a new file) is not valid (028-67, C3): the start passes over it to the block before,
     * as over a block that a crash cut. Here the stream's last block, of four, is replaced by
     * such blocks (the last: one of an older file at the same offset, which names a record of
     * that file): the start takes the stream whole, its records all checked from the block
     * before, and writes nothing. Before 028-67 the start took each of them as the last valid
     * block (035-02, section 10.2).
     */
    @Nano
    private static void testOtherBlocksPassedOver() throws IOException {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(s).clock(clock).start()) {
            for (int i = 0; db.getStreamLength() < 3 * RecoverableStream.META_BLOCK_DISTANCE
                    + 50000; i++) {
                clock.setTime(10 + i);
                db.execute(db.trans().put("k" + i, new byte[1000 + i % 100]));
            }
        }
        final long block = 3L * RecoverableStream.META_BLOCK_DISTANCE;
        byte[] own = new byte[RecoverableStream.META_BLOCK_SIZE];
        s.read(block, own, 0, own.length);

        byte[] otherId = own.clone();
        otherId[30] ^= 1;
        byte[] otherPlace = own.clone();
        Bytes.longToBytesLE(block - RecoverableStream.META_BLOCK_DISTANCE, otherPlace, 46);
        byte[] olderFile = own.clone();
        Bytes.longToBytesLE(block - 2 * RecoverableStream.META_BLOCK_DISTANCE, olderFile, 46);
        Bytes.longToBytesLE(block - 2 * RecoverableStream.META_BLOCK_DISTANCE - 50000,
                olderFile, 16);
        for (byte[] b : new byte[][] {otherId, otherPlace, olderFile}) {
            MemoryStream m = s.copy();
            MemoryStream.TestAccess.write(m, b, block);
            final long length = m.getLength();
            try (Db db = Db.builder().testSetup(m).clock(clock).start()) {
                Assert.assertTrue(DbUtil.get(db, Long.MAX_VALUE, "k0") != null);
                Assert.assertEquals(length, m.getLength());
                Assert.assertTrue("from the block before",
                        db.internal().nodeStream().getLastTransPosOfLastValidMetaBlock()
                        < 2 * RecoverableStream.META_BLOCK_DISTANCE + 1);
            }
        }
    }

    // ======== FileStream: the last file ========

    /**
     * The cases of 035-02, section 10.3, on a file database, its last file of 1 MB from
     * stream position 10,000,000 (DbTesterStream.testZeroedTailOverMetaBlock's layout) with
     * records of small values after a few of 400 kB: from Z, a page of 16 KiB of the
     * last file, to its end, with the file's length as it was: zeros (of which FileStream's
     * open leaves a run of at most 8 MB out, bergdb 028-60), the stream's own bytes from
     * 2,000,000 before (an older stream file of the database at the same offsets, meta blocks
     * included) and from 1,004,096 before (at other offsets), another database's last file
     * (its records at the same positions, another ID), and that file 4,096 bytes on; and a
     * record's size of 100,000,000 at a record's start. Each start takes the records that end
     * before Z' and no other, or refuses with a BadTailException, every file as it was; the
     * last file cut at P less its first position, as the message says, then starts with those
     * records, writes one more and starts again.
     */
    @Nano("f")
    private static void testStaleTailFiles(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        final File dirA = env.createTempDir();
        final File dirB = env.createTempDir();
        final Workload a = writeFiles(dirA, DatabaseId.TEST_ID, 2861);
        final Workload b = writeFiles(dirB, OTHER_ID, 2862);
        final long fileStart = a.lastFileStart;
        Assert.assertEquals("the same last file", a.lastFile, b.lastFile);

        final byte[] lastA = java.nio.file.Files.readAllBytes(new File(dirA, a.lastFile).toPath());
        final byte[] lastB = java.nio.file.Files.readAllBytes(new File(dirB, b.lastFile).toPath());
        final int n = lastA.length;
        Assert.assertTrue("the last file " + n, n > 600 * 1000);
        List<Object[]> sources = new ArrayList<Object[]>();
        sources.add(new Object[] {"zeros", new byte[n]});
        sources.add(new Object[] {"an older stream file at the same offsets",
                streamBytes(dirA, fileStart - 2000 * 1000, n)});
        sources.add(new Object[] {"its own bytes at other offsets",
                streamBytes(dirA, fileStart - 1004096, n)});
        sources.add(new Object[] {"another database, the same positions",
                shifted(lastB, 0, n)});
        sources.add(new Object[] {"another database, 4096 after", shifted(lastB, -4096, n)});

        Counts counts = new Counts();
        final long page = 16 * 1024;
        long time = 100000;
        for (Object[] s : sources) {
            for (long z = page; z < n; z += 4 * page) {
                byte[] file = lastA.clone();
                System.arraycopy((byte[]) s[1], (int) z, file, (int) z, n - (int) z);
                time = checkFile(env, dirA, a, file, z, s[0] + ", Z " + z, time, counts);
            }
        }
        // The size at the records after the last file's last meta block, which the start's
        // walk reads (before it, the size is damage in the middle of the stream).
        final long lastBlock = (n - RecoverableStream.META_BLOCK_SIZE)
                / RecoverableStream.META_BLOCK_DISTANCE * RecoverableStream.META_BLOCK_DISTANCE;
        for (int i = 0; i < a.lastPos.length; i += 37) {
            final long r = a.tpos[i] - fileStart;
            if (r < lastBlock + RecoverableStream.META_BLOCK_SIZE) {
                continue;
            }
            byte[] file = lastA.clone();
            Bytes.intToBytesLE(100 * 1000 * 1000, file, (int) r);
            time = checkFile(env, dirA, a, file, r, "a size of 100,000,000 at " + a.tpos[i],
                    time, counts);
        }
        Assert.assertTrue(counts.toString(), counts.refused > 20);
    }

    /** A file database's workload: its puts' keys and values, and its records. */
    private static final class Workload {
        String lastFile;
        long lastFileStart;
        String[] keys;
        byte[][] values;
        long[] tpos;
        long[] lastPos;
    }

    /**
     * Writes the workload of testStaleTailFiles() to a file database in 'dir' of ID 'id':
     * values of 400 kB to stream position 10,000,000, then values of 1 to 400 random bytes
     * ('seed'), each a transaction, up to 3,000 and 10,850,000 (the last file is of 1 MB); a startup distance of 200,000, so that a start reads
     * little. Not forced: no kill comes.
     */
    private static Workload writeFiles(File dir, DatabaseId id, long seed) throws IOException {
        final Random r = new Random(seed);
        final Random sizes = new Random(seed + 1);
        final long fileStart = 10 * 1000 * 1000;
        final List<String> keys = new ArrayList<String>();
        final List<byte[]> values = new ArrayList<byte[]>();
        final List<Long> tpos = new ArrayList<Long>();
        final List<Long> lastPos = new ArrayList<Long>();
        final CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(new FileStream(dir, false)).clock(clock).id(id)
                .start()) {
            clock.setTime(5);
            db.setStartupDistance(200 * 1000);
            long time = 10;
            for (int i = 0; db.getStreamLength() < fileStart; i++) {
                put(db, clock, time++, "f" + i, new byte[400 * 1000], keys, values, tpos,
                        lastPos);
            }
            for (int i = 0; i < 3000 && db.getStreamLength() < fileStart + 850 * 1000; i++) {
                byte[] v = new byte[1 + sizes.nextInt(400)];
                r.nextBytes(v);
                put(db, clock, time++, "k" + i, v, keys, values, tpos, lastPos);
            }
        }
        Workload w = new Workload();
        String last = null;
        for (String name : dir.list()) {
            if (name.endsWith(".bergdb") && (last == null || name.compareTo(last) > 0)) {
                last = name;
            }
        }
        w.lastFile = last;
        w.lastFileStart = Long.parseLong(last.substring(0, last.length() - 7)) * 100000;
        Assert.assertEquals("the last file's start", fileStart, w.lastFileStart);
        w.keys = keys.toArray(new String[0]);
        w.values = values.toArray(new byte[0][]);
        w.tpos = new long[tpos.size()];
        w.lastPos = new long[lastPos.size()];
        for (int i = 0; i < w.tpos.length; i++) {
            w.tpos[i] = tpos.get(i);
            w.lastPos[i] = lastPos.get(i);
        }
        return w;
    }

    private static void put(Db db, CoreTestClock clock, long time, String key, byte[] value,
            List<String> keys, List<byte[]> values, List<Long> tpos, List<Long> lastPos) {
        clock.setTime(time);
        Trans t = db.trans().put(key, value).build();
        db.execute(t);
        keys.add(key);
        values.add(value);
        tpos.add(t.tpos);
        lastPos.add(t.lastPos);
    }

    /** 'n' bytes of the stream in 'dir' from stream position 'pos'. */
    private static byte[] streamBytes(File dir, long pos, int n) throws IOException {
        FileStream fs = new FileStream(dir);
        try {
            byte[] b = new byte[n];
            fs.read(pos, b, 0, n);
            return b;
        } finally {
            fs.close();
        }
    }

    /**
     * Starts a copy of 'dir' whose last file is 'file' (the workload's, with other bytes from
     * offset 'z' on), and checks it as check() does: the records that end before Z', or a
     * BadTailException with every file as it was, and the last file cut at P less its first
     * position then holding them; then one more transaction and a start again. Returns the
     * clock's time for the next.
     */
    private static long checkFile(TestEnvironment env, File dir, Workload w, byte[] file,
            long z, String what, long time, Counts counts) throws IOException {
        final byte[] own = java.nio.file.Files.readAllBytes(new File(dir, w.lastFile).toPath());
        long zz = z;
        while (zz < file.length && file[(int) zz] == own[(int) zz]) {
            zz++;
        }
        final long zPos = w.lastFileStart + zz;
        final File copy = env.createTempDir();
        for (File f : dir.listFiles()) {
            if (f.getName().endsWith(".bergdb") && !f.getName().equals(w.lastFile)) {
                java.nio.file.Files.copy(f.toPath(), new File(copy, f.getName()).toPath());
            }
        }
        final File last = new File(copy, w.lastFile);
        java.nio.file.Files.write(last.toPath(), file);
        counts.copies++;

        final CoreTestClock clock = new CoreTestClock();
        clock.setTime(time);
        try (Db db = Db.builder().testSetup(new FileStream(copy)).clock(clock).start()) {
            holds(db, w, zPos, what + ": started");
            counts.started++;
            return time + 10;
        } catch (BadTailException e) {
            final long p = e.getCutPos();
            Assert.assertArrayEquals(what + ": the last file as it was", file,
                    java.nio.file.Files.readAllBytes(last.toPath()));
            Assert.assertTrue(what + ": P " + p + " in the last file",
                    p > w.lastFileStart && p <= w.lastFileStart + file.length);
            Assert.assertTrue(what + ": " + e.getMessage(), e.getMessage().contains(
                    "cut the stream file that holds it to " + p + " less the file's first "
                    + "position, which is the number in its name times 100,000"));
            try (RandomAccessFile f = new RandomAccessFile(last, "rw")) {
                f.setLength(p - w.lastFileStart);
            }
        }
        try (Db db = Db.builder().testSetup(new FileStream(copy)).clock(clock).start()) {
            holds(db, w, zPos, what + ": cut at P");
            clock.setTime(time + 5);
            db.execute(db.trans().put("after", "after-value"));
        }
        try (Db db = Db.builder().testSetup(new FileStream(copy)).clock(clock).start()) {
            holds(db, w, zPos, what + ": after the cut and one more");
            Assert.assertTrue(what, DbUtil.get(db, Long.MAX_VALUE, "after") != null);
        }
        counts.refused++;
        return time + 10;
    }

    /** Whether 'db' holds the workload's puts whose records end before 'zPos', and no other. */
    private static void holds(Db db, Workload w, long zPos, String what) {
        for (int i = 0; i < w.keys.length; i++) {
            byte[] v = DbUtil.get(db, Long.MAX_VALUE, w.keys[i]);
            if (w.lastPos[i] < zPos) {
                Assert.assertTrue(what + ": " + w.keys[i] + " lost", Arrays.equals(v, w.values[i]));
            } else {
                Assert.assertTrue(what + ": " + w.keys[i] + " taken", v == null);
            }
        }
    }
}
