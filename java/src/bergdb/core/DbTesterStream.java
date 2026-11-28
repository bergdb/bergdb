package bergdb.core;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.common.Util;
import bergdb.dag.Keys;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.DbFailedException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.storage.VersioningStreamException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;
import bergdb.stream.MemoryStream;
import bergdb.stream.OneFileStream;
import bergdb.stream.ReadOnlyStream;
import bergdb.stream.StreamContract.NoForceIo;

/**
 * Tests the database with a stream.
 * 
 * @author Frans Lundberg
 */
public class DbTesterStream {
    
    public static void test1() {
        Db db = Db.builder().testSetup().build();
        db.start();
        db.close();
    }
    
    public static void test2() {
        Db db = Db.builder().testSetup().build();
        db.start();
        
        db.execute(db.trans().put("admin1", "Sanna").build());
        byte[] value = DbUtil.get(db, 99, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        db.close();
    }
    
    public static void testSimpleRestart1() {
        byte[] value;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("admin1", "Sanna").build());
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup(stream).start();
        
        value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, 5, StringUtil.toBytes("admin1"));
        Assert.assertNull(value);
        db2.stop();
    }
    
    public static void testSimpleRestart2() {
        //
        // Like testSimpleRestart1, but 2-segment key
        //
        byte[] value;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(db.trans().put("admin10", "Sanna").build());
        db.sync(SyncLevel.ORDINARY);
        
        value = DbUtil.get(db, 99, "admin10");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        
        db.stop();
        db = null;
        Db db2 = Db.builder().testSetup().mainStream(stream).build();
        db2.start();
        
        value = DbUtil.get(db2, 99, "admin10");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, 5, "admin10");
        Assert.assertNull(value);
        db2.stop();
    }
    
    public static void testRestartWithMultipleTransactions() {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(db.trans().put("admin1", "Sanna1").build());
        clock.setTime(20);
        db.execute(db.trans().put("admin2", "Sanna2").build());
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup(stream).build();
        db2.start();
        
        byte[] value;
        
        value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna1"), value);
        value = DbUtil.get(db2, 5, "admin1");
        Assert.assertNull(value);
        
        value = DbUtil.get(db2, 99, "admin2");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna2"), value);
        value = DbUtil.get(db2, 15, "admin2");
        Assert.assertNull(value);
        db2.stop();
    }
    
    public static void testRestart2() {
        //
        // Like testRestartWithMultipleTransactions, but keys are
        // one char longer, "admin10" instead of "admin1".
        //
        MemoryStream stream = new MemoryStream();
        byte[] value;
        Db db;
        
        db = Db.builder().testSetup(stream).build();
        db.start();
        
        db.execute(db.trans().put("admin10", "Sanna1").build());
        db.execute(db.trans().put("admin20", "Sanna2").build());
        
        value = DbUtil.get(db, 999, "admin10");
        Assert.assertEquals("Sanna1", StringUtil.toString(value));
        value = DbUtil.get(db, 999, "admin20");
        Assert.assertEquals("Sanna2", StringUtil.toString(value));
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(stream).build();
        db2.start();
        
        value = DbUtil.get(db2, 999, "admin10");
        Assert.assertEquals("Sanna1", StringUtil.toString(value));
        value = DbUtil.get(db2, 999, "admin20");
        Assert.assertEquals("Sanna2", StringUtil.toString(value));
        db2.stop();
    }
    
    public static void testRestartWithTimeSplit() {
        MemoryStream stream = new MemoryStream();
        byte[] value;
        long time;
        Db db;
        int n = 10;
        
        CoreTestClock clock = new CoreTestClock();
        db = Db.builder().testSetup(stream).clock(clock).build();
        db.start();
        
        time = 100;
        for (int i = 0; i < n; i++) {
            clock.setTime(time);
            db.execute(db.trans().put("admin" + time, "Sanna" + time).build());
            time += 10;
        }
        
        time = 100;
        for (int i = 0; i < n; i++) {
            value = DbUtil.get(db, 999, "admin" + time);
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("Sanna" + time), value);
            time += 10;
        }
        
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup(stream).build();
        db2.start();
        
        time = 100;
        for (int i = 0; i < n; i++) {
            value = DbUtil.get(db2, 999, "admin" + time);
            Assert.assertEquals("i=" + i, "Sanna" + time, StringUtil.toString(value));
            time += 10;
        }
        db2.stop();
    }
    
    public static void testRestartWithTwoSuperRoots() {
        MemoryStream stream = new MemoryStream();
        byte[] value;
        long time;
        Db db;
        int n = 10;
        CoreTestClock clock = new CoreTestClock();
        db = Db.builder().testSetup(stream).clock(clock).build();
        db.start();
        
        time = 100;
        for (int i = 0; i < n; i++) {
            clock.setTime(time);
            db.execute(db.trans().put("a" + time, "v" + time).build());
            time += 10;
        }
        
        time = 100;
        for (int i = 0; i < n; i++) {
            value = DbUtil.get(db, 999,"a" + time);
            Assert.assertArrayEquals("i=" + i, StringUtil.toBytes("v" + time), value);
            time += 10;
        }
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(stream).build();
        db2.start();
        
        time = 100;
        for (int i = 0; i < n; i++) {
            value = DbUtil.get(db2, 999, "a" + time);
            Assert.assertEquals("i=" + i, "v" + time, StringUtil.toString(value));
            time += 10;
        }
        db2.stop();
    }
    
    public static Db createRandomDb(int n, AppendOnlyStream stream) {
        Random random = new Random(1);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).build();
        db.start();
        
        for (int i = 0; i < n; i++) {
            String key = "" + random.nextInt();
            Trans t = db.trans().put(key, "v" + key).build();
            clock.setTime(i * 10 + 10);
            db.execute(t);
            
            byte[] value = DbUtil.get(db, n * 10 + 999, key);
            Assert.assertEquals("i=" + i, "v" + key, StringUtil.toString(value));
        }
        return db;
    }
    
    public static void checkRandomDb(Db db, int n) {
        Random random = new Random(1);
        
        for (int i = 0; i < n; i++) {
            String key = "" + random.nextInt();
            byte[] value = DbUtil.get(db, n * 10 + 999, key);
            Assert.assertEquals("i=" + i, "v" + key, StringUtil.toString(value));
        }
    }
    
    public static void testMoreData0() {
        int n = 50;
        MemoryStream stream = new MemoryStream();
        Db db = createRandomDb(n, stream);
        checkRandomDb(db, n);
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        checkRandomDb(db2, n);
        db2.stop();
    }
    
    private static String key(int i) {
        String key = "" + i;
        if (i < 10) {
            key = "0" + key;
        }
        return key;
    }
    
    public static void testMoreData1() {
        int n = 100;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        
        for (int i = 0; i < n; i++) {
            clock.setTime(100 + i * 10);
            String key = key(i);
            Trans t = db.trans().put(key, "v" + key).build();
            db.execute(t);
        }
        
        for (int i = 0; i < n; i++) {
            String key = key(i);
            String valueString = StringUtil.toString(DbUtil.get(db, n * 10 + 9999, key));
            Assert.assertEquals("v" + key, valueString);
        }
        
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup(stream).start();
        
        for (int i = 0; i < n; i++) {
            String key = key(i);
            String valueString = StringUtil.toString(DbUtil.get(db2, n * 10 + 9999, key));
            Assert.assertEquals("v" + key, valueString);
        }
        db2.stop();
    }
    
    @Nano("f")   // Too slow to be "unit".
    public static void testMoreData2() {
        int n = 2000;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(stream).clock(clock).start();

        for (int i = 0; i < n; i++) {
            int k = i + 100;
            clock.setTime(100 + k * 10);
            Trans t = db.trans().put("" + k, "v" + k).build();
            db.execute(t);
        }
        
        for (int i = 0; i < n; i++) {
            int k = i + 100;
            String valueString = StringUtil.toString(DbUtil.get(db, n * 10 + 9999, "" + k));
            Assert.assertEquals("v" + k, valueString);
        }
        
        db.sync(SyncLevel.ORDINARY);
        db.close();
        
        Db db2 = Db.builder().testSetup().mainStream(stream.copy()).start();
        
        for (int i = 0; i < n; i++) {
            int k = i + 100;
            String valueString = StringUtil.toString(DbUtil.get(db2, n * 10 + 9999, "" + k));
            Assert.assertEquals("v" + k, valueString);
        }   
        db2.close();
    }
    
    public static void testDbOnMemStream() throws IOException {
        AppendOnlyStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("k", "k-value"));
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup(s).start();
        
        byte[]value = DbUtil.get(db2, 99, "k");
        Assert.assertArrayEquals(StringUtil.toBytes("k-value"), value);
        
        value = DbUtil.get(db2, 5, "k");
        Assert.assertNull(value);
        db2.stop();
    }
    
    public static void testDbOnFile() throws IOException {
        // 
        // Tests writing db data to file.
        //
        
        if (Util.runsAndroid()) {
            return;
        }
        
        File f = File.createTempFile(DbTesterStream.class.getSimpleName() + ".testDbOnFile.", ".bergdb");
        f.deleteOnExit();
        
        try {
            AppendOnlyStream s = new OneFileStream(f);
            CoreTestClock clock = new CoreTestClock();
            Db db = Db.builder().testSetup(s).clock(clock).start();
            clock.setTime(10);
            db.execute(db.trans().put("k", "k-value"));
            db.sync(SyncLevel.ORDINARY);
            db.close();
            s = null;
            
            AppendOnlyStream s2 = new OneFileStream(f);
            Db db2 = Db.builder().testSetup(s2).start();
            
            byte[] value = DbUtil.get(db2, 99, "k");
            Assert.assertArrayEquals(StringUtil.toBytes("k-value"), value);
            
            value = DbUtil.get(db2, 5, StringUtil.toBytes("k"));
            Assert.assertNull(value);
            db2.close();
        } finally {
            f.delete();
        }
    }
    
    @Nano
    public static void testDbOnFileMultipleTransactions() throws FileNotFoundException, IOException {
        
        if (Util.runsAndroid()) {
            return;
        }
        
        File f = File.createTempFile(DbTesterStream.class.getSimpleName() + ".testDbOnFileMultipleTransactions.", ".bergdb");
        f.deleteOnExit();
        
        AppendOnlyStream s = new OneFileStream(f);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("admin1", "Sanna1").build());
        clock.setTime(20);
        db.execute(db.trans().put("admin2", "Sanna2").build());
        db.sync(SyncLevel.ORDINARY);
        db.close();
        s = null;
        
        AppendOnlyStream s2 = new OneFileStream(f);
        Db db2 = Db.builder().testSetup(s2).start();
        
        byte[] value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna1"), value);
        value = DbUtil.get(db2, 5, "admin1");
        Assert.assertNull(value);
        
        value = DbUtil.get(db2, 99, "admin2");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna2"), value);
        value = DbUtil.get(db2, 15, "admin2");
        Assert.assertNull(value);
        
        db2.close();
        f.delete();
    }
    
    /**
     * The creation is durable when start() returns, with created.txt (bergdb 028-17): both
     * its records, the primordial one and the creating start's record of the startup
     * distance (bergdb 028-15). The files are copied while the database runs, after a
     * transaction that no sync made durable, as a kill of the process leaves them, and a
     * start on the copy finds the creator's startup distance (the default, 50 MB, since
     * bergdb 028-13), and a time before the lost transaction's. Until 028-17 the second
     * record waited in the write buffer: the copy held the primordial record alone, and its
     * start put the KV with its own builder's setting at its own time, after the lost
     * transaction's (night.sh's kill-restart.sh, 2026-11-18). Since 028-18 such a copy is
     * refused (DatabaseNotCreatedException); testCreatedTxtAfterBothRecords checks the
     * order of the sync and created.txt.
     */
    @Nano
    private static void testCreationDurableWhenStartReturns(TestEnvironment env)
            throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File dir = env.createTempDir();
        File copy = env.createTempDir();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(new FileStream(dir)).clock(clock).createdTxt(dir)
                .start();
        Db again = null;
        try {
            clock.setTime(1000);
            db.execute(db.trans().put("k", "k-value"));     // no sync
            File[] files = dir.listFiles();
            Assert.assertTrue("files", files != null);
            for (File f : files) {
                if (f.getName().endsWith(".bergdb") || f.getName().equals("created.txt")) {
                    java.nio.file.Files.copy(f.toPath(), new File(copy, f.getName()).toPath());
                }
            }
            CoreTestClock clock2 = new CoreTestClock();
            clock2.setTime(2000);
            again = Db.builder().testSetup(new FileStream(copy)).clock(clock2).createdTxt(copy)
                    .start();
            Assert.assertEquals("the creator's startup distance", Db.DEFAULT_STARTUP_DISTANCE,
                    again.getStartupDistance());
            if (DbUtil.get(again, Long.MAX_VALUE, "k") == null) {
                long t = again.lookupTime(Long.MAX_VALUE);
                Assert.assertTrue("the start's time, " + t + ", before the lost transaction's",
                        t < 1000);
            }
        } finally {
            db.close();
            if (again != null) {
                again.close();
            }
        }
    }
    
    /**
     * Bergdb 028-18 (option C; Frans, 2026-11-19, 09:53): with created.txt, a creation's two
     * records, the primordial one and the creating start's record of the startup distance,
     * are forced to the file before created.txt is written, and created.txt is there when
     * start() returns. Every force of the start is recorded with the file's length and
     * whether created.txt existed: one force covers the whole stream as start() leaves it,
     * more than the primordial record, without created.txt; until 028-18 created.txt was
     * written after the primordial record's force alone. A restart and a change of the
     * startup distance follow.
     */
    @Nano
    private static void testCreatedTxtAfterBothRecords(TestEnvironment env)
            throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        final File dir = env.createTempDir();
        final File txt = new File(dir, "created.txt");
        final java.util.List<long[]> forces =
                java.util.Collections.synchronizedList(new java.util.ArrayList<long[]>());
        FileStreamIo io = new FileStreamIo() {
            protected void forceFile(File file, RandomAccessFile handle) throws IOException {
                super.forceFile(file, handle);
                forces.add(new long[] {handle.length(), txt.exists() ? 1 : 0});
            }
        };
        CoreTestClock clock = new CoreTestClock();
        long length;
        try (Db db = Db.builder().testSetup(new FileStream(dir, io)).clock(clock)
                .createdTxt(dir).start()) {
            length = db.getStreamLength();
            Assert.assertTrue("created.txt when start() returns", txt.isFile());
            Assert.assertTrue("both records, " + length, length > Db.CREATION_LENGTH);
            boolean covered = false;
            synchronized (forces) {
                for (long[] f : forces) {
                    Assert.assertEquals("created.txt at a force of the start", 0, f[1]);
                    covered |= f[0] >= length;
                }
            }
            Assert.assertTrue("a force of both records, of " + forces.size(), covered);
            db.setStartupDistance(5000000);     // after the start (bergdb 028-13)
        }
        clock.setTime(1000);
        try (Db db = Db.builder().testSetup(new FileStream(dir)).clock(clock).createdTxt(dir)
                .start()) {
            Assert.assertEquals("the first run's", 5000000, db.getStartupDistance());
            db.setStartupDistance(3000000);
        }
        clock.setTime(2000);
        try (Db db = Db.builder().testSetup(new FileStream(dir)).clock(clock).createdTxt(dir)
                .start()) {
            Assert.assertEquals("the changed setting", 3000000, db.getStartupDistance());
        }
    }
    
    /**
     * Bergdb 028-60: after a kill of the process during an append, the last stream file can
     * end in zeros within its length, from a page boundary on (macOS, APFS; bergdb 031-02,
     * F1), and the zeros can cover a meta block's position. Made here on a stopped database's
     * last file, of 1 MB from stream position 10,000,000 (FileStream's files are of 1 MB from
     * 4,000,000 on; from 10,000,000 on with the tenth alone, from 2026-11-26 to 2026-11-27,
     * bergdb 028-62): its last record, a value of 400 kB over the meta blocks at 10,400,000
     * and 10,600,000, zero from the first 16 KiB page of the file after the record's header to the
     * file's end, with the file's length as it is and cut inside the record, as the kill of
     * 031-02's seed 91 left it. The start takes it as a cut tail: the records before it,
     * synced, are there and the zeroed one is not; the database writes and starts again.
     * Zeros that reach past a record's end, here from inside the record of 230 kB before it,
     * as the kill of seed 63 left them, are left out by FileStream's open (2026-11-26, part 2
     * of 028-60): the start has the records before that record, and writes and starts again;
     * until then they were refused, "Bad transaction size in db stream, 0, spos P". Zeros
     * after the last record's end, 0, 1 and 8 MB of them (FileStream.ZERO_TAIL_MAX), are
     * left out and the start has every record; 8 MB + 1 are left in, and the start refuses them
     * with that message. Until 2026-11-25 the start refused the first three, "Invalid magic
     * bytes in stream", from the zero meta block (Db.refuseOtherNodeSize).
     */
    @Nano("f")
    private static void testZeroedTailOverMetaBlock(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        final File dir = env.createTempDir();
        final CoreTestClock clock = new CoreTestClock();
        final byte[] a = new byte[230 * 1000];
        final byte[] c = new byte[400 * 1000];
        new Random(2860).nextBytes(a);
        new Random(2861).nextBytes(c);
        final long fileStart = 10 * 1000 * 1000;
        final long recordC;
        // Not forced: no kill comes before the files are zeroed by hand.
        try (Db db = Db.builder().testSetup(new FileStream(dir, false)).clock(clock).start()) {
            for (int i = 0; db.getStreamLength() < fileStart; i++) {
                clock.setTime(10 + i);
                db.execute(db.trans().put("f" + i, new byte[400 * 1000]));
            }
            clock.setTime(100);
            db.execute(db.trans().put("z", "z-value"));
            clock.setTime(200);
            db.execute(db.trans().put("a", a));
            clock.setTime(300);
            db.execute(db.trans().put("b", "b-value"));
            db.sync(SyncLevel.ORDINARY);
            recordC = db.getStreamLength();
            clock.setTime(400);
            db.execute(db.trans().put("c", c));
        }
        final String lastName = "00000000000100.bergdb";
        final long fileLength = new File(dir, lastName).length();
        Assert.assertTrue("files " + java.util.Arrays.toString(dir.list()),
                fileLength > 0 && !new File(dir, "00000000000110.bergdb").exists());
        final long page = 16 * 1024;
        final long zerosInC = fileStart + ((recordC - fileStart) / page + 1) * page;
        Assert.assertTrue("c from " + recordC + ", zeros from " + zerosInC + ", end "
                + (fileStart + fileLength), recordC > fileStart + 2 * page
                && zerosInC > recordC + 8 && zerosInC < fileStart + 400 * 1000
                && fileStart + fileLength > fileStart + 600 * 1000 + 1000);

        long time = 500;
        for (long length : new long[] {fileStart + fileLength, fileStart + 600 * 1000 + 1000}) {
            final String what = "length " + length;
            final File copy = copyStreamFiles(dir, env.createTempDir());
            zeroFileTail(new File(copy, lastName), zerosInC - fileStart, length - fileStart);
            final FileStream fs = new FileStream(copy);
            Assert.assertTrue(what + ", removed " + fs.getZeroTailRemoved(),
                    fs.getZeroTailRemoved() >= length - zerosInC);
            try (Db db = Db.builder().testSetup(fs).clock(clock).start()) {
                Assert.assertArrayEquals(what, StringUtil.toBytes("z-value"),
                        DbUtil.get(db, Long.MAX_VALUE, "z"));
                Assert.assertArrayEquals(what, a, DbUtil.get(db, Long.MAX_VALUE, "a"));
                Assert.assertArrayEquals(what, StringUtil.toBytes("b-value"),
                        DbUtil.get(db, Long.MAX_VALUE, "b"));
                Assert.assertTrue(what, DbUtil.get(db, Long.MAX_VALUE, "c") == null);
                clock.setTime(time += 100);
                db.execute(db.trans().put("d", "d-value"));
            }
            try (Db db = Db.builder().testSetup(new FileStream(copy)).clock(clock).start()) {
                Assert.assertArrayEquals(what, a, DbUtil.get(db, Long.MAX_VALUE, "a"));
                Assert.assertTrue(what, DbUtil.get(db, Long.MAX_VALUE, "c") == null);
                Assert.assertArrayEquals(what, StringUtil.toBytes("d-value"),
                        DbUtil.get(db, Long.MAX_VALUE, "d"));
            }
        }

        // Zeros from inside a's record, over b's and c's: removed at the open (part 2).
        File copy = copyStreamFiles(dir, env.createTempDir());
        zeroFileTail(new File(copy, lastName), page, fileLength);
        FileStream fs = new FileStream(copy);
        Assert.assertTrue("removed " + fs.getZeroTailRemoved(),
                fs.getZeroTailRemoved() >= fileLength - page);
        try (Db db = Db.builder().testSetup(fs).clock(clock).start()) {
            Assert.assertArrayEquals(StringUtil.toBytes("z-value"),
                    DbUtil.get(db, Long.MAX_VALUE, "z"));
            Assert.assertTrue(DbUtil.get(db, Long.MAX_VALUE, "a") == null);
            Assert.assertTrue(DbUtil.get(db, Long.MAX_VALUE, "b") == null);
            Assert.assertTrue(DbUtil.get(db, Long.MAX_VALUE, "c") == null);
            clock.setTime(time += 100);
            db.execute(db.trans().put("d", "d-value"));
        }
        try (Db db = Db.builder().testSetup(new FileStream(copy)).clock(clock).start()) {
            Assert.assertArrayEquals(StringUtil.toBytes("z-value"),
                    DbUtil.get(db, Long.MAX_VALUE, "z"));
            Assert.assertTrue(DbUtil.get(db, Long.MAX_VALUE, "a") == null);
            Assert.assertArrayEquals(StringUtil.toBytes("d-value"),
                    DbUtil.get(db, Long.MAX_VALUE, "d"));
        }
        
        // Zeros after c's end, the stream's: removed up to 8 MB, the records whole.
        for (long zeros : new long[] {0, 1, FileStream.ZERO_TAIL_MAX}) {
            final String what = zeros + " zeros after the end";
            copy = copyStreamFiles(dir, env.createTempDir());
            try (RandomAccessFile f = new RandomAccessFile(new File(copy, lastName), "rw")) {
                f.setLength(fileLength + zeros);
            }
            fs = new FileStream(copy);
            Assert.assertEquals(what, zeros, fs.getZeroTailRemoved());
            Assert.assertEquals(what, fileStart + fileLength, fs.getLength());
            try (Db db = Db.builder().testSetup(fs).clock(clock).start()) {
                Assert.assertArrayEquals(what, a, DbUtil.get(db, Long.MAX_VALUE, "a"));
                Assert.assertArrayEquals(what, StringUtil.toBytes("b-value"),
                        DbUtil.get(db, Long.MAX_VALUE, "b"));
                Assert.assertArrayEquals(what, c, DbUtil.get(db, Long.MAX_VALUE, "c"));
                clock.setTime(time += 100);
                db.execute(db.trans().put("d", "d-value"));
            }
            try (Db db = Db.builder().testSetup(new FileStream(copy)).clock(clock).start()) {
                Assert.assertArrayEquals(what, c, DbUtil.get(db, Long.MAX_VALUE, "c"));
                Assert.assertArrayEquals(what, StringUtil.toBytes("d-value"),
                        DbUtil.get(db, Long.MAX_VALUE, "d"));
            }
        }
        
        // 8 MB + 1 zeros after the end: left, and refused at the size 0 after c.
        copy = copyStreamFiles(dir, env.createTempDir());
        final File last = new File(copy, lastName);
        try (RandomAccessFile f = new RandomAccessFile(last, "rw")) {
            f.setLength(fileLength + FileStream.ZERO_TAIL_MAX + 1);
        }
        fs = new FileStream(copy);
        Assert.assertEquals(0L, fs.getZeroTailRemoved());
        try (Db db = Db.builder().testSetup(fs).clock(clock).start()) {
            throw new AssertionError("started with 8 MB + 1 zeros");
        } catch (StreamFormatException e) {
            final String prefix = "Bad transaction size in db stream, 0, spos ";
            final String message = e.getMessage();
            Assert.assertTrue(message, message.startsWith(prefix)
                    && message.contains(". Stream length: "));
            final long p = Long.parseLong(message.substring(prefix.length(),
                    message.indexOf(". Stream length: ")));
            Assert.assertTrue("P " + p, p >= fileStart + fileLength
                    && p <= fileStart + fileLength + RecoverableStream.META_BLOCK_SIZE);
        }
        Assert.assertTrue("nothing removed", last.length() >= fileLength
                + FileStream.ZERO_TAIL_MAX + 1);
    }

    /**
     * Bergdb 028-60, Codex's review of part 2 (2026-11-26), finding 4: a start refused before
     * it writes, for another node size (bergdb 005-50) or an unsupported version of the meta
     * block (005-40), leaves the stream's file as it was, also its tail of zeros: FileStream's
     * open leaves the zeros out of the stream and cuts them from the file only at an append.
     * So the refusals' "The start has written nothing" holds. On the branch 028-60b before
     * this, the open truncated the zeros first. With the node size or the version restored,
     * each starts.
     */
    @Nano
    private static void testRefusedStartsKeepZeroTail(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        // Another node size.
        File dir = env.createTempDir();
        try (Db db = TestNodeSize.builder(8).testSetup(new FileStream(dir)).start()) {
            db.execute(db.trans().put("a", "a-value"));
        }
        File file = new File(dir, "00000000000000.bergdb");
        try (RandomAccessFile f = new RandomAccessFile(file, "rw")) {
            f.setLength(f.length() + 4096);
        }
        byte[] before = java.nio.file.Files.readAllBytes(file.toPath());
        try (Db db = Db.builder().testSetup(new FileStream(dir)).start()) {
            throw new AssertionError("started with another node size");
        } catch (StreamFormatException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("node size")
                    && e.getMessage().contains("written nothing"));
        }
        Assert.assertArrayEquals(before, java.nio.file.Files.readAllBytes(file.toPath()));
        try (Db db = TestNodeSize.builder(8).testSetup(new FileStream(dir)).start()) {
            Assert.assertArrayEquals(StringUtil.toBytes("a-value"),
                    DbUtil.get(db, Long.MAX_VALUE, "a"));
        }
        
        // An unsupported version of the meta block (the first, at 0; its version at 4).
        dir = env.createTempDir();
        try (Db db = Db.builder().testSetup(new FileStream(dir)).start()) {
            db.execute(db.trans().put("a", "a-value"));
        }
        file = new File(dir, "00000000000000.bergdb");
        int version;
        try (RandomAccessFile f = new RandomAccessFile(file, "rw")) {
            f.seek(4);
            version = f.read();
            f.seek(4);
            f.write(157);
            f.setLength(f.length() + 4096);
        }
        before = java.nio.file.Files.readAllBytes(file.toPath());
        try (Db db = Db.builder().testSetup(new FileStream(dir)).start()) {
            throw new AssertionError("started with version 157");
        } catch (VersioningStreamException e) {
            // Expected (bergdb 005-40).
        }
        Assert.assertArrayEquals(before, java.nio.file.Files.readAllBytes(file.toPath()));
        try (RandomAccessFile f = new RandomAccessFile(file, "rw")) {
            f.seek(4);
            f.write(version);
        }
        try (Db db = Db.builder().testSetup(new FileStream(dir)).start()) {
            Assert.assertArrayEquals(StringUtil.toBytes("a-value"),
                    DbUtil.get(db, Long.MAX_VALUE, "a"));
        }
    }
    
    /**
     * Bergdb 028-80 (033's review of the start, F3): a creation's first write that a kill
     * left as zeros, the stream's only file all zeros, which FileStream's open leaves as it
     * is (a repair never empties a stream). The start refuses it as a creation that did not
     * complete, a DatabaseNotCreatedException, and changes no file: as long as the creation
     * (416 bytes), a page, 16 KiB, and the first file's 200,000 bytes; and 200,000 zeros with
     * a second file of zeros, which the open leaves out. Before, a StreamFormatException,
     * "Could not find *any* valid meta block". With the file removed, the start creates the
     * database.
     */
    @Nano
    private static void testCreationLeftAsZeros(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        File made = env.createTempDir();
        try (Db db = Db.builder().testSetup(new FileStream(made, new NoForceIo())).start()) {
            // The creation only.
        }
        final int creation = (int) new File(made, "00000000000000.bergdb").length();
        Assert.assertEquals(416, creation);
        for (int n : new int[] {creation, 4096, 16384, 200000, -200000}) {
            final String what = n < 0 ? "200000 zeros and a second file of zeros" : n + " zeros";
            File dir = env.createTempDir();
            File first = new File(dir, "00000000000000.bergdb");
            java.nio.file.Files.write(first.toPath(), new byte[Math.abs(n)]);
            File second = new File(dir, "00000000000002.bergdb");
            if (n < 0) {
                java.nio.file.Files.write(second.toPath(), new byte[3000]);
            }
            try (Db db = Db.builder().testSetup(new FileStream(dir, new NoForceIo())).start()) {
                throw new AssertionError(what + ": started");
            } catch (DatabaseNotCreatedException e) {
                Assert.assertTrue(what + ": " + e.getMessage(),
                        e.getMessage().contains("Remove its files"));
            }
            Assert.assertArrayEquals(what, new byte[Math.abs(n)],
                    java.nio.file.Files.readAllBytes(first.toPath()));
            Assert.assertEquals(what, n < 0 ? 3000 : 0, second.length());
            if (n == creation) {
                Assert.assertTrue(what, first.delete());
                try (Db db = Db.builder().testSetup(new FileStream(dir, new NoForceIo()))
                        .start()) {
                    db.execute(db.trans().put("a", "a-value"));
                }
                try (Db db = Db.builder().testSetup(new FileStream(dir, new NoForceIo()))
                        .start()) {
                    Assert.assertArrayEquals(what, StringUtil.toBytes("a-value"),
                            DbUtil.get(db, Long.MAX_VALUE, "a"));
                }
            }
        }
    }
    
    /** Copies the stream files of 'from' to 'to', and returns 'to'. */
    private static File copyStreamFiles(File from, File to) throws IOException {
        for (File f : from.listFiles()) {
            if (f.getName().endsWith(".bergdb")) {
                java.nio.file.Files.copy(f.toPath(), new File(to, f.getName()).toPath());
            }
        }
        return to;
    }

    /** Sets the file's length to 'length' and writes zeros from 'from' to its end. */
    private static void zeroFileTail(File file, long from, long length) throws IOException {
        try (RandomAccessFile f = new RandomAccessFile(file, "rw")) {
            f.setLength(length);
            f.seek(from);
            f.write(new byte[(int) (length - from)]);
        }
    }

    /** created.txt names the database's ID, and no crypto key since bergdb 028-69. */
    @Nano
    private static void testCreatedTxt(TestEnvironment env) throws IOException {
        if (Util.runsAndroid()) {
            return;
        }
        
        File dir = env.createTempDir();
        
        FileStream fileStream = new FileStream(dir);
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(fileStream).clock(clock).createdTxt(dir).start();
        clock.setTime(10);
        db.execute(db.trans().put("k", "k-value"));
        db.sync(SyncLevel.ORDINARY);
        db.close();
        
        File file = new File(dir, "created.txt");
        Assert.assertTrue(file.exists());
        
        String s = new String(Util.fileToBytes(file.getPath()), "UTF-8");
        Assert.assertTrue(s, s.contains("database ID:   "));
        Assert.assertFalse(s, s.toLowerCase().contains("crypto key"));
    }
    
    public static void testOverwriteAndRestart() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        
        clock.setTime(10);
        db.execute(db.trans().put("k1", "k1-value").put("k2", "k2-value"));
        
        clock.setTime(20);
        db.execute(db.trans().put("k1", "k1-value-b"));
        
        clock.setTime(30);
        db.execute(db.trans().put("k2", "k2-value-b"));
        db.sync(SyncLevel.ORDINARY);
        db.close();
        
        Db db2 = Db.builder().testSetup(s.copy()).start();
        
        // t = 15
        
        byte[] value = DbUtil.get(db2, 15, "k2");
        Assert.assertArrayEquals(StringUtil.toBytes("k2-value"), value);
        
        value = DbUtil.get(db2, 15, "k1");
        Assert.assertArrayEquals(StringUtil.toBytes("k1-value"), value);
        
        // t = 25
        
        value = DbUtil.get(db2, 25, "k1");
        Assert.assertArrayEquals(StringUtil.toBytes("k1-value-b"), value);
        
        value = DbUtil.get(db2, 25, "k2");
        Assert.assertArrayEquals(StringUtil.toBytes("k2-value"), value);
        
        // t = 35
        
        value = DbUtil.get(db2, 35, "k1");
        Assert.assertArrayEquals(StringUtil.toBytes("k1-value-b"), value);
        
        value = DbUtil.get(db2, 35, "k2");
        Assert.assertEquals("k2-value-b", StringUtil.toString(value));
        db2.close();
    }

    @Nano
    public static void testTwoKvsInOneTransaction() {
        MemoryStream s = new MemoryStream();
        TestClock clock = new TestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        int n = 2;
        Trans.Builder b = db.trans();
            
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.intKey(n - i);
            byte[] value = new byte[4];
            Bytes.intToBytesLE(i, value, 0);
            b.put(key, value);
        }
        
        db.execute(b);
        
        // Check
        
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.intKey(n - i);
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
            Assert.assertTrue("i=" + i, value != null);
            Assert.assertEquals(4, value.length);
            int valueInt = Bytes.bytesToIntLE(value, 0);
            Assert.assertEquals(i, valueInt);
        }
        
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        // Now, let's create a new Db from stream.
        
        db = Db.builder().testSetup(s.copy()).start();
        
        for (int i = 0; i < n; i++) {
            byte[] key = KeyFactory.intKey(n - i);
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, key);
            Assert.assertTrue("i=" + i, value != null);
            Assert.assertEquals(4, value.length);
            int valueInt = Bytes.bytesToIntLE(value, 0);
            Assert.assertEquals(i, valueInt);
        }
        db.close();
    }
    
    @Nano("f")     // Too slow to be "unit".
    public static void testLargeTransaction() {
        MemoryStream s = new MemoryStream();
        int n = 2;
        int valueSize = Db.MAX_VALUE_BYTES;     // L4 (bergdb 024-24); 20 MB until then
        Db db = createRandomDb(n, s);  // Make sure we have some data
        
        db.execute(db.trans().put("/large", new byte[valueSize]));
        db.sync(SyncLevel.ORDINARY);
        db.close();
        
        db = Db.builder().testSetup().mainStream(s.copy()).start();
        checkRandomDb(db, n);
        byte[] value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("/large"));
        Assert.assertTrue(value != null);
        Assert.assertEquals(valueSize, value.length);
        db.close();
    }
    
    @Nano("f")    // Too slow to be "unit".
    public static void testLargeTransactions() {
        MemoryStream s = new MemoryStream();
        int valueSize = 1000*1000;
        Db db = Db.builder().testSetup().mainStream(s).start();
        db.setStartupDistance(100*1000);
        int n = 5;
        
        db.execute(db.trans().put("/small1", "v-small1"));
        
        for (int i = 0; i < n; i++) {
            db.execute(db.trans().put("/large-" + i, new byte[valueSize + i]));
        }
        
        db.execute(db.trans().put("/small2", "v-small2"));
        db.sync(SyncLevel.ORDINARY);
        
        db.close();
        
        // ---- Restart
        
        s = s.copy();
        db = Db.builder().testSetup().mainStream(s).build();
        db.start();
        
        Assert.assertEquals("v-small1", DbUtil.getString(db, "/small1"));
        Assert.assertEquals("v-small2", DbUtil.getString(db, "/small2"));
        
        for (int i = 0; i < n; i++) {
            byte[] value = DbUtil.get(db, Long.MAX_VALUE, Keys.toBytes("/large-" + i));
            Assert.assertEquals(valueSize + i, value.length);
        }
        db.close();
    }
    
    @Nano
    public static void testReadOnlyStream1() {
        MemoryStream s1 = new MemoryStream();
        Db db = Db.builder().testSetup(s1).start();
        db.execute(db.trans().put("my-string-key", new byte[0]));
        
        long c1 = DbUtil.checksum(db);
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        
        ReadOnlyStream s2 = new ReadOnlyStream(s1);
        Db db2 = Db.builder().testSetup(s2).start();
        long c2 = DbUtil.checksum(db2);
        db2.stop();
        
        Assert.assertEquals(c1, c2);
    }
    
    // An f-test: the sync after the failed append returns at StorageManager's next 500 ms
    // poll, as nothing wakes it.
    @Nano("f")
    public static void testReadOnlyStream2() {
        // Test to write to read-only Db. Should throw exception.
        // Because of BufferedStream, the actual append to underlying stream
        // is done in a separate thread. That is the reason why the io exception
        // is not visible until the next write.
        // NOTE This is problematic! And why does sync() work? We should at 
        // least be able to query or something? To check whether transaction
        // was successful.
        // 2026-10-13: sync() worked because a failed flush was counted as
        // appended. Now sync() throws. Since bergdb 005-30 it fails the database: a
        // DbFailedException with the StreamIoException as the cause.
        
        MemoryStream s1 = new MemoryStream();
        Db db1 = Db.builder().testSetup(s1).start();
        db1.execute(db1.trans().put("my-string-key", new byte[0]));
        db1.sync(SyncLevel.ORDINARY);
        db1.stop();
        
        ReadOnlyStream s2 = new ReadOnlyStream(s1);
        Db db2 = Db.builder().testSetup(s2).start();
        
        db2.execute(db2.trans().put("my-string-key-2", new byte[0]));
        DbFailedException syncEx = null;
        try {
            db2.sync(SyncLevel.ORDINARY);
        } catch (DbFailedException e) {
            syncEx = e;
        }
        Assert.assertTrue(syncEx != null);
        Assert.assertTrue(syncEx.getCause() instanceof StreamIoException);
        
        // The database has failed (bergdb 005-30; before, the next transaction's append
        // failed in store(), after its go point, and failed it, bergdb 005-01): it refuses
        // what comes after it, with the sync's StreamIoException as the cause.
        DbFailedException ex = null;
        try {
            db2.execute(db2.trans().put("my-string-key-3", new byte[0]));
        } catch (DbFailedException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
        Assert.assertTrue(ex.getCause() instanceof StreamIoException);
        
        ex = null;
        try {
            db2.execute(db2.trans().put("my-string-key-4", new byte[0]));
        } catch (DbFailedException e) {
            ex = e;
        }
        Assert.assertTrue(ex != null);
        Assert.assertTrue(ex.getCause() instanceof StreamIoException);
        
        db2.stop();
    }
    
    /** A FileStreamIo whose file forces take sleepMs longer, and that counts them (005-48). */
    private static final class SlowForces extends FileStreamIo {
        volatile int sleepMs = 0;
        final AtomicInteger forces = new AtomicInteger();
        
        protected void forceFile(File file, RandomAccessFile handle) throws IOException {
            forces.incrementAndGet();
            if (sleepMs > 0) {
                try {
                    Thread.sleep(sleepMs);
                } catch (InterruptedException e) {
                    throw new IOException(e);
                }
            }
            super.forceFile(file, handle);
        }
    }
    
    /**
     * Group commit (2026-10-27, bergdb 005-48): a sync after a single commit returns within
     * about one force of the stream's file, here made 50 ms longer, as the sync has the
     * write buffer written at once. Before, it waited for the buffer's timer, about the
     * buffer time (60 s here; 4 s until bergdb 021-28, with a bound of 250 ms that load
     * could pass), and then for the force.
     */
    @Nano
    public static void testSyncAfterOneCommitWaitsForOneForce(TestEnvironment env)
            throws IOException {
        SlowForces io = new SlowForces();
        DbBuilder b = Db.builder();
        b.testSetupExceptStream();
        Db db = b.stream("main", new FileStream(env.createTempDir(), io), 100 * 1000, 60000)
                .start();
        try {
            db.execute(db.trans().put("/a", new byte[100]).build());
            db.sync(SyncLevel.ORDINARY);
            
            io.sleepMs = 50;
            int forces = io.forces.get();
            long t0 = System.nanoTime();
            db.execute(db.trans().put("/b", new byte[100]).build());
            db.sync(SyncLevel.ORDINARY);
            long ms = (System.nanoTime() - t0) / 1000000;
            Assert.assertEquals("forces during the sync", 1, io.forces.get() - forces);
            // At least the force's 50 ms; the upper bound only a hang guard (bergdb 028-23:
            // 60 s, 5 s until then).
            Assert.assertTrue("the sync took " + ms + " ms", ms >= 50 && ms < 60000);
        } finally {
            io.sleepMs = 0;
            db.close();
        }
    }
    
    /**
     * bergdb 015-78 (review R5-F1): a close of the stream that fails, once, is reported by
     * the database's close(), and by every later close(). The storage thread closed the
     * stream as it ended and dropped the IOException; BufferedStream.close() closed it again,
     * which worked, and close() returned as if the close had worked.
     */
    @Nano
    public static void testFirstCloseFailureIsReported() {
        final AtomicInteger closes = new AtomicInteger();
        final MemoryStream inner = new MemoryStream();
        AppendOnlyStream s = new AppendOnlyStream() {
            public long getLength() { return inner.getLength(); }
            public long getFirstPos() { return inner.getFirstPos(); }
            public void append(byte[] bytes, int off, int len) throws IOException {
                inner.append(bytes, off, len);
            }
            public void read(long pos, byte[] bytes, int off, int len) throws IOException {
                inner.read(pos, bytes, off, len);
            }
            public void pretruncate(long pos) throws IOException { inner.pretruncate(pos); }
            public void close() throws IOException {
                inner.close();
                if (closes.incrementAndGet() == 1) {
                    throw new IOException("the first close fails");
                }
            }
        };
        Db db = Db.builder().testSetup(s).start();
        db.execute(db.trans().put("/a", "a0").build());
        for (int i = 0; i < 2; i++) {
            StreamIoException failure = null;
            try {
                db.close();
            } catch (StreamIoException e) {
                failure = e;
            }
            Assert.assertTrue("close() " + i + " reports the failed close; closes: "
                    + closes.get(), failure != null);
            Assert.assertEquals("the first close fails", failure.getCause().getMessage());
        }
    }
}
