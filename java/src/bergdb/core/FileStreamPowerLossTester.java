package bergdb.core;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StorageManager;
import bergdb.stream.BadDirStateException;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;

/**
 * Power-loss model over the production FileStream operations. Volatile data,
 * forced data and durable directory names are separate. Deletions can survive
 * without a directory force. Recovery always uses a new directory and Db.
 * This proves tested ordering under the model, not physical hardware behavior.
 * In bergdb.core, not bergdb.stream: it also runs StorageManager and Db over
 * the model, and stream must not depend on storage or core (package.html).
 * 
 * @author Frans Lundberg
 */
public class FileStreamPowerLossTester {
    static final long SEC = Clock.UNITS_PER_SEC;

    static class Image {
        final String event;
        final Map<String, byte[]> files;
        final long acknowledgedTime;
        final long logicalNow, acknowledgedFrontier;

        Image(String event, Map<String, byte[]> files, long acknowledgedTime,
                long logicalNow, long acknowledgedFrontier) {
            this.event = event;
            this.files = files;
            this.acknowledgedTime = acknowledgedTime;
            this.logicalNow = logicalNow;
            this.acknowledgedFrontier = acknowledgedFrontier;
        }

        long end() {
            long end = 0;
            for (Map.Entry<String, byte[]> e : files.entrySet()) {
                long start = Long.parseLong(e.getKey().substring(0, 14)) * 100000;
                end = Math.max(end, start + e.getValue().length);
            }
            return end;
        }

        File restore() throws IOException {
            File dir = Files.createTempDirectory("bergdb-power-recovery-").toFile();
            for (Map.Entry<String, byte[]> e : files.entrySet()) {
                Files.write(new File(dir, e.getKey()).toPath(), e.getValue());
            }
            return dir;
        }
    }

    /** Force operations are modeled, not delegated to the actual disk. */
    static class ModelIo extends FileStreamIo {
        final File dir;
        final Map<String, byte[]> forced = new TreeMap<String, byte[]>();
        final Set<String> names = new TreeSet<String>();
        final AtomicLong acknowledged = new AtomicLong();
        final AtomicLong logicalNow = new AtomicLong(SEC);
        final AtomicLong acknowledgedFrontier = new AtomicLong();
        final Map<String, byte[]> pendingDeleted = new TreeMap<String, byte[]>();
        final Map<String, List<Image>> images = new LinkedHashMap<String, List<Image>>();
        final Map<String, Integer> seen = new TreeMap<String, Integer>();
        final Random random;
        final int perEvent;
        final List<RandomAccessFile> handles = new ArrayList<RandomAccessFile>();
        boolean recording;
        boolean omitFileForce, omitDirectoryForce;
        boolean failFileForce, failDirectoryForce;
        int failDeleteAt, deletes, deletesSinceDirectoryForce, maxDeleteBatch;

        ModelIo(File dir, long seed, int perEvent) {
            this.dir = dir;
            this.random = new Random(seed);
            this.perEvent = perEvent;
        }

        synchronized Map<String, byte[]> durableFiles() {
            Map<String, byte[]> result = new TreeMap<String, byte[]>();
            for (String name : names) {
                byte[] bytes = forced.get(name);
                // A directory entry can survive before a file has any forced data.
                result.put(name, bytes == null ? new byte[0] : bytes);
            }
            return result;
        }

        synchronized Image image(String event) {
            return new Image(event, durableFiles(), acknowledged.get(),
                    logicalNow.get(), acknowledgedFrontier.get());
        }

        synchronized void checkpoint(String event) throws IOException {
            if (!recording) return;
            keep(event, image(event));
        }

        void keep(String event, Image image) {
            int count = seen.containsKey(event) ? seen.get(event) + 1 : 1;
            seen.put(event, count);
            List<Image> bucket = images.get(event);
            if (bucket == null) {
                images.put(event, bucket = new ArrayList<Image>());
            }
            if (bucket.size() < perEvent) bucket.add(image);
            else {
                int replace = random.nextInt(count);
                if (replace < perEvent) bucket.set(replace, image);
            }
        }

        protected synchronized RandomAccessFile open(File file) throws IOException {
            checkpoint("before_open");
            RandomAccessFile handle = super.open(file);
            handles.add(handle);
            checkpoint("after_open");
            return handle;
        }

        protected synchronized void write(File file, RandomAccessFile handle, byte[] bytes,
                int offset, int length) throws IOException {
            checkpoint("before_write");
            super.write(file, handle, bytes, offset, length);
            checkpoint("after_write");
            // Power loss may also retain an arbitrary prefix of the unforced tail.
            // This is independent of the force outcome and does not change the model.
            if (recording && names.contains(file.getName())) {
                Map<String, byte[]> partial = durableFiles();
                byte[] current = Files.readAllBytes(file.toPath());
                byte[] old = partial.get(file.getName());
                int previous = old == null ? 0 : old.length;
                int end = previous + (current.length - previous) / 2;
                partial.put(file.getName(), Arrays.copyOf(current, end));
                keep("partial_write", new Image("partial_write", partial, acknowledged.get(),
                        logicalNow.get(), acknowledgedFrontier.get()));
            }
        }

        protected synchronized void forceFile(File file, RandomAccessFile handle) throws IOException {
            checkpoint("before_file_force");
            if (failFileForce) throw new IOException("injected file force failure");
            if (!omitFileForce) forced.put(file.getName(), Files.readAllBytes(file.toPath()));
            checkpoint("after_file_force");
        }

        protected synchronized void forceDirectory(File directory) throws IOException {
            checkpoint("before_directory_force");
            if (failDirectoryForce) throw new IOException("injected directory force failure");
            if (!omitDirectoryForce && directory.getAbsoluteFile().equals(dir.getAbsoluteFile())) {
                names.clear();
                File[] files = directory.listFiles();
                if (files == null) throw new IOException("cannot list model directory");
                for (File file : files) {
                    if (file.getName().endsWith(".bergdb")) names.add(file.getName());
                }
                pendingDeleted.clear();
                maxDeleteBatch = Math.max(maxDeleteBatch, deletesSinceDirectoryForce);
                deletesSinceDirectoryForce = 0;
            }
            checkpoint("after_directory_force");
        }

        protected synchronized boolean delete(File file) throws IOException {
            checkpoint("before_delete");
            if (failDeleteAt > 0 && deletes + 1 == failDeleteAt) {
                throw new IOException("injected deletion failure");
            }
            boolean result = super.delete(file);
            if (result) {
                if (names.contains(file.getName())) {
                    byte[] before = forced.get(file.getName());
                    pendingDeleted.put(file.getName(), before == null ? new byte[0] : before);
                }
                // Adversarial but allowed: unlink survives power loss immediately.
                names.remove(file.getName());
                forced.remove(file.getName());
                deletes++;
                deletesSinceDirectoryForce++;
            }
            checkpoint("after_delete");
            if (recording && result) {
                // Alternatively only the latest unforced unlink survives. Earlier
                // unforced removals can roll back, leaving a hole unless each is forced.
                Map<String, byte[]> unordered = durableFiles();
                for (Map.Entry<String, byte[]> deleted : pendingDeleted.entrySet()) {
                    if (!deleted.getKey().equals(file.getName())) unordered.put(deleted.getKey(), deleted.getValue());
                }
                keep("unordered_delete", new Image("unordered_delete", unordered, acknowledged.get(),
                        logicalNow.get(), acknowledgedFrontier.get()));
                Map<String, byte[]> rollback = durableFiles();
                byte[] before = pendingDeleted.get(file.getName());
                if (before != null) rollback.put(file.getName(), before);
                keep("unpersisted_delete", new Image("unpersisted_delete", rollback, acknowledged.get(),
                        logicalNow.get(), acknowledgedFrontier.get()));
            }
            return result;
        }

        protected synchronized boolean rename(File file, File destination) throws IOException {
            checkpoint("before_rename");
            boolean result = super.rename(file, destination);
            if (result) names.remove(file.getName());
            checkpoint("after_rename");
            return result;
        }

        List<Image> snapshots() {
            List<Image> result = new ArrayList<Image>();
            for (List<Image> bucket : images.values()) result.addAll(bucket);
            return result;
        }
    }

    @Nano
    public static void testUnforcedBytesCanBeLostAfterDeletion() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-model-").toFile();
        ModelIo io = new ModelIo(dir, 1, 1);
        FileStream stream = new FileStream(dir, io);
        try {
            byte[] first = new byte[400000];
            Arrays.fill(first, (byte) 1);
            stream.append(first, 0, first.length);
            io.omitFileForce = true;
            byte[] replacement = new byte[200000];
            Arrays.fill(replacement, (byte) 2);
            stream.append(replacement, 0, replacement.length);
            stream.pretruncate(400000);
            stream.awaitDeletes();      // The cut's thread deletes (bergdb 005-46).
            Assert.assertTrue("deletion did not survive", io.deletes >= 2);
            Assert.assertTrue("model incorrectly made replacements durable at cut",
                    io.image("power loss").end() < stream.getLength());
        } finally { stream.close(); remove(dir); }
    }

    @Nano
    public static void testMissingDirectoryForceLosesReplacementFile() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-names-").toFile();
        ModelIo io = new ModelIo(dir, 2, 1);
        FileStream stream = new FileStream(dir, io);
        try {
            stream.append(new byte[200000], 0, 200000);
            io.omitDirectoryForce = true;
            stream.append(new byte[100], 0, 100);
            stream.pretruncate(200000);
            stream.awaitDeletes();
            Assert.assertTrue("replacement name should be lost", io.durableFiles().isEmpty());
        } finally { stream.close(); remove(dir); }
    }

    // This and the next two are f-tests: the sync after the failed force returns at
    // StorageManager's next 500 ms poll, as nothing wakes it.
    @Nano("f")
    public static void testSyncDoesNotAdvanceAfterFailedFileForce() throws Exception {
        testFailedForce(false);
    }

    @Nano("f")
    public static void testSyncDoesNotAdvanceAfterFailedDirectoryForce() throws Exception {
        testFailedForce(true);
    }

    static void testFailedForce(boolean directory) throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-failure-").toFile();
        ModelIo io = new ModelIo(dir, 3, 1);
        FileStream stream = new FileStream(dir, io);
        Object lock = new Object();
        StorageManager manager = new StorageManager.Builder()
                .stream(stream, 500000, 10).build();
        try {
            synchronized (lock) { manager.start(); }
            if (directory) io.failDirectoryForce = true;
            else io.failFileForce = true;
            byte[] data = new byte[directory ? 200100 : 100];
            synchronized (lock) { manager.append(data, 0, data.length); }
            try {
                manager.sync(data.length);
                throw new AssertionError("failed force was acknowledged");
            } catch (IOException expected) { }
            Assert.assertEquals(0, manager.getDurableLength());
        } finally {
            manager.stop();
            for (RandomAccessFile handle : io.handles) {
                Assert.assertTrue("failed storage leaked a file handle", !handle.getFD().valid());
            }
            remove(dir);
        }
    }

    @Nano
    public static void testDurableFrontierWaitsForForce() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-barrier-").toFile();
        final CountDownLatch entered = new CountDownLatch(1), release = new CountDownLatch(1);
        ModelIo io = new ModelIo(dir, 4, 1) {
            volatile boolean gate;
            protected void write(File file, RandomAccessFile handle, byte[] bytes, int offset, int length)
                    throws IOException {
                gate = true;
                super.write(file, handle, bytes, offset, length);
            }
            protected void forceFile(File file, RandomAccessFile handle) throws IOException {
                if (gate) {
                    entered.countDown();
                    try {
                        if (!release.await(5, TimeUnit.SECONDS)) throw new IOException("force barrier timed out");
                    } catch (InterruptedException e) { Thread.currentThread().interrupt(); throw new IOException(e); }
                }
                super.forceFile(file, handle);
            }
        };
        Object lock = new Object();
        StorageManager manager = new StorageManager.Builder()
                .stream(new FileStream(dir, io), 1000, 10).build();
        try {
            synchronized (lock) { manager.start(); manager.append(new byte[100], 0, 100); }
            Assert.assertTrue("force not reached", entered.await(5, TimeUnit.SECONDS));
            Assert.assertEquals(0, manager.getDurableLength());
            release.countDown();
            manager.sync(100);
            Assert.assertEquals(100, manager.getDurableLength());
            Assert.assertEquals(100, io.image("after force").end());
        } finally { release.countDown(); manager.stop(); remove(dir); }
    }

    @Nano("f")
    public static void testPendingCutForceFailureFailsTheStream() throws Exception {
        // Since 2026-10-27 (bergdb 005-46) the cut's thread deletes; a failed delete or
        // directory force fails the stream at its next operation, and the flush before it,
        // whose bytes are forced, stays acknowledged (Frans: "Yes"). Before, the failure kept
        // that flush from being acknowledged (bergdb 011-07).
        File dir = Files.createTempDirectory("bergdb-power-pending-cut-").toFile();
        final CountDownLatch entered = new CountDownLatch(1), release = new CountDownLatch(1);
        ModelIo io = new ModelIo(dir, 7, 1) {
            volatile boolean gate;
            protected void write(File file, RandomAccessFile handle, byte[] bytes, int offset, int length)
                    throws IOException {
                gate = true;
                super.write(file, handle, bytes, offset, length);
            }
            protected void forceFile(File file, RandomAccessFile handle) throws IOException {
                if (gate) {
                    entered.countDown();
                    try {
                        if (!release.await(5, TimeUnit.SECONDS)) throw new IOException("pending-cut barrier timed out");
                    } catch (InterruptedException e) { Thread.currentThread().interrupt(); throw new IOException(e); }
                }
                super.forceFile(file, handle);
            }
            protected synchronized void forceDirectory(File directory) throws IOException {
                if (deletes > 0) throw new IOException("injected pending-cut directory force failure");
                super.forceDirectory(directory);
            }
        };
        Object lock = new Object();
        FileStream stream = new FileStream(dir, io);
        StorageManager manager = new StorageManager.Builder()
                .stream(stream, 500000, 10).build();
        try {
            synchronized (lock) {
                manager.start();
                manager.append(new byte[200100], 0, 200100);
            }
            Assert.assertTrue("append force not reached", entered.await(5, TimeUnit.SECONDS));
            synchronized (lock) { manager.pretruncate(200000); }
            release.countDown();
            manager.sync(200100);
            Assert.assertEquals(200100, manager.getDurableLength());
            try { stream.awaitDeletes(); throw new AssertionError("failed cut not passed on"); }
            catch (IOException expected) { }
            Assert.assertEquals(1, io.deletes);
            try {
                synchronized (lock) { manager.append(new byte[100], 0, 100); }
                manager.sync(200200);
                throw new AssertionError("the stream went on after a failed cut");
            } catch (IOException expected) { }
            Assert.assertEquals(200100, manager.getDurableLength());
        } finally { release.countDown(); manager.stop(); remove(dir); }
    }

    @Nano
    public static void testPartialDeletionAndDirectoryFailureKeepForcedBytes() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-delete-").toFile();
        ModelIo io = new ModelIo(dir, 5, 1);
        FileStream stream = new FileStream(dir, io);
        byte[] data = new byte[1000000];
        Arrays.fill(data, (byte) 7);
        try {
            stream.append(data, 0, data.length);
            io.failDeleteAt = 2;
            // The cut's thread deletes; its failure is the stream's (bergdb 005-46).
            stream.pretruncate(800000);
            try { stream.awaitDeletes(); throw new AssertionError("delete should fail"); }
            catch (IOException expected) { }
            Image crash = io.image("partial deletion");
            Assert.assertEquals(1, io.deletes);
            Assert.assertEquals(1000000, crash.end());
            File recovered = crash.restore();
            FileStream reopened = new FileStream(recovered);
            try {
                byte[] tail = new byte[200000];
                reopened.read(800000, tail, 0, tail.length);
                for (byte value : tail) Assert.assertEquals(7, value);
            } finally { reopened.close(); remove(recovered); }
        } finally { closeFaulted(stream); remove(dir); }

        dir = Files.createTempDirectory("bergdb-power-delete-dir-").toFile();
        io = new ModelIo(dir, 6, 1);
        stream = new FileStream(dir, io);
        try {
            stream.append(data, 0, data.length);
            io.failDirectoryForce = true;
            stream.pretruncate(800000);
            try { stream.awaitDeletes(); throw new AssertionError("directory force should fail"); }
            catch (IOException expected) { }
            Assert.assertEquals("deletion continued after failed namespace force", 1, io.deletes);
            Assert.assertEquals(1000000, io.image("directory failure").end());
        } finally { closeFaulted(stream); remove(dir); }
    }

    @Nano
    public static void testRecoveryBetweenEveryPrefixDeletion() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-delete-order-").toFile();
        ModelIo io = new ModelIo(dir, 21, 5);
        FileStream stream = new FileStream(dir, io);
        byte[] data = new byte[1000000]; Arrays.fill(data, (byte) 31);
        try {
            stream.append(data, 0, data.length);
            io.recording = true;
            stream.pretruncate(800000);
            stream.awaitDeletes();
            Assert.assertEquals(4, io.deletes);
            Assert.assertEquals(1, io.maxDeleteBatch);
            for (Image image : io.snapshots()) {
                File recovered = image.restore();
                FileStream reopened = new FileStream(recovered);
                try {
                    byte[] tail = new byte[200000]; reopened.read(800000, tail, 0, tail.length);
                    for (byte value : tail) Assert.assertEquals(31, value);
                } finally { reopened.close(); remove(recovered); }
            }
        } finally { stream.close(); remove(dir); }
    }

    @Nano
    public static void testUnorderedUnforcedDeletionsAreDetected() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-unordered-").toFile();
        ModelIo io = new ModelIo(dir, 22, 5);
        FileStream stream = new FileStream(dir, io);
        try {
            stream.append(new byte[1000000], 0, 1000000);
            io.recording = true; io.omitDirectoryForce = true;
            stream.pretruncate(800000);
            stream.awaitDeletes();
            boolean caught = false;
            for (Image image : io.images.get("unordered_delete")) {
                File recovered = image.restore();
                FileStream reopened = null;
                try { reopened = new FileStream(recovered); }
                catch (BadDirStateException expected) { caught = true; }
                finally { if (reopened != null) reopened.close(); remove(recovered); }
            }
            Assert.assertTrue("unordered deletion negative control escaped", caught);
        } finally { stream.close(); remove(dir); }
    }

    static class Change {
        final long time;
        final String key;
        final byte[] value;
        Change(long time, String key, byte[] value) { this.time = time; this.key = key; this.value = value; }
    }

    static class DetectedLoss extends AssertionError {
        private static final long serialVersionUID = 1L;
        DetectedLoss(String event, Throwable cause) {
            super("weakened ordering lost recovery at " + event);
            initCause(cause);
        }
    }

    static String key(int i) { return "/history/long-key-segment-" + i; }

    static Db start(FileStream stream, CoreTestClock clock) {
        return Db.builder().testSetup(stream).clock(clock).startupDistance(20000)
                .retainDuration(2 * SEC).start();
    }

    static void verify(Image image, List<Change> changes, int keys, long lastTime, boolean exhaustive)
            throws Exception {
        if (image.files.isEmpty() && image.acknowledgedTime > 0) {
            throw new AssertionError(image.event + ": lost all backing file names after an acknowledged commit");
        }
        File dir = image.restore();
        Db db = null;
        try {
            CoreTestClock clock = new CoreTestClock();
            clock.setTime(lastTime + SEC);
            db = start(new FileStream(dir), clock);
            long actual = db.lookupTime(Long.MAX_VALUE);
            if (actual < image.acknowledgedTime) {
                throw new AssertionError(image.event + ": acknowledged time " + image.acknowledgedTime
                        + " lost; recovered " + actual);
            }
            long first = db.getFirstAvailableLookupTime();
            if (first > actual || first > image.logicalNow - 2 * SEC
                    || first < image.acknowledgedFrontier) {
                throw new AssertionError(image.event + ": invalid retained frontier " + first);
            }
            TreeMap<String, TreeMap<Long, byte[]>> model = new TreeMap<String, TreeMap<Long, byte[]>>();
            List<Long> times = new ArrayList<Long>();
            for (Change change : changes) {
                TreeMap<Long, byte[]> history = model.get(change.key);
                if (history == null) model.put(change.key, history = new TreeMap<Long, byte[]>());
                history.put(change.time, change.value);
                if (change.time >= first && change.time <= actual) times.add(change.time);
            }
            check(db, model, keys, actual, image.event);
            int stride = exhaustive ? 1 : Math.max(1, times.size() / 32);
            for (int i = 0; i < times.size(); i += stride) check(db, model, keys, times.get(i), image.event);
            db.checkNodes();
            // The recovered database must remain writable, durable and restartable.
            String freshKey = "/after-power-loss";
            clock.setTime(lastTime + 2 * SEC);
            byte[] value = new byte[] {9, 8, 7};
            db.execute(db.trans().put(freshKey, value).build());
            db.sync(SyncLevel.ORDINARY);
            db.close(); db = null;      // Closed before the directory opens again (bergdb 005-63).
            CoreTestClock clock2 = new CoreTestClock(); clock2.setTime(lastTime + 3 * SEC);
            db = start(new FileStream(dir), clock2);
            if (!Arrays.equals(value, DbUtil.get(db, Long.MAX_VALUE, freshKey))) {
                throw new AssertionError(image.event + ": write/sync/restart after recovery failed");
            }
            check(db, model, keys, actual, image.event + ", second restart");
        } finally {
            if (db != null) db.close();     // close() waits for the cut's deletes (bergdb 015-16)
            remove(dir);
        }
    }

    static void check(Db db, TreeMap<String, TreeMap<Long, byte[]>> model, int keys, long time, String where) {
        for (int i = 0; i < keys; i++) {
            TreeMap<Long, byte[]> history = model.get(key(i));
            Map.Entry<Long, byte[]> last = history == null ? null : history.floorEntry(time);
            byte[] expected = last == null ? null : last.getValue();
            byte[] actual = DbUtil.get(db, time, key(i));
            if (!Arrays.equals(expected, actual)) throw new AssertionError(where + ": " + key(i) + " at " + time);
        }
    }

    /** Called by the full gate and stress runner; parameters are reproducible. */
    public static int runTrace(long seed, int transactions, int perEvent, boolean negativeFile,
            boolean negativeDirectory, boolean exhaustive) throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-trace-").toFile();
        ModelIo io = new ModelIo(dir, seed, perEvent);
        CoreTestClock clock = new CoreTestClock(); clock.setTime(SEC);
        FileStream stream = new FileStream(dir, io);
        Db db = start(stream, clock);
        Random random = new Random(seed);
        List<Change> changes = new ArrayList<Change>();
        long previousIteration = 0, previousStartup = 0;
        long previousFrontier = 0;
        int keys = 12;
        long time = SEC;
        try {
            for (int i = 0; i < transactions; i++) {
                time += SEC / 10; io.logicalNow.set(time); clock.setTime(time);
                String key = key(random.nextInt(keys));
                byte[] value = null;
                Trans transaction;
                if (i % 11 == 0) transaction = db.trans().delete(key).build();
                else {
                    value = new byte[i % 37 == 0 ? 18000 : 1000 + random.nextInt(1000)];
                    random.nextBytes(value);
                    transaction = db.trans().put(key, value).build();
                }
                db.execute(transaction);
                // The cut's thread deletes after the commit (bergdb 005-46); waiting for it
                // keeps the order of the trace's events, and so its images, deterministic.
                stream.awaitDeletes();
                changes.add(new Change(transaction.tt, key, value));
                long iteration = db.getReclaimIterationCount();
                long startup = db.internal().getStartupPosForEvict();
                long frontier = db.getFirstAvailableLookupTime();
                if (io.recording) {
                    io.checkpoint("after_user_commit");
                    if (iteration != previousIteration) io.checkpoint("after_iteration_end");
                    if (startup != previousStartup) io.checkpoint("after_writeout_progress");
                    if (frontier != previousFrontier) io.checkpoint("after_cut_decision");
                }
                previousIteration = iteration;
                previousStartup = startup;
                previousFrontier = frontier;
                if (i % 5 == 0) {
                    db.sync(SyncLevel.ORDINARY);
                    io.acknowledged.set(db.lookupTime(Long.MAX_VALUE));
                    io.acknowledgedFrontier.set(db.getFirstAvailableLookupTime());
                    if (i >= 30 && !io.recording) {
                        io.recording = true;
                        io.omitFileForce = negativeFile;
                        io.omitDirectoryForce = negativeDirectory;
                    }
                    io.checkpoint("after_durable_publication");
                }
            }
            db.sync(SyncLevel.ORDINARY);
            io.acknowledged.set(db.lookupTime(Long.MAX_VALUE));
            io.acknowledgedFrontier.set(db.getFirstAvailableLookupTime());
            io.checkpoint("final_acknowledgement");
            db.close(); db = null;
            if (io.deletes < 2) throw new AssertionError("trace did not exercise physical deletion: " + io.deletes);
            List<Image> cases = negativeFile || negativeDirectory ? io.images.get("after_delete") : io.snapshots();
            if (cases == null || cases.isEmpty()) throw new AssertionError("no power-loss checkpoints");
            int checked = 0;
            for (Image image : cases) {
                try {
                    verify(image, changes, keys, time, exhaustive);
                } catch (BadDirStateException failure) {
                    if (negativeFile || negativeDirectory) throw new DetectedLoss(image.event, failure);
                    throw failure;
                } catch (AssertionError failure) {
                    if (negativeFile || negativeDirectory) throw new DetectedLoss(image.event, failure);
                    throw failure;
                }
                checked++;
            }
            System.out.println("POWER TRACE seed=" + seed + " checkpoints=" + checked
                    + " physical_deletes=" + io.deletes + " stages=" + io.seen);
            return checked;
        } finally { if (db != null) db.close(); remove(dir); }
    }

    @Nano("f")
    public static void testColdRecoveryAtPersistenceBoundaries() throws Exception {
        runTrace(17, 600, 1, false, false, true);
    }

    @Nano("f")
    public static void testWeakenedForceOrderingIsDetected() throws Exception {
        for (boolean file : new boolean[] {true, false}) {
            boolean caught = false;
            try { runTrace(19, 600, 2, file, !file, false); }
            catch (DetectedLoss expected) {
                caught = true;
                System.out.println("NEGATIVE CONTROL " + (file ? "file" : "directory")
                        + " force caught: " + expected.getCause());
            }
            Assert.assertTrue("weakened " + (file ? "file" : "directory") + " force escaped recovery tests", caught);
        }
    }

    static void remove(File file) throws IOException {
        if (file.isDirectory()) {
            File[] children = file.listFiles();
            if (children == null) throw new IOException("cannot list " + file);
            for (File child : children) remove(child);
        }
        if (file.exists() && !file.delete()) throw new IOException("cannot delete test file " + file);
    }

    static void closeFaulted(FileStream stream) {
        try { stream.close(); } catch (IOException expected) { }
    }
}
