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

import bergdb.common.Bytes;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.StorageManager;
import bergdb.storage.StreamFormatException;
import bergdb.storage.StreamIoException;
import bergdb.stream.BadDirStateException;
import bergdb.stream.FileStream;
import bergdb.stream.FileStreamIo;
import bergdb.stream.ReadBelowFirstPosException;

/**
 * Power-loss model over the production FileStream operations. Volatile data,
 * forced data and durable directory names are separate. Deletions can survive
 * without a directory force. Recovery always uses a new directory and Db.
 * This proves tested ordering under the model, not physical hardware behavior.
 * In bergdb.core, not bergdb.stream: it also runs StorageManager and Db over
 * the model, and stream must not depend on storage or core (package.html).
 * 
 * The deletes of a cut (2026-11-27, bergdb 028-66). The cut's thread deletes a batch of
 * files with one force of the directory after it (FileStream.runCuts). An unforced unlink
 * may survive a power loss while an earlier one rolls back, in any combination: the images
 * unordered_delete (only the latest pending unlink survives), unpersisted_delete (the
 * latest rolls back) and subset_delete (a random subset of the pending unlinks survives)
 * leave gaps in the files' sequence. FileStream's open takes the files after the last gap
 * as the stream, and each such image must start, hold every acknowledged commit, and have
 * its start delete the files before the gap, which it does only after it has found each
 * one's first meta block to be the database's (Frans, 2026-11-27; RecoverableStream,
 * checkLeftovers()); a file before a gap that is not the database's is refused
 * (testStartRefusesAFileBeforeAGapThatIsNotTheDatabases). Until 2026-11-27 the thread forced
 * the directory after each file, and a gap image was the negative control of that order
 * (BadDirStateException at the open).
 * 
 * Without per-append forces (2026-11-04, bergdb 005-47): runTraceWithoutAppendForces runs
 * the trace on a FileStream with per-append forcing off. A sync then means written, and an
 * image keeps what was acknowledged when the last file force began, not the last sync. Its
 * images also have holes in the unforced tail (hole_write: a page, or a part of a short
 * tail, zeros with later bytes intact). Recovery does not handle holes (bergdb 005-83; open
 * in 014-01), so the hole images are counted, recovered or failed, and do not fail the
 * trace; every other image must recover. Its negative controls leave out the force before
 * a new file (SWITCH) or before a cut's deletes (CUT), and must fail.
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
        /** The FileStream's per-append forcing (bergdb 005-47); off, the images have holes. */
        boolean appendForces = true;
        /** A kind of file force left out, a negative control without per-append forces. */
        FileStreamIo.Force omitForce;
        /** What was acknowledged when the last modeled file force began (bergdb 005-47). */
        long forcedAcknowledged, forcedFrontier;
        final Map<FileStreamIo.Force, Integer> forces =
                new TreeMap<FileStreamIo.Force, Integer>();
        final List<Image> holes = new ArrayList<Image>();
        int holeCount;
        boolean failFileForce, failDirectoryForce;
        int failDeleteAt, deletes, deletesSinceDirectoryForce, maxDeleteBatch;
        /**
         * While true, the cut's thread waits at its next delete, outside this model's monitor,
         * so that the cuts meanwhile queue a batch of several files (bergdb 028-66). Under
         * 'gate'.
         */
        boolean gated;
        final Object gate = new Object();

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
            return new Image(event, durableFiles(), acknowledgedTime(),
                    logicalNow.get(), acknowledgedFrontier());
        }
        
        /**
         * The acknowledged time an image must keep. Without per-append forces, a sync does
         * not force: what it acknowledged is durable only after a file force (bergdb 005-47).
         */
        synchronized long acknowledgedTime() {
            return appendForces ? acknowledged.get() : forcedAcknowledged;
        }
        
        /** The acknowledged frontier an image must keep; as acknowledgedTime(). */
        synchronized long acknowledgedFrontier() {
            return appendForces ? acknowledgedFrontier.get() : forcedFrontier;
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
                keep("partial_write", new Image("partial_write", partial, acknowledgedTime(),
                        logicalNow.get(), acknowledgedFrontier()));
                if (!appendForces) {
                    keepHole(file.getName(), current, previous);
                }
            }
        }
        
        /**
         * Without per-append forces (bergdb 005-47), the OS may write the unforced tail out of
         * order: keeps an image of the whole tail with a hole of zeros in it, and later bytes
         * intact. The hole is a random 4,096-byte page of the file inside the unforced tail
         * and before its last byte, or, in a tail too short for that, its middle third. A
         * hole that changes no byte is no hole and is not kept. At most 4 * perEvent images,
         * by reservoir sampling.
         */
        void keepHole(String name, byte[] current, int previous) {
            final int page = 4096;
            int from, to;
            int firstPage = (previous + page - 1) / page;
            int pages = (current.length - 1) / page - firstPage;   // Pages that end before the last byte.
            if (pages > 0) {
                from = (firstPage + random.nextInt(pages)) * page;
                to = from + page;
            } else {
                int n = current.length - previous;
                if (n < 3) return;
                from = previous + n / 3;
                to = previous + 2 * n / 3;
            }
            boolean changes = false;
            for (int i = from; i < to; i++) {
                if (current[i] != 0) { changes = true; break; }
            }
            if (!changes) return;
            Map<String, byte[]> files = durableFiles();
            byte[] bytes = current.clone();
            Arrays.fill(bytes, from, to, (byte) 0);
            files.put(name, bytes);
            Image hole = new Image("hole_write " + name + " [" + from + ", " + to + ")", files, 
                    acknowledgedTime(), logicalNow.get(), acknowledgedFrontier());
            holeCount++;
            if (holes.size() < 4 * perEvent) holes.add(hole);
            else {
                int replace = random.nextInt(holeCount);
                if (replace < holes.size()) holes.set(replace, hole);
            }
        }

        protected synchronized void forceFile(File file, RandomAccessFile handle, 
                FileStreamIo.Force why) throws IOException {
            forces.put(why, forces.containsKey(why) ? forces.get(why) + 1 : 1);
            if (why == omitForce) {
                checkpoint("omitted_force");
                return;
            }
            super.forceFile(file, handle, why);
        }

        protected synchronized void forceFile(File file, RandomAccessFile handle) throws IOException {
            checkpoint("before_file_force");
            if (failFileForce) throw new IOException("injected file force failure");
            if (!omitFileForce) {
                // What was acknowledged before the force is written, in this file or in an
                // earlier one, forced before the stream moved on (bergdb 005-47).
                long acknowledgedBefore = acknowledged.get();
                long frontierBefore = acknowledgedFrontier.get();
                forced.put(file.getName(), Files.readAllBytes(file.toPath()));
                forcedAcknowledged = acknowledgedBefore;
                forcedFrontier = frontierBefore;
            }
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

        void hold() {
            synchronized (gate) { gated = true; }
        }
        
        void release() {
            synchronized (gate) { gated = false; gate.notifyAll(); }
        }
        
        protected boolean delete(File file) throws IOException {
            synchronized (gate) {
                while (gated) {
                    try { gate.wait(); }
                    catch (InterruptedException e) { throw new IOException(e); }
                }
            }
            return modelDelete(file);
        }
        
        synchronized boolean modelDelete(File file) throws IOException {
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
                keep("unordered_delete", new Image("unordered_delete", unordered, acknowledgedTime(),
                        logicalNow.get(), acknowledgedFrontier()));
                Map<String, byte[]> rollback = durableFiles();
                byte[] before = pendingDeleted.get(file.getName());
                if (before != null) rollback.put(file.getName(), before);
                keep("unpersisted_delete", new Image("unpersisted_delete", rollback, acknowledgedTime(),
                        logicalNow.get(), acknowledgedFrontier()));
                // Any subset of the pending unlinks survives (bergdb 028-66): here a random one.
                Map<String, byte[]> subset = durableFiles();
                for (Map.Entry<String, byte[]> deleted : pendingDeleted.entrySet()) {
                    if (random.nextBoolean()) subset.put(deleted.getKey(), deleted.getValue());
                }
                Image subsetImage = new Image("subset_delete", subset, acknowledgedTime(),
                        logicalNow.get(), acknowledgedFrontier());
                keep("subset_delete", subsetImage);
                // The images with a gap, also in a bucket of their own, so that a trace checks
                // more of them than the reservoirs of the events keep.
                if (hasGap(subsetImage)) keep("gap_delete", subsetImage);
                Image unorderedImage = new Image("unordered_delete", unordered, acknowledgedTime(),
                        logicalNow.get(), acknowledgedFrontier());
                if (hasGap(unorderedImage)) keep("gap_delete", unorderedImage);
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
            // close(), not stop() (2026-11-10): after the failed force, the storage's thread
            // closes the stream, and stop() returned before that close ended. The next test's
            // new directory got this one's inode (ext4), while the stream was between its
            // close of bergdb.lock and the release of the directory's key, and its FileStream
            // was refused with DirectoryInUseException. close() waits for that thread.
            manager.close();
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
                        if (!release.await(30, TimeUnit.SECONDS)) throw new IOException("force barrier timed out");
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
            Assert.assertTrue("force not reached", entered.await(30, TimeUnit.SECONDS));
            Assert.assertEquals(0, manager.getDurableLength());
            release.countDown();
            manager.sync(100);
            Assert.assertEquals(100, manager.getDurableLength());
            Assert.assertEquals(100, io.image("after force").end());
        } finally { release.countDown(); manager.close(); remove(dir); }     // As testFailedForce.
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
                        if (!release.await(30, TimeUnit.SECONDS)) throw new IOException("pending-cut barrier timed out");
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
            Assert.assertTrue("append force not reached", entered.await(30, TimeUnit.SECONDS));
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
        } finally { release.countDown(); manager.close(); remove(dir); }     // As testFailedForce.
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
            // One batch, its four deletes before its one force (bergdb 028-66), which fails:
            // the stream fails, and no later cut deletes.
            stream.pretruncate(800000);
            try { stream.awaitDeletes(); throw new AssertionError("directory force should fail"); }
            catch (IOException expected) { }
            Assert.assertEquals(4, io.deletes);
            try { stream.pretruncate(900000); throw new AssertionError("cut after a failure"); }
            catch (IOException expected) { }
            Assert.assertEquals("deletion continued after failed namespace force", 4, io.deletes);
            Assert.assertEquals(1000000, io.image("directory failure").end());
        } finally { closeFaulted(stream); remove(dir); }
    }

    /**
     * bergdb 028-66: a cut of four files deletes them as one batch, one force of the directory
     * after it; every image of the model, and every subset of the batch's files that a power
     * loss before the force can leave (16), opens with the bytes from the cut on, its first
     * position at or before the cut, and a cut there on the reopened stream leaves the files
     * from the cut's file on only. Until 2026-11-27 (testRecoveryBetweenEveryPrefixDeletion)
     * the deletes were one at a time, each forced, and only prefixes could survive.
     */
    @Nano
    public static void testRecoveryAfterEverySubsetOfABatch() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-delete-order-").toFile();
        ModelIo io = new ModelIo(dir, 21, 5);
        FileStream stream = new FileStream(dir, io);
        byte[] data = new byte[1000000]; Arrays.fill(data, (byte) 31);
        try {
            stream.append(data, 0, data.length);
            Map<String, byte[]> before = io.durableFiles();
            io.recording = true;
            stream.pretruncate(800000);
            stream.awaitDeletes();
            Assert.assertEquals(4, io.deletes);
            Assert.assertEquals(4, io.maxDeleteBatch);
            List<Image> images = new ArrayList<Image>(io.snapshots());
            List<String> batch = new ArrayList<String>(before.keySet()).subList(0, 4);
            for (int mask = 0; mask < 16; mask++) {
                Map<String, byte[]> files = new TreeMap<String, byte[]>(before);
                for (int i = 0; i < 4; i++) {
                    if ((mask & (1 << i)) == 0) files.remove(batch.get(i));
                }
                images.add(new Image("subset " + mask, files, 0, 0, 0));
            }
            int gaps = 0;
            for (Image image : images) {
                File recovered = image.restore();
                FileStream reopened = new FileStream(recovered);
                try {
                    Assert.assertTrue(image.event, reopened.getFirstPos() <= 800000);
                    if (reopened.getLeftoverCount() > 0) gaps++;
                    byte[] tail = new byte[200000]; reopened.read(800000, tail, 0, tail.length);
                    for (byte value : tail) Assert.assertEquals(31, value);
                    reopened.checkLeftovers((position, length, piece) -> null);
                    reopened.pretruncate(800000);
                    reopened.awaitDeletes();
                } finally { reopened.close(); }
                try {
                    Assert.assertEquals(image.event, Arrays.asList("00000000000008.bergdb"),
                            Arrays.asList(recovered.list((d, name) -> name.endsWith(".bergdb"))));
                } finally { remove(recovered); }
            }
            Assert.assertTrue("gaps " + gaps, gaps >= 11);    // 11 of the 16 subsets have one.
        } finally { stream.close(); remove(dir); }
    }

    /**
     * bergdb 028-66: deletes with no force of the directory, whose images keep the latest
     * unlink and roll back the earlier ones, leave a gap, which the open takes: the stream is
     * the files after it. Until 2026-11-27 this was the negative control of the order of
     * deletes (testUnorderedUnforcedDeletionsAreDetected): the open refused the gap.
     */
    @Nano
    public static void testUnorderedUnforcedDeletionsLeaveAGapThatOpens() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-unordered-").toFile();
        ModelIo io = new ModelIo(dir, 22, 5);
        FileStream stream = new FileStream(dir, io);
        try {
            byte[] data = new byte[1000000]; Arrays.fill(data, (byte) 5);
            stream.append(data, 0, 1000000);
            io.recording = true; io.omitDirectoryForce = true;
            stream.pretruncate(800000);
            stream.awaitDeletes();
            boolean gap = false;
            for (Image image : io.images.get("unordered_delete")) {
                File recovered = image.restore();
                FileStream reopened = new FileStream(recovered);
                try {
                    if (reopened.getLeftoverCount() > 0) gap = true;
                    byte[] tail = new byte[200000]; reopened.read(800000, tail, 0, tail.length);
                    for (byte value : tail) Assert.assertEquals(5, value);
                } finally { reopened.close(); remove(recovered); }
            }
            Assert.assertTrue("no image with a gap", gap);
        } finally { stream.close(); remove(dir); }
    }
    
    /**
     * bergdb 028-66: a database whose stream misses a file of the bytes it needs is refused at
     * its start, with a message that names the gap, and the start leaves the files as they
     * were: nothing deleted, nothing written (the stream ended cleanly, so recovery has
     * nothing to complete). First a middle file removed by hand, a gap in the live stream;
     * then the first file too, no gap, the stream beginning after its cut (0, never cut).
     * Until 2026-11-27 FileStream refused the gap (BadDirStateException), and the second
     * case started and failed at reads.
     */
    @Nano
    public static void testStartRefusesAStreamThatLacksBytes() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-lacks-").toFile();
        try {
            CoreTestClock clock = new CoreTestClock(); clock.setTime(SEC);
            Db db = Db.builder().testSetup(new FileStream(dir)).clock(clock).start();
            try {
                Random random = new Random(66);
                for (int i = 0; i < 400; i++) {
                    clock.setTime(2 * SEC + i * SEC / 10);
                    byte[] value = new byte[2000]; random.nextBytes(value);
                    db.execute(db.trans().put(key(i % 50), value).build());
                }
                db.sync(SyncLevel.ORDINARY);
            } finally { db.close(); }
            Assert.assertTrue(new File(dir, "00000000000006.bergdb").exists());
            
            Assert.assertTrue(new File(dir, "00000000000002.bergdb").delete());
            Map<String, byte[]> files = streamFiles(dir);
            refusedLacking(dir, "gap");
            Assert.assertTrue("the start changed the files", sameFiles(files, streamFiles(dir)));
            
            Assert.assertTrue(new File(dir, "00000000000000.bergdb").delete());
            files = streamFiles(dir);
            refusedLacking(dir, "first position, 400000");
            Assert.assertTrue("the start changed the files", sameFiles(files, streamFiles(dir)));
        } finally { remove(dir); }
    }
    
    /**
     * bergdb 028-66, the rule of the files before a gap (Frans, 2026-11-27): a file of the
     * database before a gap, here its first file, kept before a cut deleted it and put back,
     * is checked at the start (its first meta block holds its own position and the
     * database's ID) and deleted by the start's cut, as the stream after the gap holds its
     * cut, after the gap's end; every key reads as before, and the directory has no gap.
     */
    @Nano
    public static void testStartDeletesTheDatabasesFileBeforeAGap() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-before-gap-").toFile();
        try {
            CoreTestClock clock = new CoreTestClock();
            Map<String, byte[]> model = new TreeMap<String, byte[]>();
            byte[] first = writeUntilCut(dir, clock, model, null);
            File kept = new File(dir, "00000000000000.bergdb");
            Assert.assertFalse(kept.exists());
            Files.write(kept.toPath(), first);
            
            clock.setTime(clock.getTime() + SEC);
            FileStream again = new FileStream(dir);
            Assert.assertEquals(1, again.getLeftoverCount());
            Db db = start(again, clock);
            try {
                for (Map.Entry<String, byte[]> e : model.entrySet()) {
                    Assert.assertTrue(e.getKey(), Arrays.equals(e.getValue(),
                            DbUtil.get(db, Long.MAX_VALUE, e.getKey())));
                }
                Assert.assertEquals(0, again.getLeftoverCount());
            } finally { db.close(); }
            Assert.assertFalse("the file before the gap stayed", kept.exists());
            Assert.assertFalse(hasGap(dir));
        } finally { remove(dir); }
    }
    
    /**
     * bergdb 028-66, the rule of the files before a gap (Frans, 2026-11-27): a file before a
     * gap whose first meta block is not the database's is refused at the start, with a
     * StreamIoException whose cause is a BadDirStateException that names the file, what is
     * wrong and the way out, and the start deletes and writes nothing (the files compared
     * byte for byte): another database's first file; the database's own first file with its
     * first block of version 155, the meta version of release 2026.6 and of main before
     * 028-67; with that block's last byte damaged, or its position; a file of zeros; a file
     * of 100,000 bytes at 100,000, which holds no meta block. Until 2026-11-27 such a file
     * of zeros was deleted by the start (testStartDeletesAFileBeforeAGap), and before
     * 028-66 the open refused every gap. Then, with the file moved out, as the message says,
     * the database starts and reads as before.
     */
    @Nano
    public static void testStartRefusesAFileBeforeAGapThatIsNotTheDatabases() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-not-ours-").toFile();
        File other = Files.createTempDirectory("bergdb-power-other-").toFile();
        try {
            CoreTestClock clock = new CoreTestClock();
            Map<String, byte[]> model = new TreeMap<String, byte[]>();
            byte[] first = writeUntilCut(dir, clock, model, null);
            byte[] id = new byte[16];
            Arrays.fill(id, (byte) 67);
            byte[] another = writeUntilCut(other, new CoreTestClock(),
                    new TreeMap<String, byte[]>(), DatabaseId.createFromBytes(id));
            Assert.assertEquals(200000, first.length);
            Assert.assertEquals(200000, another.length);
            
            byte[] older = first.clone();
            Bytes.intToBytesLE(155, older, 4);
            byte[] lastByte = first.clone();
            lastByte[127] = 0;
            byte[] position = first.clone();
            position[46] ^= 1;
            
            String name = "00000000000000.bergdb";
            refusedBeforeGap(dir, clock, name, another, "holds the database ID 4343");
            refusedBeforeGap(dir, clock, name, older, "of version 155");
            refusedBeforeGap(dir, clock, name, lastByte, "its last byte 0");
            refusedBeforeGap(dir, clock, name, position, "holds the position 1, not its own");
            refusedBeforeGap(dir, clock, name, new byte[200000], "does not begin as a meta block");
            refusedBeforeGap(dir, clock, "00000000000001.bergdb", first.clone(), // no block
                    "holds no meta block");
            
            clock.setTime(clock.getTime() + SEC);
            Db db = start(new FileStream(dir), clock);
            try {
                for (Map.Entry<String, byte[]> e : model.entrySet()) {
                    Assert.assertTrue(e.getKey(), Arrays.equals(e.getValue(),
                            DbUtil.get(db, Long.MAX_VALUE, e.getKey())));
                }
            } finally { db.close(); }
        } finally { remove(dir); remove(other); }
    }
    
    /**
     * Puts 'bytes' into 'dir' as the file 'name', before a gap, and asserts that a start on
     * 'dir' refuses it with 'what' in the message and leaves the files as they were; then
     * removes the file (bergdb 028-66).
     */
    static void refusedBeforeGap(File dir, CoreTestClock clock, String name, byte[] bytes,
            String what) throws IOException {
        File file = new File(dir, name);
        Assert.assertFalse(file.exists());
        Files.write(file.toPath(), name.equals("00000000000001.bergdb")
                ? Arrays.copyOf(bytes, 100000) : bytes);
        Map<String, byte[]> files = streamFiles(dir);
        clock.setTime(clock.getTime() + SEC);
        try {
            Db db = start(new FileStream(dir), clock);
            db.close();
            throw new AssertionError("started with a file before a gap that is not its own: "
                    + what);
        } catch (StreamIoException e) {
            Assert.assertTrue(e.getMessage(), e.getCause() instanceof BadDirStateException
                    && e.getMessage().contains(name) && e.getMessage().contains(what)
                    && e.getMessage().contains("move the files before the gap out")
                    && e.getMessage().contains("has written nothing"));
        }
        Assert.assertTrue("the start changed the files: " + what,
                sameFiles(files, streamFiles(dir)));
        Assert.assertTrue(file.delete());
    }
    
    /**
     * Writes a database in 'dir' until a cut has deleted its first three files, its stream
     * from 600,000 on, and closes it; 'model' gets each key's last value; 'id' is its
     * database ID, or null for the tests' (DbBuilder.testId()). Returns the bytes of its
     * first file, read when it was complete, before a cut deleted it (bergdb 028-66).
     */
    static byte[] writeUntilCut(File dir, CoreTestClock clock, Map<String, byte[]> model,
            DatabaseId id) throws IOException {
        clock.setTime(SEC);
        FileStream stream = new FileStream(dir);
        DbBuilder b = Db.builder().testSetup(stream).clock(clock);
        Db db = (id == null ? b : b.id(id)).start();
        db.setStartupDistance(20000);
        db.setRetainDuration(2 * SEC);
        Random random = new Random(28066);
        File firstFile = new File(dir, "00000000000000.bergdb");
        byte[] first = null;
        long time = SEC;
        try {
            for (int i = 0; i < 2000 && stream.getFirstPos() < 600000; i++) {
                time += SEC / 10; clock.setTime(time);
                byte[] value = new byte[1000 + random.nextInt(1000)]; random.nextBytes(value);
                db.execute(db.trans().put(key(i % 12), value).build());
                model.put(key(i % 12), value);
                if (first == null && stream.getLength() > 300000) {
                    db.sync(SyncLevel.ORDINARY);
                    first = Files.readAllBytes(firstFile.toPath());
                }
            }
            Assert.assertTrue("no cut: " + stream.getFirstPos(), stream.getFirstPos() >= 600000);
            db.sync(SyncLevel.ORDINARY);
        } finally { db.close(); }
        Assert.assertTrue(first != null);
        return first;
    }
    
    /**
     * A start on 'dir' must throw a StreamIoException that says the stream lacks bytes, with a
     * ReadBelowFirstPosException as the cause (bergdb 028-66).
     */
    static void refusedLacking(File dir, String also) {
        CoreTestClock clock = new CoreTestClock(); clock.setTime(100 * SEC);
        try {
            Db db = Db.builder().testSetup(new FileStream(dir)).clock(clock).start();
            db.close();
            throw new AssertionError("started on a stream that lacks bytes");
        } catch (StreamIoException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("lacks bytes")
                    && e.getMessage().contains(also)
                    && e.getCause() instanceof ReadBelowFirstPosException);
        } catch (IOException e) {
            throw new AssertionError(e);
        }
    }
    
    /** The stream files of 'dir', by name. */
    static Map<String, byte[]> streamFiles(File dir) throws IOException {
        Map<String, byte[]> result = new TreeMap<String, byte[]>();
        for (File f : dir.listFiles((d, name) -> name.endsWith(".bergdb"))) {
            result.put(f.getName(), Files.readAllBytes(f.toPath()));
        }
        return result;
    }
    
    static boolean sameFiles(Map<String, byte[]> a, Map<String, byte[]> b) {
        if (!a.keySet().equals(b.keySet())) return false;
        for (String name : a.keySet()) {
            if (!Arrays.equals(a.get(name), b.get(name))) return false;
        }
        return true;
    }
    
    /** The names of the stream files in 'dir' have a gap: a file after the end of the one before. */
    static boolean hasGap(File dir) {
        File[] files = dir.listFiles((d, name) -> name.endsWith(".bergdb"));
        Arrays.sort(files);
        for (int i = 1; i < files.length; i++) {
            long end = Long.parseLong(files[i - 1].getName().substring(0, 14)) * 100000
                    + files[i - 1].length();
            if (Long.parseLong(files[i].getName().substring(0, 14)) * 100000 > end) return true;
        }
        return false;
    }
    
    /** As hasGap(), for the files of an image. */
    static boolean hasGap(Image image) {
        long end = -1;
        for (Map.Entry<String, byte[]> e : image.files.entrySet()) {
            long start = Long.parseLong(e.getKey().substring(0, 14)) * 100000;
            if (end != -1 && start > end) return true;
            end = start + e.getValue().length;
        }
        return false;
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
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        db.setStartupDistance(20000);
        db.setRetainDuration(2 * SEC);      // Writes nothing after the first start (bergdb 015-87).
        return db;
    }

    static void verify(Image image, List<Change> changes, int keys, long lastTime, boolean exhaustive)
            throws Exception {
        if (image.files.isEmpty() && image.acknowledgedTime > 0) {
            throw new AssertionError(image.event + ": lost all backing file names after an acknowledged commit");
        }
        // No stream byte: the start makes a new database, with no history. Without per-append
        // forces, the image before the first force of a file with bytes (bergdb 005-47).
        boolean fresh = image.end() == 0;
        if (fresh && image.acknowledgedTime > 0) {
            throw new AssertionError(image.event + ": lost all stream bytes after an acknowledged commit");
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
            if (!fresh && (first > actual || first > image.logicalNow - 2 * SEC
                    || first < image.acknowledgedFrontier)) {
                throw new AssertionError(image.event + ": invalid retained frontier " + first);
            }
            TreeMap<String, TreeMap<Long, byte[]>> model = new TreeMap<String, TreeMap<Long, byte[]>>();
            List<Long> times = new ArrayList<Long>();
            for (Change change : fresh ? new ArrayList<Change>() : changes) {
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
            if (hasGap(dir)) {
                // The start's cut deletes the files before a gap (bergdb 028-66).
                throw new AssertionError(image.event + ": the start left the files before a gap");
            }
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
        return trace(seed, transactions, perEvent, true, negativeFile, negativeDirectory, null,
                exhaustive)[0];
    }
    
    /**
     * As runTrace, on a FileStream without per-append forces (2026-11-04, bergdb 005-47), with
     * hole images. 'omit', if not null, is a kind of force left out, a negative control: an
     * image without a hole that does not recover throws DetectedLoss. Returns the images
     * checked that must recover, the hole images that recovered and those that failed (bergdb
     * 014-01); the hole images are not checked with 'omit'.
     */
    public static int[] runTraceWithoutAppendForces(long seed, int transactions, int perEvent,
            FileStreamIo.Force omit, boolean exhaustive) throws Exception {
        return trace(seed, transactions, perEvent, false, false, false, omit, exhaustive);
    }
    
    static int[] trace(long seed, int transactions, int perEvent, boolean appendForces,
            boolean negativeFile, boolean negativeDirectory, FileStreamIo.Force omit, 
            boolean exhaustive) throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-trace-").toFile();
        ModelIo io = new ModelIo(dir, seed, perEvent);
        io.appendForces = appendForces;
        boolean negative = negativeFile || negativeDirectory || omit != null;
        CoreTestClock clock = new CoreTestClock(); clock.setTime(SEC);
        FileStream stream = new FileStream(dir, io, appendForces);
        Db db = start(stream, clock);
        Random random = new Random(seed);
        // The cut's thread is held, and released every BATCH_EVERY commits, so that it deletes
        // batches of several files, as for a fast writer (bergdb 028-66).
        io.hold();
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
                // Held between, it deletes in batches (bergdb 028-66).
                if (i % BATCH_EVERY == 0) {
                    io.release();
                    stream.awaitDeletes();
                    io.hold();
                }
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
                        io.omitForce = omit;
                    }
                    io.checkpoint("after_durable_publication");
                }
            }
            io.release();
            stream.awaitDeletes();
            db.sync(SyncLevel.ORDINARY);
            io.acknowledged.set(db.lookupTime(Long.MAX_VALUE));
            io.acknowledgedFrontier.set(db.getFirstAvailableLookupTime());
            io.checkpoint("final_acknowledgement");
            db.close(); db = null;
            if (io.deletes < 2) throw new AssertionError("trace did not exercise physical deletion: " + io.deletes);
            if (io.maxDeleteBatch < 2 && !negative) {
                throw new AssertionError("trace made no batch of two deletes: " + io.maxDeleteBatch);
            }
            List<Image> cases;
            if (appendForces) {
                cases = negative ? io.images.get("after_delete") : io.snapshots();
            } else {
                cases = io.snapshots();
                // close() forced the last file (bergdb 005-47): all that was acknowledged.
                cases.add(new Image("after_close", io.durableFiles(), io.acknowledged.get(),
                        io.logicalNow.get(), io.acknowledgedFrontier.get()));
                if (omit == null) checkForcesWithoutAppendForces(io);
            }
            if (cases == null || cases.isEmpty()) throw new AssertionError("no power-loss checkpoints");
            int checked = 0, gapImages = 0;
            for (Image image : cases) {
                if (hasGap(image)) gapImages++;
                try {
                    verify(image, changes, keys, time, exhaustive);
                } catch (Exception | AssertionError failure) {
                    // Without per-append forces, any failure of a negative control is a detection.
                    // A start refused for a gap (bergdb 028-66): a StreamFormatException.
                    if (omit != null || ((negativeFile || negativeDirectory) 
                            && (failure instanceof BadDirStateException || failure instanceof AssertionError
                                    || failure instanceof StreamFormatException))) {
                        throw new DetectedLoss(image.event, failure);
                    }
                    throw failure;
                }
                checked++;
            }
            int holesRecovered = 0, holesFailed = 0;
            String firstFailure = null;
            if (!appendForces && omit == null) {
                // Holes are a known limit (bergdb 005-83; open in 014-01): counted, not failed.
                for (Image image : io.holes) {
                    try {
                        verify(image, changes, keys, time, false);
                        holesRecovered++;
                    } catch (Exception | AssertionError failure) {
                        holesFailed++;
                        if (firstFailure == null) firstFailure = image.event + ": " + failure;
                    }
                }
            }
            System.out.println("POWER TRACE seed=" + seed + " checkpoints=" + checked
                    + " physical_deletes=" + io.deletes + " largest_batch=" + io.maxDeleteBatch
                    + " gap_images=" + gapImages + " stages=" + io.seen
                    + (appendForces ? "" : " append_forces=off forces=" + io.forces 
                            + " hole_images=" + io.holes.size() + " of " + io.holeCount 
                            + " recovered=" + holesRecovered + " failed=" + holesFailed
                            + (firstFailure == null ? "" : " first_failure=" + firstFailure)));
            return new int[] {checked, holesRecovered, holesFailed};
        } finally { io.release(); if (db != null) db.close(); remove(dir); }
    }
    
    /** The commits between two releases of the cut's thread in trace() (bergdb 028-66). */
    static final int BATCH_EVERY = 300;
    
    /**
     * Without per-append forces, the trace forced no append, and forced the last file before
     * a new file, before a cut's deletes and at close() (bergdb 005-47).
     */
    static void checkForcesWithoutAppendForces(ModelIo io) {
        Map<FileStreamIo.Force, Integer> f = io.forces;
        if (f.containsKey(FileStreamIo.Force.APPEND)) {
            throw new AssertionError("an append was forced: " + f);
        }
        for (FileStreamIo.Force why : new FileStreamIo.Force[] {FileStreamIo.Force.SWITCH, 
                FileStreamIo.Force.CUT, FileStreamIo.Force.CLOSE}) {
            if (!f.containsKey(why)) {
                throw new AssertionError("the trace made no " + why + " force: " + f);
            }
        }
    }

    @Nano("f")
    public static void testColdRecoveryAtPersistenceBoundaries() throws Exception {
        runTrace(17, 600, 1, false, false, true);
    }

    /**
     * Without per-append forces (bergdb 005-47), a crash of the process loses nothing that
     * was written: a synced commit is in the files, which the OS keeps, before any close. Here
     * the files are copied while the database runs, as a crash leaves them, and a new
     * database on the copy finds the commit.
     */
    @Nano
    public static void testProcessCrashKeepsWhatWasWritten() throws Exception {
        File dir = Files.createTempDirectory("bergdb-power-process-").toFile();
        File copy = Files.createTempDirectory("bergdb-power-process-copy-").toFile();
        CoreTestClock clock = new CoreTestClock(); clock.setTime(SEC);
        Db db = start(new FileStream(dir, false), clock);
        Db again = null;
        try {
            byte[] value = new byte[] {5, 0, 4, 7};
            clock.setTime(2 * SEC);
            db.execute(db.trans().put(key(1), value).build());
            db.sync(SyncLevel.ORDINARY);
            File[] files = dir.listFiles();
            if (files == null) throw new IOException("cannot list " + dir);
            for (File f : files) {
                if (f.getName().endsWith(".bergdb")) {
                    Files.copy(f.toPath(), new File(copy, f.getName()).toPath());
                }
            }
            CoreTestClock clock2 = new CoreTestClock(); clock2.setTime(3 * SEC);
            again = start(new FileStream(copy), clock2);
            Assert.assertTrue("the synced commit is in the files", 
                    Arrays.equals(value, DbUtil.get(again, Long.MAX_VALUE, key(1))));
        } finally {
            db.close();
            if (again != null) again.close();
            remove(dir);
            remove(copy);
        }
    }
    
    /**
     * Without per-append forces (bergdb 005-47): every image without a hole recovers, and
     * the hole images are counted (bergdb 014-01).
     */
    @Nano("f")
    public static void testColdRecoveryWithoutAppendForces() throws Exception {
        int[] result = runTraceWithoutAppendForces(17, 600, 1, null, true);
        Assert.assertTrue("no hole images", result[1] + result[2] > 0);
    }
    
    /**
     * Without per-append forces (bergdb 005-47), the negative controls: without the force of
     * the last file before a new file, or before a cut's deletes, an image fails recovery.
     */
    @Nano("f")
    public static void testWeakenedForcesWithoutAppendForcesAreDetected() throws Exception {
        for (FileStreamIo.Force omit : new FileStreamIo.Force[] {FileStreamIo.Force.SWITCH, 
                FileStreamIo.Force.CUT}) {
            boolean caught = false;
            try { runTraceWithoutAppendForces(19, 600, 2, omit, false); }
            catch (DetectedLoss expected) {
                caught = true;
                System.out.println("NEGATIVE CONTROL without append forces, no " + omit 
                        + " force caught: " + expected.getCause());
            }
            Assert.assertTrue("no " + omit + " force escaped recovery tests", caught);
        }
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
