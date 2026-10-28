import java.io.File;
import java.nio.file.Files;

import bergdb.common.NullProgressListener;
import bergdb.storage.StorageManager;
import bergdb.stream.FileStream;
import bergdb.stream.MemoryStream;

/**
 * bergdb 005-67, found on the way (for 005-11): StorageManager.close() while a replica is
 * being added. addReplica() leaves the replica's place in the list of streams null until
 * the replica is active, so close() does not close the replica's BufferedStream. Run with the
 * instrumented copy (forced.py) and -Dr67.syncPause=200, so that the sync is under way when
 * close() comes. Prints whether the buffer's thread is alive after close() and whether the
 * replica's directory is still held (since 005-63 a FileStream holds bergdb.lock).
 *
 * java -ea -Dr67.syncPause=200 -cp cls:forced-before.jar CloseDuringSync67
 */
public class CloseDuringSync67 {
    public static void main(String[] args) throws Exception {
        File dir = Files.createTempDirectory("r67-replica").toFile();
        MemoryStream m1 = new MemoryStream();
        m1.append(new byte[1000], 0, 700);
        Object writeLock = new Object();
        StorageManager manager = new StorageManager.Builder(writeLock).stream("main", m1).build();
        manager.syncStreams(new NullProgressListener());
        java.util.Set<Thread> mainThreads = consumers();
        FileStream replica = new FileStream(dir);
        StorageManager.SynchingStorage ss = manager.addReplica("r", replica, 1000, 10);
        java.util.Set<Thread> replicaThreads = consumers();
        replicaThreads.removeAll(mainThreads);
        Thread sync = new Thread(() -> manager.syncReplica(ss, new NullProgressListener()));
        sync.start();
        Thread.sleep(50);                // the sync pauses with the write lock (r67.syncPause)
        manager.close();
        sync.join();
        Thread.sleep(500);
        java.util.Set<Thread> alive = consumers();
        System.out.println("after close(): the main's BufferedStream thread alive: "
                + alive.containsAll(mainThreads) + "; the replica's alive: "
                + alive.containsAll(replicaThreads) + " (" + replicaThreads.size() + " thread)");
        try {
            new FileStream(dir).close();
            System.out.println("the replica's directory is free after close()");
        } catch (Exception e) {
            System.out.println("the replica's directory is still held after close(): " + e);
        }
        for (File f : dir.listFiles()) {
            f.delete();
        }
        dir.delete();
        System.exit(0);
    }

    static java.util.Set<Thread> consumers() {
        java.util.Set<Thread> set = new java.util.HashSet<>();
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            if (t.getName().startsWith("BufferedStream-consumer-") && t.isAlive()) {
                set.add(t);
            }
        }
        return set;
    }
}
