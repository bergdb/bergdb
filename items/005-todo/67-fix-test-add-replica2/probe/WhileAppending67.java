import bergdb.common.NullProgressListener;
import bergdb.pub.util.StorageInfo;
import bergdb.storage.StorageManager;
import bergdb.stream.MemoryStream;

/**
 * bergdb 005-67. StorageManagerTester.testAddReplicaWhileAppending's steps, with close()
 * where the test calls syncStrong(750), and the lengths of the two streams printed: the
 * bytes that the replica lacks. Args: N, and "lock" to have the writer append with the
 * write lock, as StorageManager.append requires (the test's writer does not).
 *
 * java -ea [-Dr67.syncPause=30] -cp cls:bergdb.jar WhileAppending67 5 [lock]
 */
public class WhileAppending67 {
    public static void main(String[] args) throws Exception {
        int n = Integer.parseInt(args[0]);
        boolean lock = args.length > 1 && args[1].equals("lock");
        for (int i = 0; i < n; i++) {
            run(lock);
        }
    }

    static void run(boolean lock) throws Exception {
        final MemoryStream m1 = new MemoryStream();
        final MemoryStream m2 = new MemoryStream();
        final byte[] bytes = new byte[1000];
        m1.append(bytes, 0, 700);
        m2.append(bytes, 0, 200);
        final Object writeLock = new Object();
        final StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", m1).build();
        manager.syncStreams(new NullProgressListener());

        Thread writer = new Thread(() -> {
            for (int i = 0; i < 5; i++) {
                try {
                    if (lock) {
                        synchronized (writeLock) {
                            manager.append(bytes, 0, 10);
                        }
                    } else {
                        manager.append(bytes, 0, 10);
                    }
                    Thread.sleep(10);
                } catch (Exception e) {
                    throw new RuntimeException(e);
                }
            }
        });
        writer.start();

        final StorageManager.SynchingStorage ss = manager.addReplica("r", m2, 1000, 10);
        Thread thread = new Thread(() -> manager.syncReplica(ss, new NullProgressListener()));
        thread.start();
        while (manager.getStorageInfo("r").getStatus() != StorageInfo.STATUS_ACTIVE) {
            Thread.sleep(10);
        }
        writer.join();
        manager.close();
        System.out.println("main " + m1.getLength() + ", replica " + m2.getLength()
                + (m1.getLength() == m2.getLength() ? "" : ", the replica lacks "
                + (m1.getLength() - m2.getLength()) + " bytes"));
    }
}
