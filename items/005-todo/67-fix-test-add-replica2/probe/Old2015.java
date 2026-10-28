import java.util.Map;
import java.util.TreeMap;

import bergdb.common.NullProgressListener;
import bergdb.pub.util.StorageInfo;
import bergdb.storage.StorageManager;
import bergdb.stream.MemoryStream;

/**
 * bergdb 005-67. testAddReplica2 as it was before Frans's note of 2015-07-23 (7c458d1^ of
 * the 2013 to 2017 history: no assertions between the append and close()), run N times;
 * prints how often each pair of lengths after close() came. With the BufferedStream of
 * 2015 (old2015.py) before the jar on the class path, it shows where the replica's 1200
 * bytes of the note came from.
 *
 * The BufferedStream of 2015, from the 2013 to 2017 history (F1-007's bundle, or a clone of it):
 *   git show 7c458d1:bergdb/src/bergdb/storage/BufferedStream.java > BufferedStream.java
 *   python3 -I old2015.py BufferedStream.java
 *   javac -nowarn -cp bergdb.jar -d old2015/cls BufferedStream.java
 *
 * java -ea [-Dr67.closePause=5 -Dr67.betweenAppends=20] -cp old2015/cls:cls:bergdb.jar Old2015 20
 */
public class Old2015 {
    public static void main(String[] args) throws Exception {
        int n = Integer.parseInt(args[0]);
        Map<String, Integer> outcomes = new TreeMap<>();
        for (int i = 0; i < n; i++) {
            outcomes.merge(run(), 1, Integer::sum);
        }
        for (Map.Entry<String, Integer> o : outcomes.entrySet()) {
            System.out.println(o.getValue() + " x " + o.getKey());
        }
    }

    static String run() throws Exception {
        final MemoryStream m1 = new MemoryStream();
        final MemoryStream m2 = new MemoryStream();
        final byte[] bytes = new byte[1000];
        m1.append(bytes, 0, 700);
        m2.append(bytes, 0, 200);
        Object writeLock = new Object();
        final StorageManager manager = new StorageManager.Builder(writeLock)
                .stream("main", m1).build();
        manager.syncStreams(new NullProgressListener());
        final StorageManager.SynchingStorage ss = manager.addReplica("r", m2, 1000, 10);
        Thread thread = new Thread(() -> manager.syncReplica(ss, new NullProgressListener()));
        thread.start();
        while (manager.getStorageInfo("r").getStatus() != StorageInfo.STATUS_ACTIVE) {
            Thread.sleep(10);
        }
        manager.append(bytes, 0, 100);
        manager.close();
        return "main " + m1.getLength() + ", replica " + m2.getLength()
                + (m2.getLength() == 800 ? "" : " (the test: \"Expected 800, got "
                + m2.getLength() + "\")");
    }
}
