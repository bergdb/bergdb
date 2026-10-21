import java.io.File;
import java.util.Arrays;
import java.util.Locale;

import bergdb.core.Db;
import bergdb.core.SyncLevel;
import bergdb.storage.StorageManager;
import bergdb.stream.FileStream;

/**
 * 005-13, follow-up: a commit and a sync after an idle second, N times; the sync latency.
 * Then close, and check that the consumer thread has ended.
 * Usage: java -cp bergdb.jar:CLASSES SporadicProbe BUFFERMS DIR N
 */
public class SporadicProbe {
    public static void main(String[] args) throws Exception {
        int bufferMs = Integer.parseInt(args[0]);
        File dir = new File(args[1]);
        int n = Integer.parseInt(args[2]);
        dir.mkdirs();
        File[] fs = dir.listFiles();
        if (fs != null) for (File f : fs) if (f.getName().endsWith(".bergdb")) f.delete();
        Db db = Db.builder().stream("main", new FileStream(dir), StorageManager.DEFAULT_BUFFER_SIZE, bufferMs).build();
        db.start();
        long[] t = new long[n];
        for (int i = 0; i < n; i++) {
            Thread.sleep(1000);
            long t0 = System.nanoTime();
            db.execute(db.trans().put("/sporadic/" + i, "value " + i));
            db.sync(SyncLevel.ORDINARY);
            t[i] = System.nanoTime() - t0;
        }
        db.close();
        Thread.sleep(200);
        int alive = 0;
        for (Thread th : Thread.getAllStackTraces().keySet()) {
            if (th.getName().startsWith("BufferedStream-consumer")) alive++;
        }
        long[] s = t.clone();
        Arrays.sort(s);
        System.out.printf(Locale.ROOT, "bufferMs %d: commit+sync after 1 s idle, %d times: min %.1f ms, p50 %.1f ms, max %.1f ms; consumer threads alive after close: %d%n",
                bufferMs, n, s[0] / 1e6, s[n / 2] / 1e6, s[n - 1] / 1e6, alive);
    }
}
