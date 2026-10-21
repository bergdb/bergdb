import java.io.File;

import bergdb.core.Db;
import bergdb.core.SyncLevel;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.storage.StorageManager;
import bergdb.stream.FileStream;

/**
 * 005-14: what a restart does with the bytes that a flush of 0 bytes appends at close:
 * the ring buffer from the consumer's position to its end (zeros, here) and then from its
 * start (a copy of the stream's first bytes). Writes N transactions, closes, appends those
 * bytes to the files as the faulty flush would, and opens the database again.
 * Usage: java -cp bergdb.jar:. GarbageTail DIR N
 */
public class GarbageTail {
    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        int n = Integer.parseInt(args[1]);
        dir.mkdirs();
        for (File f : dir.listFiles()) if (f.getName().endsWith(".bergdb")) f.delete();
        int cap = StorageManager.DEFAULT_BUFFER_SIZE;

        Db db = Db.builder().stream("main", new FileStream(dir)).build();
        db.start();
        for (int i = 0; i < n; i++) db.execute(db.trans().put("/k/" + i, "value " + i));
        db.sync(SyncLevel.ORDINARY);
        db.close();

        FileStream fs = new FileStream(dir);
        long len = fs.getLength();
        if (len > cap) throw new IllegalStateException("stream longer than the buffer: " + len);
        byte[] head = new byte[(int) len];
        fs.read(0, head, 0, head.length);
        int k = (int) (len % cap);
        fs.append(new byte[cap - k], 0, cap - k);   // buffer[k, cap): never written, zeros
        fs.append(head, 0, k);                      // buffer[0, k): the stream's bytes again
        System.out.println("stream " + len + " bytes; appended " + cap + " bytes as the faulty flush would; now " + fs.getLength());
        fs.close();

        Db db2 = Db.builder().stream("main", new FileStream(dir)).build();
        try {
            db2.start();
            System.out.println("restart OK: stream length " + db2.getStreamLength());
            int wrong = 0;
            GetData gd = db2.newGetData();
            for (int i = 0; i < n; i++) {
                byte[] v = db2.getOne(Long.MAX_VALUE, Keys.toSegments(Keys.toBytes("/k/" + i)), gd);
                if (v == null || !new String(v, "UTF-8").equals("value " + i)) wrong++;
            }
            System.out.println("keys checked: " + n + ", wrong or missing: " + wrong);
            db2.execute(db2.trans().put("/after", "x"));
            db2.sync(SyncLevel.ORDINARY);
            db2.close();
            Db db3 = Db.builder().stream("main", new FileStream(dir)).build();
            db3.start();
            byte[] v = db3.getOne(Long.MAX_VALUE, Keys.toSegments(Keys.toBytes("/after")), db3.newGetData());
            System.out.println("second restart OK; /after = " + (v == null ? null : new String(v, "UTF-8")));
            db3.close();
        } catch (Throwable t) {
            System.out.println("restart FAILED: " + t);
            t.printStackTrace(System.out);
        }
    }
}
