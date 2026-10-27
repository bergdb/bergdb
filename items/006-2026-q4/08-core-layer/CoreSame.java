import java.io.File;
import java.security.MessageDigest;
import java.util.Random;

import bergdb.core.DatabaseId;
import bergdb.core.Db;
import bergdb.core.DbBuilder;
import bergdb.core.SyncLevel;
import bergdb.core.TestClock;
import bergdb.core.Trans;
import bergdb.dag.GetMany;
import bergdb.dag.Keys;
import bergdb.dag.Kvt;
import bergdb.stream.FileStream;

/**
 * A fixed workload on Db, for comparing two builds of the Core (bergdb 006-08): the
 * Core Layer as it is and the Core without its test code. By P2 (bergdb 010-01) the
 * stream is a function of the transactions, so the two must write the same bytes.
 *
 * In a directory: 6,000 transactions of puts and deletes on 3,000 keys, from a seeded
 * Random and a test clock (10 ms a transaction), with a small startup distance (index
 * nodes written), a small cache (eviction), a retain duration (reclaim cuts the front
 * of the stream) and a restart every 1,000 transactions. Prints the stream's first
 * position, its length and the SHA-256 of its bytes, and the same for the latest
 * state, read with getMany.
 *
 * Usage: java -ea -cp JAR:. CoreSame DIR  (DIR new or empty)
 */
public class CoreSame {
    static final long STEP = 100 * 1000;            // 10 ms in clock units (100 ns)

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        TestClock clock = new TestClock();
        Random random = new Random(17);
        long time = 0;
        Db db = start(dir, clock);
        for (int i = 1; i <= 6000; i++) {
            time += STEP;
            clock.setTime(time);
            Trans.Builder b = db.trans();
            int n = 1 + random.nextInt(4);
            for (int j = 0; j < n; j++) {
                String key = "/k/" + random.nextInt(3000);
                if (random.nextInt(10) == 0) {
                    b.delete(key);
                } else {
                    b.put(key, "v" + i + "-" + j + "-" + "x".repeat(random.nextInt(40)));
                }
            }
            db.execute(b.build());
            if (i % 1000 == 0) {
                db.sync(SyncLevel.ORDINARY);
                db.close();
                db = start(dir, clock);
            }
        }
        MessageDigest state = MessageDigest.getInstance("SHA-256");
        GetMany g = db.newGetMany();
        g.lookupTime = Long.MAX_VALUE;
        db.getMany(g);
        for (Kvt kvt : g.result) {
            state.update((Keys.toString(kvt.key) + "=").getBytes("UTF-8"));
            state.update(kvt.value);
        }
        long kvs = g.result.size();
        db.close();

        FileStream s = new FileStream(dir);
        long first = s.getFirstPos();
        long length = s.getLength();
        MessageDigest stream = MessageDigest.getInstance("SHA-256");
        byte[] buffer = new byte[64 * 1024];
        for (long pos = first; pos < length; pos += buffer.length) {
            int len = (int) Math.min(buffer.length, length - pos);
            s.read(pos, buffer, 0, len);
            stream.update(buffer, 0, len);
        }
        s.close();
        System.out.println("stream from " + first + " to " + length + ", sha-256 " + hex(stream.digest()));
        System.out.println("latest state, " + kvs + " keys, sha-256 " + hex(state.digest()));
    }

    static Db start(File dir, TestClock clock) throws Exception {
        DbBuilder b = Db.builder().mainStream(new FileStream(dir)).clock(clock)
                .id(DatabaseId.TEST_ID).startupDistance(20 * 1000).cacheSizeIndicator(64 * 1000)
                .retainDuration(5 * 10 * 1000 * 1000L);
        return b.start();
    }

    static String hex(byte[] bytes) {
        StringBuilder b = new StringBuilder();
        for (byte x : bytes) {
            b.append(String.format("%02x", x));
        }
        return b.toString();
    }
}
