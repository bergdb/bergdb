import bergdb.core.Db;
import bergdb.core.DbUtil;
import bergdb.core.SyncLevel;
import bergdb.core.Trans;
import bergdb.stream.MemoryStream;

/**
 * Probe of bergdb 005-44: does a crash right after sync() returns keep the transaction?
 * Three puts of /k (v1, v2, v3, values of the same size) on a main stream whose write
 * buffer is 2 S - 2 bytes, S the size of the third put's record, so that the buffer writes
 * S - 1 bytes of that record at once and its last byte, the commit byte, a buffer time (200
 * ms) later. After the third put, sync(lastPos) and then, at once, a crash image: a copy of
 * the stream cut at the durable length, which is what a crash keeps. A database started on
 * the image gives /k: v3 if the sync kept its promise, v2 if the transaction was lost.
 *
 * Usage: java -ea -cp DIR:bergdb.jar SyncCommitByteProbe [runs]
 */
public class SyncCommitByteProbe {
    public static void main(String[] args) throws Exception {
        int runs = args.length > 0 ? Integer.parseInt(args[0]) : 5;
        long size = recordSize();
        int lost = 0;
        for (int i = 0; i < runs; i++) {
            MemoryStream stream = new MemoryStream();
            Db db = Db.builder().stream("m", stream, (int) (2 * size - 2), 200).start();
            db.execute(db.trans().put("/k", value(1)).build());
            db.execute(db.trans().put("/k", value(2)).build());
            while (db.getDurableLength() < db.getStreamLength()) {
                Thread.sleep(5);
            }
            Trans t = db.trans().put("/k", value(3)).build();
            db.execute(t);
            db.sync(t.lastPos, SyncLevel.ORDINARY);
            long durable = db.getDurableLength();
            MemoryStream image = stream.copy();
            image.truncate(durable);
            db.close();
            
            Db after = Db.builder().mainStream(image).start();
            String v = DbUtil.getString(after, "/k");
            after.stop();
            boolean kept = v.equals(value(3));
            if (!kept) {
                lost++;
            }
            System.out.println("run " + i + ": record of " + (t.lastPos + 1 - t.tpos)
                    + " bytes, its last byte at " + t.lastPos + "; sync() returned with the "
                    + "durable length " + durable + "; after a crash then: /k = "
                    + v.substring(0, 2) + (kept ? ", kept" : ", the transaction lost"));
        }
        System.out.println("lost after its sync: " + lost + " of " + runs);
    }

    /** The size of the third put's record, in a database of its own. */
    static long recordSize() {
        Db db = Db.builder().stream("m", new MemoryStream(), 10 * 1000, 10).start();
        Trans t = null;
        for (int i = 1; i <= 3; i++) {
            t = db.trans().put("/k", value(i)).build();
            db.execute(t);
        }
        db.close();
        return t.lastPos + 1 - t.tpos;
    }

    /** "v1", "v2", ..., padded to 100 characters. */
    static String value(int i) {
        StringBuilder b = new StringBuilder("v" + i);
        while (b.length() < 100) {
            b.append('.');
        }
        return b.toString();
    }
}
