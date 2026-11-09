// bergdb 022-06, u2's U2-6 in Java's Core: repro_deleted_file.c. The only stream file deleted
// while the database is open (after a put of 100 kB and a sync), then three more puts of
// 100 kB, a sync and a close; then a new start.
// Usage: java -ea -cp CLASSES:. U2_6 DIR   (DIR new)
import bergdb.core.Db;
import bergdb.pub.util.SyncLevel;
import bergdb.stream.FileStream;
import java.io.File;

public class U2_6 {
    static String cut(Throwable e) {
        String m = String.valueOf(e);
        return m.length() > 240 ? m.substring(0, 240) + "..." : m;
    }

    static String put(Db db, int k) {
        try {
            db.execute(db.trans().put(new byte[] { (byte) k }, new byte[100000]));
            return "OK";
        } catch (Throwable e) {
            return cut(e);
        }
    }

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        if (!dir.mkdirs()) throw new IllegalStateException("not new: " + dir);
        Db db = Db.builder().mainStream(new FileStream(dir)).start();
        System.out.println("put 0: " + put(db, 0));
        db.sync(SyncLevel.ORDINARY);
        File f = new File(dir, "00000000000000.bergdb");
        System.out.println("delete " + f.getName() + ": " + f.delete());    // the only stream file
        for (int k = 1; k < 4; k++) System.out.println("put " + k + ": " + put(db, k));
        try {
            db.sync(SyncLevel.ORDINARY);
            System.out.println("sync: OK");
        } catch (Throwable e) {
            System.out.println("sync: " + cut(e));
        }
        try {
            db.close();
            System.out.println("close: OK");
        } catch (Throwable e) {
            System.out.println("close: " + cut(e));
        }
        String[] names = dir.list();
        java.util.Arrays.sort(names);
        System.out.println("files: " + String.join(" ", names));
        try {
            Db db2 = Db.builder().mainStream(new FileStream(dir)).start();
            System.out.println("start: OK");
            db2.close();
        } catch (Throwable e) {
            System.out.println("start: " + cut(e));
        }
    }
}
