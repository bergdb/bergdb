// bergdb 022-06, u2's U2-8 in Java's Core: a put of "garbage" (7 bytes) under reclaim's
// settings key, /#i/dreclaim/-settings.txt, as repro_reserved_key.c does through C's API.
// Usage: java -ea -cp CLASSES:. U2_8 DIR   (DIR new)
import bergdb.core.Db;
import bergdb.stream.FileStream;
import java.io.File;

public class U2_8 {
    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        if (!dir.mkdirs()) throw new IllegalStateException("not new: " + dir);
        Db db = Db.builder().mainStream(new FileStream(dir)).start();
        db.setRetainDuration(3600L * 10_000_000L);         // reclaim's settings, as the C repro
        String ik = "/#i/dreclaim/-settings.txt";
        try {
            db.execute(db.trans().put(ik, "garbage"));     // Keys.toBytes(ik): the bkey
            System.out.println("put under " + ik + ": taken");
        } catch (RuntimeException e) {
            System.out.println("put under " + ik + ": refused: " + e);
        }
        db.close();
        try {
            Db db2 = Db.builder().mainStream(new FileStream(dir)).start();
            System.out.println("start: OK");
            db2.close();
        } catch (Throwable e) {
            String m = e.toString();
            System.out.println("start: " + m);
            if (e.getCause() != null) System.out.println("  cause: " + e.getCause());
        }
    }
}
