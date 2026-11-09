// bergdb 022-06, u2's U2-2 in Java's Core: repro_full_zerofill.c. "fill": a transaction of
// 12 values of 1 MB, which fails on a nearly full disk; "open": a start and a stop. Run by
// U2_2.sh, which makes the full disk.
// "use": a start, a small transaction and a sync, and a stop.
// Usage: java -ea -cp CLASSES:. U2_2 DIR fill|open|use
import bergdb.core.Db;
import bergdb.stream.FileStream;
import java.io.File;

public class U2_2 {
    static String cut(Throwable e) {
        String m = String.valueOf(e);
        return m.length() > 200 ? m.substring(0, 200) + "..." : m;
    }

    public static void main(String[] args) throws Exception {
        File dir = new File(args[0]);
        dir.mkdirs();
        Db db;
        try {
            db = Db.builder().mainStream(new FileStream(dir)).start();
            System.out.println("open: OK");
        } catch (Throwable e) {
            System.out.println("open: " + cut(e));
            for (Throwable c = e.getCause(); c != null; c = c.getCause()) {
                System.out.println("  cause: " + cut(c));
            }
            return;
        }
        System.out.println("stream length " + db.getStreamLength());
        if (args[1].equals("use")) {
            // A small transaction and a sync after the start: the start's zero fill is
            // written by the storage's thread after the start returned.
            try {
                Thread.sleep(500);
                db.execute(db.trans().put(new byte[] { 's' }, new byte[] { 1 }));
                db.sync(bergdb.pub.util.SyncLevel.ORDINARY);
                System.out.println("a small transaction and a sync: OK");
            } catch (Throwable e) {
                System.out.println("a small transaction and a sync: " + cut(e));
            }
        }
        if (args[1].equals("fill")) {
            byte[] big = new byte[1 << 20];
            bergdb.core.Trans.Builder b = db.trans();
            for (int i = 0; i < 12; i++) b.put(new byte[] { 'k', (byte) i }, big);
            try {
                db.execute(b);
                db.sync(bergdb.pub.util.SyncLevel.ORDINARY);
                System.out.println("a 12 MB transaction and a sync: OK");
            } catch (Throwable e) {
                System.out.println("a 12 MB transaction: " + cut(e));
            }
        }
        try {
            db.close();
            System.out.println("close: OK");
        } catch (Throwable e) {
            System.out.println("close: " + cut(e));
        }
    }
}
