// bergdb 022-06, u1's U1-2 in Java's Core: long_key_memory.c. The 16 keys of 1 MiB of that
// program (written by keys16.c with C's rand() and srand(3)), each put with the value
// "0123456789" in its own transaction, in a directory with a cache size indicator of 10 MB;
// the stream's length after keys 1, 8 and 16 and after a restart, and the heap after a GC.
// Usage: java -ea -cp CLASSES:. U1_2 KEYFILE DIR   (DIR new)
import bergdb.core.Db;
import bergdb.stream.FileStream;
import java.io.File;
import java.nio.file.Files;
import java.util.Arrays;

public class U1_2 {
    static long heap() {
        Runtime r = Runtime.getRuntime();
        for (int i = 0; i < 3; i++) System.gc();
        return r.totalMemory() - r.freeMemory();
    }

    static void report(Db db, String what) {
        System.out.printf("%-28s stream %d bytes, heap after GC %.1f MB%n", what,
                db.getStreamLength(), heap() / 1e6);
    }

    public static void main(String[] args) throws Exception {
        byte[] all = Files.readAllBytes(new File(args[0]).toPath());
        File dir = new File(args[1]);
        if (!dir.mkdirs()) throw new IllegalStateException("not new: " + dir);
        int n = 1 << 20;
        Db db = Db.builder().mainStream(new FileStream(dir)).cacheSizeIndicator(10000000).start();
        report(db, "a new database");
        for (int i = 0; i < 16; i++) {
            byte[] k = Arrays.copyOfRange(all, i * n, (i + 1) * n);
            db.execute(db.trans().put(k, "0123456789".getBytes("UTF-8")));
            if (i == 0 || i == 7 || i == 15) report(db, "after " + (i + 1) + " keys of 1 MiB");
        }
        db.close();
        db = Db.builder().mainStream(new FileStream(dir)).cacheSizeIndicator(10000000).start();
        report(db, "after a restart");
        db.close();
    }
}
