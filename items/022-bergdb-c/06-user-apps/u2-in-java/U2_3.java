// bergdb 022-06, u2's U2-3 in Java's Core: repro_long_key.c's run. Keys of N/16, N/4 and N
// bytes that share all but their last byte, each put in its own transaction, then small
// transactions and puts of values of 1, 4 and 16 MB under a 2-byte key; in a directory
// (FileStream) with Java's default settings, which C's bergdb_options_init has. One short run:
// the seconds of each call, and the heap after a GC, to compare with C's.
// Usage: java -ea -cp CLASSES:. U2_3 N DIR [keys]   (DIR new; "keys": the three keys only)
import bergdb.core.Db;
import bergdb.stream.FileStream;
import java.io.File;
import java.util.Arrays;

public class U2_3 {
    static Db db;
    static byte[] big = new byte[64 << 20];

    static void put(byte[] key, int vlen) {
        db.execute(db.trans().put(key, Arrays.copyOf(big, vlen)));
    }

    static double now() { return System.nanoTime() / 1e9; }

    static long heap() {
        Runtime r = Runtime.getRuntime();
        for (int i = 0; i < 3; i++) System.gc();
        return r.totalMemory() - r.freeMemory();
    }

    public static void main(String[] args) throws Exception {
        int n = Integer.parseInt(args[0]);
        File dir = new File(args[1]);
        if (!dir.mkdirs()) throw new IllegalStateException("not new: " + dir);
        db = Db.builder().mainStream(new FileStream(dir)).start();
        byte[] small = { 'a', 0 };
        double a = now();
        for (int i = 0; i < 10; i++) { small[1] = (byte) i; put(small, 1); }
        System.out.printf("10 small transactions before: %.4f s%n", now() - a);
        long h0 = heap();
        System.out.printf("heap after GC: %d bytes%n", h0);
        for (int i = 0; i < 3; i++) {
            int len = i == 0 ? n / 16 : i == 1 ? n / 4 : n;
            byte[] key = new byte[len];
            Arrays.fill(key, (byte) 'K');
            key[len - 1] = (byte) i;
            a = now();
            put(key, 1);
            double t = now() - a;
            key = null;
            System.out.printf("a key of %d bytes: OK in %.3f s, heap after GC %d bytes (+%d)%n",
                    len, t, heap(), heap() - h0);
        }
        if (args.length > 2 && args[2].equals("keys")) {     // the keys only
            db.close();
            return;
        }
        a = now();
        for (int i = 0; i < 10; i++) { small[1] = (byte) (i + 10); put(small, 1); }
        System.out.printf("10 small transactions after: %.4f s%n", now() - a);
        for (int j = 0; j < 3; j++) {
            int vlen = 1 << (20 + 2 * j);
            small[1] = (byte) (100 + j);
            a = now();
            put(small, vlen);
            System.out.printf("a value of %d bytes after it: OK in %.3f s%n", vlen, now() - a);
        }
        db.close();
    }
}
