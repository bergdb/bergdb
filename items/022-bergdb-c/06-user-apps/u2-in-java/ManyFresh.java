// bergdb 022-06 (f2): one transaction of N new keys of 16 random bytes (the first byte 0x10)
// in memory, as many_fresh.c: the execute's time. Db's bound of the index nodes before the go
// point (Dag.dirtyNodeBound) runs for it; its fresh keys are counted by a HashMap.
// Usage: java -ea -cp CLASSES:. ManyFresh N
import bergdb.core.Db;
import bergdb.core.Trans;
import bergdb.stream.MemoryStream;
import java.util.Random;

public class ManyFresh {
    public static void main(String[] args) {
        int n = Integer.parseInt(args[0]);
        Db db = Db.builder().mainStream(new MemoryStream()).start();
        Trans.Builder b = db.trans();
        Random r = new Random(5);
        for (int i = 0; i < n; i++) {
            byte[] k = new byte[16];
            r.nextBytes(k);
            k[0] = 0x10;
            b.put(k, new byte[] { 'v' });
        }
        long t0 = System.nanoTime();
        db.execute(b);
        System.out.printf("one transaction of %d new keys of 16 bytes: OK in %.3f s%n", n,
                (System.nanoTime() - t0) / 1e9);
        db.close();
    }
}
