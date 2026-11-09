// bergdb 022-06, u1's U1-1 in Java's Core: long_key_time.c and long_key_4mib.c. Keys of random
// bytes (java.util.Random, not C's rand(); the first byte 0x10) of 256 KiB to 2 MiB, each
// sharing the one before as its prefix; the 1 MiB key + 1 byte; a 1 MiB key of zeros and it
// + 1 byte. "4mib": a random key of 2 MiB, then one of 4 MiB that shares it. In memory
// (a MemoryStream), the builder's defaults; each put a transaction with the value "v".
// Usage: java -ea -cp CLASSES:. U1_1 [4mib]
import bergdb.core.Db;
import bergdb.stream.MemoryStream;
import java.util.Arrays;
import java.util.Random;

public class U1_1 {
    static Db db;

    static void put(byte[] k, int n, String what) {
        long t0 = System.nanoTime();
        db.execute(db.trans().put(Arrays.copyOf(k, n), new byte[] { 'v' }));
        System.out.printf("key of %8d bytes (%s): execute OK in %.3f s%n", n, what,
                (System.nanoTime() - t0) / 1e9);
    }

    public static void main(String[] args) {
        db = Db.builder().mainStream(new MemoryStream()).start();
        if (args.length > 0 && args[0].equals("4mib")) {
            byte[] k = new byte[4 << 20];
            new Random(2).nextBytes(k);
            k[0] = 0x10;
            put(k, 2 << 20, "random");
            put(k, 4 << 20, "random, sharing the 2 MiB key");
        } else {
            int max = 2 << 20;
            byte[] k = new byte[max + 1];
            new Random(1).nextBytes(k);
            k[0] = 0x10;
            for (int n = 256 << 10; n <= max; n *= 2) put(k, n, "random");
            put(k, (1 << 20) + 1, "random, the 1 MiB key + 1 byte");
            Arrays.fill(k, (byte) 0);
            put(k, 1 << 20, "zeros");
            put(k, (1 << 20) + 1, "zeros + 1 byte");
        }
        db.close();
    }
}
