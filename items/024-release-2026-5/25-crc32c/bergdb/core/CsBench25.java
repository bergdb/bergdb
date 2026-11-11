package bergdb.core;

/**
 * bergdb 024-25: NodeChecksum.sum's time over 16 MiB and over a key node of 544 bytes, on
 * the build it runs against (Fletcher-16 before 024-25, CRC32C after). Not product code.
 * Usage: java -cp probe:build/bergdb.jar bergdb.core.CsBench25
 */
public class CsBench25 {
    public static void main(String[] a) {
        byte[] b = new byte[16777216];
        new java.util.Random(1).nextBytes(b);
        int x = 0;
        for (int r = 0; r < 10; r++) {
            long t0 = System.nanoTime();
            x += NodeChecksum.sum(b, 0, b.length);
            long t1 = System.nanoTime();
            for (int i = 0; i < 30000; i++) {
                x += NodeChecksum.sum(b, (i * 544) % 1000000, 544);
            }
            long t2 = System.nanoTime();
            if (r >= 5) {
                System.out.printf("16 MiB: %.2f ms (%.3f ms a MB); a 544-byte node: %.3f us%n",
                        (t1 - t0) / 1e6, (t1 - t0) / 1e6 / 16.777216, (t2 - t1) / 1e3 / 30000);
            }
        }
        System.out.println(x);
    }
}
