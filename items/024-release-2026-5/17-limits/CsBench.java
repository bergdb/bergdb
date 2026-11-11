package bergdb.core;
public class CsBench {
    public static void main(String[] a) throws Exception {
        byte[] b = new byte[16777216];
        new java.util.Random(1).nextBytes(b);
        int x = 0;
        for (int r = 0; r < 8; r++) {
            long t0 = System.nanoTime();
            x += NodeChecksum.sum(b, 0, b.length);
            long t1 = System.nanoTime();
            java.util.zip.CRC32C c = new java.util.zip.CRC32C();
            c.update(b, 0, b.length);
            x += (int) c.getValue();
            long t2 = System.nanoTime();
            byte[] copy = b.clone();
            long t3 = System.nanoTime();
            x += copy[5];
            if (r >= 5) System.out.printf("16 MiB: Fletcher %.1f ms, CRC32C %.1f ms, copy %.1f ms%n",
                    (t1 - t0) / 1e6, (t2 - t1) / 1e6, (t3 - t2) / 1e6);
        }
        System.out.println(x);
    }
}
