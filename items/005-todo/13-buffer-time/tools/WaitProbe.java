public class WaitProbe {
    public static void main(String[] a) throws Exception {
        final Object o = new Object();
        for (int ms : new int[] {2, 5, 6, 12, 25, 50}) {
            long[] t = new long[100];
            for (int i = 0; i < t.length; i++) {
                long t0 = System.nanoTime();
                synchronized (o) { o.wait(ms); }
                t[i] = System.nanoTime() - t0;
            }
            java.util.Arrays.sort(t);
            System.out.printf("wait(%d): p50 %.2f ms, p90 %.2f ms%n", ms, t[50] / 1e6, t[90] / 1e6);
        }
    }
}
