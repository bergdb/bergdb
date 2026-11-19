/**
 * bergdb 026-25, perf2: the set test of Props CORE (bergdb.test.Set.corePerfMethod) N times in
 * one JVM, for a profile; prints each run's time a transaction in microseconds and the median.
 * Written 2026-11-19. Compiled against a build's bergdb.jar.
 */
public class SetLoop {
    public static void main(String[] args) {
        int n = args.length > 0 ? Integer.parseInt(args[0]) : 30;
        double[] t = new double[n];
        for (int i = 0; i < n; i++) {
            t[i] = bergdb.test.Set.corePerfMethod() * 1e6;
            System.out.printf(java.util.Locale.ROOT, "set %d %.3f us%n", i, t[i]);
        }
        java.util.Arrays.sort(t);
        System.out.printf(java.util.Locale.ROOT, "SET median %.3f us, min %.3f, max %.3f (%d runs)%n",
                t[n / 2], t[0], t[n - 1], n);
    }
}
