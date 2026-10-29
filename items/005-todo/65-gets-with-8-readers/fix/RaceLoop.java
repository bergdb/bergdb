package bergdb.core;

/**
 * bergdb 005-65's fix: runs Eviction's race tests N times in one JVM and counts the failures:
 * testNoLostRequest (with f, testNoLostRequestF) and testInterruptWithRequestPending; for the
 * fix, and for the broken versions of mkvariant.py (run.sh). Written 2026-10-29 by Claude
 * (Opus 5.5, Claude Code).
 * Usage: java -ea -cp PROBE:CLASSES bergdb.core.RaceLoop N [f]
 */
public class RaceLoop {
    public static void main(String[] args) throws Exception {
        int n = Integer.parseInt(args[0]);
        boolean f = args.length > 1 && args[1].equals("f");
        int failRace = 0, failInt = 0;
        String first = null;
        long t0 = System.nanoTime();
        for (int i = 0; i < n; i++) {
            try {
                if (f) Eviction.testNoLostRequestF(); else Eviction.testNoLostRequest();
            } catch (Throwable x) {
                failRace++;
                if (first == null) first = x.getMessage();
            }
            try {
                Eviction.testInterruptWithRequestPending();
            } catch (Throwable x) {
                failInt++;
                if (first == null) first = x.getMessage();
            }
        }
        System.out.printf("RACELOOP %s: %d runs, race test failed %d, interrupt test failed %d, %.1f s; first failure: %s%n",
                f ? "f" : "unit", n, failRace, failInt, (System.nanoTime() - t0) / 1e9, first);
        System.exit(0);
    }
}
