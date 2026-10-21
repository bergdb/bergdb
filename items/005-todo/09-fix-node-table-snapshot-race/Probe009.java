// 005-09: runs EvictionReaderTester.testReaderPausedInsideAFollow (the unit test: one try, 50 ms
// for the sweep) or, with F, testReaderPausedInsideAFollowF (the f-test: three tries, 500 ms; the
// unit test before 2026-10-20, 006-03) N times in one JVM and counts the failures, with their
// messages.
// Usage: java -ea -cp BERGDB_JAR:CLASSES Probe009 N [F]
public class Probe009 {
    public static void main(String[] args) throws Exception {
        int n = Integer.parseInt(args[0]);
        boolean f = args.length > 1 && args[1].equals("F");
        int failures = 0;
        long t0 = System.nanoTime();
        for (int k = 0; k < n; k++) {
            try {
                if (f) bergdb.core.EvictionReaderTester.testReaderPausedInsideAFollowF();
                else bergdb.core.EvictionReaderTester.testReaderPausedInsideAFollow();
            } catch (Throwable e) {
                failures++;
                System.out.println("FAILURE run " + k + ": " + e);
            }
        }
        long ms = (System.nanoTime() - t0) / 1000000;
        System.out.println("PROBE runs " + n + " failures " + failures + " ms " + ms);
    }
}
