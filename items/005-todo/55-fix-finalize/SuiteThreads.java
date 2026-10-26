import java.util.Map;
import java.util.TreeMap;

/**
 * Probe for bergdb 005-55: runs a test suite (bergdb.dev.Unit or bergdb.dev.F), then
 * collects garbage and counts the BergDB threads still alive: one BufferedStream consumer
 * per stream of a database that was not stopped and not finalized, and an eviction thread
 * per such database whose eviction thread had started.
 *
 * Usage: java -ea -cp build/bergdb.jar:. SuiteThreads bergdb.dev.Unit
 * Run it once with finalization on (the default) and once with --finalization=disabled.
 */
public class SuiteThreads {
    public static void main(String[] args) throws Exception {
        long t0 = System.nanoTime();
        Class.forName(args[0]).getMethod("main", String[].class).invoke(null,
                (Object) new String[0]);
        System.out.format("suite %s done in %.0f s%n", args[0], (System.nanoTime() - t0) * 1e-9);
        report("at the end");
        for (int i = 0; i < 20; i++) {
            System.gc();
            Thread.sleep(100);
        }
        report("after 20 collections");
        System.exit(0);
    }

    private static void report(String when) {
        Map<String, Integer> counts = new TreeMap<String, Integer>();
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            String name = t.getName().replaceAll("[-0-9]+$", "");
            counts.merge(name, 1, Integer::sum);
        }
        Runtime r = Runtime.getRuntime();
        System.out.format("  %s: heap used %d MB, threads %s%n", when,
                (r.totalMemory() - r.freeMemory()) >> 20, counts);
    }
}
