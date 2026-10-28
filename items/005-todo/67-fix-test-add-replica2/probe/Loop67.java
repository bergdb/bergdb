import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Map;
import java.util.TreeMap;

/**
 * bergdb 005-67. Runs a test of StorageManagerTester N times in one JVM, each in a thread
 * of its own with a timeout, and counts the failures by message and line, and the runs that
 * did not end in time (a test that waits for ever).
 *
 * javac -cp bergdb.jar -d cls Loop67.java
 * java -ea -cp cls:bergdb.jar Loop67 testAddReplica2 1000 [TIMEOUT_MS]
 *
 * The instrumented copy (forced.diff) reads -Dr67.replicaFlushDelay, -Dr67.afterAppend and
 * -Dr67.syncPause (milliseconds).
 */
public class Loop67 {
    public static void main(String[] args) throws Exception {
        String name = args[0];
        int n = Integer.parseInt(args[1]);
        long timeoutMs = args.length > 2 ? Long.parseLong(args[2]) : 10000;
        Method m = Class.forName("bergdb.storage.StorageManagerTester").getMethod(name);
        Map<String, Integer> failures = new TreeMap<>();
        int failed = 0;
        int hung = 0;
        long t0 = System.nanoTime();
        for (int i = 0; i < n; i++) {
            Throwable[] thrown = new Throwable[1];
            Thread t = new Thread(() -> {
                try {
                    m.invoke(null);
                } catch (InvocationTargetException e) {
                    thrown[0] = e.getCause();
                } catch (Throwable e) {
                    thrown[0] = e;
                }
            });
            t.setDaemon(true);
            t.start();
            t.join(timeoutMs);
            if (t.isAlive()) {
                hung++;
                failures.merge("did not end in " + timeoutMs + " ms", 1, Integer::sum);
                continue;
            }
            Throwable e = thrown[0];
            if (e != null) {
                failed++;
                String where = "";
                for (StackTraceElement el : e.getStackTrace()) {
                    if (el.getClassName().equals("bergdb.storage.StorageManagerTester")) {
                        where = " (line " + el.getLineNumber() + ")";
                        break;
                    }
                }
                failures.merge(e.getClass().getSimpleName() + ": " + e.getMessage() + where, 1,
                        Integer::sum);
            }
        }
        long ms = (System.nanoTime() - t0) / 1000000;
        for (Map.Entry<String, Integer> f : failures.entrySet()) {
            System.out.println(f.getValue() + " x " + f.getKey());
        }
        System.out.println(name + ": runs " + n + ", failed " + failed + ", did not end " + hung
                + " (" + ms + " ms)");
        System.exit(0);
    }
}
