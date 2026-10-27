package bergdb.dev;

import java.util.HashSet;
import java.util.Set;

import bergdb.common.Create;
import bergdb.nanotest.ClassFilter;
import bergdb.nanotest.ConsoleUI;
import bergdb.nanotest.IPack;
import bergdb.nanotest.MethodFilter;
import bergdb.nanotest.TestRunner;

/**
 * Probe for bergdb 005-55: runs a Nano test group of BergDB (unit, f or night) and prints,
 * after each test, the storage threads (BufferedStream-consumer-N) and eviction threads
 * (bergdb-evictor) that the test left alive, once the Db-close threads that stop() started
 * have ended (and the eviction threads have had 1.5 s to see the stop): each line is a
 * database that the test did not stop. Run it with --finalization=disabled, so that the
 * collector stops nothing on the way (before 005-55, Db.finalize() did).
 *
 * Usage, from java/ after build.sh, the probe's classes first on the class path (they are in
 * package bergdb.dev, as the jar's):
 *   java -ea --finalization=disabled -cp CLASSES:build/bergdb.jar bergdb.dev.LeakFinder GROUP [classRegex]
 * leaks.sh runs it on the unit and f groups.
 */
public class LeakFinder {
    static Set<Thread> before;
    static String current;
    static int totalLeaked;

    public static void main(String[] args) {
        String group = args[0];
        String classPattern = args.length > 1 ? args[1] : ".*";
        Set<Class<?>> classes = new HashSet<Class<?>>();
        for (IPack p : TestClasses.getIPacksStatic()) {
            for (Class<?> c : p.getClasses()) {
                classes.add(c);
            }
        }
        ConsoleUI ui = new ConsoleUI() {
            public void testAboutToRun(String name) {
                current = name;
                before = storageThreads();
                super.testAboutToRun(name);
            }
            public void testDone(Throwable t) {
                super.testDone(t);
                joinClosers();
                Set<Thread> after = storageThreads();
                after.removeAll(before);
                if (!after.isEmpty()) {
                    totalLeaked += after.size();
                    StringBuilder b = new StringBuilder();
                    for (Thread th : after) {
                        b.append(' ').append(th.getName().replaceAll("[-0-9]+$", ""));
                    }
                    System.out.println("\nLEAK " + after.size() + " " + current + ":" + b);
                }
            }
        };
        ui.dots();
        TestRunner r = new TestRunner(ui, new ClassFilter(classPattern).filter(classes),
                new MethodFilter(".*", Create.set(group)));
        r.run();
        System.out.println("LEAKED TOTAL " + totalLeaked);
        System.exit(0);
    }

    static Set<Thread> storageThreads() {
        Set<Thread> s = new HashSet<Thread>();
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            String n = t.getName();
            if (t.isAlive() && (n.startsWith("BufferedStream-consumer-") || n.startsWith("bergdb-evictor"))) {
                s.add(t);
            }
        }
        return s;
    }

    static void joinClosers() {
        for (Thread t : Thread.getAllStackTraces().keySet()) {
            if (t.getName().startsWith("Db-close-")) {
                try {
                    t.join(5000);
                } catch (InterruptedException e) {
                    throw new RuntimeException(e);
                }
            }
        }
        // The eviction thread checks isActive() once a second; give it time to see a stop.
        long end = System.currentTimeMillis() + 1500;
        while (System.currentTimeMillis() < end) {
            boolean any = false;
            for (Thread t : storageThreads()) {
                if (!before.contains(t) && t.getName().startsWith("bergdb-evictor")) any = true;
            }
            if (!any) break;
            try { Thread.sleep(50); } catch (InterruptedException e) { throw new RuntimeException(e); }
        }
    }
}
