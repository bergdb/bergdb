import java.util.HashSet;
import java.util.Set;

import bergdb.nanotest.ClassFilter;
import bergdb.nanotest.ConsoleUI;
import bergdb.nanotest.IPack;
import bergdb.nanotest.MethodFilter;
import bergdb.nanotest.TestRunner;

/**
 * Runs the Nano tests of the given packages, with only the Core Layer on the
 * class path (bergdb 006-08). As bergdb.dev.Unit and F, which also run the
 * tests of pubimp and src-dev, and need them on the class path.
 *
 * Usage: java -ea -cp bergdb-core.jar:. CoreUnit GROUP PKG...
 *   GROUP: unit or f. PKG: core, dag and so on; a package without a Pack
 *   class has no tests.
 */
public class CoreUnit {
    public static void main(String[] args) throws Exception {
        Set<Class<?>> classes = new HashSet<Class<?>>();
        for (int i = 1; i < args.length; i++) {
            Class<?> pack;
            try {
                pack = Class.forName("bergdb." + args[i] + ".Pack");
            } catch (ClassNotFoundException e) {
                System.out.println("No tests in " + args[i] + " (no Pack class)");
                continue;
            }
            for (Class<?> c : ((IPack) pack.getDeclaredConstructor().newInstance()).getClasses()) {
                classes.add(c);
            }
        }
        Set<String> groups = new HashSet<String>();
        groups.add(args[0]);
        ConsoleUI ui = new ConsoleUI();
        new TestRunner(ui, new ClassFilter(".*").filter(classes), new MethodFilter(".*", groups)).run();
    }
}
