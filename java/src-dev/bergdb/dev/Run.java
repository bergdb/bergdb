package bergdb.dev;

import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Main entry point to run other executable classes. Useful when it is not possible to run 
 * specified classes directly, for example when BergDB is compiled to a native executable.
 * 
 * @author Frans Lundberg
 */
public class Run {
    private String[] args;
    
    private void go(String[] args) throws Exception {
        this.args = args;
        
        if (args.length == 0 || args.length >= 1 && args[0].equals("help")) {
            printHelp();
            return;
        }
        
        runClass();
    }

    private void printHelp() {
        PrintStream out = System.out;
        out.println("======== " + Run.class.getName() + " ========");
        out.println("This executable class can be used to start another executable class.");
        out.println("Useful when the application is compiled with a single entry point");
        out.println("(the main method of this class).");
        out.println();
        out.println("Some available executable classes:");
        out.println("  " + bergdb.dev.Unit.class.getName() + " - Runs 'unit' tests.");
        out.println("  " + bergdb.dev.F.class.getName() + " - Runs 'f' tests.");
        out.println("  " + bergdb.dev.Night.class.getName() + " - Runs 'night' tests.");
        out.println("  " + bergdb.dev.Perf.class.getName() + " - Runs 'perf' tests.");
        out.println("  " + bergdb.dev.props.Props.class.getName() + " - Computes project properties (performance, etc).");
        out.println("  " + bergdb.dev.props.Core.class.getName() + " - Standard performance test for Core.");
        out.println("  " + bergdb.dev.Info.class.getName() + " - Prints info about the system.");
        out.println("  " + bergdb.dev.Swing.class.getName() + " - Test the graphics environment by displaying a Swing window.");
        out.println();
        out.println("Use args: '<nameOfClass> <argsForClass>' to run an executable class.");
        out.println("Many executable classes print help text, if executed with the single argument 'help'.");
        out.println();
    }
    
    private void runClass() throws ClassNotFoundException, NoSuchMethodException, 
            SecurityException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
        String className = args[0];
        String[] methodArgs = new String[args.length - 1];
        System.arraycopy(args, 1, methodArgs, 0, methodArgs.length);
        
        Class<?> c = Class.forName(className);
        Method main = c.getMethod("main", String[].class);
        // The class may not be public, as most of pubimp's since 2026-11-09 (bergdb 020-10,
        // B2): the method is, but getMethod() gives it with its class's access. A tool of
        // src-dev only; the release jar has no Main-Class.
        main.setAccessible(true);
        main.invoke(null, new Object[]{methodArgs});
    }
    
    public static void main(String[] args) throws Exception {
        new Run().go(args);
    }
    
    // ======== Tests ========
    
    /** What main() of 'args' prints, run through Run. */
    private static String printed(String... args) throws Exception {
        PrintStream saved = System.out;
        java.io.ByteArrayOutputStream bytes = new java.io.ByteArrayOutputStream();
        System.setOut(new PrintStream(bytes, true, "UTF-8"));
        try {
            main(args);
        } finally {
            System.setOut(saved);
        }
        return bytes.toString("UTF-8");
    }
    
    /**
     * Run starts main() of a class that is not public (2026-11-09: getMethod().invoke() threw
     * IllegalAccessException for each since 2917cdb narrowed pubimp, bergdb 020-10, B2):
     * RwEnvironmentImp, IndexHarness (a short run) and src-dev's Demo.
     */
    @Nano
    private static void testRunsMainOfAClassThatIsNotPublic() throws Exception {
        String out = printed("bergdb.pubimp.RwEnvironmentImp");
        Assert.assertTrue(out, out.contains("000000111222333444"));
        out = printed("bergdb.pubimp.IndexHarness", "1", "40");
        Assert.assertTrue(out, out.contains("IndexHarness OK"));
        out = printed("bergdb.demo.Demo");
        Assert.assertTrue(out, out.contains("Use one of: put, get, delete."));
    }
}
