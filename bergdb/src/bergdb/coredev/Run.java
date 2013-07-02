package bergdb.coredev;

import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

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
        out.println("Available executable classes:");
        out.println("  " + bergdb.coredev.CoreUnit.class.getName() + " - Runs unit tests for Core Layer.");
        out.println("  " + bergdb.coredev.Info.class.getName() + " - Prints info about BergDB and the environment.");
        out.println();
        out.println("Use args: '<nameOfClass> <argsForClass>' to run an executable class.");
        out.println("Many executable classes print help text if executed with the single argument 'help'.");
        out.println();
    }
    
    private void runClass() throws ClassNotFoundException, NoSuchMethodException, 
            SecurityException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
        String className = args[0];
        String[] methodArgs = new String[args.length - 1];
        System.arraycopy(args, 1, methodArgs, 0, methodArgs.length);
        
        Class<?> c = Class.forName(className);
        Method main = c.getMethod("main", String[].class);
        main.invoke(null, new Object[]{methodArgs});
    }
    
    public static void main(String[] args) throws Exception {
        new Run().go(args);
    }
}
