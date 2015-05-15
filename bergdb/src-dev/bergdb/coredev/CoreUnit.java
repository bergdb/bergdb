package bergdb.coredev;

import java.util.Date;
import java.util.HashSet;
import java.util.Set;

import bergdb.common.AssertStatus;
import bergdb.common.Create;
import bergdb.common.IPack;
import bergdb.common.Util;
import bergdb.dev.TestClasses;
import bergdb.nanotest.ClassFilter;
import bergdb.nanotest.CommandLine;
import bergdb.nanotest.ConsoleUI;
import bergdb.nanotest.MethodFilter;
import bergdb.nanotest.TestRunner;

/**
 * This class has a main method used to run the unit tests for the Core BergDB classes.
 * 
 * @author Frans Lundberg
 */
public class CoreUnit {
    
    /**
     * A subset of the classes.
     */
    private static IPack[] ipacks = new IPack[]{
        new bergdb.common.Pack(),
        new bergdb.core.Pack(),
        new bergdb.stream.Pack()
    };
    
    public IPack[] getIPacks() {
        return ipacks;
    }
    
    /**
     * Creates and returns a set of all classes in the packages
     * specified in this.ipacks.
     */
    public Set<Class<?>> getClasses() {
        Set<Class<?>> classes = new HashSet<Class<?>>();
        IPack[] ipacks = getIPacks();
        for (IPack p : ipacks) {
            for (Class<?> c : p.getClasses()) {
                classes.add(c);
            }
        }
        return classes;
    }

    private String getHeader() {
        StringBuilder b = new StringBuilder();
        b.append("\n======== " + this.getClass().getName() + " ========\n");
        String computer = Util.hostname();
        b.append("'unit' tests on " + computer + ", " + new Date() + ".\n");
        return b.toString();
    }
    
    private String getHelp() {
        StringBuilder b = new StringBuilder();
        b.append("---- help ----\n");
        b.append("Use options:\n");
        b.append("-c <classPattern> is a regexp for the name of the classes to include.\n");
        b.append("-m <methodPattern> is a regexp for the method names to include.\n");
        b.append("-d   Print dots.\n");
        b.append("-s   Be silent\n");
        b.append("-v   Be verbose\n");
        b.append("-vv  Be max verbose\n");
        b.append("\n");
        b.append("If methodPattern is missing, all test methods of the selected classes will run.\n");
        b.append("If classPattern is missing, all classes with test methods will be tested.\n");
        return b.toString();
    }
    
    /**
     * Called from main().
     */
    public void go(String[] args) {
        if (args.length > 0 && args[0].equals("help")) {
            System.out.println(getHelp());
            return;
        }
        
        CommandLine c = new CommandLine(args);        
        ConsoleUI ui = new ConsoleUI();
        ui.applyOptions(c);
        
        System.out.println(getHeader());
        
        if (!AssertStatus.enabled()) {
            System.out.println("Assertions (-ea) NOT ENABLED.");
        }
        
        String classPatternString = ".*";
        if (c.has("c")) {
            classPatternString = c.getOne("c");
        }
        
        String methodPatternString = ".*";
        if (c.has("m")) {
            methodPatternString = c.getOne("m");
        }
        
        Set<Class<?>> classes = new ClassFilter(classPatternString).filter(TestClasses.getClasses());
        MethodFilter methodFilter = new MethodFilter(methodPatternString, Create.setOfStrings("unit"));
        
        TestRunner testRunner = new TestRunner(ui, classes, methodFilter);
        testRunner.run();
    }
    
    /**
     * Override for other set of groups.
     * The implementation in this class returns a set with "unit" as the only
     * member.
     */
    protected Set<String> getGroups() {
        Set<String> groups = new HashSet<String>();
        groups.add("unit");
        return groups;
    }
    
    /**
     * Runs the unit tests (nano tests in group "unit"). No parameters used.
     */
    public static void main(String[] args) {
        new CoreUnit().go(args);
    }
}
