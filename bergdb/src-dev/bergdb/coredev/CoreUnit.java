package bergdb.coredev;

import java.util.Date;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import bergdb.common.IPack;
import bergdb.common.Util;
import bergdb.nanotest.ClassFilter;
import bergdb.nanotest.MethodFilter;
import bergdb.nanotest.TestRunner;

/**
 * This class has a main method used to run the unit tests for the BergDB classes.
 * Run this class before every commit. All tests should run within 30 s.
 * 
 * @author Frans Lundberg
 */
public class CoreUnit {
    
    private static IPack[] ipacks = new IPack[]{
        new bergdb.common.Pack(),
        new bergdb.core.Pack(),
        new bergdb.stream.Pack()
    };
    
    public IPack[] getIPacks() {
        return ipacks;
    }

    private String getHeader() {
        StringBuilder b = new StringBuilder();
        b.append("\n======== " + this.getClass().getName() + " ========\n");
        String computer = Util.getComputerName();
        b.append("'unit' tests on " + computer + ", " + new Date() + ".\n");
        return b.toString();
    }
    
    private String getHelp() {
        StringBuilder b = new StringBuilder();
        b.append("---- help ----\n");
        b.append("Use args: [<classPattern> [<methodPattern>]]\n");
        b.append("  <classPattern> is a regexp for the name of the classes to include.\n");
        b.append("  <methodPattern> is a regexp for the method names to include.\n");
        b.append("\n");
        b.append("If methodPattern is missing, all test methods of the selected classes will run.\n");
        b.append("If classPattern is missing, all classes will be tested.\n");
        return b.toString();
    }
    
    /**
     * Called from main().
     */
    public void go(String[] args) {
        BergDBTestRunConsumer c = new BergDBTestRunConsumer();
        
        System.out.println(getHeader());
        
        if (args.length >= 1 && args[0].equals("help")) {
            System.out.println(getHelp());
            return;
        }
        
        String classPatternString = ".*";
        if (args.length >= 1) {
            classPatternString = args[0];
        }
        
        String methodPatternString = ".*";
        if (args.length >= 2) {
            methodPatternString = args[1];
        }
        
        go(c, classPatternString, methodPatternString);
    }
    
    /**
     * Runs unit tests (bergdb.nanotest, group "unit") on all method specified with the
     * given class and method patterns (regex).
     * This method is for general use - used by both main method and other callers.
     * 
     * @param consumer The test result consumer.
     * @param classPatternString Regex for classname.
     * @param methodPatternString Regex for method name.
     */
    public void go(BergDBTestRunConsumer consumer, 
            String classPatternString, 
            String methodPatternString) {
        Set<Class<?>> classes = new ClassFilter(classPatternString).filter(getClasses());
        
        consumer.setClassCount(classes.size());
        MethodFilter methodFilter = new MethodFilter(methodPatternString, getGroups());
        
        TestRunner testRunner = new TestRunner(consumer, classes, methodFilter);
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
    
    private Set<Class<?>> getClasses() {
        Set<Class<?>> classes = new HashSet<Class<?>>();
        IPack[] ipacks = getIPacks();
        for (IPack p : ipacks) {
            for (Class<?> c : p.getClasses()) {
                classes.add(c);
            }
        }
        return classes;
    }
    
    /**
     * A special hack to print stack traces of all threads.
     */
    @SuppressWarnings("unused")
    private void printStacks() {
        Map<Thread, StackTraceElement[]> map = Thread.getAllStackTraces();
        System.out.println("JVM thread count: " + map.size());
        
        for (Map.Entry<Thread, StackTraceElement[]> element : map.entrySet()) {
            System.out.println("---- " + element.getKey().getName() + "----");
            StackTraceElement[] trace = element.getValue();
            for (StackTraceElement traceElement : trace) {
                System.out.println("    " + traceElement);
            }
        }
    }
    
    /**
     * Very special hack, rarely used.
     */
    @SuppressWarnings("unused")
    private int bufferedStreamThreadCount() {
        if (Util.runsIkvm() || Util.runsGcj()) {
            // The getAllStackTraces() method is not available when running IKVM .NET.
            // or the GCJ VM.
            return 0;
        }
        
        Map<Thread, StackTraceElement[]> map = Thread.getAllStackTraces();
        int count = 0;
        
        for (Map.Entry<Thread, StackTraceElement[]> element : map.entrySet()) {
            String name = element.getKey().getName();
            if (name.startsWith("BufferedStream-")) {
                count++;
            }
        }
        return count;
    }
    
    /**
     * Very special hack.
     */
    @SuppressWarnings("unused")
    private void printBufferedStreamStacks() {
        Map<Thread, StackTraceElement[]> map = Thread.getAllStackTraces();
        System.out.println("JVM thread count: " + map.size());
        
        for (Map.Entry<Thread, StackTraceElement[]> element : map.entrySet()) {
            String name = element.getKey().getName();
            if (name.startsWith("BufferedStream-")) {
                System.out.println("---- " + element.getKey().getName() + "----");
                StackTraceElement[] trace = element.getValue();
                for (StackTraceElement traceElement : trace) {
                    System.out.println("    " + traceElement);
                }
            }
        }
    }
    
    /**
     * Runs the unit tests (nano tests in group "unit"). No parameters used.
     */
    public static void main(String[] args) {
        new CoreUnit().go(args);
    }
}
