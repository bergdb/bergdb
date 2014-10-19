package bergdb.coredev;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Date;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import bergdb.common.IPack;
import bergdb.common.Util;
import bergdb.nanotest.TestRunner;

/**
 * This class has a main method used to run the unit tests for the BergDB classes.
 * Run this class before every commit. All tests should run within 30 s.
 * 
 * @author Frans Lundberg
 */
public class CoreUnit {
    // 130221 Frans: making Unit runs more flexible, configurable.
    
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
        BergDBTestCollector c = new BergDBTestCollector();
        c.setPrintProps(false);
        c.setPrintMethods(true);
        
        System.out.println(getHeader());
        
        if (args.length >= 1 && args[0].equals("help")) {
            System.out.println(getHelp());
            return;
        }
        
        String classPatternString = null;
        if (args.length >= 1) {
            classPatternString = args[0];
        }
        
        String methodPatternString = null;
        if (args.length >= 2) {
            methodPatternString = args[1];
        }
        
        go(c, classPatternString, methodPatternString);
        
        System.out.println(c.getReport());
    }
    
    /**
     * Runs unit tests (bergdb.nanotest, group "unit") on all method specified with the
     * given class and method patterns (regex).
     * This method is for general use - used by both main method and other callers.
     * 
     * @param collector The test result collector.
     * @param classPatternString Regex for classname or null for all classes.
     * @param methodPatternString Regex for method name or null for all nano unit test methods.
     */
    public void go(BergDBTestCollector collector, String classPatternString, 
            String methodPatternString) {
        List<Class<?>> classes = new ArrayList<Class<?>>();
        IPack[] ipacks = getIPacks();
        Pattern classPattern = null;
        Pattern methodPattern = null;
        
        if (classPatternString != null) {
            classPattern = Pattern.compile(classPatternString);
        }
        
        if (methodPatternString != null) {
            methodPattern = Pattern.compile(methodPatternString);
        }
        
        for (IPack p : ipacks) {
            for (Class<?> c : p.getClasses()) {
                if (mathes(classPattern, c)) {
                    classes.add(c);
                }
            }
        }
        
        Class<?>[] classesArray = classes.toArray(new Class<?>[0]);
        Arrays.sort(classesArray, new Comparator<Class<?>>() {
            public int compare(Class<?> c0, Class<?> c1) {
                return c0.getName().toLowerCase(Locale.US)
                        .compareTo(c1.getName().toLowerCase(Locale.US));
            }
        });
        
        collector.setClassCount(classes.size());
        String[] groups = new String[]{"unit"};
        
        for (Class<?> c : classesArray) {
            TestRunner.run(groups, c, methodPattern, collector);
        }
    }

    private boolean mathes(Pattern classPattern, Class<?> c) {
        boolean result;
        if (classPattern == null) {
            result = true;
        } else {
            Matcher m = classPattern.matcher(c.getName());
            //result = m.matches();
            result = m.find();
        }
        return result;
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
     * Very special hack.
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
