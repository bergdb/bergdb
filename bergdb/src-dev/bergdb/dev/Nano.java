package bergdb.dev;

import java.util.Date;
import java.util.HashSet;
import java.util.Set;

import bergdb.common.AssertStatus;
import bergdb.common.IPack;
import bergdb.common.Util;
import bergdb.nanotest.ClassFilter;
import bergdb.nanotest.CommandLine;
import bergdb.nanotest.ConsoleUI;
import bergdb.nanotest.MethodFilter;
import bergdb.nanotest.TestRunner;

/**
 * Common BergDB code to run a set of nano tests from command line.
 * 
 * @author Frans Lundberg
 */
public class Nano {
    private final String[] args;
    private final Set<Class<?>> classes;
    private final Set<String> groups;
    
    public Nano(String[] args, IPack[] ipacks, Set<String> groups) {
        this.args = args;
        this.classes = createSetOfClasses(ipacks);
        this.groups = groups;
    }
    
    public void go() {
        if (args.length > 0 && args[0].equals("help")) {
            System.out.println(getHelp());
            return;
        }
        
        CommandLine c = new CommandLine(args);        
        ConsoleUI ui = new ConsoleUI();
        ui.applyOptions(c);
        
        System.out.print(getHeader());
        
        if (!AssertStatus.enabled()) {
            System.out.println("NOTE: assertions disabled, use -ea to enable.");
        }
        
        String classPatternString = ".*";
        if (c.has("c")) {
            classPatternString = c.getOne("c");
        }
        
        String methodPatternString = ".*";
        if (c.has("m")) {
            methodPatternString = c.getOne("m");
        }
        
        Set<Class<?>> classesChosen = new ClassFilter(classPatternString).filter(classes);
        MethodFilter methodFilter = new MethodFilter(methodPatternString, groups);
        
        TestRunner testRunner = new TestRunner(ui, classesChosen, methodFilter);
        testRunner.run();
    }
    
    /**
     * Prints header, override if needed.
     */
    public String getHeader() {
        StringBuilder b = new StringBuilder();
        
        b.append("\n======== " + this.getClass().getSimpleName() + ": " + groupsToString() + " ========\n");
        
        String computer = Util.hostname();
        String time = Util.dateAndTime();
        String jvm = System.getProperty("java.vm.name") + " " + System.getProperty("java.runtime.version");
        
        if (jvm.startsWith("Java HotSpot")) {
            jvm = jvm.substring(5);
        }
        
        b.append("On " + computer + " " + time + ", " + jvm + "\n");
        
        return b.toString();
    }
    
    /**
     * Prints header, override if needed.
     */
    public String getHelp() {
        StringBuilder b = new StringBuilder();
        b.append("---- help ----\n");
        b.append("Options:\n");
        b.append("-c <classPattern> is a regexp for the name of the classes to include.\n");
        b.append("-m <methodPattern> is a regexp for the method names to include.\n");
        b.append("-s Be silent (quiet)\n");
        b.append("-d Print less, only dots and result.\n");
        b.append("-v Be verbose\n");
        b.append("-vv Be max verbose\n");
        b.append("\n");
        b.append("If methodPattern is missing, all test methods of the selected classes will run.\n");
        b.append("If classPattern is missing, all classes with test methods will be tested.\n");
        return b.toString();
    }
    
    private String groupsToString() {
        StringBuilder b = new StringBuilder();
        for (String g : groups) {
            b.append(g + " ");
        }
        
        return b.toString().trim();
    }
    
    private Set<Class<?>> createSetOfClasses(IPack[] ipacks) {
        Set<Class<?>> classes = new HashSet<Class<?>>();
        for (IPack p : ipacks) {
            for (Class<?> c : p.getClasses()) {
                classes.add(c);
            }
        }
        return classes;
    }
}
