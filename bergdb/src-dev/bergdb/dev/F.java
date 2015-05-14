package bergdb.dev;

import java.util.Date;
import java.util.Set;

import bergdb.common.Create;
import bergdb.common.Util;
import bergdb.nanotest.ClassFilter;
import bergdb.nanotest.CommandLine;
import bergdb.nanotest.ConsoleUI;
import bergdb.nanotest.MethodFilter;
import bergdb.nanotest.TestRunner;

/**
 * Runs functional tests ("f").
 * Run this class without arguments every week and after every major change.
 * Each f-test should run within 10 seconds.
 * 
 * @author Frans Lundberg
 */
public class F {
    public static void main(String[] args) {
        CommandLine c = new CommandLine(args);
        boolean verbose = c.has("v");
        
        ConsoleUI ui = ConsoleUI.builder()
                .printStart(true)
                .printMethods(true)
                .printProps(verbose)
                .printTestOutput(verbose)
                .build();
        printHeader();
        
        String classPatternString = ".*";
        if (c.has("c")) {
            classPatternString = c.getOne("c");
        }
        
        String methodPatternString = ".*";
        if (c.has("m")) {
            methodPatternString = c.getOne("m");
        }
        
        Set<Class<?>> classes = new ClassFilter(classPatternString).filter(TestClasses.getClasses());
        MethodFilter methodFilter = new MethodFilter(methodPatternString, Create.setOfStrings("f"));
        
        TestRunner testRunner = new TestRunner(ui, classes, methodFilter);
        testRunner.run();
    }
    
    private static void printHeader() {
        System.out.println("\n======== F ========");
        String computer = Util.hostname();
        System.out.println("'f' tests on " + computer + ", " 
                    + new Date().toString() + ".\n");
    }
}
