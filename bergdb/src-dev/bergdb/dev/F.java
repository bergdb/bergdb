package bergdb.dev;

import java.util.Date;
import java.util.Set;
import bergdb.common.Create;
import bergdb.common.Util;
import bergdb.nanotest.ClassFilter;
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
        ConsoleUI ui = ConsoleUI.builder()
                .printStart(true).printProps(false).printMethods(true)
                //.printTestOutput(true)   // TODO A. working here
                .build();
        printHeader();
        
        String classPatternString = ".*";
        if (args.length >= 1) {
            classPatternString = args[0];
        }
        
        String methodPatternString = ".*";
        if (args.length >= 2) {
            methodPatternString = args[1];
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
