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
 * Runs nightly tests, Nano test group 'night'.
 * 'night' tests can be long-running and might not be deterministic.
 * They are automatic tests that fails with an exception.
 * 
 * @author Frans Lundberg
 */
public class Night {
    public static void main(String[] args) {
        ConsoleUI ui = ConsoleUI.builder()
                .printStart(true).printProps(true).printMethods(true)
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
        
        Set<Class<?>> classes = new ClassFilter(classPatternString).filter(Unit.getClasses());
        MethodFilter methodFilter = new MethodFilter(methodPatternString, Create.setOfStrings("night"));
        
        TestRunner testRunner = new TestRunner(ui, classes, methodFilter);
        testRunner.run();
    }
    
    private static void printHeader() {
        System.out.println("\n======== Night ========");
        String computer = Util.hostname();
        System.out.println("'night' tests on " + computer + ", " 
                    + new Date().toString() + ".\n");
    }
}
