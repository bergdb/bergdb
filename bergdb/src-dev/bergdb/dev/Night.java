package bergdb.dev;

import java.util.Date;
import java.util.Set;

import bergdb.common.AssertStatus;
import bergdb.common.Create;
import bergdb.common.Util;
import bergdb.nanotest.ClassFilter;
import bergdb.nanotest.CommandLine;
import bergdb.nanotest.ConsoleUI;
import bergdb.nanotest.MethodFilter;
import bergdb.nanotest.TestRunner;

// TODO D. f/unit/night - use same class.

/**
 * Runs nightly tests, Nano test group 'night'.
 * 'night' tests can be long-running and might not be deterministic.
 * They are automatic tests that fails with an exception.
 * 
 * @author Frans Lundberg
 */
public class Night {
    public static void main(String[] args) {
        CommandLine c = new CommandLine(args);
        ConsoleUI ui = new ConsoleUI();
        ui.applyOptions(c);
        
        printHeader();
        
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
