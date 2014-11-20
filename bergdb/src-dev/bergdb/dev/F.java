package bergdb.dev;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Date;
import java.util.HashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import bergdb.common.IPack;
import bergdb.nanotest.ConsoleUI;
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
        printHeader();
        
        Set<Class<?>> classes = new HashSet<Class<?>>();
        IPack[] ipacks = Unit.getIPacksStatic();
        
        Pattern classPattern = null;
        String methodRegex = null;
        
        if (args.length > 0) {
            classPattern = Pattern.compile(args[0]);
        }
        
        if (args.length > 1) {
            methodRegex = args[1];
        } else {
            methodRegex = ".*";
        }
        
        for (IPack p : ipacks) {
            for (Class<?> c : p.getClasses()) {
                if (classPattern != null) {
                    Matcher m = classPattern.matcher(c.getName());
                    if (m.find()) {
                        classes.add(c);
                    }
                } else {          
                    classes.add(c);
                }
            }
        }
        
        ConsoleUI ui = ConsoleUI.builder()
                .printStart(true).printProps(false).printMethods(true)
                .build();
        Set<String> groups = new HashSet<String>();
        groups.add("f");
        
        TestRunner runner = new TestRunner(ui, classes, methodRegex, groups);
        runner.run();
    }
    
    private static void printHeader() {
        System.out.println("\n======== F ========");
        String computer = "'unknown'";
        try {
            computer = InetAddress.getLocalHost().getHostName();
        } catch (UnknownHostException e) {
            // empty
        }
        System.out.println("'f' tests on " + computer + ", " 
                    + new Date().toString() + ".\n");
    }
}
