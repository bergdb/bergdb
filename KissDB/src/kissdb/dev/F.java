package kissdb.dev;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import kissdb.common.IPack;
import kissdb.nanotest.BasicCollector;
import kissdb.nanotest.TestRunner;

/**
 * Runs functional tests ("f").
 * Run this class without arguments every week and after every major change.
 * Each f-test should run within around 10 seconds.
 * 
 * @author Frans Lundberg
 */
public class F {
    public static void main(String[] args) {
        printHeader();
        
        List<Class<?>> classes = new ArrayList<Class<?>>();
        IPack[] ipacks = Unit.getIPacksStatic();
        
        Pattern classPattern = null;
        Pattern methodPattern = null;
        
        if (args.length > 0) {
            classPattern = Pattern.compile(args[0]);
        }
        
        if (args.length > 1) {
            methodPattern = Pattern.compile(args[1]);
        }
        
        for (IPack p : ipacks) {
            for (Class<?> c : p.getClasses()) {
                if (classPattern != null) {
                    Matcher m = classPattern.matcher(c.getName());
                    if (m.matches()) {
                        classes.add(c);
                    }
                } else {          
                    classes.add(c);
                }
            }
        }
        
        BasicCollector collector = new BasicCollector(System.out);
        collector.setPrintOutput(false);
        collector.setPrintProps(false);
        collector.setPrintMethods(true);
        
        String[] groups = new String[]{"f"};
        
        for (Class<?> c : classes) {
            TestRunner.run(groups, c, methodPattern, collector);
        }
        
        System.out.println();
        System.out.println("======================================================================");
        System.out.print(collector.getReport());
        System.out.println("======================================================================");
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
