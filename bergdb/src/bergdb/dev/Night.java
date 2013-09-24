package bergdb.dev;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import bergdb.common.IPack;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.TestRunner;

/**
 * Runs nightly tests, Nano test group 'night'.
 * 
 * @author Frans Lundberg
 */
public class Night {
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
        collector.setPrintOutput(true);
        collector.setPrintProps(false);
        collector.setPrintMethods(true);
        collector.setPrintStart(true);
        
        String[] groups = new String[]{"night"};
        
        for (Class<?> c : classes) {
            TestRunner.run(groups, c, methodPattern, collector);
        }
        
        System.out.println();
        System.out.println("======================================================================");
        System.out.print(collector.getReport());
        System.out.println("======================================================================");
    }
    
    private static void printHeader() {
        System.out.println("\n======== Night ========");
        String computer = "'unknown'";
        try {
            computer = InetAddress.getLocalHost().getHostName();
        } catch (UnknownHostException e) {
            // empty
        }
        System.out.println("'night' tests on " + computer + ", " 
                    + new Date().toString() + ".\n");
    }
}
