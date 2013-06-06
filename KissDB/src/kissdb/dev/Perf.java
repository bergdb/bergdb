package kissdb.dev;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import kissdb.common.IPack;
import kissdb.nanotest.BasicCollector;
import kissdb.nanotest.TestRunner;


/**
 * Runs performance tests; nanotests in group "perf".
 * 
 * @author Frans Lundberg
 */
public class Perf {
    
    public static void main(String[] args) {
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
        
        BasicCollector collector = new BasicCollector();
        collector.setPrintProps(true);
        collector.setPrintMethods(false);
        String[] groups = new String[]{"perf"};
        
        for (Class<?> c : classes) {
            TestRunner.run(groups, c, methodPattern, collector);
        }
        
        System.out.println(collector.getReport());
    }
}
