package bergdb.dev;

import java.util.Date;
import java.util.Map;
import java.util.TreeMap;

import bergdb.common.Util;
import bergdb.nanotest.BasicCollector;
import bergdb.nanotest.TestRunner;
import bergdb.test.Get;
import bergdb.test.GetThreaded;
import bergdb.test.PerfGetMany;
import bergdb.test.Set;

/**
 * <p>An executable class that runs a fixed set of performance tests of Core Layer.
 * Use this class to quickly detect how code changes affect performance.
 * Should run within 3 minutes on a standard development computer.</p>
 * 
 * <p>Run the executable class with no arguments, or a single argument 'dots' to 
 * reduce printed output.</p>
 * 
 * <p>Baseline1 is measured with my netbook, "rose", Feb 2013.
 * 32-bit Ubuntu OS.<p>
 * 
 * <p>Baseline2 is measured with "linda"; a virtual private server hosted by linode.com
 * (1 GB RAM version). Runs 64-bit Ubuntu. 
 * "java -version": Java(TM) SE Runtime Environment (build 1.6.0_22-b04)
 * Java HotSpot(TM) 64-Bit Server VM (build 17.1-b03, mixed mode).
 * Run with -server flag.
 * OS (cat /proc/version): Linux version 2.6.39.1-x86_64-linode19.</p>
 * 
 * @author Frans Lundberg
 */
public class CorePerf {
    private Map<String, Double> result;
    private Map<String, Double> baseline1;     // rose, 2013-03
    private Map<String, Double> baseline2;     // linda, 2013-05-02.
    private boolean printDots = false;
    
    public CorePerf() {
        result = new TreeMap<String, Double>();
        baseline1 = new TreeMap<String, Double>();
        baseline2 = new TreeMap<String, Double>();
    }
    
    private BasicCollector createCollector() {
        BasicCollector collector = new BasicCollector();
        collector.setPrintProps(false);
        collector.setPrintMethods(false);
        collector.setPrintOutput(false);
        return collector;
    }
    
    private void printHeader() {
        System.out.println("\n======== " + CorePerf.class.getName() + " ========");
        String computer = Util.getComputerName();
        System.out.println("Running on " + computer + ", " + new Date() + ".");
        System.out.println("JVM: " + System.getProperty("java.vm.name") + ", " + System.getProperty("java.vm.version"));
        
        if (!printDots) {
            System.out.println();
        }
    }
    
    public void go(String[] args) {
        if (args.length >= 1 && args[0].equals("help")) {
            printHeader();
            System.out.println("Standard set of performance tests for Core.");
            System.out.println("These tests form a standard performance test suit.");
            System.out.println("Use no arguments to run the tests, or one argument 'dots' to reduced printed output.");
            return;
        }
        
        if (args.length >= 1 && args[0].equals("dots")) {
            printDots = true;
        }
        
        printHeader();
        
        // rose
        baseline1.put("get",      6.4e-6);
        baseline1.put("get4t",    4.2e-6);
        baseline1.put("getmany",  1.4e-6);
        baseline1.put("set",     29.0e-6);
        baseline1.put("set2",    18.0e-6);
        
        // linda
        baseline2.put("get",     1.50e-6);
        baseline2.put("get4t",   0.50e-6);
        baseline2.put("getmany", 0.26e-6);
        baseline2.put("set",     8.00e-6);
        baseline2.put("set2",    4.30e-6);
        
        int n = 5;
        
        for (int i = 0; i < n; i++) {
            runMethod(Get.class, "run", "get-time", "get");
            runMethod(GetThreaded.class, "get4t", "get-time-4", "get4t");
            runMethod(PerfGetMany.class, "standard", "time-per-kv", "getmany");
            runMethod(Set.class, "normal", "time-per-trans", "set");
            runMethod(Set.class, "noWritesToStream", "time-per-trans", "set2");
        }
        
        handleResult();
    }

    private void handleResult() throws Error {
        System.out.println("\n---- Result ----");
        double product = 1.0;
        double productGeo1 = 1.0;
        double productGeo2 = 1.0;
        int count = 0;
        
        for (Map.Entry<String, Double> entry : result.entrySet()) {
            double value = entry.getValue();
            String name = entry.getKey();
            product = product * value;
            count++;
            double normalized1 = value / baseline1.get(name);
            double normalized2 = value / baseline2.get(name);
            productGeo1 = productGeo1 * normalized1;
            productGeo2 = productGeo2 * normalized2;
            //System.out.printf(Locale.US, "%-10s %.3g  %.2f  %.2f\n", name, value, normalized1, normalized2);
            String s = Util.spaceFill(name + ":", 10) 
                    + Util.twoDecimals(normalized1) + ",  " 
                    + Util.twoDecimals(normalized2) + ",  " + value;
            System.out.println(s);
        }
        
        if (count < 2) {
            throw new Error("At least two values required!");
        }
        
        double normalizedGeoMean1 = Math.pow(productGeo1, 1.0 / count);
        double normalizedGeoMean2 = Math.pow(productGeo2, 1.0 / count);
        
        System.out.println();
        //System.out.printf(Locale.US, "%-20s %.2f  %.2f\n", "**** GEO MEANS:", normalizedGeoMean1, normalizedGeoMean2);
        String s = "GEO MEAN: " + Util.twoDecimals(normalizedGeoMean1) + ",  " + Util.twoDecimals(normalizedGeoMean2);
        System.out.println(s);
        
        System.out.println();
    }
    
    private void runMethod(Class<?> clazz, String methodName, String propName, 
            String shortName) {
        BasicCollector collector = createCollector();
        long nanos = System.nanoTime();
        
        TestRunner.runMethod(clazz, methodName, collector);
        
        nanos = System.nanoTime() - nanos;
        
        
        String fullPropName = clazz.getCanonicalName() + "." + methodName + "." + propName;
        Object value = collector.getProp(fullPropName);
        
        if (value == null) {
            throw new Error("No value for property " + fullPropName);
        }
        
        if (!(value instanceof Double)) {
            throw new Error("Property " + fullPropName + " not a Double.");
        }
        
        Double dValue = (Double) value;
        Double previous = this.result.get(shortName);
        
        if (previous == null) {
            previous = Double.POSITIVE_INFINITY;
        }
        
        if (dValue < previous) {
            result.put(shortName, dValue);
        }
        
        double normalized1 = dValue / (baseline1.get(shortName));
        double normalized2 = dValue / (baseline2.get(shortName));
        
        if (printDots) {
            System.out.print(".");
        } else {
            // 1305 Frans: following printf does not work for GCJ build.
            //System.out.printf(Locale.US, "%-10s %.3g  %.2f  %.2f\n", shortName, value, normalized1, normalized2);
            
            String s = Util.spaceFill(shortName + ":", 10) 
                    + Util.twoDecimals(normalized1) + "   " 
                    + Util.twoDecimals(normalized2) + "   " + value;
            System.out.println(s);
        }
    }
    
    public static void main(String[] args) {
        new CorePerf().go(args);
    }
}

/*

Log 
===

130530 Removed use of System.out.printf() since it does not work for GCJ build.


*/