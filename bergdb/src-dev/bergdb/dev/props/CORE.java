package bergdb.dev.props;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.TreeMap;

import bergdb.common.Util;
import bergdb.test.Get;
import bergdb.test.GetThreaded;
import bergdb.test.PerfGetMany;
import bergdb.test.Set;

/**
 * <p>An executable class that runs a fixed set of performance tests of Core Layer.
 * Use this class to quickly detect how code changes affect performance.
 * Should run within 3 minutes on an ordinary development computer.
 * Run the executable class with no arguments, or a single argument 'dots' to 
 * reduce printed output.</p>
 * 
 * <p>Baseline1 is measured with my laptop, "cissi", July 2013.
 * 64-bit Ubuntu 12.04 server, Java 1.7 from Oracle.<p>
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
public class CORE {
    Map<String, Double> resultMap;
    Map<String, Double> baseline1;
    Map<String, Double> baseline2;
    boolean printDots = true;
    boolean verbose = false;
    boolean beShort = true;
    Result result;
    
    public CORE() {
        resultMap = new TreeMap<String, Double>();
        baseline1 = new TreeMap<String, Double>();
        baseline2 = new TreeMap<String, Double>();
    }
    
    public void go(String[] args) {
        if (args.length >= 1 && args[0].equals("help")) {
            printHeader();
            printHelp();
            return;
        }
        
        if (args.length >= 1 && args[0].equals("dots")) {
            printDots = true;
        }
        
        if (args.length >= 1 && args[0].equals("verbose")) {
            verbose = true;
        }
        
        if (args.length >= 1 && args[0].equals("short")) {
            beShort = true;
        }
        
        
        printHeader();
        go();
        
        if (beShort) {
            System.out.println("\n" + result.shortReport);
        } else {
            System.out.println("\n" + result.longReport);
        }
    }
    
    public double go() {
        createBaselines();
        List<PerfMethod> methods = createMethods();
        runMethods(methods);
        computeResult();
        return result.geoMean;
    }
    
    private List<PerfMethod> createMethods() {
        List<PerfMethod> methods;
        methods = new ArrayList<PerfMethod>();
        PerfMethod method;
        
        method = new PerfMethod() {
            public double runPerf() {
                return Get.corePerfMethod();
            }
            
            public String name() {
                return "get";
            }
        };
        methods.add(method);
        
        method = new PerfMethod() {
            public double runPerf() {
                return GetThreaded.corePerfMethod();
            }
            
            public String name() { return "get4t"; }
        };
        methods.add(method);
        
        method = new PerfMethod() {
            public double runPerf() {
                try {
                    return PerfGetMany.corePerfMethod();
                } catch (InterruptedException e) {
                    throw new Error(e);
                }
            }
            
            public String name() { return "getmany"; }
        };
        methods.add(method);
        
        method = new PerfMethod() {
            public double runPerf() {
                return Set.corePerfMethod();
            }
            
            public String name() { return "set"; }
        };
        methods.add(method);
        return methods;
    }

    private void runMethods(List<PerfMethod> methods) {
        for (int i = 0; i < 5; i++) {
            for (PerfMethod m : methods) {
                runMethod(m);
            }
        }
    }
    
    private void runMethod(PerfMethod method) {
        double time = method.runPerf();
        String name = method.name();
        
        if (!resultMap.containsKey(name)) {
            resultMap.put(name, Double.MAX_VALUE);
        }
        
        double current = resultMap.get(name);
        if (time < current) {
            resultMap.put(name, time);
        }

        double normalized1 = time / (baseline1.get(name));
        double normalized2 = time / (baseline2.get(name));
        
        if (verbose) {
            String s = Util.spaceFill(name + ":", 10) 
                    + Util.twoDecimals(normalized1) + "   " 
                    + Util.twoDecimals(normalized2) + "   " + time;
            System.out.println(s);
        } else if (printDots) {
            System.out.print(".");
        }
    }
    
    private double computeResult() {
        result = new Result();
        
        StringBuilder shortReport = new StringBuilder();
        StringBuilder longReport = new StringBuilder();
        
        longReport.append("---- Result ----\n");
        double product = 1.0;
        double productGeo1 = 1.0;
        double productGeo2 = 1.0;
        int count = 0;
        boolean isFirst = true;
        
        for (Map.Entry<String, Double> entry : resultMap.entrySet()) {
            double value = entry.getValue();
            String name = entry.getKey();
            product = product * value;
            count++;
            double normalized1 = value / baseline1.get(name);
            double normalized2 = value / baseline2.get(name);
            productGeo1 = productGeo1 * normalized1;
            productGeo2 = productGeo2 * normalized2;
            
            String s = Util.spaceFill(name + ":", 10) 
                    + Util.twoDecimals(normalized1) + ",  " 
                    + Util.twoDecimals(normalized2) + ",  " + value;
            
            longReport.append(s + "\n");
            
            if (isFirst) {
                isFirst = false;
            } else {
                shortReport.append(", ");
            }
            shortReport.append(Util.twoDecimals(normalized1));
        }
        
        if (count < 2) {
            throw new Error("At least two values required!");
        }
        
        double normalizedGeoMean1 = Math.pow(productGeo1, 1.0 / count);
        double normalizedGeoMean2 = Math.pow(productGeo2, 1.0 / count);
        
        String s = "GEO MEAN: " + Util.twoDecimals(normalizedGeoMean1) + ",  " 
                + Util.twoDecimals(normalizedGeoMean2);
        longReport.append(s + "\n");
        
        result.shortReport = String.format(Locale.US, "CORE:%.2f", normalizedGeoMean1)
                + " (" + shortReport.toString() + ")";
        result.longReport = longReport.toString();
        result.geoMean = normalizedGeoMean1;
        
        return result.geoMean;
    }
    
    private void printHeader() {
        System.out.println("\n==== " + CORE.class.getName() + " ====");
        
        String computer = Util.hostname();
        String today = Util.today();
        String jvm = Util.jvm();
        
        System.out.println(today + ", " + computer);
        System.out.println(jvm);
        
        if (!printDots) {
            System.out.println();
        }
    }

    private void printHelp() {
        System.out.println("Standard set of performance tests for Core.");
        System.out.println("These tests form a standard performance test suit.");
        System.out.println("Argument: dots/verbose, or none.");
    }

    private void createBaselines() {
        // cissi
        baseline1.put("get",      1.0e-6);
        baseline1.put("get4t",    0.4e-6);
        baseline1.put("getmany",  0.2e-6);
        baseline1.put("set",      5.0e-6);
        
        // linda
        baseline2.put("get",     1.50e-6);
        baseline2.put("get4t",   0.50e-6);
        baseline2.put("getmany", 0.26e-6);
        baseline2.put("set",     8.00e-6);
    }
    
    interface PerfMethod {
        /**
         * Runs the performance tests and returns the measured time
         * in seconds.
         */
        public double runPerf();
        
        public String name();
    }
    
    static class Result {
        double geoMean;
        String shortReport;
        String longReport;
    }
    
    public static void main(String[] args) {
        CORE c = new CORE();
        c.go(args);
    }
}

/*

Log 
===


== 150515 ==
cissi, Java HotSpot(TM) 64-Bit Server VM 24.76-b04, java 1.7.0_76
CORE:0.77 (0.78, 0.98, 0.82, 0.55)

== 150422 ==
cissi, Java HotSpot(TM) 64-Bit Server VM 24.65-b04, java 1.7.0_67
CORE:0.75 (0.76, 0.96, 0.81, 0.55).

== 150106 ==
cissi, Java HotSpot(TM) 64-Bit Server VM 24.65-b04, java 1.7.0_67
CORE:0.77 (0.78, 0.98, 0.85, 0.54).

== 141109 ==
Running on cissi, BergDB 2014.2. JVM: Java HotSpot(TM) 64-Bit Server VM 24.65-b04, java 1.7.0_67.

---- Result ----
get:      0.74,  0.49,  7.384251724477857E-7
get4t:    0.96,  0.76,  3.821072264260492E-7
getmany:  0.84,  0.65,  1.679440933171994E-7
set:      0.54,  0.34,  2.7217045700000004E-6
GEO MEAN: 0.75,  0.54

Great! Running even faster with kv2 approach... And I have not even started to optimize :-)


== 140909 ==
On Cissi. OpenJDK 64-Bit Server VM 24.65-b04, java 1.7.0_65. Ubuntu 14.04.
main branch. Before kv2 branching.

---- Result ----
get:      0.80,  0.54,  8.039992727904227E-7
get4t:    0.98,  0.78,  3.923383108572271E-7
getmany:  0.84,  0.65,  1.683493660953631E-7
set:      1.01,  0.63,  5.069338365E-6
GEO MEAN: 0.91,  0.64

== 140826 ==
Running on cissi. JVM: OpenJDK 64-Bit Server VM 24.65-b04, java 1.7.0_65
get:      0.81,  0.54,  8.087790093721592E-7
get4t:    1.00,  0.80,  3.984744443304732E-7
getmany:  0.86,  0.66,  1.7207912748321522E-7
set:      0.99,  0.62,  4.949910585E-6
GEO MEAN: 0.91,  0.65

== 140715 ==
On Cissi.
get:      0.78,  0.52,  7.791102764702836E-7
get4t:    1.03,  0.82,  4.115720094654181E-7
getmany:  0.86,  0.66,  1.7254319529026488E-7
set:      0.92,  0.58,  4.60915452E-6
GEO MEAN: 0.89,  0.64

== 140715 ==
Removed "set2" since it is still not working.

== 131011 ==
Disabled "set2" temporarily because of issue I do not want to fix now.

== 130927 ==
Running on cissi, Fri Sep 27 21:02:38 CEST 2013. BergDB 2013.2.130818.
JVM: Java HotSpot(TM) 64-Bit Server VM 23.25-b01, java 1.7.0_25
get:      0.81,  0.54,  8.116645672748937E-7
get4t:    0.97,  0.78,  3.880243678605605E-7
getmany:  1.02,  0.79,  2.0477340709234035E-7
set:      0.87,  0.55,  4.3674387250000005E-6
set2:     0.84,  0.68,  2.9322052450000004E-6
GEO MEAN: 0.90,  0.66

== 130705 New profile ==
Rose profile replace - low-end 32-bit system. Of little interest.
Best run of 4. Note, values for "getmany", "get4t" varies with a factor of 3! 
For the total aggregate (min value).

Running on cissi, Fri Jul 05 10:53:26 CEST 2013.
JVM: Java HotSpot(TM) 64-Bit Server VM 23.25-b01, java 1.7.0_25
Result:
get:      0.14,  0.58,  8.661556043895126E-7
get4t:    0.09,  0.78,  3.907786488820986E-7
getmany:  0.12,  0.65,  1.6793923348358178E-7
set:      0.15,  0.54,  4.355589125E-6
set2:     0.17,  0.72,  3.1073825050000005E-6
GEO MEAN: 0.13,  0.65

Resulting profile (manual edit):

    baseline1.put("get",      1.0e-6);
    baseline1.put("get4t",    0.4e-6);
    baseline1.put("getmany",  0.2e-6);
    baseline1.put("set",      5.0e-6);
    baseline1.put("set2",     3.5e-6);
    
    
== 130705 Rose profile deleted ==
From test running on Rose - low-end 32-bit Ubuntu netbook, Feb 2013. Profile values:
    baseline1.put("get",      6.4e-6);
    baseline1.put("get4t",    4.2e-6);
    baseline1.put("getmany",  1.4e-6);
    baseline1.put("set",     29.0e-6);
    baseline1.put("set2",    18.0e-6);


*/