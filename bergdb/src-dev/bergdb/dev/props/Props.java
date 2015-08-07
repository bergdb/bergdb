package bergdb.dev.props;

import bergdb.common.Util;

/**
 * An executable that measures the main performance properties of the projecct.
 * 
 * @author Frans Lundberg
 */
public class Props {
    
    private static void printHeader() {
        System.out.println("\n==== " + Props.class.getName() + " ====");
        
        String computer = Util.hostname();
        String today = Util.today();
        String jvm = Util.jvm();
        
        System.out.println(today + ", " + computer);
        System.out.println(jvm);
    }

    public static void main(String[] args) throws Exception {
        printHeader();
        
        MEM mem = new MEM();
        mem.go();
        System.out.println(mem.report);
        
        CORE corePerf = new CORE();
        corePerf.go();
        System.out.println(corePerf.result.shortReport);
        
        SS ss = new SS();
        ss.go();
        System.out.println(ss.longResultText);
    }
}

/*

150721
======

2015-07-21, cissi, Java HotSpot(TM) 64-Bit Server VM 24.76-b04, java 1.7.0_76
MEM:161
CORE:0.79 (0.81, 1.01, 0.86, 0.56)
SS:1.48 (1.16, 1.26, 1.60, 2.06)

150106 Four JVMs
================

150106 Frans: Running Props with three different JVMs. computer: cissi. 
SS prop is shown once only, since it does not vary between JVMs.

    Java HotSpot(TM) 64-Bit Server VM 24.65-b04, java 1.7.0_67
    MEM:161
    CorePerf:0.78 (0.83, 0.98, 0.85, 0.55)
    SS:1.56 (1.25, 1.34, 1.66, 2.12)
    
    Java HotSpot(TM) 64-Bit Server VM 1.5.0_22-b03, java 1.5.0_22
    MEM:203
    CORE:1.05 (0.86, 1.91, 0.88, 0.84)
    
    OpenJDK 64-Bit Server VM 23.25-b01, java 1.6.0_33
    MEM:161
    CORE:0.77 (0.79, 1.00, 0.81, 0.54)
    
    IKVM.NET 7.2.4630.5, java 1.7.0
    MEM:268
    CORE:1.64 (1.36, 1.59, 2.34, 1.43)

CONSLUSIONS: HotSpot 7 is faster and uses less memory then HotSpot 5. OpenJDK 1.6
is very similar to HotSpot 7 in performance (same code base?). IKVM is slower and 
uses more memory then the others, but I am still impressed by the performance.
Something within a factor of 2.0 is impressive.

*/