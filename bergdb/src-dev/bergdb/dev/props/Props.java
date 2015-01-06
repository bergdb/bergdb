package bergdb.dev.props;

import bergdb.common.Util;

/**
 * An executable that computes the main properties of the projecct.
 * 
 * @author Frans Lundberg
 */
public class Props {
    
    private static void printHeader() {
        System.out.println("\n==== " + Props.class.getName() + " ====");
        
        String computer = Util.hostname();
        String date = Util.today();
        String jvm = System.getProperty("java.vm.name") + " " 
                + System.getProperty("java.vm.version");
        String javaVersion = "java " + System.getProperty("java.version");
        
        System.out.println(date + ", " + computer);
        System.out.println(jvm + ", " + javaVersion);
    }

    public static void main(String[] args) {
        printHeader();
        
        CorePerf corePerf = new CorePerf();
        corePerf.go();
        System.out.println(corePerf.result.shortReport);
        
        SS ss = new SS();
        ss.go();
        System.out.println(ss.longResultText);
    }
}
