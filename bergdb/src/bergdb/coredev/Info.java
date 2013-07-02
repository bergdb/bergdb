package bergdb.coredev;

import java.io.PrintWriter;
import java.util.Properties;

import bergdb.common.Util;
import bergdb.core.BuildInfo;

// TODO A. Limit set of System.getProperties() that are printed to the most important ones.

/**
 * Development tool, executable class that prints information about the environment
 * to System.out.
 * 
 * @author Frans Lundberg
 */
public class Info {
    private PrintWriter out;
    
    /**
     * Called from main().
     */
    public void go(String[] args) {
        go(new PrintWriter(System.out));
    }
    
    /**
     * Entry point for external caller.
     * 'out' is flushed, but not closed.
     */
    public void go(PrintWriter out) {
        this.out = out;
        
        out.println("======== " + Info.class.getName() + " ========");
        out.println("Information about this computer, the JVM and the environment of the process in general.");
        out.println();
        
        buildInfo();
        general();
        runtime();
        system();
        
        out.flush();
    }
    
    private void buildInfo() {
        out.println("---- BergDB build info ----");
        out.println("BuildInfo.version: " + BuildInfo.version);
        out.println("BuildInfo.versionInt: " + BuildInfo.versionInt);
        out.println("BuildInfo.release: " + BuildInfo.release);
        out.println("BuildInfo.build: " + BuildInfo.build);
        out.println();
    }
    
    private void general() {
        out.println("---- General ----");
        out.println("Util.runsIkvm(): " + Util.runsIkvm());
        out.println("Util.runsGcj(): " + Util.runsGcj());
        out.println("Util.runsAndroid(): " + Util.runsAndroid());
        out.println();
    }
    
    private void runtime() {
        out.println("---- Runtime ----");
        Runtime r = Runtime.getRuntime();
        out.println("availableProcessors: " + r.availableProcessors());
        out.println("freeMemory: " + r.freeMemory());
        out.println("totalMemory: " + r.totalMemory());
        out.println("maxMemory: " + r.maxMemory());
        out.println();
    }
    
    private void system() {
        out.println("---- System.getProperties() ----");
        Properties p = System.getProperties();
        p.list(out);
        out.println();
        
        /*out.println("---- System.getenv() ----");
        Map<String, String> env = System.getenv();
        for (Map.Entry<String, String> entry : env.entrySet()) {
            out.println(entry.getKey() + " = " + entry.getValue());
        }
        out.println();*/
    }
    
    public static void main(String[] args) throws Exception {
        new Info().go(args);
    }
}
