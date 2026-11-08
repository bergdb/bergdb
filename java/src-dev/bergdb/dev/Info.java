package bergdb.dev;

import java.io.PrintWriter;

import bergdb.common.Util;
import bergdb.core.BuildInfo;

/**
 * Development tool, prints information about the environment.
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
        out.println("Information about the BergDB environment.");
        out.println();
        
        buildInfo();
        runtime();
        system();
        
        out.flush();
    }
    
    private void buildInfo() {
        out.println("---- BergDB ----");
        out.println("BuildInfo.release: " + BuildInfo.RELEASE);
        out.println("BuildInfo.versionInt: " + BuildInfo.RELEASE_INT);
        out.println("BuildInfo.build: " + BuildInfo.BUILD);
        out.println();
    }
    
    private void runtime() {
        out.println("---- Runtime ----");
        
        Runtime r = Runtime.getRuntime();
        out.println("availableProcessors: " + r.availableProcessors());        
        out.println("Util.runsAndroid(): " + Util.runsAndroid());
        
        out.println();
    }
    
    private void system() {
        // Properties we want to print if not null.
        
        String[] props = new String[] {
                "java.vm.name",
                "java.runtime.version",
                "java.vm.vendor",
                "java.vm.version",
                "sun.boot.library.path",
                "user.country",
                "file.encoding",
                "os.name",
                "os.version"
        };
        
        out.println("---- System.getProperties() ----");
        
        for (String p : props) {
            String s = System.getProperty(p);
            if (s != null) {
                out.println(p + ": " + s);
            }
        }
        out.println();
    }
    
    public static void main(String[] args) throws Exception {
        new Info().go(args);
    }
}
