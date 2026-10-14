package bergdb.test.java;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;

/**
 * Class with a nano test ("perf") that reports the most important figures about the environment.
 */
public class Environment {
    
    @Nano("perf")
    public static void figures(TestEnvironment c) {
        Runtime rt = Runtime.getRuntime();
        
        c.report("maxMemory", rt.maxMemory());
        c.report("availableProcessors", rt.availableProcessors());
        
        String[] props = new String[]{
                "java.version", "java.vm.name",
                "os.name", "os.arch", "os.version",
                "user.name"
        };
        
        for (String p : props) {
            c.report(p, System.getProperty(p));
        }
    }
}
