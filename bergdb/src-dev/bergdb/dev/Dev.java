package bergdb.dev;

// TODO C. Improve Nanotest, terminal app, command-line params, flexible way to specify set of classes.

/**
 * Dummy test code; for development only.
 */
public class Dev {    
    public static void main(String[] args) throws Exception { 
        go();
    }
    
    public static void go() {
        String s = "a";
        
        assert (s = "b").equals("b");
        
        boolean assertsEnabled = false;
        assert (assertsEnabled = true) == true;
        
        System.out.println("s = " + s);
        System.out.println("assertsEnabled = " + assertsEnabled);
    }
}
