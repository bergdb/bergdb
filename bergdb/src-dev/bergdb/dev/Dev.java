package bergdb.dev;

// TODO A24. Fix test and general issue: sometimes spos = -1 is written to stream. The pointee, p, of a node has p.getSpos() == -1 because it has not ever been written to stream.
// TODO A24/1: Add failing test for the A24 issue.

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
