package bergdb.common;

/**
 * Use the public method to check whether asserts are enabled.
 * 
 * @author Frans Lundberg
 */
public class AssertStatus {
    private static boolean assertOn = false;
    
    static {
        assert assertOn = true;
    }
    
    public static boolean enabled() {
        return assertOn;
    }
}
