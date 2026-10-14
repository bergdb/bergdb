package bergdb.common;

/**
 * Use the public method to check whether asserts are enabled.
 * 
 * @author Frans Lundberg
 */
public class AssertStatus {
    // Global state should be avoided, but this is fundamentally a JVM-global 
    // property, so the static is OK here.
    
    private static boolean assertOn = false;
    
    static {
        assert assertOn = true;
    }
    
    public static boolean enabled() {
        return assertOn;
    }
    
    // ======== Tests ========
    
    public static void test0() {
        if (assertOn != enabled()) throw new AssertionError();
    }
}
