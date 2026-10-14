package bergdb.nanotest;

/**
 * Class used for testing Nanotest itself.
 * 
 * @author Frans Lundberg
 */
public class DummyTestClass {
    
    private DummyTestClass() {}
    
    @Nano("f")
    public static void t1() {}
    
    @Nano("unit perf")
    public static void t2() {}
    
    public static void testWithParameter(TestEnvironment t) {}
    
    @Nano 
    public static void test3() {}
    
    public static void testWithoutAnnotation() {}
    
    @SuppressWarnings("unused")
    private static void testInPrivateMethod() {}
    
    static void testInPackageAccessMethod() {}
    
    public static int testNotAValidTestBecauseReturnInt() { return 0; }
    
    public static void testNotAValidTestBecauseParams(int p1) { }
}
