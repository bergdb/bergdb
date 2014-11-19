package bergdb.nanotest;

/**
 * Class used for testing Nanotest.
 * 
 * @author Frans Lundberg
 */
public class DummyTestClass {
    
    private DummyTestClass() {}
    
    @T("f")
    public static void t1() {}
    
    @T("unit f perf")
    public static void t2() {
        throw new MyRuntimeException();
    }
    
    @T 
    public static void test3() {
    }
    
    public static void testWithoutAnnotation() {}
    
    public static int testNotAValidTestBecauseReturnInt() { return 0; }
    
    public static void testNotAValidTestBecauseParams(int p1) { }
    
    public static void testOfPrivateMethod() {}
    
    private static class MyRuntimeException extends RuntimeException {
        private static final long serialVersionUID = 1L;
    }
}
