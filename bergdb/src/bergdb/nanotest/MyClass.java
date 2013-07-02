package bergdb.nanotest;

public class MyClass {
    
    @T("f")
    public static void t1() {}
    
    @T("unit f perf")
    public static void t2() {
        throw new RuntimeException("Error!");
    }
    
    @T 
    public static void test3() {
    }
    
    public static void testWithoutAnnotation() {}
    
    public static int testNotAValidTestBecauseReturnInt() { return 0; }
    
    public static void testNotAValidTestBecauseParams(int p1) { }
    
    public static void testOfPrivateMethod() {}
    
    //
    // Lines below removed to remove dependence on JUnit.
    // Just used  to test that JUnit tests can be run.
    // NOTE if JUnit is not on the classpath, the JUnit-annotated methods will NOT run.
    //
    //@org.junit.Test
    //public void testJUnitMethod() {
    //    System.out.println("   (Hello from testJUnitMethod)");
    //}
}
