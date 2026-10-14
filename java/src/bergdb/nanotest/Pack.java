package bergdb.nanotest;

/**
 * Pack class for bergdb.nanotest package.
 * 
 * @author Frans Lundberg
 */
public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        Assert.class,
        SimpleTestEnvironment.class,
        ClassFilter.class,
        CommandLine.class,
        ConsoleUI.class,
        ConsumerDecorator.class,
        DummyTestClass.class,
        IPack.class,
        MethodFilter.class,
        Nano.class,
        NullPrintStream.class,
        Pack.class,
        TempDirCreator.class,
        TestEnvironment.class,
        TestRunConsumer.class,
        TestRunner.class        
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
