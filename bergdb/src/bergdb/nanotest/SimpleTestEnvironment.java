package bergdb.nanotest;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.HashMap;

/**
 * A simple, basic, test environment. Can be used to easily run a single test 
 * by calling the test method directly.
 * 
 * @author Frans Lundberg
 */
public class SimpleTestEnvironment implements TestEnvironment {
    protected boolean printProps = true;
    protected PrintStream baseOut;
    private PrintStream testOut;
    private TempDirCreator tempDirCreator;
    private HashMap<String, Object> props = new HashMap<String, Object>();
    
    /**
     * A test environment that prints to System.out.
     */
    public SimpleTestEnvironment() {
        this(System.out);
    }
    
    public SimpleTestEnvironment(PrintStream output) {
        if (output == null) {
            throw new IllegalArgumentException("output == null not allowed");
        }
        baseOut = output;
        
        this.testOut = baseOut;
        this.tempDirCreator = new TempDirCreator();
    }
    
    public void setPrintOutput(boolean printOutput) {
        if (printOutput) {
            this.testOut = baseOut;
        } else {
            this.testOut = new NullPrintStream();
        }
    }
    
    public void report(String name, Object value) {
        props.put(name, value);
        
        if (printProps) {
            baseOut.println("* " + name + ": " + value);
        }
    }
    
    public PrintStream out() {
        return testOut;
    }

    public File createTempDir() throws IOException {
        return tempDirCreator.createTempDir();
    }
    
    
    // ======== Tests ======== 
    
    /**
     * For internal testing, do not include in Pack class.
     */
    static class ClassUnderTest {
        @Nano
        static void aTestThatTakesEnvironmentParameter(TestEnvironment te) {
            te.report("count", 1234);
        }
    }
    
    @Nano
    private static void testOneMethod() {
        SimpleTestEnvironment te = new SimpleTestEnvironment(new NullPrintStream());
        ClassUnderTest.aTestThatTakesEnvironmentParameter(te);
        Assert.assertEquals(1234, te.props.get("count"));
    }
}
