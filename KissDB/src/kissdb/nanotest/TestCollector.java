package kissdb.nanotest;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

// NOTE Consider calling the class TestEnvironment or TestResultCollector.

/**
 * A test method can choose to take a TestCollector as the single parameter.
 * This allows the test to report back information to the test runner.
 * This allows for more advanced testing than unit tests.
 * 
 * @author Frans Lundberg
 */
public interface TestCollector {
    /**
     * Reports something from the test. A named value. The name will be prefixed with the name
     * of the class and method that runs the test, so 'name' does not have to be globally unique
     * for the test run.
     * If name "note" is used, it should have a String value with text describing the test.
     * 
     * @param name The name of the reported value.
     * @param value The value. Typically a small object like a String, Long. It should have a
     * readable toString() representation.
     */
    public void report(String name, Object value);
    
    /**
     * Things written to the out() print stream in the test is typically reported immediately
     * to the user while the test is running.
     * Often, the returned object is System.out, but tests should use this PrintStream instead 
     * for flexibility of the test runner implementation.
     * The test MUST NOT close the returned PrintStream.
     */
    public PrintStream out();
    
    /**
     * Creates a temporary directory to be used in the test. 
     * Files in the directory and the directory itself will be removed by the test runner when 
     * the test finishes.
     * Tests should always try to use this method instead of creating files directly. 
     * It allows tests that works on vastly different platforms including: Unix, Windows, and
     * Android.
     */
    public File createTempDir() throws IOException;
}
