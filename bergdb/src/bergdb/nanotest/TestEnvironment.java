package bergdb.nanotest;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

/**
 * A test method can choose to take a TestCollector as the single parameter.
 * This allows the test to report back information to the test runner.
 * This allows for more advanced testing than unit tests.
 * 
 * @author Frans Lundberg
 */
public interface TestEnvironment {
    /**
     * Reports a property of the test run. A named value. 'name' does not have to be unique
     * for all tests, just unique for within this particular test.
     * If name "note" is used, it should have a String value with text describing the test.
     * 
     * @param name  The name of the reported value.
     * @param value  The value. Typically a small object like a String, Long. It should have a
     * human-readable toString() representation.
     */
    public void report(String name, Object value);
    
    /**
     * Things written to the out() print stream in the test is typically reported immediately
     * to the user interface while the test is running.
     * Tests should NOT write to System.out/err, write to this PrintStream instead.
     * The test MUST NOT close the PrintStream.
     */
    public PrintStream out();
    
    /**
     * Creates a temporary directory to be used in the test. 
     * Files in the directory and the directory itself will be removed by the test runner when 
     * the test finishes.
     * Tests should always use this method instead of creating files directly. 
     * It allows tests that works on vastly different platforms including: Unix, Windows, and
     * Android.
     */
    public File createTempDir() throws IOException;
}
