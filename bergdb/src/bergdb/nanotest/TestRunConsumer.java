package bergdb.nanotest;

import java.io.PrintStream;

/**
 * A consumer of a test run implements this interface.
 * A consumer may, for example, be a console UI, graphical UI or a report generator.
 * 
 * @author Frans Lundberg
 */
public interface TestRunConsumer {
    /** Reports that the test run is about to start. */
    public void aboutToRun(int classCount);
    
    public void classAboutToRun(Class<?> clazz);
    
    public void classDone();
   
    public void testAboutToRun(String longMethodName);
    
    /** @see TestEnvironment#report(String, Object) */
    public void report(String name, Object value);

    /** @see TestEnvironment#out() */
    public PrintStream out();
    
    public void testDone(Throwable t);
    
    /** Reports that test run has completed. */
    public void done();
}
