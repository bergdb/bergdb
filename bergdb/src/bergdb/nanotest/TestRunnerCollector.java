package bergdb.nanotest;

/**
 * @deprecated
 */
public interface TestRunnerCollector extends TestEnvironment {
    public void classAboutToRun(Class<?> clazz);
    public void classDone();
    public void testAboutToRun(String longMethodName);
    public void testDone(Throwable t);
}
