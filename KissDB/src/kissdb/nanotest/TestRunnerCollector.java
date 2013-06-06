package kissdb.nanotest;

public interface TestRunnerCollector extends TestCollector {
    public void classAboutToRun(Class<?> clazz);
    public void classDone();
    public void testAboutToRun(String longMethodName);
    public void testDone(Throwable t);
}
