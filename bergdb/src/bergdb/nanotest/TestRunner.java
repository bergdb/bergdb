package bergdb.nanotest;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Set;
import java.util.regex.Pattern;

/**
 * Takes a set of classes and a TestRunConsumer and runs the
 * nano tests in the classes and reports the results to the TestRunConsumer.
 * 
 * @author Frans Lundberg
 */
public class TestRunner {
    private TestRunConsumer consumer;
    private Pattern methodPattern;
    private Set<Class<?>> classes;
    private Set<String> groups;
    private final TempDirCreator tempDirCreator;

    public TestRunner(TestRunConsumer consumer, Set<Class<?>> classes, String methodRegex, Set<String> groups) {
        this.consumer = consumer;
        this.classes = classes;
        this.groups = groups;
        this.tempDirCreator = new TempDirCreator();
        
        if (methodRegex == null) {
            methodRegex = ".*";
        }
        
        this.methodPattern = Pattern.compile(methodRegex);
    }
    
    public void run() {
        TestEnvironment testEnv = new TestEnvironment() {
            public void report(String name, Object value) {
                consumer.report(name, value);
            }

            public PrintStream out() {
                return consumer.out();
            }

            public File createTempDir() throws IOException {
                return tempDirCreator.createTempDir();
            }
        };
        
        TestRunConsumer myConsumer = new ConsumerDecorator(consumer) {
            public void testDone(Throwable t) {
                tempDirCreator.deleteTempDirs();
                tempDirCreator.clearTempDirs();
                super.testDone(t);
            }
        };
        
        for (Class<?> c : classes) {
            TestRunnerUtil.runClassTests(groups, c, methodPattern, myConsumer, testEnv);
        }
    }
}
