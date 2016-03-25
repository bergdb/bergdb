package bergdb.nanotest;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Locale;
import java.util.Set;

/**
 * Takes a set of classes and a TestRunConsumer and runs the
 * nano tests in the classes and reports the results to the TestRunConsumer.
 * 
 * @author Frans Lundberg
 */
public class TestRunner {
    private TestRunConsumer consumer;
    private Set<Class<?>> classes;
    private final TempDirCreator tempDirCreator;
    private MethodFilter methodFilter;

    public TestRunner(TestRunConsumer consumer, Set<Class<?>> classes, MethodFilter methodFilter) {
        this.consumer = consumer;
        this.classes = classes;
        this.tempDirCreator = new TempDirCreator();
        this.methodFilter = methodFilter;
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
        
        Class<?>[] array = createArrayOfClasses();
        
        consumer.aboutToRun(array.length);
        
        for (Class<?> c : array) {
            runClassTests(c, myConsumer, testEnv, methodFilter);
        }
        
        consumer.done();
    }

    private Class<?>[] createArrayOfClasses() {
        Class<?>[] array = classes.toArray(new Class<?>[0]);
        Arrays.sort(array, new Comparator<Class<?>>() {
            public int compare(Class<?> c1, Class<?> c2) {
                return c1.getName().toLowerCase(Locale.US)
                        .compareTo(c2.getName().toLowerCase(Locale.US));
            }
        });
        return array;
    }
    
    /**
     * Runs the tests in a class.
     * Only the tests belonging to one of the groups in 'groups' will be run.
     * The result is collected by 'collector'.
     */
    public static void runClassTests(Class<?> c, TestRunConsumer consumer, TestEnvironment testEnv, 
            MethodFilter filter) {        
        Method[] methods = c.getDeclaredMethods();
        sort(methods);
        
        ArrayList<Method> methodsToRun = new ArrayList<Method>(methods.length);
        
        for (Method m : methods) {
            if (filter.include(m)) {
                methodsToRun.add(m);
            }
        }
        
        if (methodsToRun.size() > 0) {
            consumer.classAboutToRun(c);
    
            for (Method m : methodsToRun) {
                invokeTestMethod(m, consumer, testEnv);
            }
            
            consumer.classDone();
        }
    }
    
    /**
     * @param groups If empty, run method no matter what.
     */
    private static void invokeTestMethod(Method m, TestRunConsumer consumer, TestEnvironment testEnv) {
        Object object = null;
        boolean isJunit = MethodFilter.isJunitTest(m);
        Throwable testError = null;
        Object[] params = null;
        
        consumer.testAboutToRun(m.getDeclaringClass().getCanonicalName() + "." + m.getName());
        
        try {
            if (isJunit) {
                object = m.getDeclaringClass().newInstance();
            } else {
                Class<?>[] paramTypes = m.getParameterTypes();
                if (paramTypes.length == 1) {
                    params = new Object[1];
                    params[0] = testEnv;
                }
                
                // Can run private methods too. 
                // It should, methods like "private static testMethod()" are supported.
                m.setAccessible(true);
            }
            
            m.invoke(object, params);
        } catch (Throwable ex) {
            testError = ex;
        }
        
        consumer.testDone(testError);
    }
    
    private static void sort(Method[] methods) {
        Arrays.sort(methods, new Comparator<Method>() {
            public int compare(Method m0, Method m1) {
                return m0.getName().toLowerCase(Locale.US)
                        .compareTo(m1.getName().toLowerCase(Locale.US));
            }
        });
    }
}
