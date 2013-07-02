package bergdb.nanotest;

import java.lang.annotation.Annotation;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Locale;
import java.util.regex.Pattern;

/**
 * This class is used to run Nanotests.
 * 
 * @author Frans Lundberg
 */
public class TestRunner {    
    
    /**
     * Run a nanotest method (static void method with zero or one ICollector param).
     * 
     * @param c  The class.
     * @param methodName  Name of the method.
     * @param collector  Test result collector.
     */
    public static void runMethod(Class<?> c, String methodName, TestRunnerCollector collector) {
        Method[] methods = c.getDeclaredMethods();
        Method m = null;
        
        for (Method method : methods) {
            if (method.getName().equals(methodName)) {
                m = method;
            }
        }
        
        if (m == null) {
            return;
        }
        
        if (!m.isAnnotationPresent(T.class)) {
            return;
        }
        
        m.setAccessible(true);    // can run a private method, useful feature.

        Class<?>[] paramTypes = m.getParameterTypes();
    
        Object[] params = null;
        if (paramTypes.length == 1) {
            params = new Object[1];
            params[0] = collector;
        }
        
        Throwable testError = null;
        Object object = null;
        
        collector.testAboutToRun(c.getCanonicalName() + "." + m.getName());
        
        try {
            m.invoke(object, params);
        } catch (Throwable ex) {
            testError = ex;
        }
        
        collector.testDone(testError);
    }
    
    /**
     * Runs the tests in a class.
     * Only the tests belonging to one of the groups in 'groups' will be run.
     * The result is collected by 'collector'.
     */
    public static void run(String[] groups, Class<?> c, Pattern methodPattern, 
            TestRunnerCollector collector) {
        collector.classAboutToRun(c);
        
        Method[] methods = c.getDeclaredMethods();
        Arrays.sort(methods, new Comparator<Method>() {
            public int compare(Method m0, Method m1) {
                return m0.getName().toLowerCase(Locale.US)
                        .compareTo(m1.getName().toLowerCase(Locale.US));
            }
        });
        
        for (Method m : methods) {
            boolean handle = false;
            if (methodPattern == null) {
                handle = true;
            } else {
                handle = methodPattern.matcher(m.getName()).matches();
            }
            
            if (handle) {
                handleMethod(m, collector, groups);
            }
        }
        
        collector.classDone();
    }
    
    private static void handleMethod(Method m, TestRunnerCollector collector, String[] groups) {
        boolean runTest = false;
        boolean junit = false;
        
        A: {
            if (m.isAnnotationPresent(T.class)) {
                // Always try to run test if method has annotation and it is
                // in the the groups to run.
                // If method is not static, or has bad parameter set, we 
                // should report error to user, not just skip the test method.
                
                T annotation = m.getAnnotation(T.class);
                if (!isInGroups(annotation.value(), groups)) {
                    break A;
                }
                
                runTest = true;
                
            } else {
                
                // A static void method named "test*" is considered a "unit" test
                // method if it takes no parameters.
                
                String mName = m.getName();
                if (isInGroups("unit", groups) && mName.startsWith("test")) {
                    int mod = m.getModifiers();
                    if (Modifier.isStatic(mod)) {
                        Class<?> returnType = m.getReturnType();
                        Class<?>[] paramTypes = m.getParameterTypes();
                        
                        if (paramTypes.length == 0 && returnType.equals(Void.TYPE)) {
                            runTest = true;
                        }
                    }
                }
            }
            
            // Check for JUnit test. If we are running "unit" test group.
            
            B: if (!runTest && isInGroups("unit", groups)) {
                Annotation[] annotations = m.getDeclaredAnnotations();
                for (Annotation an : annotations) {
                    String junitTestClass = "org.junit.Test";
                    if (an.annotationType().getCanonicalName().equals(junitTestClass)) {
                        runTest = true;
                        junit = true;
                        break B;
                    }
                }
            }
        }
        
        if (!runTest) {
            return;
        }
        
        m.setAccessible(true);    // can run private methods, useful feature.

        Class<?>[] paramTypes = m.getParameterTypes();
    
        Object[] params = null;
        if (paramTypes.length == 1) {
            params = new Object[1];
            params[0] = collector;
        }
        
        // NOTE, When <T> annoted method has bad params, or is not static, we 
        // could generate a better message to user.
        
        // NOTE, when JUnit <Test> annoted method has bad params or constructor,
        // we could generate a better message to user.
        
        Throwable testError = null;
        Object object = null;
        
        collector.testAboutToRun(m.getDeclaringClass().getCanonicalName() + "." + m.getName());
        
        try {
            if (junit) {
                object = m.getDeclaringClass().newInstance();
            }
            
            m.invoke(object, params);
        } catch (Throwable ex) {
            testError = ex;
        }
        
        collector.testDone(testError);
    }
    
    private static boolean isInGroups(String annotationValue, String[] groups) {
        String[] aGroups = annotationValue.split(" ");
        boolean result = false;
        
        A: for (String g : aGroups) {
            for (int i = 0; i < groups.length; i++) {
                if (g.equals(groups[i])) {
                    result = true;
                    break A;
                }
            }
        }
        return result;
    }

    /**
     * @throws ClassNotFoundException
     * @throws SecurityException
     */
    public static void main(String[] args) {
        BasicCollector collector = new BasicCollector();
        
        Class<?> c = MyClass.class;
        
        run(new String[]{"unit", "f"}, c, null, collector);
        
        int failed = collector.getFailed();
        if (failed == 0) {
            System.out.printf("SUCCESS! %d success tests.", collector.getTotal());
        } else {
            System.out.printf("Total: %d, failed %d%n", 
                collector.getTotal(), collector.getFailed());
        }
    }
}
