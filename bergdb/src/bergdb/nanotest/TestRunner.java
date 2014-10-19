package bergdb.nanotest;

import java.lang.annotation.Annotation;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Locale;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

// TODO LATER. A main method like bergdb.dev.Unit.main() for general use.

/**
 * Functions to run Nanotests.
 * 
 * @author Frans Lundberg
 */
public class TestRunner {
    private TestRunner() {}
    
    /**
     * Runs the tests in a class.
     * Only the tests belonging to one of the groups in 'groups' will be run.
     * The result is collected by 'collector'.
     */
    public static void run(String[] groups, Class<?> c, Pattern methodPattern, 
            TestRunnerCollector collector) {
        collector.classAboutToRun(c);
        
        Method[] methods = c.getDeclaredMethods();
        sort(methods);
        
        for (Method m : methods) {
            if (matches(methodPattern, m)) {
                runMethod(m, collector, groups);
            }
        }
        
        collector.classDone();
    }

    private static void sort(Method[] methods) {
        Arrays.sort(methods, new Comparator<Method>() {
            public int compare(Method m0, Method m1) {
                return m0.getName().toLowerCase(Locale.US)
                        .compareTo(m1.getName().toLowerCase(Locale.US));
            }
        });
    }

    /**
     * Matches any occurences of regexp in method name.
     */
    private static boolean matches(Pattern methodPattern, Method m) {
        boolean result;
        if (methodPattern == null) {
            result = true;
        } else {
            Matcher matcher = methodPattern.matcher(m.getName());
            result = matcher.find();
        }
        return result;
    }
    
    /**
     * Runs a single nanotest 'unit' test method.
     * 
     * @param c  The class.
     * @param methodName  Name of the method.
     * @param collector  Test result collector.
     */
    public static void runOneMethod(Class<?> c, String methodName, TestRunnerCollector collector) {
        if (c == null) {
            throw new IllegalArgumentException("c == null not allowed");
        }
        
        if (methodName == null) {
            throw new IllegalArgumentException("methodName == null not allowed");
        }
        
        if (collector == null) {
            throw new IllegalArgumentException("collector == null not allowed");
        }
        
        Method[] methods = c.getDeclaredMethods();
        Method m = null;
        
        for (Method method : methods) {
            if (method.getName().equals(methodName) && method.isAnnotationPresent(T.class)) {
                m = method;
            }
        }
        
        if (m == null) {
            return;
        }
        
        runMethod(m, collector, new String[0]);
    }
    
    /**
     * @param m
     * @param collector
     * @param groups   If empty, run method no matter what.
     */
    private static void runMethod(Method m, TestRunnerCollector collector, String[] groups) {
        boolean runTest = false;
        boolean junit = false;
        int modifiers = m.getModifiers();
        
        A: {
            if (m.isAnnotationPresent(T.class)) {
                // Always try to run test if method has annotation and it is
                // in the the groups to run.
                // If method is not static, or has bad parameter set, we 
                // should report error to user, not just skip the test method.
                
                T annotation = m.getAnnotation(T.class);
                if (!(groups.length == 0 || isInGroups(annotation.value(), groups))) {
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
        
        // Can run private methods, useful feature.
        m.setAccessible(true);

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
            
            if (!Modifier.isStatic(modifiers)) {
                throw new RuntimeException("Nanotest method must be static.");
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
     * Test.
     * 
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
