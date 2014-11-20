package bergdb.nanotest;

import java.lang.annotation.Annotation;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Locale;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

// TODO LATER. A main method like bergdb.dev.Unit.main() for general use.

/**
 * Functions to run Nanotests.
 * 
 * @author Frans Lundberg
 */
public class TestRunnerUtil {
    private TestRunnerUtil() {}
    
    /**
     * Runs the tests in a class.
     * Only the tests belonging to one of the groups in 'groups' will be run.
     * The result is collected by 'collector'.
     */
    public static void runClassTests(Set<String> groups, Class<?> c, Pattern methodPattern, 
            TestRunConsumer consumer, TestEnvironment testEnv) {
        consumer.classAboutToRun(c);
        
        Method[] methods = c.getDeclaredMethods();
        sort(methods);
        
        for (Method m : methods) {
            if (matches(methodPattern, m)) {
                runMethod(m, consumer, groups, testEnv);
            }
        }
        
        consumer.classDone();
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
    public static void runOneMethod(Class<?> c, String methodName, TestRunConsumer collector, TestEnvironment testEnv) {
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
        
        runMethod(m, collector, Collections.<String>emptySet(), testEnv);
    }
    
    /**
     * @param groups   If empty, run method no matter what.
     */
    private static void runMethod(Method m, TestRunConsumer consumer, Set<String> groups, TestEnvironment testEnv) {
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
                if (!(groups.size() == 0 || isInGroups(annotation.value(), groups))) {
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
            params[0] = testEnv;
        }
        
        // NOTE, When <T> annoted method has bad params, or is not static, we 
        // could generate a better message to user.
        
        // NOTE, when JUnit <Test> annoted method has bad params or constructor,
        // we could generate a better message to user.
        
        Throwable testError = null;
        Object object = null;
        
        consumer.testAboutToRun(m.getDeclaringClass().getCanonicalName() + "." + m.getName());
        
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
        
        consumer.testDone(testError);
    }
    
    private static boolean isInGroups(String annotationValue, Set<String> groups) {
        String[] aGroups = annotationValue.split(" ");
        boolean result = false;
        
        for (String g : aGroups) {
            if (groups.contains(g)) {
                result = true;
                break;
            }
        }
        return result;
    }
}
