package bergdb.nanotest;

import java.lang.annotation.Annotation;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.HashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import bergdb.common.Create;

/**
 * A method filter that includes methods that are Nanotests and
 * belongs to one of the specified groups.
 * 
 * @author Frans Lundberg
 */
public class MethodFilter {
    private Pattern pattern;
    private Set<String> groups;
    
    /** Filter that represents all unit test (nanotests belonging to "unit" group). */
    public static final MethodFilter UNIT_TESTS = new MethodFilter(Create.set("unit"));
    
    public MethodFilter(Set<String> groups) {
        this(".*", groups);
    }
    
    public MethodFilter(String regex, Set<String> groups) {
        this.pattern = Pattern.compile(regex);
        this.groups = new HashSet<String>(groups);
    }
    
    public boolean include(Method m) {
        Matcher matcher = pattern.matcher(m.getName());
        boolean nameMatches = matcher.find();
        if (!nameMatches) {
            return false;
        }
        
        if (isJunitTest(m)) {
            return groups.contains("unit");
        } else if (isNanoTestByAnnotation(m)) {
            Nano annotation = m.getAnnotation(Nano.class);
            return isInGroups(annotation.value());
        } else if (isNanoTestByConvention(m)) {
            return groups.contains("unit");
        }
        
        return false;
    }
    
    public static boolean isJunitTest(Method m) {
        Annotation[] annotations = m.getDeclaredAnnotations();
        boolean isJunit = false;
        
        for (Annotation an : annotations) {
            if (an.annotationType().getCanonicalName().equals("org.junit.Test")) {
                isJunit = true;
            }
        }
        
        return isJunit;
    }
    
    private boolean isNanoTestByAnnotation(Method m) {
        return m.isAnnotationPresent(Nano.class);
    }
    
    private boolean isNanoTestByConvention(Method m) {
        String name = m.getName();
        boolean nameOk = name.startsWith("test") && name.length() > "test".length();
        if (!nameOk) {
            return false;
        }
        
        boolean isStatic = Modifier.isStatic(m.getModifiers());
        boolean returnsVoid = m.getReturnType().equals(Void.TYPE);
        
        Class<?>[] paramTypes = m.getParameterTypes();
        boolean paramsOk = (paramTypes.length == 0) 
                           || (paramTypes.length == 1 && paramTypes[0].equals(TestEnvironment.class));
        
        boolean isNanoTest = nameOk && isStatic && paramsOk && returnsVoid;
        return isNanoTest;
    }
    
    private boolean isInGroups(String annotationValue) {
        String[] annotationGroups = annotationValue.split(" ");
        boolean result = false;
        
        for (String g : annotationGroups) {
            if (groups.contains(g)) {
                result = true;
                break;
            }
        }
        return result;
    }
    
    
    // ======== Tests ========
    
    static class TestClassA {
        static void test1() {}
        static void t2() {}
        @Nano static void t3() {}
        @Nano static void bamseStor() {}
    }
    
    static void testImplicitUnitGroup() throws SecurityException, NoSuchMethodException {
        MethodFilter f = new MethodFilter(Create.set("unit"));
        Method m = TestClassA.class.getDeclaredMethod("test1");
        Assert.assertTrue(m != null);
        Assert.assertEquals(true, f.include(m));
    }
    
    static void testT3() throws SecurityException, NoSuchMethodException {
        MethodFilter f = MethodFilter.UNIT_TESTS;
        Method m = TestClassA.class.getDeclaredMethod("t3");
        Assert.assertTrue(m != null);
        Assert.assertEquals(true, f.include(m));
    }
    
    static void testBamse() throws SecurityException, NoSuchMethodException {
        MethodFilter f = new MethodFilter("bamse", Create.set("unit"));
        Method m = TestClassA.class.getDeclaredMethod("bamseStor");
        Assert.assertTrue(m != null);
        Assert.assertEquals(true, f.include(m));
    }
}
