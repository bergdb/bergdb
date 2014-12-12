package bergdb.nanotest;

import java.lang.annotation.Annotation;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.HashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class MethodFilter {
    private Pattern pattern;
    private Set<String> groups;
    
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
}
