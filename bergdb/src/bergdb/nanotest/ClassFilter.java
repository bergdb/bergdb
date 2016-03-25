package bergdb.nanotest;

import java.util.HashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import bergdb.common.Create;

/** 
 * A filter for classes based on a regular expression applied to the
 * class names.
 * 
 * @author Frans Lundberg
 */
public class ClassFilter {
    private Pattern pattern;
    
    /**
     * @param regex  Regular expression to match any substring of the full classname.
     */
    public ClassFilter(String regex) {
        pattern = Pattern.compile(regex);
    }

    public Set<Class<?>> filter(Set<Class<?>> classes) {
        Set<Class<?>> result = new HashSet<Class<?>>();
        for (Class<?> c : classes) {
            if (include(c.getName())) {
                result.add(c);
            }
        }
        return result;
    }
    
    /**
     * The predicate function.
     * 
     * @return True if the class, c, should be included in the result set.
     */
    private boolean include(String className) {
        Matcher m = pattern.matcher(className);
        boolean result = m.find();
        return result;
    }
    
    
    // ======== Tests ========
    
    private class TestClassAlice {}
    private class TestClassBob {}
    private class TstClassCharlie {}
    
    @Nano
    static void test0() {
        @SuppressWarnings("unchecked")
        Set<Class<?>> classes = Create.set(TestClassAlice.class, TestClassBob.class, TstClassCharlie.class);
        classes = new ClassFilter(".*").filter(classes);
        Assert.assertEquals(3, classes.size());
    }
    
    @Nano
    static void test1() {
        @SuppressWarnings("unchecked")
        Set<Class<?>> classes = Create.set(TestClassAlice.class, TestClassBob.class, TstClassCharlie.class);
        classes = new ClassFilter("TestClass").filter(classes);
        Assert.assertEquals(2, classes.size());
    }
    
    @Nano
    static void test2() {
        @SuppressWarnings("unchecked")
        Set<Class<?>> classes = Create.set(TestClassAlice.class, TestClassBob.class, TstClassCharlie.class);
        classes = new ClassFilter("Bob").filter(classes);
        Assert.assertEquals(1, classes.size());
    }
}
