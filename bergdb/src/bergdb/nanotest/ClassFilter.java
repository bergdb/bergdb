package bergdb.nanotest;

import java.util.HashSet;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ClassFilter {
    private Pattern pattern;
    
    /**
     * @param regex  Regular expression to match any substring of full classname.
     */
    public ClassFilter(String regex) {
        pattern = Pattern.compile(regex);
    }
    
    public boolean include(Class<?> c) {
        Matcher m = pattern.matcher(c.getName());
        boolean result = m.find();
        return result;
    }

    public Set<Class<?>> filter(Set<Class<?>> classes) {
        Set<Class<?>> result = new HashSet<Class<?>>();
        for (Class<?> c : classes) {
            if (include(c)) {
                result.add(c);
            }
        }
        return result;
    }
}
