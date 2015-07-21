package bergdb.common;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Utility methods for creating objects.
 * 
 * @author Frans Lundberg
 */
public class Create {
    private Create() {}
    
    /**
     * Creates and returns a set of strings from the given parameters.
     */
    public static Set<String> setOfStrings(String... strings) {
        HashSet<String> set = new HashSet<String>(strings.length);
        
        for (String s : strings) {
            set.add(s);
        }
        
        return set;
    }
    
    /**
     * Creates and returns a list of items given as parameters.
     */
    public static <T> List<T> list(T... items) {
        ArrayList<T> list = new ArrayList<T>(items.length);
        for (T item : items) {
            list.add(item);
        }
        
        return list;
    }
}
