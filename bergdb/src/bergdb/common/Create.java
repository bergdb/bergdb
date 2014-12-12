package bergdb.common;

import java.util.HashSet;
import java.util.Set;

/**
 * Utility methods for creating objects.
 * 
 * @author Frans Lundberg
 */
public class Create {
    private Create() {}
    
    /**
     * Creates and returns a set of strings from the given strings.
     */
    public static Set<String> setOfStrings(String... strings) {
        HashSet<String> set = new HashSet<String>(strings.length);
        
        for (String s : strings) {
            set.add(s);
        }
        
        return set;
    }
}
