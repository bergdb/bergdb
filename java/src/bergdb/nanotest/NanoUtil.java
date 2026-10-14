package bergdb.nanotest;

import java.util.HashSet;
import java.util.Set;

/**
 * Public static utility methods for this lib.
 * 
 * @author Frans Lundberg
 */
public class NanoUtil {
    //
    // Some methods may be duplicated from other source to avoid
    // library dependencies.
    //
    
    private NanoUtil() {}
    
    /**
     * Creates and returns set of items.
     */
    public static <T> Set<T> createSet(T... items) {
        // Taken from java-cut.
        
        HashSet<T> set = new HashSet<T>(items.length);
        
        for (T item : items) {
            set.add(item);
        }
        
        return set;
    }
}
