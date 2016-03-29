package bergdb.common;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * Utility methods for creating objects.
 * 
 * @author Frans Lundberg
 */
public class Create {
    private Create() {}
    
    /**
     * Creates and returns set of items.
     */
    public static <T> Set<T> set(T... items) {
        HashSet<T> set = new HashSet<T>(items.length);
        
        for (T item : items) {
            set.add(item);
        }
        
        return set;
    }
    
    /**
     * Creates and returns a list of items.
     */
    public static <T> List<T> list(T... items) {
        ArrayList<T> list = new ArrayList<T>(items.length);
        for (T item : items) {
            list.add(item);
        }
        
        return list;
    }
    
    // ======== Tests ========
    
    @Nano
    public static void testSet() {
        Set<String> strings = Create.set("hello", "hi", "hej");
        Assert.assertEquals(3, strings.size());
        Assert.assertTrue(strings.contains("hej"));
    }
    
    @Nano
    public static void testList() {
        List<String> strings = Create.list("hello", "hi");
        Assert.assertEquals(2, strings.size());
        Assert.assertEquals("hi", strings.get(1));
    }
}
