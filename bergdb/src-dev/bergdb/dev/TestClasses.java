package bergdb.dev;

import java.util.HashSet;
import java.util.Set;

import bergdb.common.IPack;

/**
 * Methods related to the collection of test classes.
 * 
 * @author Frans Lundberg
 */
public class TestClasses {
    
    private static IPack[] ipacks = new IPack[]{
        new bergdb.common.Pack(),
        new bergdb.core.Pack(),
        new bergdb.dag.Pack(),
        new bergdb.storage.Pack(),
        new bergdb.test.Pack(),
        new bergdb.test.java.Pack(),
        new bergdb.test.night.Pack(),
        new bergdb.pubimp.Pack(),
        new bergdb.pubimp.PackForPub(),
        new bergdb.stream.Pack(),
        new bergdb.dev.Pack()
    };
    
    public static IPack[] getIPacksStatic() {
        return ipacks;
    }
    
    /**
     * Creates and returns a set of all classes in the packages
     * specified in TestClasses.ipacks.
     */
    public static Set<Class<?>> getClasses() {
        Set<Class<?>> classes = new HashSet<Class<?>>();
        IPack[] ipacks = getIPacksStatic();
        for (IPack p : ipacks) {
            for (Class<?> c : p.getClasses()) {
                classes.add(c);
            }
        }
        return classes;
    }    
}
