package bergdb.dev;


import bergdb.nanotest.IPack;

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
        new bergdb.nanotest.Pack(),
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
}
