package bergdb.dev;

import bergdb.common.IPack;

/**
 * Almost identical to bergdb.coredev.CoreUnit, but ipacks array contains a larger set of 
 * packages to test. Run the unit tests before every commit.
 * 
 * @author Frans Lundberg
 */
public class Unit extends bergdb.coredev.CoreUnit {
     
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
    
    @Override
    public IPack[] getIPacks() {
        return ipacks;
    }

    /**
     * Runs the unit tests (nano tests in group "unit"). No parameters used.
     */
    public static void main(String[] args) {
        new Unit().go(args);
    }
}
