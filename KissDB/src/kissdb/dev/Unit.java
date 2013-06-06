package kissdb.dev;

import kissdb.common.IPack;

/**
 * Almost identical to kissdb.dbdev.Unit, but ipacks array contains a larger set of 
 * packages to test.
 * 
 * @author Frans Lundberg
 */
public class Unit extends kissdb.coredev.CoreUnit {
     
    private static IPack[] ipacks = new IPack[]{
        new kissdb.common.Pack(),
        new kissdb.core.Pack(),
        new kissdb.test.java.Pack(),
        new kissdb.pubimp.Pack(),
        new kissdb.stream.Pack(),
        new kissdb.test.Pack(),
        new kissdb.dev.Pack()
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
