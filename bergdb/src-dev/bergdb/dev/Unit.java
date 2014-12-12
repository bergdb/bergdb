package bergdb.dev;

import bergdb.common.IPack;

/**
 * Almost identical to bergdb.coredev.CoreUnit, but ipacks array contains a larger set of 
 * packages to test. Run the unit tests before every commit.
 * 
 * @author Frans Lundberg
 */
public class Unit extends bergdb.coredev.CoreUnit {
    
    @Override
    public IPack[] getIPacks() {
        return TestClasses.getIPacksStatic();
    }

    /**
     * Runs the unit tests (nano tests in group "unit").
     */
    public static void main(String[] args) {
        new Unit().go(args);
    }
}
