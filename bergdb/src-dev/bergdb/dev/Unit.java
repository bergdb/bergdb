package bergdb.dev;

import bergdb.common.IPack;

/**
 * Runs unit tests for the project. Run them before every commit.
 * Almost identical to bergdb.coredev.CoreUnit, but ipacks array contains a larger set of 
 * packages.
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
