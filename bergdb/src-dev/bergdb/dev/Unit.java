package bergdb.dev;

import bergdb.common.Create;

/**
 * Runs unit tests for the project. Run them before every commit.
 * 
 * @author Frans Lundberg
 */
public class Unit {
    public static void main(String[] args) {
        NanotestForBergDB nano = new NanotestForBergDB(args, TestClasses.getIPacksStatic(), 
                Create.setOfStrings("unit"));
        nano.go();
    }
}
