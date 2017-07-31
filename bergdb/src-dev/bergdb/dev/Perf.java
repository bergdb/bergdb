package bergdb.dev;

import bergdb.common.Create;

/**
 * Runs "perf" tests for the project.
 * 
 * @author Frans Lundberg
 */
public class Perf {
    public static void main(String[] args) {
        NanotestForBergDB nano = new NanotestForBergDB(args, TestClasses.getIPacksStatic(), 
                Create.set("perf"));
        nano.go();
    }
}
