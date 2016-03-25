package bergdb.dev;

import bergdb.common.Create;

/**
 * Runs functional tests ("f").
 * Run this class without arguments every week and after every major change.
 * Each f-test should run within 10 seconds.
 * 
 * @author Frans Lundberg
 */
public class F {
    public static void main(String[] args) {
        NanotestForBergDB nano = new NanotestForBergDB(args, TestClasses.getIPacksStatic(), Create.setOfStrings("f"));
        nano.go();
    }
}
