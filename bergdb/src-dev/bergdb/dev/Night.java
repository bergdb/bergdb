package bergdb.dev;

import bergdb.common.Create;

/**
 * Runs nightly tests, Nano test group 'night'.
 * 'night' tests can be long-running and might not be deterministic.
 * They are automatic tests that fails with an exception.
 * 
 * @author Frans Lundberg
 */
public class Night {
    public static void main(String[] args) {
        Nano nano = new Nano(args, TestClasses.getIPacksStatic(), Create.setOfStrings("night"));
        nano.go();
    }
}
