package bergdb.dev;

import bergdb.common.Create;

/**
 * Runs functional tests ("f") for testing proper function.
 * These tests have a larger scope then unit tests and are allow 
 * to run for longer. 
 * Each f-test should run within 10 seconds.
 * These tests are not performance tests.
 * Run this class after every major change.
 * 
 * @author Frans Lundberg
 */
public class F {
    public static void main(String[] args) {
        NanotestForBergDB nano = new NanotestForBergDB(args, 
                TestClasses.getIPacksStatic(), Create.set("f"));
        nano.go();
    }
}
