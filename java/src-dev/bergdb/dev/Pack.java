package bergdb.dev;

import bergdb.nanotest.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        NanotestForBergDB.class,
        Run.class,
        StringTester.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
