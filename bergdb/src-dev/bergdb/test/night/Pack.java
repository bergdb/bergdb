package bergdb.test.night;

import bergdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        PayTest.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
