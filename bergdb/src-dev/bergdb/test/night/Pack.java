package bergdb.test.night;

import bergdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        CcDbTest.class,
        Issue150420.class,
        PayTest.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
