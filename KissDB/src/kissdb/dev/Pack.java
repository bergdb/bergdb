package kissdb.dev;

import kissdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        StringTester.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
