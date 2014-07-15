package bergdb.pubimp;

import bergdb.common.IPack;

public class PackForPub implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        bergdb.pub.Time.class,
        bergdb.pub.Duration.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
