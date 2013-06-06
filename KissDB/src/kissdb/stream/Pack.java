package kissdb.stream;

import kissdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        FileStream.class,
        MemoryStream.class,
        MemoryStream.Tester.class,
        NullStream.class,
        OneFileStream.class,
        Pack.class,
        SalsaStream.class
    };
   
    public Class<?>[] getClasses() {
        return classes;
    }
}
