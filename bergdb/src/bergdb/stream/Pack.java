package bergdb.stream;

import bergdb.common.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        FileStream.class,
        MemoryStream.class,
        MemoryStream.Tester.class,
        DummyStream.class,
        OneFileStream.class,
        Pack.class,
        ReadOnlyStream.class,
        SalsaStream.class
    };
   
    public Class<?>[] getClasses() {
        return classes;
    }
}
