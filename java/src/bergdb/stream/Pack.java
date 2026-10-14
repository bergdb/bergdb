package bergdb.stream;

import bergdb.nanotest.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        AppendOnlyStream.class,
        BadDirStateException.class,
        DummyStream.class,
        FileStream.class,
        FileStreamPowerLossTester.class,
        MemoryStream.class,
        OneFileStream.class,
        Pack.class,
        ReadOnlyStream.class,
        SalsaStream.class
    };
   
    public Class<?>[] getClasses() {
        return classes;
    }
}
