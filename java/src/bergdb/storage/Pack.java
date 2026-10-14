package bergdb.storage;

import bergdb.nanotest.IPack;

public class Pack implements IPack {
    
    private static Class<?>[] classes = new Class<?>[] {
        BufferedStream.class,
        MetaBlock.class,
        MetaBlock.Tester.class,
        Pack.class,
        RecoverableStream.class,
        RecoverableStream.Tester.class,
        StorageManager.class,
        StorageManagerTester.class,
        StreamException.class,
        StreamFormatException.class,
        StreamIoException.class,
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
