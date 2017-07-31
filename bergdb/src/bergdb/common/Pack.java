package bergdb.common;

import bergdb.nanotest.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        AssertStatus.class,
        Bug.class,
        ByteArrayComparator.class,
        Bytes.class,
        Create.class,
        EventToWaitFor.class,
        HashUtil.class,
        MyChecksum.class,
        MyLongSet.class,
        NullOutputStream.class,
        Pack.class,
        Pair.class,
        Salsa.class,
        SeedGenerator.class,
        StringMap.class,
        StringUtil.class,
        Util.class,
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
