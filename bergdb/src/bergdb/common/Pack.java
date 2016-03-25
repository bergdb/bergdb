package bergdb.common;

import bergdb.nanotest.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        AssertStatus.class,
        ByteArrayComparator.class,
        Bytes.class,
        EventToWaitFor.class,
        FrequencySensor.class,
        Bug.class,
        MyLongSet.class,
        NullOutputStream.class,
        Pack.class,
        ReportHandler.class,
        Salsa.class,
        StringMap.class,
        Util.class,
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
