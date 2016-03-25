package bergdb.common;

import bergdb.nanotest.IPack;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        ByteArrayComparator.class,
        Bytes.class,
        EventToWaitFor.class,
        FrequencySensor.class,
        Bug.class,
        MyLongSet.class,
        NullOutputStream.class,
        NullReportHandler.class,
        Pack.class,
        ReportHandler.class,
        Salsa.class,
        StringMap.class,
        SystemOutReportHandler.class,
        Util.class,
        
        // Classes in nanotest:
        bergdb.nanotest.CommandLine.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
