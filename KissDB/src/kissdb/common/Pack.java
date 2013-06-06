package kissdb.common;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        BadFormatException.class,
        ByteArrayComparator.class,
        Bytes.class,
        FrequencySensor.class,
        HashCodeUtil.class,
        Bug.class,
        MemoryOutputStream.class,
        MyLongSet.class,
        NullOutputStream.class,
        NullReportHandler.class,
        Pack.class,
        ReportHandler.class,
        Salsa.class,
        StringMap.class,
        SystemOutReportHandler.class,
        Util.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
