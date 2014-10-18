package bergdb.test;

import bergdb.common.IPack;
import bergdb.test.manual.StreamSizeVsStartupDistance;
import bergdb.test.manual.TransThroughput;

public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        BigDb.class,
        BigDbEvict.class,
        BigDbWithDeletes.class,
        Bug130924.class,
        Concurrency2.class,
        Crazy.class,
        CreateIndexTester.class,
        DeleteIndexTester.class,
        FileSynchPerformance.class,
        GetScalability.class,
        GetManyScalability.class,
        Get.class,
        GetThreaded.class,
        IsDeterministic.class,
        OneByteToFile.class,
        OneGig.class,
        Pack.class,
        PerfDBMem.class,
        PerfGetMany.class,
        PerfTreeMapGet.class,
        PerfTreeMapSet.class,
        ScenarioTester.class,
        StartupDistanceTester.class,
        StreamSizeTest.class,
        StreamSizeVsStartupDistance.class,
        Set.class,
        StreamSize.class,
        TransThroughput.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
