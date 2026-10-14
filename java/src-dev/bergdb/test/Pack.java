package bergdb.test;

import bergdb.dev.MemPerf;
import bergdb.nanotest.IPack;
import bergdb.test.java.PerfTreeMapGet;
import bergdb.test.java.PerfTreeMapSet;
import bergdb.test.manual.StreamSizeVsStartupDistance;
import bergdb.test.manual.TransThroughput;

/**
 * Pack class for bergdb.nanotest package. 
 * Cannot be included in bergdb.nanotest itself since IPack interface not included
 * in bergdb.nanotest package.
 * 
 * @author Frans 
 */
public class Pack implements IPack {
    private static Class<?>[] classes = new Class<?>[] {
        BigDb.class,
        BigDbWithDeletes.class,
        BryanIssue.class,
        Bug130924.class,
        Bug141109.class,
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
        MemPerf.class,
        PerfGetMany.class,
        PerfTreeMapGet.class,
        PerfTreeMapSet.class,
        ScenarioTester.class,
        StartupDistanceTester.class,
        StreamSizeVsStartupDistance.class,
        Set.class,
        StreamSize.class,
        TransThroughput.class
    };
    
    public Class<?>[] getClasses() {
        return classes;
    }
}
