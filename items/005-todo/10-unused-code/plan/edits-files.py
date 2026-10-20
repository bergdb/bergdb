EDITS = [
("java/src-dev/bergdb/test/Pack.java",
"""import bergdb.dev.MemPerf;
import bergdb.nanotest.IPack;
import bergdb.test.java.PerfTreeMapGet;
import bergdb.test.java.PerfTreeMapSet;
import bergdb.test.manual.StreamSizeVsStartupDistance;
import bergdb.test.manual.TransThroughput;
""",
"""import bergdb.nanotest.IPack;
"""),
("java/src-dev/bergdb/test/Pack.java",
"""        DeleteIndexTester.class,
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
    };""",
"""        DeleteIndexTester.class,
        IsDeterministic.class,
        Pack.class,
        ScenarioTester.class,
        StartupDistanceTester.class
    };"""),
("java/src/bergdb/common/Pair.java",
""" * Immutable 2-tuple implementation.
 * This class and Triplet forms a very simple tuple library for BergDB. 
 * If we need more, we could switch to http://www.javatuples.org/.
 * 
 * @see Triplet
 * @author Frans Lundberg""",
""" * Immutable 2-tuple implementation.
 * If we need more, we could switch to http://www.javatuples.org/.
 * 
 * @author Frans Lundberg"""),
("java/src-dev/bergdb/dev/TestClasses.java",
"""        new bergdb.test.java.Pack(),
""", ""),
("java/src-dev/bergdb/dev/TestClasses.java",
"""        new bergdb.stream.Pack(),
        new bergdb.dev.Pack()
""",
"""        new bergdb.stream.Pack()
"""),
("java/src/bergdb/core/Pack.java", """        Cache2.class,
""", ""),
("java/src/bergdb/dag/Pack.java", """        DagChecksum.class,
""", ""),
("java/src-dev/bergdb/dev/Run.java",
"""        out.println("  " + bergdb.dev.Perf.class.getName() + " - Runs 'perf' tests.");
""", ""),
("java/src-dev/bergdb/dev/Run.java",
"""        out.println("  " + bergdb.dev.Info.class.getName() + " - Prints info about the system.");
        out.println("  " + bergdb.dev.Swing.class.getName() + " - Test the graphics environment by displaying a Swing window.");
""", ""),
("java/build.sh", "# Non-Java resources, as in the original build.xml.",
 "# Non-Java resources, as the 2017 Ant build copied them."),
("java/src/bergdb/core/BuildInfo.java",
""" * Information about the build. BuildInfoTemplate.txt is a source code template for the 
 * generated file BuildInfo.java. Do not edit BuildInfo.java.""",
""" * Information about the build: the release of the 2017 source. The 2017 Ant build
 * generated this file from a template; build.sh compiles it as it is."""),
("java/in/readme.txt",
"""jarjar-1.4.jar is used for the build process only (for building bergdb-versioned.jar). 

""", ""),
("java/src-dev/bergdb/test/Concurrency2.java",
""" * Simpler version of Concurrency.""",
""" * Simpler version of the Concurrency test of 2013 (removed in bergdb 005-10)."""),
("docs/level4-plan.md",
"""The old [Cache2.java](../java/src/bergdb/core/Cache2.java) implements""",
"""The old Cache2.java (removed in bergdb 005-10; `git show
0597329:java/src/bergdb/core/Cache2.java`) implements"""),
]
