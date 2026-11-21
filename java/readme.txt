readme.txt for BergDB Java project
==================================

To build
--------

build.sh builds BergDB with a JDK 17 or later (javac --release 17), from src/
and src-dev/, in a few seconds. It uses javac, jar, jdeps and java from the
path, or JAVAC, JAR, JDEPS and JAVA. Its output, in build/:

    bergdb.jar           src and src-dev; Main-Class bergdb.dev.Run. The jar
                         of the tests, the level scripts, night.sh and the
                         tools.
    bergdb-release.jar   The jar for users, which a release ships (bergdb
                         020-10, section 7): the classes and resources of src
                         only, no Main-Class.
    stress/              The stress tests, stress/*.java.

The build fails unless the release jar passes its checks (build.sh's header):
no class of src-dev, no Main-Class, every class that it uses in it or in the
JDK (jdeps), and user code, stress/release-jar/ReleaseDemo.java, that compiles
and runs with the release jar alone on the class path.

The API is the packages bergdb.pub and bergdb.pub.util, and the Core's Db
with the types of its signatures (bergdb 020-10, section 7). The release jar
holds the rest of src as well, which the API needs; it is not API, whatever
is public in it.

The Ant script of 2013 to 2017, build.xml, is gone since 2026.4 (bergdb 020-10,
step B2); release 2026.3's source has it.


To test
-------

    java -ea -cp build/bergdb.jar bergdb.dev.Unit

The scripts that build and test, from the repository's root. Each says more
in its header. Set JAVA_HOME, or JAVA, JAVAC, JAR and JDEPS, if the JDK tools
are not on the path. level2.sh to level4.sh and the proofs need Lean (elan).

    java/build.sh                  # builds build/bergdb.jar, bergdb-release.jar and the stress tests
    java/before-commit.sh          # the check before a commit: unit and f-tests, demos (about 2 minutes)
    java/unit.sh                   # runs the unit tests
    java/f.sh                      # runs the f-tests
    java/perf.sh                   # runs the perf-tests
    java/props.sh                  # runs the Props tests: MEM, CORE, SS (about 50 s)
    java/javadoc-pub.sh            # the Pub API's Javadoc, in build/javadoc-pub/
    java/night.sh                  # the night run: the checks below, on a clone of HEAD (about 2.5 hours)
    java/week.sh                   # the week run: conformance large, apps, kills, fuzzing, Android, large reclaim (about 10 hours)
    java/timing.sh                 # the timing run: CORE, pauses, performance.sh ab against the last release (quiet machine)
    java/night.sh tests            # only the night tests (about 4.5 minutes)
    java/stress/core-build.sh      # the Core Layer built alone, its tests on it (about 15 s; unit f: 50 s)
    java/stress/level1.sh          # full replay          (about 80 s)
    java/stress/level2.sh          # bounded startup      (about 17 minutes; quick: 2)
    java/stress/level3.sh          # reclaim              (about 8 minutes)
    java/stress/level4.sh          # eviction             (about 16 minutes; quick: 4)
    java/stress/harness-soak.sh    # the Pub layer's randomized harnesses
    java/stress/fuzz.sh            # fuzzing of the readers of bytes
    java/stress/kill-restart.sh    # the Pub layer under kills of its JVM (1,000 kills: about 26 minutes)
    java/stress/large.sh           # long functional reclaim: 10M keys, old reads and restarts (60 to 90 minutes; quick: a few)
    java/stress/apps.sh            # the user apps of 024-26 and 026-13 (quick: 6 minutes; soak N, kill N)
    java/stress/android.sh         # the unit tests and demos on an Android emulator (ANDROID_SDK; week.sh runs it)
    cd lean && lake build          # checks all proofs

before-commit.sh must print BEFORE COMMIT OK before a change to the Java code
is committed; it is the only requirement. The level scripts print LEVEL n OK;
they are deeper checks, not commit gates. night.sh and week.sh are not gates
either; their reports are in build/night/ and build/week/.

Each script says its kind in its header and prints it first (bergdb 028-23):
functional (the result does not depend on the machine's speed or load; time
limits inside are hang guards) or timing (the number is the result). The
functional testing is in three scripts: before-commit.sh before each commit
(about 2 minutes), night.sh about once a day while there is development, and
week.sh on demand and before every release. They may run while someone works
on the machine, night.sh and week.sh also at a low priority. Timing is in
timing.sh, the only one of them that needs a quiet machine: it checks the load
itself and refuses when the machine is busy. night.sh, week.sh and timing.sh
are disjoint sets of tests (bergdb 028-27): no step runs in two of them,
except before-commit.sh, which night.sh and week.sh run first; week.sh does
not run night.sh, and it runs the Android tests (stress/android.sh, with
ANDROID_SDK set). night.sh, week.sh and timing.sh run before every release,
on a commit near it; minor changes after are acceptable. The other timing
scripts (perf.sh, props.sh for CORE, stress/performance.sh,
stress/objectbench.sh, stress/soak.sh) also need a quiet machine.


Files
-----

in       - Non-source input: BuildInfoTemplate.txt (in/readme.txt).
build    - Output from the build.
src      - The main Java source code; the release jar's classes.
src-dev  - Development and test packages (bergdb, bergdb.dev, bergdb.test,
           bergdb.demo, frans and their subpackages), not in the release jar.
stress   - The stress tests and the scripts that run them.
