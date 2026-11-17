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
    java/night.sh                  # the night run: the checks below, on a clone of HEAD (about 100 minutes)
    java/night.sh large            # the same and the large conformance set (about 6 hours)
    java/night.sh tests            # only the night tests (about 4.5 minutes)
    java/stress/core-build.sh      # the Core Layer built alone, its tests on it (about 15 s; unit f: 50 s)
    java/stress/level1.sh          # full replay          (about 80 s)
    java/stress/level2.sh          # bounded startup      (about 17 minutes; quick: 2)
    java/stress/level3.sh          # reclaim              (about 8 minutes)
    java/stress/level4.sh          # eviction             (about 16 minutes; quick: 4)
    java/stress/harness-soak.sh    # the Pub layer's randomized harnesses
    java/stress/fuzz.sh            # fuzzing of the readers of bytes
    java/stress/kill-restart.sh    # the Pub layer under kills of its JVM (1,000 kills: about 26 minutes)
    java/stress/android.sh         # the unit tests and demos on an Android emulator (ANDROID_SDK)
    cd lean && lake build          # checks all proofs

before-commit.sh must print BEFORE COMMIT OK before a change to the Java code
is committed; it is the only requirement. The level scripts print LEVEL n OK;
they are deeper checks, not commit gates. night.sh is not a gate either; its
report is in build/night/.


Files
-----

in       - Non-source input: BuildInfoTemplate.txt (in/readme.txt).
build    - Output from the build.
src      - The main Java source code; the release jar's classes.
src-dev  - Development and test packages (bergdb, bergdb.dev, bergdb.test,
           bergdb.demo, frans and their subpackages), not in the release jar.
stress   - The stress tests and the scripts that run them.
