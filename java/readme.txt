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

The scripts that build and test, before-commit.sh first, are listed in the
repository's README.md, under "Build and test".


Files
-----

in       - Non-source input: BuildInfoTemplate.txt (in/readme.txt).
build    - Output from the build.
src      - The main Java source code; the release jar's classes.
src-dev  - Development and test packages (bergdb, bergdb.dev, bergdb.test,
           bergdb.demo, frans and their subpackages), not in the release jar.
stress   - The stress tests and the scripts that run them.
