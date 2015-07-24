readme.txt for BergDB Java project
==================================

An Apache Ant build script (build.xml) is available to build the project. 
See CHANGEIT markers in the script for sections that need to be updated to match
your environment.


To build
--------

The Java source code is available in src/ and src-icu/.
Dependencies: Java 5, in/icu-for-bergdb.jar, in/BuildInfoTemplate.txt.

To build the source:

    ant jar
    
The output class files and jar files are written to out/.

To test
-------

To test the generated jar file:

    java -jar out/bergdb.jar bergdb.dev.Unit


Files
-----

in       - Non-source input for build.
out      - Output from build.
src      - The main Java source code directory.
src-icu  - Source code for package bergdb.pubimpicu.
src-dev  - Development and test packages not needed in production 
           and could be omitted from the final build.

----
    
Good luck!

/ Frans Lundberg
