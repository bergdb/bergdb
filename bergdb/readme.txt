readme.txt for bergdb Java project
==================================

An Apache Ant build script (build.xml) is available to build the project. 
See CHANGEIT markers in the script for sections that need to be updated to match
your environment.


To build
--------

The Java source code is available in src/ and src-icu/.
Dependencies: Java 5, in/icu-for-kissdb.jar, in/BuildInfoTemplate.txt.

To build the source:

    ant jar
    
The output class files and jar files are written to out/.

To test
-------

To test the generated jar file:

    java -jar out/kissdb.jar kissdb.dev.Unit
    
Good luck!

/ Frans Lundberg
