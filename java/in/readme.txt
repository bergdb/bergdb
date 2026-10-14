jarjar-1.4.jar is used for the build process only (for building bergdb-versioned.jar). 

icu-for-bergdb.jar is ICU 50 (International Components for Unicode, for
collation), repackaged in July 2013 under the package bergdb.icu50 so that it
cannot clash with another ICU on the class path. It is used by the build
(src-icu/) and bundled in the release jar.

ICU-LICENSE.html is the license file of ICU4J 50.1.1 (ICU License and the
third-party notices it lists), which is the ICU version of this jar.

How the ICU collator module was made (from Frans's notes; ICU4J 50.1
source release downloaded December 2012). Extract it to icu4j-50-1/, then:

    cd icu4j-50-1/
    ant collator
    ant moduleJar
    cp icu4j.jar ../icu4j-collator-module.jar

icu-for-bergdb.jar appears to be that module with its package renamed to
bergdb.icu50 (built 2013-07-05, per its manifest). The notes do not record how
the renaming was done.
