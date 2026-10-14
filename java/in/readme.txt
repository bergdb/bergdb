jarjar-1.4.jar is used for the build process only (for building bergdb-versioned.jar). 

icu-for-bergdb.jar is ICU 50 (International Components for Unicode, for
collation), repackaged in July 2013 under the package bergdb.icu50 so that it
cannot clash with another ICU on the class path. It is used by the build
(src-icu/) and bundled in the release jar.

ICU-LICENSE.html is the license file of ICU4J 50.1.1 (ICU License and the
third-party notices it lists), which is the ICU version of this jar.
