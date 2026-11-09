BuildInfoTemplate.txt is the template of src/bergdb/core/BuildInfo.java that
the Ant build of 2013 to 2017 (build.xml) filled in; BuildInfo.java is edited by
hand since. jarjar-1.4.jar and style.css, which only build.xml used, went with it
in 2026.4 (bergdb 020-10, step B2).

ICU 50 (icu-for-bergdb.jar, as the package bergdb.icu50, with its license
ICU-LICENSE.html), which BergDB used for the collation of string indexes, was
removed in 2026.4 (bergdb 020-10, step B2): an index of strings orders them by
their code points. Release 2026.3's source has it, with the notes on how it was
made.
