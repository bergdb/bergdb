jarjar-1.4.jar is used for the build process only (for building bergdb-versioned.jar). 

ICU 50 (icu-for-bergdb.jar, as the package bergdb.icu50, with its license
ICU-LICENSE.html), which BergDB used for the collation of string indexes, was
removed in 2026.4 (bergdb 020-10, step B2): an index of strings orders them by
their code points. Release 2026.3's source has it, with the notes on how it was
made.
