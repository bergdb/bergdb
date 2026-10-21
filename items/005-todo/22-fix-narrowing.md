005-22. Fix: a stored value too large for its Java field is truncated silently
==============================================================================

Status: open. Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in a review of the Java code for overflow, by Claude
(Opus 5.5, Claude Code), at Frans's request. Frans decided on 2026-10-21:
throw.


The issue
---------

An object is read into its Java class field by field
(`DbValue.toJavaObject`). When the field is narrower than the stored value,
`DbValue.toInt()`, `toShort()`, `toByte()` and `toChar()` cast, as Java
does: after a field changed from `long` to `int`, a stored 3,000,000,000
reads as -1,294,967,296. A unit test (`DbInt.testToMethods1`) asserts the cast.
Java `byte`, `short` and `char` fields are stored as `int` values, so these
conversions are used for every such field.


The fix
-------

Reading into a Java field throws a `DataFormatException` naming the field
when the stored value does not fit it; a value that fits reads as today.
The plain `DbValue` conversions (`toInt()` and the others) keep the cast,
since they are also used inside the code; the check is where a value is
written to a Java field.


Done when
---------

* Unit tests: an out-of-range value for `int`, `short`, `byte` and `char`
  fields throws, an in-range one reads.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.
