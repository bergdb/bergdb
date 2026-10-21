005-22. Fix: a stored value too large for its Java field is truncated silently
==============================================================================

Status: done (2026-10-21). Kind: fix. Created 2026-10-21.

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


Outcome
-------

2026-10-21, by Claude (Opus 5.5, Claude Code). `DbValue.toJavaObject`
checks, before it converts a number to a primitive type or its wrapper
(`checkFits`): an `int` or `long` must be in the range of a `byte`,
`short`, `char` or `int`; a `double` in the range of an integral type, and
not NaN; a finite `double` within the range of a `float`. Otherwise a
`DataFormatException`, and `DbObject.toJavaObject` adds the field's name
and class. Array elements are checked the same way. Fractions are still
truncated, and float precision is lost as before. The plain conversions
(`toInt()` and the others, and `DbArray.toIntArray()`) still cast;
`DbInt.testToMethods1` is unchanged.

Tests: `DbObjectTester.testNarrowingOutOfRange` (twelve values that do not
fit) and `DbObjectTester.testNarrowingInRange`. `before-commit.sh`: BEFORE
COMMIT OK (956 unit tests, 61 f-tests).
