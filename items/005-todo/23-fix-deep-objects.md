005-23. Fix: StackOverflowError for a cyclic or deeply nested object
====================================================================

Status: open. Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in a review of the Java code for overflow, by Claude
(Opus 5.5, Claude Code), at Frans's request; checked with a probe. Frans
decided on 2026-10-21: clear exceptions.


The issue
---------

`DbObject.toDbObject` converts nested objects by recursion. A put of an
object with a reference cycle, or of a linked list 20,000 long, throws
`StackOverflowError`. It happens before the transaction runs, so the
database is not harmed, but the error says nothing about the cause.


The fix
-------

`toDbObject` keeps the path of objects it is in: an object already on the
path is a cycle, and a path deeper than 1,000 objects is too deep. Both
throw an `IllegalArgumentException` that names the field path.


Done when
---------

* Unit tests: a cycle and a 2,000-deep list are refused with the field path;
  a 100-deep list is stored and read back; an object referenced twice
  without a cycle is stored as before.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.
