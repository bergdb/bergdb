005-23. Fix: StackOverflowError for a cyclic or deeply nested object
====================================================================

Status: done (2026-10-21). Kind: fix. Created 2026-10-21.

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
  a list as deep as allowed is stored and read back; an object referenced
  twice without a cycle is stored as before.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Outcome
-------

2026-10-21, by Claude (Opus 5.5, Claude Code). `DbObject.toDbObject` keeps,
per thread, the path of objects it is converting (by identity) and the
field of each. An object already on the path is a cycle ("The object has a
reference cycle: the ...Circular0 at c.c is also at the top"); a path of
more than `MAX_DEPTH`, 1,000, objects is too deep. Both throw an
`IllegalArgumentException`. Arrays are on the path through the field that
holds them. The field values are read in the `try` that turns reflection
errors into a `Bug`, but converted outside it, so that these exceptions of
nested objects pass.

Tests: `DbObjectTester.testCycleRefused` (a cycle through fields and one
through an array; an object referenced twice is stored), `testDeepRefused`
(2,000 deep), `testDeepAtLimit` (f-test, 1,000 deep, stored and read back,
2 s: the nested bytes are copied at every level), and
`testCircularRefs`, which asserted the `StackOverflowError`, now asserts
the exception. Not measured: whether 1,000 levels fit a thread with a small
stack; the tests run on the default stacks. `before-commit.sh`: BEFORE
COMMIT OK (958 unit tests, 62 f-tests).
