028-10. Investigate: the public Db.start(StartParams) takes unchecked values
============================================================================

Status: done (2026-11-14). Kind: Investigate. Frans: decision (A).
Created 2026-11-13 by Frans Lundberg.

The task is to find out whether this is a bug (Frans, 2026-11-13, 13:04:
"Add these as todo items. The is to evaluate whether or not they really
are bugs.").

What: the draft of 027-11 found that `Db.start(StartParams)` is public and
takes a caller's startup pos and startup distance unchecked, and then
leaves the meta block's lastTrans and sd as read: another startup section
than the stream's (R5), another next meta block (P2). Only
`StartParams.NULL` is passed anywhere in `java/` (027-11, at c82bce56).

Why: a caller of the Core API can start a database from a section the
stream does not name, against R5 (010-04) and P2 (010-01). The Core API is
low-level and less safe (Frans, 2026-11-09), but a wrong start may write a
stream that later starts differently.

Frans: none; the evaluation's answer is the result: a bug, or acceptable
for the Core API, with the reason; and if a bug, which fix: make it
package-private, check the values, or remove the parameters.

Done when: the evaluation in this entry; if a fix is chosen, the change, a
test, and `java/before-commit.sh` OK.

First step: list every use of `StartParams` (java/, src-dev, tests) and
what a wrong value does at the next start.


Result
------

Verdict: **a bug**, by R5 (010-04: "A call of the Core API, whatever its
arguments, keeps the integrity of the Core's key-value store"): a public
call with a wrong startup pos loses committed keys, lastingly, with no
exception. The fix is a choice of API, for Frans; not made.

The uses of `StartParams` (`java/src`, `java/src-dev`, the tests):

* `Db.start()` passes `StartParams.NULL`, the only value passed in
  production code; `Db.handleStartParams` reads s and sd from the stream
  for `NULL` and takes the caller's otherwise.
* `DbTesterJavadoc` calls `start(null)` (020-27, Q2: refused with
  `IllegalArgumentException` before the locks), and in its list of calls
  after `stop()`.
* `bergdb.test.BigDb` has `start(StartParams.NULL, ...)` in a comment.
* The Pub API never passes one; no other value is passed anywhere but in
  this entry's test.

What a caller's values do (the test,
`DbTesterRestart.testStartParamsTakenUnchecked`, on four puts with sd
1,000,000, so the stream's s is 0):

* **A startup pos after the stream's** (the third record's position):
  the start succeeds without the keys of the records before it (/k1, /k2
  gone; /k4 there). The next commit's take starts from the caller's s, so
  its record names that s or a later one, and a normal start afterwards
  reads from there: /k1 is gone for good. With the last record's
  position, every key was gone (probe).
* **A position that is not a record's** (that position + 8): refused, a
  `StreamFormatException` ("not committed"), from the read of the
  section.
* **Another startup distance** (100): in force for the run (the take
  paces by it, so the stream's bytes depend on a start parameter, against
  P2's spirit), while the meta block in memory keeps the stream's sd, so
  the next start takes 1,000,000 again. No data lost.
* The walk of 027-11, section 1.4, with its checks (`checkStartupPos`,
  028-09's too), `MetaBlock.checkFormat` and the meta block's new
  lastTrans are skipped for any value but `NULL`.

**Options**, each in full:

* **A. Remove the parameters.** Delete `Db.start(StartParams)` and the
  class `Db.StartParams`; `start()` does what `start(StartParams.NULL)`
  does now, and `handleStartParams` keeps only its `NULL` branch (read s
  by the walk, sd from the meta block). Goes with it: the `start(null)`
  checks in `DbTesterJavadoc` (020-27, Q2's case is gone with the
  parameter), BigDb's comment, `testStartParamsTakenUnchecked`, and 027-11,
  section 1.4's sentence on it. About 40 lines less. A public Core method
  goes; nothing outside the tests calls it, and the Core API is the
  low-level, less stable one (Frans, 2026-11-09). R5 holds by
  construction: a start always takes the stream's s and sd.
* **B. Package-private.** `start(StartParams)` and `StartParams` lose
  `public`; the behaviour stays, for tests in `bergdb.core` only. The
  smallest change, but it keeps a door that no test but this entry's uses,
  and a test that passes a wrong s can still lose keys.
* **C. Check the values.** Refuse a startup pos other than the one the
  stream names, and an sd other than the meta block's, or write a
  caller's sd into the meta block. A real check needs the walk that finds
  the stream's s and the meta block's sd anyway, so a value is either the
  stream's or refused: the parameters then do nothing. A weaker check (a
  committed record's position) still lets a later s through, which is
  the case that loses data; the start cannot tell a later s from the
  take's without the walk (015-73).

**Recommendation: A.** Nothing uses the parameters, a check cannot make
them useful (C), and keeping them hidden (B) keeps the hazard and the
code. KISS (Frans, 2026-11-13, 10:06). With A, the test of this entry is
removed with the method it tests.

Log
---

2026-11-13. Registered by coord-1113, from the draft of 027-11 (Frans, 13:04).

2026-11-13. Evaluated by an agent of coord-1113 (startbugs, branch
028-startbugs): a bug by R5; the test of today's behaviour; options A to
C, recommended A; no fix made (an API choice, Frans's).

2026-11-14, 12:10. Frans: "Remove the parameters if possible. It if works
with the current testing. Then clean up the code." Option A.

2026-11-14. Done by an agent of coord-1114, on branch
028-10-remove-start-params: `Db.start(StartParams)` and the class
`Db.StartParams` removed; `Db.start()`, the only start, which
`DbBuilder.start()` and the Pub API call, does what
`start(StartParams.NULL)` did. `handleStartParams` became
`readStartupPosAndDistance()`, its `NULL` branch alone: s by the walk
from the last valid meta block's lastTrans, sd from the meta block, both
set for the run. Gone with them: the empty `Db.StartListener`,
`PrintStartListener` and `SYSTEM_OUT_START_LISTENER` (no use but
BigDb's comment, the second parameter of an older start), the
`start(null)` checks in `DbTesterJavadoc.testDbNullArguments`,
`DbTesterRestart.testStartParamsTakenUnchecked`, BigDb's comment, and
the Javadoc's mention of `Db.StartParams` among the internal members.
No test needed a chosen startup pos or distance: no test hook kept.
027-03, section 14.2's outline, and 027-11 (1.4, 6, 7, 8 and 9) say
what the code does now. The C clones (012, 022) are separate projects,
not changed: their comments name `handleStartParams`, and they never
had `StartParams` (012-03, row 27). Gates in the clone: `before-commit.sh`
(BEFORE COMMIT OK, 70 s), `level1.sh` (LEVEL 1 OK) and `level2.sh
quick` (LEVEL 2 OK, with the Lean conformance steps).
