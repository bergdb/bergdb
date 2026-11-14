028-09. Investigate: checkStartupPos accepts a record's own position
====================================================================

Status: done. Kind: Investigate. Frans: none.
Created 2026-11-13 by Frans Lundberg.

The task is to find out whether this is a bug (Frans, 2026-11-13, 13:04:
"Add these as todo items. The is to evaluate whether or not they really
are bugs.").

What: the draft of 027-11 found that `checkStartupPos` accepts a
startupPos equal to the position of its own record, which the take never
writes (s(i) < i). A damaged last record R(k) with that value gives a
startup section of R(k) alone, and its gd is never read (027-11, at
7e190010).

Why: a damaged stream should be refused rather than started from a wrong
section (detecting damage is best effort and storage owns integrity,
Frans, 2026-11-12). A one-record section would skip D's rebuild.

Frans: none; the evaluation's answer is the result: a bug (refuse it), or
harmless, with the reason.

Done when: a test with a last record whose startupPos is its own position:
what the start does today. If it starts wrongly, `checkStartupPos` refuses
s(k) >= k with a `StreamFormatException`, the test, and
`java/before-commit.sh` OK.

First step: read `checkStartupPos` and its callers.


Result
------

Verdict: **a bug**, fixed. The take never writes a record's own position:
`Db.store` gets the startup pos from `TransSeq.take` (or `takeTo`), which
returns the tpos of a transaction in the take's queue, or the current
startup pos, and the record is added to the queue only after it is
written (`transSeq.add`); the creation writes 0. So s(i) < i for every
record but the creation's, and a last record with s(k) = k is damage.

What the start did with it (the test, first without the fix): a database
of four puts with sd 1,000,000 (s = 0, no index node written after the
creation), the last record's startupPos set to its own position. The
start succeeded and every key was gone: the section was R(k) alone,
whose transaction a start does not rerun, and R(k) held no index node.
A put after it succeeded and wrote that startupPos again, so a later
start lost the keys too (probe; with sd 100 the keys survived, as R(k)
held the index nodes then, but the start still skipped D's rebuild).
Silent loss of committed data, not a refusal.

The fix: `Db.checkStartupPos` refuses s(k) >= k (before: s(k) > k) with
a `StreamFormatException`, "The record at k has startupPos k, the
record's own position." The test,
`DbTesterRestart.testOwnPositionStartupPosRefused`, also asserts
s(i) < i for each record it writes. 027-11, section 1.4, says so, and
027-03's list of the refusals at a start.

Log
---

2026-11-13. Registered by coord-1113, from the draft of 027-11 (Frans, 13:04).

2026-11-13. Done by an agent of coord-1113 (startbugs, branch
028-startbugs): a bug; the test, the check in `checkStartupPos`, 027-11
updated; `java/before-commit.sh` printed `BEFORE COMMIT OK`.
