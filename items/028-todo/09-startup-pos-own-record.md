028-09. Investigate: checkStartupPos accepts a record's own position
====================================================================

Status: open. Kind: Investigate. Frans: none.
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
section (best effort, 018 and Frans 2026-11-12: storage owns integrity,
detection is best effort). A one-record section would skip D's rebuild.

Frans: none; the evaluation's answer is the result: a bug (refuse it), or
harmless, with the reason.

Done when: a test with a last record whose startupPos is its own position:
what the start does today. If it starts wrongly, `checkStartupPos` refuses
s(k) >= k with a `StreamFormatException`, the test, and `java/before-
commit.sh` OK.

First step: read `checkStartupPos` and its callers.


Log
---

2026-11-13. Registered by coord-1113, from the draft of 027-11 (Frans, 13:04).
