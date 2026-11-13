028-10. Investigate: the public Db.start(StartParams) takes unchecked values
============================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-13 by Frans Lundberg.

The task is to find out whether this is a bug (Frans, 2026-11-13, 13:04:
"Add these as todo items. The is to evaluate whether or not they really
are bugs.").

What: the draft of 027-11 found that `Db.start(StartParams)` is public and
takes a caller's startup pos and startup distance unchecked, and then
leaves the meta block's lastTrans and sd as read: another startup section
than the stream's (R5), another next meta block (P2). Only
`StartParams.NULL` is passed anywhere in `java/` (027-11, at 7e190010).

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


Log
---

2026-11-13. Registered by coord-1113, from the draft of 027-11 (Frans, 13:04).
