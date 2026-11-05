015-54. Fix: pSafe is not "the stream length now", as `markSafePositions`'s Javadoc says (no harm shown)
========================================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R7's finding R7-F5 (items/016-release-2026-2/06-reviews/R7.md,
section R7-F5: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R7/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. In progress: session bergdb-e8's agent verifies it and fixes the comment.

2026-11-05. Verified in the code, not fixed, by session bergdb-e8's agent;
back to open. `Reclaim.transactionCompleted` reads `streamSize = t.nextPos`
before the same call's `storeTable()` (a new iteration) and `step()`, and
passes it to `markSafePositions`, so pSafe can be below the stream's length
at the marking, as 016-06, R7-F5 says (its probe output agrees; the probe
was not rerun). A Javadoc that says "the user record's end" would not be
a fix on its own: the class comment's argument for pSafe (nodes kept dirty
by the still-dirty test when the startup pos passes pEnd are written once
more before the cut) does not cover the call's own internal records. If
the call's first internal record writes a node while a child is still
dirty and its second record's take passes pEnd, that node is a got-dirty
node of a record at or after t.nextPos, and pSafe = t.nextPos does not wait
for it; the probe shows a startup pos equal to t.nextPos at such markings.
No harm is shown (a later write, or pCut being the iteration before's
pStart, may cover it), but the argument is missing. So the fix is R7-F5's
first one, a code change (`db.getStreamLength()`, which changes the stream
where a cut comes later; `level3.sh`), or a safety argument in 001-07's
register before a Javadoc change: Frans's choice.
