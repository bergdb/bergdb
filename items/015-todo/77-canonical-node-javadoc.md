015-77. Fix: dbStarter.canonicalNode's Javadoc gives a reason for the stored got-dirty ids that does not hold: a delete of a key that does not exist makes nothing dirty
========================================================================================================================================================================

Status: done. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R6's finding R6-F6 (items/016-release-2026-2/06-reviews/R6.md,
section R6-F6: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R6/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. In progress: session bergdb-e8's agent verifies it and fixes the comment.

2026-11-05. Done, by session bergdb-e8's agent. Verified in the code
(016-06, R6-F6): `Db.putKvs` ends each put or delete with `endOfOp(false)`,
which marks the operation's nodes only if it changed something; Db's own
comment and `DbTester` ("a delete of a key that does not exist changes
nothing, and marks nothing") say the same. What the rerun does not reach:
the touch of a reclaim step (`endOfOp(true)` after `touchRange`), which
`Trans.touch` says is not stored, and the nodes that the still-dirty test
keeps dirty (`Db.handleStillDirtyNodes` adds them to the got-dirty list of
the record that wrote them, whatever its puts reach). `canonicalNode`'s
Javadoc now names these two instead of the delete. A Javadoc change only,
so no test fails before it.
