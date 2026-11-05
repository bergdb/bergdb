015-54. Fix: pSafe is not "the stream length now", as `markSafePositions`'s Javadoc says (no harm shown)
========================================================================================================

Status: done. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

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

2026-11-05. In progress: session bergdb-e8's agent makes R7-F5's code fix
(Frans, 10:47: "54 as recommended").

2026-11-05. Done by session bergdb-e8's agent (R7-F5's first fix, Frans's
choice, 10:47). `Reclaim.markSafePositions` takes no argument and sets
pSafe to `db.getStreamLength()` (the write lock is held): the stream's
length when it is set, after the internal records that the call of
`transactionCompleted` appended before it (an iteration's table, a step,
the table of an iteration done); `transactionCompleted` no longer passes
`streamSize = t.nextPos`. The method's Javadoc and the class comment say
so and why (those records' takes may move the startup pos past pEnd and
keep nodes dirty). Checked against 010-01's P1 to P12: no new work, wait,
setting or API; the value is a function of the accepted transactions
(P2), and restarts give the same stream (`level3.sh`, step 3).

* Test: `Reclaim.Tester.testSafePosAfterTheCallsRecords`, R7-F5's probe's
  workload: at each marking, pSafe is at least the user record's end plus
  the bytes of the call's steps (and more when the call started an
  iteration), and at most the stream's length. Before the fix it fails at
  put 119: "pSafe 44544, the user record ends at 44544, the call's steps
  wrote 2112 bytes". In the probe's first 4000 puts every one of the 57
  markings comes in a call that made a step before it, so pSafe was below
  the length at the marking nearly always, not only in R7-F5's 2 or 3
  calls that also started an iteration.
* Lean: the model has no pSafe. Its scheme check (`checkSchemeB`,
  SIS/ReclaimExample.lean) waits for the startup pos to pass j0, the state
  after the record whose take first moved it past tEnd; with one record per
  state, that is the fixed Java's pSafe or before it, so the fix brings
  Java to the model's wait or later. The conformance (level3.sh, step 8)
  checks `CutOK` at every cut Java decides and does not read pSafe: 25
  traces, C-CUT 0 of 305 fail. Nothing in `lean/` changes.
* StreamDigest (`54-safe-pos-javadoc/digest-summary.txt`): against 2026.2's
  reference, the decided digests are the same in 24 of 36 and differ in the
  12 of the 4 configurations with reclaim (`l3-every1`, `l3-node8`,
  `l3-node14`: the table's pSafe values only; `l3-node62`: 2.1% longer, the
  last cut decided one iteration earlier); the modes agree. The new
  reference is `54-safe-pos-javadoc/digests-new.txt`; a line in
  `releases/next.md` (Reliability).
* Gates: `before-commit.sh`: `BEFORE COMMIT OK (103 s)`, unit 1135, f 81;
  `level3.sh`, full: `LEVEL 3 OK`.
