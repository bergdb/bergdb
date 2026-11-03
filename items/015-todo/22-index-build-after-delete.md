015-22. Fix: a deleted index's build job writes into its replacement
====================================================================

Status: done. Kind: Fix. Created 2026-11-03 by
Frans Lundberg.

For 2026.2 if it fits; else a known issue (in 2026.1 too).

What: An index deleted while its build runs, then created again with the same name: the old build writes into the new index, which then returns extra objects, duplicates and the wrong order, also after a restart. A wrong answer, through the Pub API.

Source: review R3, R3-F2 (016-06/R3, items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R3-F2), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R3-F2, made a test.


State
-----

2026-11-03, 20:30: done; reviewed (no fault) and committed after the
combined gate. Earlier:

2026-11-03, 20:02: the fix, its tests and the gate done in the clone
`/Users/f/fl/bench/016/015-20/repo`, on top of 015-20's commit; handed off
for review (`/Users/f/fl/bench/016/015-22/handoff/`). Open: the review,
the combined gate, the commit in `main`.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 19:54 to 20:02, in `/Users/f/fl/bench/016/015-20/repo` (from
`main` at `c657764`, after 015-20's commit): the fix.

* **The cause** (as R3-F2 and verify-1 say): a build's step
  (`IndexBuilderImp.createStep`) wrote entries under the index's name
  without looking at the index: neither the step nor its transaction
  depended on the index's state, so after a deletion the old build went
  on writing, into a new index of the same name if there was one. The
  state was looked at only at the activation, after the status was
  already 100, and the activation's IllegalStateException ended the
  thread.
* **The fix**: a build belongs to its own `Index` object, while that is
  creating (a deletion sets it deleting; it never goes back, and a new
  index of the name is a new object).
  * Each step's action, after its first read, adds the read hash of the
    index info's key (`Index.keyHash`) and then stops the build
    (`IndexDeletedException`, caught in `createStep`) unless its index is
    still creating. A deletion sets the state before it writes that key
    (`ensureDeletingState`, under the manager's lock), so either the step
    sees the state, or the deletion's write comes after the step's read
    and the step's transaction runs again (STM) and then sees it; a step
    that committed before the deletion's write is deleted by the deletion
    job, which scans after it.
  * The activation at the end (`setIndexStateToActiveUnlessDeleting`,
    under the lock) changes nothing when the index is deleting, and the
    status says done only after it.
  * A stopped build's status: progress 100, note "Stopped: the index ...
    was deleted before it was built. ...". `IndexBuilder.start`'s Javadoc
    says so (one sentence; no signature changes).
  * `RwEnvironmentImp.addReadHash` is package access (was private).
* **Tests**: a new tester, `PubTesterIndexJobs` (unit, in `Pack`), with a
  test hook `IndexBuilderImp.testHook` (per builder, for tests only: called
  with "action" at the end of each run of a step's action and with "step"
  after its transaction). Each test deletes the index during its build,
  creates it again on another field, puts an object, and checks that the
  new index gives exactly `[100]`, now and after a restart, and that the
  old build says it stopped:
  * `testBuildDeletedBeforeItsStep`: R3-F2's interleaving, with the
    existing wait event before the first step. Before the fix (the hook
    added, nothing else): `Expected '[100]', got '[200, 100, 100]'`, R3's
    output.
  * `testBuildDeletedInItsStep`: the deletion between the step's read and
    its transaction (hook "action"). Before: `got '[200, 100]'`.
  * `testBuildDeletedBeforeActivation`: the deletion after the last step
    (hook "step"). Before: the note `Done! Processed 1 entries ...` and
    the activation's uncaught `IllegalStateException`.
* **Mutations**: without the read hash, `testBuildDeletedInItsStep` fails
  (`got '[200, 100]'`); with the activation as before,
  `testBuildDeletedBeforeActivation` fails. R3's `BuildDeleteProbe` and
  verify-1's `BuildDeleteReopen` give `[100]` before and after the resume
  and the reopen, no uncaught exception, progress 100.
* **Gates**: `BEFORE COMMIT OK (103 s)`, 20:02:18; `JAVADOC PUB OK`. No
  stream byte and no Pub API signature changes.

2026-11-03, 20:30, by the coordinator (016-05, H5): reviewed by an agent
that did not write it (`/Users/f/fl/bench/016/015-20/handoff/review-findings.md`):
no fault; the new tests fail on the parent and pass on the change; the
mutants are caught. Its nits:
* nit: a build resumed at startup, then deleted, stops, but its startup
  job says "Done, created index ..."; the new sentence of
  `IndexBuilder.start` covers only `start()`'s job.
* nit: the comment at `IndexBuilderImp`'s state check gives the order
  (state, then the key) as the reason; what the argument needs is one
  section under the lock that `getState()` takes. Keep it so when 015-23
  changes `ensureDeletingState`.
Gated with 015-20, 015-22 and 015-21 together on `main` (the gate line in
the commit).
