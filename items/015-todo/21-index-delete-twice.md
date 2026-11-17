015-21. Fix: a second delete job lets the first delete a replacement index
==========================================================================

Status: done. Kind: Fix. Created 2026-11-03 by
Frans Lundberg.

For 2026.2 if it fits; else a known issue (in 2026.1 too).

What: `deleteIndex` twice, then an index of the same name created while the first job still runs: the old job deletes the new index and its entries, also after a restart. A loss of derived data, through the Pub API.

Source: review R3, R3-F1 (016-06/R3, items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R3-F1), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R3-F1, made a test.


State
-----

2026-11-03, 20:30: done; reviewed (no fault) and committed after the
combined gate. Earlier:

2026-11-03, 20:09: the fix, its tests and the gate done in the clone
`/Users/f/fl/bench/016/015-20/repo`, on top of 015-20's and 015-22's
commits; handed off for review (`/Users/f/fl/bench/016/015-21/handoff/`).
Open: the review, the combined gate, the commit in `main`.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 20:03 to 20:09, in `/Users/f/fl/bench/016/015-20/repo` (from
`main` at `66a80f3`, after 015-20's and 015-22's commits): the fix.

* **The cause** (as R3-F1 and verify-1 say): `deleteIndexInternal`
  started a new deletion job on every call, also for an index that was
  deleting already, and a job deletes by the index's name (its entries,
  its info, `nameToIndex`). So a job that ran late, after another had
  finished and the name had been taken by a new index, deleted the new
  index.
* **The fix**: a deletion job belongs to its own `Index` object, and an
  index has at most one job that runs. `deleteIndexInternal` makes the
  job's thread and `Job` as before but does not start them;
  `IndexManager.startDeletionJob`, under the manager's lock, returns the
  index's job if it runs, or if the index is no longer the one of its
  name (deleted already: then its job is the one that deleted it);
  otherwise it records the new job in the `Index` (`deletionJob`) and
  starts its thread. A job removes the index from `nameToIndex` as its
  last step, under the same lock, and only then can `addIndex` take the
  name; after that no job of the old index starts, so none runs while a
  new index has the name. A job that died early (an unexpected
  exception) leaves the index in `nameToIndex`; a later `deleteIndex`
  starts a new one, as before. `deleteIndexInfo` asserts that the index
  is still the one of its name. `Database.deleteIndex`'s Javadoc: "If a
  job that deletes the index runs already, returns that job." No
  signature changes. A thread made and not started is left to the
  garbage collector.
* **Tests** (`PubTesterIndexJobs`, unit), with a test hook
  `DatabaseImp.testHookDelete` (per database, for tests only: "call" in
  `deleteIndexInternal` once the index is deleting, before its job is
  started or found; "start" when a job starts, in its thread):
  * `testDeleteTwice`: R3-F1's interleaving. The first job waits at its
    start; a second `deleteIndex`; if it is another job, it finishes
    first, and the index is made again (field `other`) and gets its entry
    before the first job goes on; else the index is made when the
    deletion has finished. The new index must give `[100]`, also after a
    restart.
  * `testDeleteAgainAsTheFirstEnds`: the second call finds the index
    deleting; at its "call" the first job (held at its start) finishes,
    and the index is made again with its entry; the second call must not
    start a job for the deleted index.
  * On main's logic with the hooks only, both fail: `The new index was
    deleted: No index named: 'by-field' at the given lookup time.`
* **Mutations**: a job for each call (the running job not returned):
  `testDeleteTwice` fails, `Expected '[100]', got '[]'` (the stale job
  deleted the entry; the assert in `deleteIndexInfo` stopped it before
  the info). Without the "deleted already" test:
  `testDeleteAgainAsTheFirstEnds` fails (the assert `Index by-field
  deleted, by no job.`; without `-ea` the stale job would start).
* R3's `DuplicateDeleteProbe` now stops at its own precondition, "second
  job did not finish": the second call returns the first job, which the
  probe holds. That is the fix's behaviour, not a fault.
* **Gates**: `BEFORE COMMIT OK (103 s)`, 20:09:29; `JAVADOC PUB OK`. No stream byte and no Pub API
  signature changes.

2026-11-03, 20:30, by the coordinator (016-05, H5): reviewed by an agent
that did not write it (`/Users/f/fl/bench/016/015-20/handoff/review-findings.md`):
no fault; the new tests fail on the parent and pass on the change; the
mutants are caught. Its nits:
* nit, fixed by the coordinator: `Index`'s class Javadoc said "Immutable
  index class."; it now says that the state and the deletion job change,
  under `IndexManager`'s lock.
Gated with 015-20, 015-22 and 015-21 together on `main` (the gate line in
the commit).
