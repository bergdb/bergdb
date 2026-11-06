019-38. Fix: index jobs fail the database on an interrupt, an expired read or a refusal
=======================================================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: 019-10's change (01b0493) gave the index build's thread
(`IndexBuilderImp`, about line 337) and the index deletion's thread
(`DatabaseImp`, about line 313) a `catch (Throwable)` that fails the
database on everything but `StreamIoException`, `DbStoppingException` and
`DbFailedException`. That includes what is not a failure: the
`DbException` of an interrupt while a step waits to rerun after a conflict
(`RwTransaction`, about line 150), a `LookupTimeNotAvailableException` of
the step's `getMany` when a cut overtakes it, and a refusal of the step's
transaction. Before 019-10 each ended the thread silently and the index
work stopped until a restart (also wrong).

Why: review R6 of 006-13 (`/Users/f/fl/bench/006-13/review-r6.md`, B1),
shown by a probe (an interrupt during a build's rerun: the next put throws
`DbFailedException`). docs/levels.md, section 3: everything but a failure
fails only that call and the database goes on, and an interrupt never
fails the database (005-46). A regression of today's change.

Frans: none. The rule of docs/levels.md, section 3 decides it.

Done when: in both threads, an `Error` or an unexpected
`RuntimeException` (a bug) fails the database; a refusal or an expiry
waits as after a conflict and takes the step again; an interrupt goes on
with the flag set (as `sleepFiftyPercentOfDuration` does); a test in
`PubTesterIndexJobs` with R6's probe's shape (and an expiry by a hook)
fails before the fix and passes after; one sentence in levels.md, section
3 (an index job's refusal or expiry is retried, not a failure);
`BEFORE COMMIT OK`.

First step: R6's B1 and its probe (`R6Probe`, in R6's clone
`/Users/f/fl/bench/006-13/r6`).


Log
---

2026-11-06. Registered by coord-1106 from review R6.
