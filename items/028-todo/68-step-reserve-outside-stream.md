028-68. Decide: the reclaim step reserve, a setting outside the stream that changes its bytes
============================================================================================

Status: decided, built in 031-06's landing; closed when it lands on `main`.
Kind: Decide. Frans: decided.
Created 2026-11-27 by Frans Lundberg.

What: the reclaim step reserve decides where a reclaim step splits
(`Reclaim.step`: `maxNodes = Math.max(1, stepReserve / stepNodeBytes())`)
and is not kept in the stream. A start takes it from the builder
(`DbBuilder.reclaimStepReserve`, whose default is
`Reclaim.DEFAULT_STEP_RESERVE`, 4 MiB, or the system property
`stepreserve`; `Reclaim.setStepReserve`). It is a setting for tests
(015-87, F7): at the default no step is split in the stress workloads
(005-78, probe P4); below the default steps split, and the stream's
bytes change. The Javadoc of both methods says so.

Why: Frans, 2026-11-27: no setting outside the stream is to affect the
stream's bytes (P2 extended to every write, 031-05; the wording drafted
on 2026-11-27 for 031-06). Two starts of one stream with two reserves
write different bytes after the same user actions; the review of 031-05
named the reserve among the inputs that P2's draft left out (031-05,
section 12, F11). The other such setting in the code of 2026-11-27 is
the internal crypto key, removed by 028-69.

Frans: decision, between:

* **A. A value of the creation, stored in the stream.** The reserve is
  given when the database is created and stored in the stream as the
  node size is (005-50: in the meta block, from the creation); a start
  reads it from there. A builder that gives another value at a later
  start is refused, or its value ignored (to choose with A). No new
  action; the tests still choose a reserve, when they create their
  database. A change of the stream format.
* **B. A constant.** The reserve is `DEFAULT_STEP_RESERVE` for every
  database, with a hook for tests only, outside the builder. The tests
  that split steps by a small reserve then need another way to split
  them, or keep the hook and stay outside the principle, as tests.
* **C. A setting stored by a record of its own**, as the startup
  distance is (`setStartupDistance`): a new user action, and the
  reserve may change while the database lives.

Recommendation (the lead, 2026-11-27): A: no new action, and the tests
keep their choice.

When: decided in step 2 of 031-06's landing (031-06, section 9), with
the record's room: design (e) reworks the step's sizing (the step's
allowance of its own in the record), which may take over the reserve's
role or change what it bounds.

Done when: Frans's choice is built, and `RestartInvariance` passes with
a start that gives another reserve than the creation's;
`java/before-commit.sh` printing `BEFORE COMMIT OK`; the Javadoc of
`DbBuilder.reclaimStepReserve` and `Reclaim.setStepReserve`, and with A
027-03, updated.

Decision
--------

Frans, 2026-11-27, 16:09: **B**, a constant. The reclaim step reserve is
`Reclaim.DEFAULT_STEP_RESERVE` (4 MiB) for every database, with a hook
for tests only, outside the builder's public settings. The lead had
recommended B by then; the recommendation above (A) is of the
registration.

Built in 031-06's landing, step 2 (branch `031-06-landing`, 2026-11-27):

* `DbBuilder.reclaimStepReserve` and its default, the system property
  `stepreserve`, are gone. The test hook is `DbBuilder.testStepReserve`,
  package-private as `maxNodeSize8()`: for the tests and probes in
  `bergdb.core` that split steps by a small reserve. Its Javadoc says
  that such a test gives the same value at every start of its database,
  as the reserve is not kept in the stream. `Reclaim.setStepReserve` is
  package-private; Db calls it at a start with the builder's value, the
  constant but in such a test.
* Who set it: `Reclaim.Tester.testStepReserveSplitsSteps` (now through
  the hook, at its start and its restart) and `DbTesterJavadoc`'s refusal
  of a reserve below 1 (removed with the method). No script of `java/`
  passed `-Dstepreserve`. The item probes of 031-06 that vary the reserve
  (`SafetyProbe`, the review's `RvP1`) take the hook when they are run
  again.
* `Reclaim.Tester.testStepReserveIsAConstant`: `DbBuilder` has no public
  method that names a reserve, `Reclaim` no public setter of one, and a
  start with the system property `stepreserve` set has the constant.
* The Javadoc of `DEFAULT_STEP_RESERVE`, `setStepReserve` and the hook
  say that the reserve is a constant. With B, `RestartInvariance` with a
  start that gives another reserve (the done-when of A) does not apply;
  StreamDigest and RestartInvariance run in `level2.sh` and `level3.sh`.
* The review's F7 is answered: no setting outside the stream changes its
  bytes through the reserve.

First step: find what sets the reserve below the default (the tests
that call `reclaimStepReserve`, and what passes `-Dstepreserve`; no
script of `java/` or `java/stress/` names the property on 2026-11-27),
and read in 031-06's prototype whether the step's allowance replaces
the reserve's role.


Log
---

2026-11-27. Registered by lead-1127, from Frans's rule of the day for
P2's wording; found while the wording was drafted.

2026-11-27. The independent review of 031-06's prototype (031-06,
`review-fable.md`, F7) ran it: the reserve splits steps at its default
too. In the review's case for P1 (60,000 cold keys of 1,000 bytes, then
600,000 new keys put ahead of a running iteration's scan), the default
of 4 MiB split 16 steps and 1 MiB split 65, and the same actions gave
streams of 328,668,424 and 265,554,968 bytes. So "at the default no step
is split" above holds for the stress workloads only. The reviewer's
proposal is B, a constant. Decided in the landing's step 2.

2026-11-27. Decided by Frans (16:09): B, a constant. Built in 031-06's
landing, step 2, on the branch `031-06-landing` (Decision above).
