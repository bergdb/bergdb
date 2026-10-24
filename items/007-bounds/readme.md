007-bounds
==========

Created 2026-10-23 by Frans Lundberg. Status: open.

Bounds on BergDB's costs, the planned theorems T3 and T4 of
[docs/sis-model.md](../../docs/sis-model.md), section 10. First, bounded
startup: that startup takes a bounded time, whatever the size of the
database and however long it has run (Frans's top priority, 2026-10-23).


Files
=====

* [01-startup-bound.md](01-startup-bound.md). 007-01, bounded startup: the
  claim, what startup costs, T3 (proved in Lean), Java's take and the debt
  of D, what else a bound needs (T4), decisions and next steps.
* [02-take-blocked.md](02-take-blocked.md). 007-02, a finding: a
  transaction whose got-dirty nodes do not fit in one record stops the
  startup pos for good. The probe and its output are in
  [02-take-blocked/](02-take-blocked/). Registered as
  [005-31](../005-todo/31-fix-take-blocked.md).
* [03-plan.md](03-plan.md). 007-03, the plan: bounded startup for BergDB
  itself, proved for its own policy, in five steps (005-31, a test that
  drives the debt up, the deadline in `TransSeq.take`, BergDB's take in
  Lean, startup time).


Log
===

2026-10-23. Created the item, at Frans's request ("Let's get starting on
modelling the bounds"), with 007-01 and 007-02 written by Claude (Opus 5.5,
Claude Code). T3 is in Lean (`lean/SIS/Bound.lean`, `BoundTheorems.lean`,
`Proof/Bound.lean`, `BoundExample.lean`): with any cost of a record and a
startup pos policy that keeps up with a startup distance d, the startup
section without its last record costs less than d after every run, also
with restarts. BergDB's take does not keep up (4.1 of 007-01); 007-02 is a
case where it never catches up.

2026-10-23. 007-02 registered as 005-31, at Frans's request.

2026-10-24. 007-03, the plan, written by Claude (Opus 5.5, Claude Code) at
Frans's request ("Do: write this plan into item 007."), from the proposal
of 2026-10-23. Frans's go for 005-31's option A, its step 1, but not to
start yet; the deadline (007-01, D1) waits for Frans. Nothing started.

2026-10-24. D1 decided by Frans ("As you propose."): the deadline in
`TransSeq.take` at d_h = 2 × sd (007-03, step 3). Not started.
