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
  itself, proved for its own policy, in six steps (005-31, a test that
  drives the debt up, the deadline in `TransSeq.take`, BergDB's take in
  Lean, startup time, and, proposed 2026-10-26, fewer random reads at
  startup); updated from 007-04.
* [04-review-after-009.md](04-review-after-009.md). 007-04, a review of
  007 after item 009 (handles) and the work of 2026-10-26 (005-38, 005-49,
  006-06): what is unchanged, what changed, and what it does to the plan.
* [05-startup-time.md](05-startup-time.md). 007-05, step 5 of 007-03:
  startup time against the section, warm on F53 and cold on s1, with the
  reads by phase; the tool and the night's scripts in
  [05-startup-time/](05-startup-time/), scheduled for 2026-10-27, 04:00.


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

2026-10-24. Step 1 of 007-03 done: 005-31, option A, by Claude (Opus 5.5,
Claude Code), at Frans's request ("fix all todo items of type Fix"). A
transaction whose index nodes, by a bound at the largest node size, could
take more than 15/16 of the record limit is refused before its go point.
See 005-31's outcome, and the note at step 1 for step 3.

2026-10-25. 007-03, step 3: the change removes the TODO in
`TransSeq.take` that D1 came from, and the comment's claim that the
startup pos should never fall far behind (006-05, T7).

2026-10-25. Steps 2 to 5 of 007-03 after release 2026.1 (item 008), Frans:
"After the release". README.md and docs/levels.md ("Bounds, measured") say
that the startup section is not yet bounded for BergDB's own take.

2026-10-26. 007-04, a review of 007 after item 009 and the day's work, by
Claude (Opus 5.5, Claude Code), at Frans's request ("Go through bergdb item
007-bounds and check how this is still relevant or not after the 009 work
and other recent work. Update the plan if needed. Don't start any
implementation."); 007-03 updated from it, and a note added to 007-01, 5.3.
Still relevant: 009 changed nothing that 007 is about, and 005-38 measured
the take going past 2 × sd at 50 and 200 MB. Changed: step 2 is smaller;
steps 3 and 4 wait for 005-49 (smooth index writes, registered the same
day), and the deadline becomes the backstop of the take it recommends; step
5 can go first, and counts a cold startup's random reads, which take
minutes on s1 by rule 4's header reads (004-02, 10.5.8; unchanged with
handles); step 6, for those reads, is proposed; D4 and D5 are new decisions
for Frans. Nothing started.

2026-10-26. Frans: "D4:B. D5: as recommended. Schedule Step 5 tonight at
04:00; I assume night.sh is done by then; report to news.md." D4 (a
decrease of the startup distance in steps) and D5 (step 6 in this plan)
recorded in 007-03. Step 5 prepared as 007-05 by Claude (Opus 5.5, Claude
Code): StartupBench, the scripts for F53 and s1, checked on small databases
on both; scheduled for 2026-10-27, 04:00, reporting to news.md.
