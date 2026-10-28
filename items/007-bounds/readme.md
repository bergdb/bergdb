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
  reads by phase; the tool, the night's scripts, the outputs and the
  analysis in [05-startup-time/](05-startup-time/). Ran 2026-10-27.
* [06-debt-test.md](06-debt-test.md). 007-06, step 2 of 007-03, the test
  that drives the debt up: updates, deletes, single puts and decreases of
  the startup distance on today's take, on 005-49's paced take and on
  007-07's patch, at 10M keys; two ways of doing D4's option B; the tool,
  scripts and summaries in [06-debt-test/](06-debt-test/).
* [07-step3-paced-take.md](07-step3-paced-take.md). 007-07, step 3 of
  007-03 as a patch for Frans's review: 005-49's paced take with the
  deadline at 2 sd in `TransSeq.take`, its tests, gates and StreamDigest,
  the findings, and what step 3's "Done when" still needs; the patch and
  the probes in [07-step3-paced-take/](07-step3-paced-take/). In the code
  since 2026-10-28, with D4:B, its tests, gates and step 2's runs again
  (section 10).
* [08-step4-take-in-lean.md](08-step4-take-in-lean.md). 007-08, step 4 of
  007-03: BergDB's take with D4:B as a policy of the Lean model, with any
  pace and BergDB's share, and T3 for it (`T3_take` and six more): the
  trusted definitions, the statements in Lean and in words, what is true
  and what is not of the plan's statements, the checks by running, the
  proof, what is not covered, questions for Frans; the probe that runs
  `TransSeq.take` on the generated cases in
  [08-step4-take-in-lean/](08-step4-take-in-lean/).


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

2026-10-26. After the docs/ cleanup (006-07): 007-03 cites the moved
documents by ID (011-11, M10; 001-08, M44; 011-04) and docs/levels.md by
its new section 5, and lists 005-54's Q1, Q3 and Q5 under "After the plan".
007-04 and this log keep their wording, as history.

2026-10-26. docs/levels.md (sections 5 and 7) and README.md give 005-38's
figures at 50 to 1000 MB for the startup section, the write overhead and D,
in place of those at 20 and 5 MB (Frans: "We should use at a startup
distance of at least 50 MB."); section 5 gives 007-03's order, 005-49 first
and the deadline as its backstop.

2026-10-27. Step 5 of 007-03 done: the night ran from 04:00 to 05:27 with
no failures, and 007-05 has the results, by Claude (Opus 5.5, Claude
Code). Warm on F53: 7.4 s at 50 MB (a section of 2.15 sd), 12.4 s at 200
MB and 70 s at 1000 MB with 10M keys and 8-byte values; 26 and 86 s at
200 and 1000 MB with 50M keys; 9.1 s with 100-byte values and 1.9 s with
10 kB values at 200 MB. Cold on s1, 10M keys: 214 and 209 s at 50 and 200
MB, 86 to 94 percent of it in 1.1 to 1.7 million random reads, 73 to 78
percent of those rule 4's. So 10 s warm holds up to a startup distance of
about 75 MB at 10M keys with small values, and a cold start needs step 6
for both rule 4's reads and the rerun's first touches. 007-03 updated.

2026-10-27. Step 6 of 007-03 investigated in 005-57, at Frans's request
("Add this as a todo item to 005. Investigate this in detail ... but don't
implement the change in the java/ yet."), by Claude (Opus 5.5, Claude
Code). Rule 4 needs no reads: by the reconciliation's argument (a node that
stays dirty is written at least once every startup section), a pointer of
D that names a node with a canonical object names a vpos, a position in the
section's `posToId`, or that object's own position. The writer's
`resolvePointers` reads the same kind of header and needs none either, with
a map of the pinned objects by position. Prototypes of both, checked
against today's code by id in before-commit, level2.sh and level4.sh (full)
and on 007-05's two databases, with no difference. Cold on s1, 10M keys:
214 and 210 s at 50 and 200 MB today, about 46 and 51 s with the change;
warm on F53, 0.7 to 0.9 s less. java/ not changed; the change waits for Frans.
007-03's status and step 6 updated.

2026-10-27. Step 6 of 007-03 done (005-57), at Frans's word ("1. Part 1
alone. ... Go ahead. Implement and commit this."), by Claude (Opus 5.5,
Claude Code): rule 4 finds a pointer's node by its position, with no read
of the stream but for a top node's pointer that the maps do not resolve,
and with assertions on it also runs by node id and fails on a difference.
The writer's reads (part 2) and the rerun's loads (option A) are not done;
the Lean theorem for the argument is 005-58. 007-03 updated.

2026-10-27. 007-07, step 3 as a patch, by Claude (Opus 5.5, Claude Code,
at max effort) at Frans's choice (006-09: "007-03 step 3 as a patch"):
005-49's paced take with the deadline at 2 sd, gated in a scratch clone
(before-commit, level2 steps 1 to 5 and 7, level3 full, level4 quick; all
36 StreamDigest streams change, as expected); not in `java/`, for Frans to
decide. Its review found a bias in the prototype's hash (replaced by the
SplitMix64 finalizer). level2's step 6 (BryanRepro) fails on main itself
since 005-46, found on the way.

2026-10-27. 007-06, step 2 of 007-03, by Claude (Opus 5.5, Claude Code) at
Frans's choice (006-09: "007-03 step 2: debt test"): 50 runs at 10M keys.
On today's take 007-01's hypothesis holds (the largest section matches the
largest debt within 0.09 sd); single puts give the worst bursts (1.6 MB of
index nodes for one put). The paced take holds the section at 1.14 sd at
most, also on deletes and single puts, and so does 007-07's patch. For
D4's option B: the pace should use a new startup distance at once, and the
deadline come down with the lag ("pace"); a deadline that jumps to the new
2 sd writes records of 86 to 490 MB. Left: 50M keys, a longer delete run,
D4:B on 007-07's patch.

2026-10-28. Step 3 of 007-03 done, at Frans's decision (006-09, section 8,
decision 1: "apply the step 3 patch, and add D4:B the way 007-06 measured
it as "pace""), by Claude (Opus 5.5, Claude Code); 007-07, section 10.
007-07's patch and D4:B: a new startup distance applies at once to the
pace, and while the section's transactions span more than twice the
setting, the deadline is at that span, which a start rebuilds and which
shrinks with every commit. before-commit.sh, level2.sh, level3.sh and
level4.sh, full, pass; every StreamDigest stream changes against main, as
expected, and none against the patch alone. 007-06's step-2 runs again on
it: the steady runs are the patch's, byte for byte; one call from 1000 to
100 MB or from 200 to 50 MB writes no record over 5.4 MB (the patch: 87 to
486 MB), and the section comes below the new 2 sd after 0.08 to 0.67M
puts, shrinking with every record. Left: the quick performance suite, in
a quiet block (007-07's night step); whether `setStartupDistance`'s 200 kB
value should earn a share (007-06, point 4); step 4.

2026-10-28. Step 4 of 007-03 done, at Frans's go (006-10, question 3), by
Claude (Opus 5.5, Claude Code); 007-08. `TransSeq.take` with D4:B is
`takePolicy` in `lean/SIS/Bound.lean`, with any pace, and with BergDB's
share (`javaTake`), which gives Java's startup pos on 300 generated cases.
Proved for every pace and every cost of a record, with nothing else
assumed: the section without its last record costs less after a
transaction than the larger of twice the setting and what it cost before
(`T3_take_step`), so less than d_h with a constant setting, with and
without restarts (`T3_take`), and after a decrease it never grows and
loses at least one unit with every transaction until it is below the new
d_h (`T3_take_decrease`); what startup reruns and reads (`T3_take_rerun`,
`T3_take_reads`). The
plan's "keeps up with d_h" is false with D4:B, and below the new d_h right
after a decrease is false, as intended; the counterexamples are `#guard`s.
`lake build` with no warnings and no `sorry`, the axioms Lean's standard
ones, the trace tests pass.
