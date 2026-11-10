023-cleanup
===========

Created 2026-11-10 by Frans Lundberg. Status: open.

Resource cleanup in BergDB's Core: what the database keeps after nothing
needs it any more, and how it is released. It starts from the slow scans
over deleted entries found for release 2026.4 (020-30), and looks at
cleanup in general, since the Core's internals affect each other.

Frans, 2026-11-10, 09:37: "We want to solve the performance issue found.
At the same time, we want to have a look at resource cleanup in general.
[...] I want a wider framing of the question. We are dealing with the
core internals of the database. Things affect each other here. So, we
need a wider picture. So, I go slow."

Release 2026.4 is paused until this is sorted out (Frans, 09:03; 020,
log of 2026-11-10).


Files
=====

* [01-introduction.md](01-introduction.md). 023-01, an introduction for
  an AI to get up to date: what triggered the work, a glossary, and how
  the Core works today (keys and the stream, the index and its splits,
  gets and scans, the Pub API's use of it, memory and handles, startup,
  reclaim), where a deleted key's remains are, the 2012 intent never
  built, and where the docs and the code differ. No solution.
* [02-problem.md](02-problem.md). 023-02, the problem stated exactly and
  what we want from a solution: requirements R1 to R27 (Frans's rule made
  exact, R2 to R5; the bounds, R9 to R15; the constraints, R16 to R27,
  with his words of 09:55), how they are checked (the tests in 023-03),
  non-goals, and questions F1 to F12 for Frans. No solution.
* [03-test-spec.md](03-test-spec.md). 023-03, the test specification:
  T1, Frans's hello-world test (an emptied database against its twin
  that never held the deleted keys, after the same drive), T2 its shapes,
  T3 the scan bound at every time, T4 a steady-state queue, T5 the
  workloads of 020-24 and 021-25, T6 to T12 correctness, restarts,
  determinism, regression and performance; measures M1 to M14 and their
  allowances; today's numbers from a prototype (`java/stress/CleanupRule.java`,
  in [03-test-spec/](03-test-spec/)): `main` fails the rule at every size.
* [04-options.md](04-options.md). 023-04, the options, the first phase
  of the solution: building blocks (UP, the unlink at the delete; LE-a to
  LE-d for the leftmost child, LE-b "the empty key first" new; RC, root
  collapse; MG, merges; RB, reclaim rebuilds; MT, `maintain()`; and
  smaller ones), the options B, A, A+RC, C and D judged against R1 to R27
  and 023-03's tests, decisions X1 to X11, questions Y1 to Y10;
  recommended: A+RC with LE-b in format 6 for 2026.4, then C (RB) for
  strict. Probes in `/Users/f/fl/bench/2026-11-10/o23/probe`.
* [04-options/codex-options.md](04-options/codex-options.md). An
  independent options study by Codex (gpt-6.1-sol, effort max), from
  023-01 and 023-02 before Frans's answers, without 020-30's options or
  023-04: options A (copy the path on each delete; its stopped prototype,
  on branch `020-30-codex-proto` in `/Users/f/fl/bench/2026-11-10/codex30/clone`),
  B (small versioned edits with a recorded sweep; recommended), C (prune
  history keeping node ids) and D (rebuild in steps), with measurements.
* 05-prototypes/. 023-05, three prototypes in parallel, each on a branch
  in a clone of its own, measured with 023-03's tests (Frans, 10:51: "I am
  really eager to see one or multiple options coded"): P1, the upward
  unlink at the delete with the leftmost child relabelled
  (`p1-relabel.md`); P2, the same with a relaxed invariant, the leftmost
  klong covering every key below it (`p2-relax.md`); P3, reclaim
  compacts what it rewrites, towards the strict allowance, with an
  explicit `maintain()` (`p3-compact.md`); and, from 11:53 (Frans, 11:52,
  on 023-04's LE-b: "a good idea to explore further"), P4, the empty key
  first, on P1's branch instead of the relabel (`p4-empty-key.md`); and,
  from 12:23 (Frans, 12:22, on 023-06's recommendation), P5, merges at the
  delete on P4's branch (`p5-merge.md`); and, from 12:37 (Frans, 12:35,
  Y6), P6, the release of memory held by ended versions, on P4's branch
  (`p6-memory.md`); and, from 13:43 (Frans, 13:42, 023-06's Z13 and Z14),
  P7, the window of dirty top nodes fixed (`p7-topnodes.md`), and P8, each
  reclaim step scans at its own time (`p8-steptime.md`), both on P4's
  branch. P1 to P8 done.
* [06-architecture-review.md](06-architecture-review.md). 023-06, an
  architect's review of the overall solution, by an agent on a stronger
  model at effort max (Frans, 11:57 to 11:59), first pass: A+RC with LE-b
  and X5 (a) for 2026.4, as 023-04; strict by merges at the delete (MG,
  Frans's 2012 plan) rather than reclaim's rebuild (RB); LE-b sound
  everywhere checked; what the studies missed; the biggest risks;
  questions Z1 to Z11. A second pass when the prototypes of 023-05 report.
* 07-proposal.md. 023-07, the proposal for 2026.4, written down for
  independent reviews (Frans, 14:26 to 14:36: "Principle KISS? [...] write
  this down in 023-07. Then we can make multiple independent reviews with
  multiple AIs"): a KISS core (P4's unlink, P8's scan at the step's time,
  P6's dead hand, 021-28's end key, format 6) against the full set (with
  merges, the top-node window's fixes, the replaced queue, `maintain()`),
  every rule stated exactly; nine questions for the reviewers; decisions
  D1 (the tier, no recommendation) to D13.
* 08-reviews/. 023-08, three independent reviews of 023-07 (a.md, b.md,
  c.md, each with its evidence), checks of their findings (checks/), and
  the verdict merged from them (08-reviews.md): the delete design stands,
  P8 does not; a smaller core, frozen; questions 1 to 9. A: reject the
  core as written; B and C: accept the core with changes. All three: P8's
  step can stop the cuts (confirmed on P8, P4 and `main` in
  checks/p8-liveness.md, with a fix); C: fault 12, the take-back can leave
  a pointer to a node never written (confirmed in checks/take-back.md,
  also with sorted keys, with a fix).
* 09-integration.md. 023-09, the integration branch `023-core` of
  023-08's core with Frans's sort (Q4): twelve commits, the gates run,
  the expected values changed, what remains.

Earlier work, in 020: 020-30, the first study (sections 1 to 4), with
four helper studies 020-30-01 to 020-30-04, and an independent study by
Codex running on 2026-11-10 (006-21, W2).


Log
===

2026-11-10. Created the item (Frans, 09:45); 023-01 and 023-02 started
by the coordinator's agents. 023-03 started at Frans's request (09:58),
after his practical test of the rule (09:55). 023-01 and 023-02 done;
023-04, the first phase of the solution, started (Frans, 10:12).

2026-11-10. 023-03 done. Frans answered 023-02's F9 and F10 (10:30): a
change of the record format is acceptable in 2026.4, and 2026.4 refuses
the databases of earlier releases ("No need for compatibility, we can
ignore released before 2026.4").

2026-11-10. Frans answered 023-02's F5 and 023-03's Q2 (10:38): the
bounded allowance is enough; the strict one (back to the hello-world
database's resources) is wanted if a good solution is found, and may be
reached eventually, after one or several reclaims.

2026-11-10. Frans answered 023-02's F2 (10:41): the rule covers every
version that has ended, not only deleted KVs ("Yes, it should cover every
version that has ended.").

2026-11-10. Frans answered 023-02's F3 (10:44): the scan bound holds at
every available lookup time ("At every available time; this is what we
want."). F1 follows from his answers to F2 and F5: a dead klong in a node
that still holds live keys goes too, eventually.

2026-11-10. Frans answered 023-02's F7 (10:49): the user's writes drive
the cleanup, and an explicit `maintain()` is good too, to be added if a
solution needs it for its tests: called again and again, it must
eventually bring a database with only the hello-world entry to about the
resources of a fresh hello-world database. 023-03's T1 notes it as a
second drive.

2026-11-10. Frans answered 023-04's Y2 (root collapse at the delete, in
2026.4: yes), Y7 (021-28's end key into 2026.4; 021-25's fix (a)
optional), Y8 (one record format 6 for 2026.4, 2026.3's databases refused
with a message naming it) and Y10 (`maintain()`, yes; the cleanup goes on
in the ordinary operations, and calling `maintain()` is optional, never
required of the user), 12:31.

2026-11-10. Frans answered 023-04's Y6 (12:35): "Option (b), we follow the
rule for resource release, also for memory." The memory of ended versions
is released too, eventually, in the ordinary operations, not only under
the cache's pressure or at a restart.

2026-11-10. Frans answered 023-06's Z12 (merges in 2026.4's format 6 if
P5's gates and points close within days: as recommended), Z13 (the dirty
top-node window: "solve this now", in 2026.4) and Z14 (each reclaim step
scans at its own time, after a probe: yes), 13:42. P7 (the top-node
window) and P8 (the scan at the step's time) started on P4's branch.

2026-11-10. Frans answered 023-06's Z15 (13:57 to 13:59): P6's dead hand on
by default; the replaced queue on by default only if P8 removes
reclaim's reloads and a measure of reads at earlier times shows the cost
small, else kept but off by default; `noEvict()` unchanged (a Core option
for tests and benchmarks), its Javadoc saying that under it the memory of
ended versions is released only at a restart.

2026-11-10. Frans paused to review (14:26 to 14:36): the proposal has
grown; KISS. 023-07 written down for three independent reviews (Codex,
and two agents on other models). The long-run answer to Z21 (P7, 14:29):
without (b') the left-out nodes leave D within 10,000 transactions, so
(b') is an efficiency, not needed for the rule.

2026-11-10. 023-07 written (14:48). Its findings beyond the reports: the
core needs P5's retarget in the take-back and `dirtyNodeBound` counted
by node (P4's count refuses transactions of more than about 150,000
deletes); P8 alone removes the dirty top-node window's trigger in T1;
only merges carry a format cost if put off. Three independent reviews
started (023-08): A by Codex (gpt-6.1-sol, effort max), B by Fable 5.2 at
max, C by Opus 5.5 at max, each in its own clone, none reading the
others.

2026-11-10. P7 done (14:49): fix (a) closes the dirty top-node window
at every N measured (T1 at 1M: max D 35/34 against 94/178 before; objects
after a restart 25/33 against 83/184; drive bytes -27%); level1, level2
and level3 full OK, level4 quick OK (one expected C-S difference: the
model has no pull); 3 tests need new expected values. Rule (b) unsound,
proved by a unit test; (b') built behind a switch, an efficiency only.
Not done: level4 full, the Lean model and checker changes.

2026-11-10. The three reviews of 023-07 are in (B 15:36, C 15:47, A
16:06). Each found, on its own, that P8's step at its own time can stop
reclaim's cuts: a step counts every KV it scans against its 16 kB, also
keys put ahead of the scan, so a growing random workload or a queue with
a key after it outruns the scan. A check (checks/p8-liveness.md) confirmed
it on P8 and found `main` and P4 as today's rule expects; its fix (a step
counts only KVs stored before pStart) ends every probe. C found fault 12
(the take-back) and reproduced it; a check runs.

2026-11-10. Fault 12 confirmed (checks/take-back.md, 16:15): on P5's head
and on P4 with only the retarget; not on `main`. Sorted keys reach it too
(UnlinkFuzz with larger transactions, replayed through the plain Core
API): the database cannot be opened again. The fix repoints the segment
leaf's klong in place in `Dag.spaceSplitInPlace` (as `TopDs.newSuperRoot`
does); every probe and fuzz run passes with it, and before-commit. X5 (c)
is reachable (a key transformation can put and delete one key in one
transaction); only its inner branch is unreachable.

2026-11-10. Frans (16:14): "I worry about stability. Today, it seems like
each fix led to yet another fix and so on. I smell expanding complexity
where I [want] simple beauty." 023-08 merged the reviews: a smaller core
than 023-07's (P8 out, fault 12's fix in, no new mechanism), frozen, with
a stop rule; questions 1 to 8 for Frans.

2026-11-10. Frans answered 023-08's questions (16:34): Q1 to Q8 as
recommended, except Q4: sort a transaction's keys after their
transformation, in 2026.4 ("It defines equality of transactions in a
sense i like."). The design is frozen at 023-08, section 5. Q9 (005-04's
trace check) open. Next: the integration branch.

2026-11-10. 023-09: the integration branch `023-core` (head 2c67f887,
16:36 to 17:18): twelve commits, no new design; before-commit and level1
OK; UnlinkFuzz in the new modes 0 failures in 20,000 seeds; T1 at
100,000 passes; at 1M (drive 12,000) C9 over by 6, the top-node window;
at 1,000 three rows over by 1 to 7, a phase that fault 12's fix shifts.
One commit of expected values (two SE tests). level2 to level4 full next.

2026-11-10. Frans back at 17:35. Q9 as recommended (17:49). KVs that key
transformations make one key: one operation a key, by the builder's rule
of 015-40, silently; "the last operation wins" for the builder too is a
later item, for 2026.5 (17:41 to 17:48; 023-08, section 7). Being added
to 023-core.
