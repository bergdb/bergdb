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
* 04-options.md. 023-04, the options, the first phase of the solution:
  the building blocks, the options as combinations judged against 023-02's
  requirements, the open design decisions, the format and compatibility,
  and what phase 2 should do; phase 1's conclusions (020-30, section 4)
  carried into 023. Being written.

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
