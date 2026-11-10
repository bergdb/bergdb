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
* 02-problem.md. 023-02, the problem stated exactly, and what we want
  from a solution, with Frans's rule that a deleted KV eventually
  consumes no resources of the database. Being written.
* 03-test-spec.md. 023-03, the test specification: Frans's practical
  test of the rule (a hello-world database against one that adds a large
  amount of data and deletes it all but "/a.txt"; eventually its
  resources come back to about the hello-world database's), a
  steady-state churn twin, correctness and regression; with today's
  numbers from a prototype. Being written.

Earlier work, in 020: 020-30, the first study (sections 1 to 4), with
four helper studies 020-30-01 to 020-30-04, and an independent study by
Codex running on 2026-11-10 (006-21, W2).


Log
===

2026-11-10. Created the item (Frans, 09:45); 023-01 and 023-02 started
by the coordinator's agents. 023-03 started at Frans's request (09:58),
after his practical test of the rule (09:55).
