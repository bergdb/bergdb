006-2026-q4
===========

Created 2026-10-19 by Frans Lundberg. Status: open.

Small pieces of work on BergDB from October to December 2026, one subitem
each: summaries, short investigations, notes, reviews. Larger work gets an
item of its own (see [readme.md](../readme.md), "Small work"). The item is
done when the quarter ends.


The list
========

| ID | Date | What |
|---|---|---|
| [006-01](01-work-12-19-october.md) | 2026-10-19 | Summary of the work on BergDB from 12 to 19 October 2026, up to item 005 |
| [006-02](02-props-2017-vs-2026.md) | 2026-10-19 | Props, the 2013 to 2017 performance suite, on the 2017 and the 2026 code on F53, against cissi's numbers of 2015 and 2017 |
| [006-03](03-fast-unit-tests.md) | 2026-10-20 | Fast unit tests (41.5 s to 10 s), the full versions as f-tests; `java/before-commit.sh`, the only commit gate |
| [006-04](04-lean-guided-reading.md) | 2026-10-22 | Guided reading of the Lean model's definitions and theorem statements against sis-model.md, by Frans with Claude: the plan and the log |
| [006-05](05-todo-markers.md) | 2026-10-25 | The TODO markers in `java/`: the 15, what was found and done with each, and the 3.0e6 that "result in problems" in 2015 |


Files
=====

* [01-work-12-19-october.md](01-work-12-19-october.md). 006-01, the summary: the
  work phase by phase, the bugs found, the evidence, and what is open.
* [02-props-2017-vs-2026.md](02-props-2017-vs-2026.md). 006-02, the report:
  Props (MEM, CORE, SS) on four versions of the code on F53, the change from
  2017 to 2026, F53 against cissi, and the node table's tree bins. The plan,
  the scripts, the probe, an experimental patch and the output of every run
  are in [02-props-2017-vs-2026/](02-props-2017-vs-2026/).
* [03-fast-unit-tests.md](03-fast-unit-tests.md). 006-03, why the unit tests
  were slow, what changed, the times before and after, and the check before a
  commit.
* [04-lean-guided-reading.md](04-lean-guided-reading.md). 006-04, the plan:
  five sessions, each a part of sis-model.md against a file of `lean/SIS/`,
  what to check in the theorems, and the log of the sessions.
* [05-todo-markers.md](05-todo-markers.md). 006-05, the review: the
  markers in a table, what was done with each, and the bisect of T2; its
  script and log in [05-todo-markers/](05-todo-markers/).


Log
===

2026-10-19. Created the item, at Frans's request, as 006-summary-2026-10,
with the summary written by Claude (Opus 5.5, Claude Code) from this
repository's `docs/log.md`, the item readmes, item 001's final report, and
F1-007 and F1-008.

2026-10-19. Renamed to 006-2026-q4, the item for small subitems of the
quarter, at Frans's request. The summary stays 006-01.

2026-10-19. 006-02, at Frans's request (as "bergdb 002-02", an ID that item
002's report has; this is the quarter's next subitem): Props on the 2017 and
the 2026 code and on the code cissi measured in 2015 and 2017, on F53 with
JDK 27, run and written by Claude (Opus 5.5, Claude Code) working unattended.
2026 against 2017: CORE 6 percent better, MEM 16, SS 4 (all of it the startup
distance); F53 against cissi: CORE 2.6 to 2.9 times better. Found on the way:
the 2017 import is two days into an unfinished cache rewrite, and the node
table's maps degenerate into trees, also in 2026; a one-line experimental
patch gives MEM -16 percent and `set` -11 percent.

2026-10-19. 006-02: section 10 added, MEM from 158 to 227 commit by commit, at
Frans's request; the tree-bin fix registered as 005-08.

2026-10-20. 006-03, at Frans's request, by Claude (Opus 5.5, Claude Code):
the unit tests from 41.5 s to 10 s; slow tests split into a small unit test
and the full f-test, or moved to the f-tests. New `java/before-commit.sh`,
the unit and f-tests (about 2 minutes), the only check before a commit.

2026-10-20. 006-03: `java/night.sh` is the night run: the level scripts, the
night tests and the medium conformance set on a clone of HEAD, at 02:00
(launchd); `night.sh large` adds the large conformance set, by hand.

2026-10-22. 006-04, at Frans's request: a guided reading of the trusted part
of `lean/` (definitions and theorem statements) against `docs/sis-model.md`,
Frans reading and Claude (Opus 5.5, Claude Code) guiding; the plan, written
by Claude, and the log of the sessions. First session 2026-10-23.

2026-10-25. 006-05, at Frans's request, by Claude (Opus 5.5, Claude Code):
the 15 TODO markers in `java/`, and what to do with each; Frans: "as
proposed". Done with it: comments removed or changed, 005-41 to 005-43,
and lines in 004-03, 005-11 and 007-03. Three markers were done in 005-39
and 005-40, the same morning; one is kept for 007-03's step 3.
