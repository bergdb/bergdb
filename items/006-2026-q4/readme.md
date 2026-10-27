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
| [006-06](06-fast-restart.md) | 2026-10-26 | Fast restart, a note of Frans's idea: lower the startup distance for a while before a controlled restart; not investigated |
| [006-07](07-docs-cleanup.md) | 2026-10-26 | The `docs/` cleanup: most documents to items (001-07 to 001-11, 009-05, the new 011), `docs/levels.md` rewritten short, `docs/trace-format.md`, the references as IDs |
| [006-08](08-core-layer.md) | 2026-10-26 | The Core Layer: built alone (680 kB), and the Core without its tests, what `Db` needs (14,677 code lines, 335 kB, two thirds of the production code), which writes the same stream; independent of the layers above and of its tests; a C clone for an embedded target is feasible, about 35 to 90 kB of code on a Cortex-M4 by an estimate, its open questions memory and writes at small startup distances |
| [006-09](09-unattended-27-28-october.md) | 2026-10-27 | Unattended work from 27 October, 12:00, to 28 October, 07:00: the plan (005-46's measurements, 005-49, 005-58, 005-51, 005-48), its principles, the progress and the outcome |


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
* [06-fast-restart.md](06-fast-restart.md). 006-06, the note: the idea in
  Frans's words, why it matters (005-38's first numbers), and the questions
  for later.
* [07-docs-cleanup.md](07-docs-cleanup.md). 006-07, the cleanup of
  `docs/`: what moved where, the rules for references, what was carried
  forward, the checks; the script that rewrote the references and the link
  check in [07-docs-cleanup/](07-docs-cleanup/).
* [08-core-layer.md](08-core-layer.md). 006-08: the Core built alone,
  independent of the layers above and of its tests, its size, and the
  feasibility of a C clone for an embedded target; the scripts, the
  programs that use the Core and the output in
  [08-core-layer/](08-core-layer/).
* [09-unattended-27-28-october.md](09-unattended-27-28-october.md). 006-09:
  the plan for the unattended work of 27 to 28 October, the work in order
  and what 010's principles ask of each piece, the timeline, the progress
  through the night and the outcome.


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

2026-10-26. 006-06, at Frans's request, during 005-38: fast restart, a note
of Frans's idea (a lower startup distance for a while before a controlled
restart, for a short startup), written by Claude (Opus 5.5, Claude Code).
Not investigated.

2026-10-26. 006-07, at Frans's request ("I want most docs moved to
items/."; to the plan: "Everything as recommended, except the log. Keep
log.md as is."), by Claude (Opus 5.5, Claude Code): `docs/` keeps
`levels.md` (rewritten short), `sis-model.md`, `trace-format.md` (new),
`log.md` and `sources/`; the other documents are subitems of 001, 009 and
the new 011; the code and the items cite them by ID.

2026-10-26. 006-08, at Frans's request ("Check BergDB Core Layer
independence. Can a version be build from the bergdb.core package with
dependencies."), by Claude (Opus 5.5, Claude Code): the Core Layer, `core`
and the six packages it may use, compiles alone (680 kB, 415 classes); a
program outside `bergdb` calls `Db` with only it on the class path, and
its unit and f-tests pass on it. `FileStreamPowerLossTester` moved from
`stream` to `core`, as `stream` may not use `core` or `storage`
(`FileStreamIo` public, with protected methods); `dag`'s and `stream`'s
`package.html` lists fixed. `before-commit.sh` OK, `level3.sh`'s step 7
OK.

2026-10-27. 006-08 reworked, from Frans's question of 2026-10-26 ("Is The
Core independent from the test of the code. How large would a build of only
the Core be compared to the full database.") and at his request ("What is
important is that Core can be built. It is still independent. And the
feasibility for a C embedded clone."), by Claude (Opus 5.5, Claude Code).
The tests are in the production files, and production code uses `nanotest`
in one line only (`KeyNode`); with the tests removed (`strip.py`), what
`Db` and `DbBuilder` need is 121 files, 14,677 code lines and a jar of 335
kB, two thirds of the production code, and it writes the same stream, byte
for byte, as the Core with its tests (`CoreSame`). A C clone for an
embedded target: about 10,000 to 17,000 lines of C and 35 to 90 kB of code
on a Cortex-M4, by an estimate and the bytes per line of LMDB, littlefs and
SQLite measured; its open questions are memory and writes at small startup
distances, a written stream format and power loss on raw flash.
`core-build.sh` passes at `c7c6f10`. `core-size.sh`, `c-size.sh`,
`strip.py`, `lines.py`, `CoreSame.java`.

2026-10-27. 006-09, at Frans's request ("Please suggest a plan for work you
can do unattented between now and tomorrow at 07:00 am. [...] Add an item to
006 with the plan you create. Update the item with progress."), by Claude
(Opus 5.5, Claude Code): the plan, from the open items and 005's entries,
with Frans's answers of 11:39 (commit; 005-51 into `java/`; 005-58 is this
work's; 005-46's and 009's status at this work's judgement; `night.sh` may
move; "Follow BergDB's principles 010.").
