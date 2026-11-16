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
| [006-10](10-unattended-28-29-october.md) | 2026-10-28 | Unattended work from 28 October, noon, to 29 October, 07:00, in 013-01's way: the plan (007-07's performance check, 005-65's 8-thread case, 005-64's buffer time), its principles, the progress and the outcome |
| [006-11](11-stm-concurrency.md) | 2026-10-30 | STM and concurrent writers, investigated and benchmarked: keep STM for read-dependent work (1.7x to 6.9x the partially stripped serial control); tiny resident updates and hot keys do not automatically benefit; 276 checked measurements, code costs, critical-section review and reproducible evidence |
| [006-12](12-unattended-5-6-november.md) | 2026-11-05 | Unattended work from 5 November, 15:00, to 6 November, 07:00, with a coordinator: the plan (015's open fixes, 015-86's measurements, a performance check, 015-88 on s1), the progress and the outcome |
| [006-13](13-day-and-night-6-november.md) | 2026-11-06 | Day and night work of 6 to 7 November, with the coordinator coord-1106: 006-12's decisions with Frans, the plan, the progress and the outcome |
| [006-14](14-day-7-november.md) | 2026-11-07 | Day work of 7 November (a Saturday), with the coordinator coord-1107: release 2026.4's work, the plan, the progress and the outcome |
| [006-15](15-day-8-november.md) | 2026-11-08 | Day work of 8 November (a Sunday), with the coordinator coord-1108: release 2026.4's work, the plan, the progress and the outcome |
| [006-16](16-props-across-releases.md) | 2026-11-09 | Props (MEM, CORE, SS) across BergDB's history, 2013.1 to the 2026.4 candidate, 14 builds on F53: MEM 144 (2013) to 129-130 (2026.2 on), SS 1.83 to 1.51; CORE not run yet, needs a quiet F53 |
| [006-17](17-day-9-november.md) | 2026-11-09 | Day work of 9 November (a Monday), with the coordinator coord-1109: release 2026.4's bug hunts, the plan, the progress and the outcome |
| [006-18](18-ports/readme.md) | 2026-11-09 | BergDB in languages other than Java: demand (01) and technical feasibility (02), one ranking; C on Linux as the base of bindings, Java's Core on Android as a check, then Rust and Python bindings; the licence decides the reach |
| [006-19](19-write-amplification.md) | 2026-11-09 | Write amplification at large sizes: where a put's bytes go (867 at 10M keys and 50 MB, 92 % index nodes), the levers, what to measure |
| [006-20](20-ai-as-the-user-testing.md) | 2026-11-09 | AI as the user: black-box application testing, the method and the 12 applications of 020-24 as its example |
| [006-21](21-day-10-november.md) | 2026-11-10 | Day work of 10 November (a Tuesday), with the coordinator coord-1110: 2026.4 paused for 020-30, the plan, the progress and the outcome |
| [006-22](22-day-11-november.md) | 2026-11-11 | Day work of 11 November (a Wednesday), with the coordinator coord-1111: the aim of 2026.5, the plan, the progress and the outcome |
| [006-23](23-day-12-november.md) | 2026-11-12 | Day work of 12 November (a Thursday), with the coordinator coord-1112: the plan, the progress and the outcome |
| [006-24](24-day-13-november.md) | 2026-11-13 | Day work of 13 November (a Friday), with the coordinator coord-1113: the plan, the progress and the outcome |
| [006-25](25-day-14-november.md) | 2026-11-14 | Day work of 14 November (a Saturday) to Sunday morning, with the coordinator coord-1114: the plan, the progress and the outcome |
| [006-26](26-proofs-status.md) | 2026-11-14 | The proofs as of 14 November 2026: what is proved, the premises left, what the Lean model covers and not; a standalone report for Frans |
| [006-27](27-day-15-november.md) | 2026-11-15 | Day work of 15 November (a Sunday, unattended) to Monday morning, with the coordinator coord-1115: the plan, the progress and the outcome |
| [006-28](28-simpler-algorithms.md) | 2026-11-16 | Simpler algorithms for simpler proofs: where the complexity is, measured by the Lean model; the top three changes to the Java code that make the proving easier |
| [006-29](29-day-16-november.md) | 2026-11-16 | Day work of 16 November (a Monday), with the coordinator coord-1116: the plan, the progress and the outcome |


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
* [10-unattended-28-29-october.md](10-unattended-28-29-october.md). 006-10:
  the plan for the unattended work of 28 to 29 October, in 013-01's way of
  working: the questions for Frans, the work in order, the principles, the
  timeline and the quiet block's steps, the progress and the outcome.
* [11-stm-concurrency.md](11-stm-concurrency.md). 006-11: STM and concurrent
  writers, the source investigation, critical-section review and completed
  benchmarks (section 10); the source-size tool, test output, benchmark code,
  results and raw evidence in
  [11-stm-concurrency/](11-stm-concurrency/).
* [12-unattended-5-6-november.md](12-unattended-5-6-november.md). 006-12:
  the plan for the unattended work of 5 to 6 November, with the day's
  coordinator: the questions for Frans, the work in order, the timeline
  and the quiet blocks, the progress and the outcome.
* [13-day-and-night-6-november.md](13-day-and-night-6-november.md). 006-13:
  the plan for the day and night of 6 to 7 November (coord-1106): the
  decisions on 006-12's points, the work, the progress and the outcome.
* [14-day-7-november.md](14-day-7-november.md). 006-14: the plan for the
  day of 7 November (coord-1107): release 2026.4's work, the progress and
  the outcome.
* [15-day-8-november.md](15-day-8-november.md). 006-15: the plan for the
  day of 8 November (coord-1108): release 2026.4's work, the progress and
  the outcome.
* [16-props-across-releases.md](16-props-across-releases.md). 006-16, the
  report: Props on 14 builds from 2013 to the 2026.4 candidate, what it
  measures and how it changed, MEM and SS of each build, cissi's figures of
  2013 to 2017 and 2012's, and what is left (CORE). The plan, the scripts
  (`run.sh`, the port `P16.java.in`, `summary.py`) and the runs are in
  [16-props-across-releases/](16-props-across-releases/).
* [17-day-9-november.md](17-day-9-november.md). 006-17: the plan for the
  day of 9 November (coord-1109): release 2026.4's bug hunts, the progress
  and the outcome.
* [18-ports/](18-ports/readme.md). 006-18, the study of BergDB in
  languages other than Java: the combined ranking, the facts that decide
  it, the first steps and Frans's decisions in its readme; demand and
  landscape in [01-demand.md](18-ports/01-demand.md), technical
  feasibility in [02-technical.md](18-ports/02-technical.md).
* [19-write-amplification.md](19-write-amplification.md). 006-19, write
  amplification at large sizes: where the bytes of a put go, how they grow
  with the keys and the startup distance, other engines, the levers (with
  and without a format change), and the measurements to make.
* [20-ai-as-the-user-testing.md](20-ai-as-the-user-testing.md). 006-20, a
  note on testing with an AI agent as the user: black-box applications
  written from the jar and the Javadoc alone, each with its own oracle; why it
  finds what reviews and harnesses miss, how to run it, and the 12
  applications of 9 November (020-24) as the worked example.


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

2026-10-28. 006-10, at Frans's request ("You gave me proposed work for
tonight. Create 006-10 for planning tonight's unattended work. Similar to
006-09 in way of working."), by Claude (Opus 5.5, Claude Code): a draft
plan in 013-01's way of working, from the proposal of the morning (007-07's
quick performance suite, 005-65's 8-thread case, 005-64's buffer time),
with five questions for Frans before the work starts.

2026-10-30. 006-11, at Frans's request, by Codex: the current STM and writer
concurrency design, existing correctness and performance evidence, a fresh
source-size count and focused tests, and a proposed first comparison of
optimistic actions with serialized application actions. No production code
changed; writer-scaling measurements remain proposed.

2026-10-30. 006-11, section 9, at Frans's request, by Codex: a source-only
review of the single-writer section, its required ordering and candidates
for less work under the lock, especially record encoding/checksums and
reclaim preparation. No code changes or new performance measurements.

2026-10-30. 006-11 benchmark complete, at Frans's request to code and run it
unattended, by Codex with two subagents: 276 measured runs with
verified counter totals and stored computations; the unchanged baseline's
1,071 unit and 78 functional checks pass. Concurrent read-dependent work
gives 1.7x to 6.9x the throughput of a partially stripped serial control;
small resident actions favor the serial path, hot-key retries reach ten
seconds, and preparation keeps almost all storage reads outside the write
lock in the eviction workload. Recommendation: keep STM; code, full results,
measurement conditions and raw evidence are in 006-11. Production Java and
Lean were not edited, and no commit was made.

2026-11-05. 006-12 created at Frans's request: the plan for the unattended
work of 5 to 6 November, 15:00 to 07:00, with a coordinator session;
preliminary, with five questions for Frans.
