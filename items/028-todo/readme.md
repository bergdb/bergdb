028-todo
========

Created 2026-11-13 by Frans Lundberg. Status: open.

Simple tasks on BergDB: faults to fix, things to investigate, decisions to
prepare, changes to make, each done and closed in about a day, mostly by
an AI agent, often unattended. Each entry is a subitem with its own ID.
The list is not tied to a release: an entry names no release, and a
release item decides which entries its release takes.

Frans, 2026-11-13, 10:13: "I like to have a list of simple todos. Those
are tasks that AI often can do unattended. The release items like 026
were meant for bigger things. For planning what to include in a release.
For open-ended work. Features that may or may not be included in the
release. Human+AI work. [...] I don't want the big release items hidden
among 80 simple tasks." And 10:18: "Create a new todo item. The entries
of the todo item do not need a release, by default. The release item
itself will decided the scope of the release."

It takes every new todo entry from 2026-11-13. The earlier lists, 019 and
021, have no open entry; their entries stay where they are.


Rules
=====

What goes where
---------------

* **Here**: a task with a clear "Done when" that one agent can finish and
  close in about a day, its gates included, needing from Frans at most a
  choice between options written in the entry.
* **A release item** (such as 026): the release's plan and scope, its
  decisions, and subitems for the bigger work: designs, studies, features
  that may or may not be included, work that needs Frans's thinking or
  several steps. It lists the todo entries its release takes, by ID.
* **017-07, "To consider"**: an idea that Frans may consider some day.
* **017-long-term**: open-ended, long-term and strategy topics with no
  fixed "Done when" (017's rules).
* **006-2026-q4**: small work done at once at Frans's request, such as a
  summary or a review.
* An entry that turns out larger moves to an item of its own, or to a
  release item's subitems; its row moves to Closed with status moved, and
  its file stays with a link to where the work went.


Entries
-------

* An entry is a file `nn-short-name.md`, or a directory `nn-short-name/`
  with a `readme.md` when it has scripts or results:

      028-nn. Fix: a short title
      ==========================

      Status: open. Kind: Fix. Frans: none.
      Created 2026-11-13 by Frans Lundberg.

      What: the fault or the task, and where it is.

      Why: what goes wrong, or what it is for; the source.

      Frans: none; or the questions; or the options, each in full.

      Done when: the test, the gate, the measurement or the decision
      that closes it.

      First step: what an agent does first.


      Log
      ---

      2026-11-13. Registered by <session or Frans>.

* Kind: Fix, Investigate, Decide, Implement, Measure.
* `Frans:` says what the entry needs from him: `none` (an agent does it
  all), `answers` (questions in the entry), or `decision` (options in
  full with a recommendation). His answer goes into the entry's log,
  quoted, with date and time.
* An agent or a coordinator may take an open entry without asking: it sets
  the status to `in progress` and names its session in the log; if it
  stops before the entry is done, it writes a State note.
* Entries are numbered 028-01 to 028-99, the next after the highest
  issued; while a coordinator runs, a session asks it for the number
  (013-02). When the numbers run out, a new todo item continues the list.


The list
========

Two tables: what is left to do, and what is closed (newest first). A
subitem's own `Status:` line is the source.


Open
----

| ID | Kind | What | Frans | Status |
|---|---|---|---|---|
| [028-01](01-keymodset-bin-spread.md) | Measure | KeyModSet's bins and sequential keys | none | open |
| [028-19](19-pe-performance.md) | Change | PE's speed and reclaim's pace with PE | decided (09:32) | open |
| [028-34](34-transaction-info.md) | Decide | transactionInfo() in the Pub API, or the walk in the Core | to decide | open |


Closed
------

| ID | Kind | What | Frans | Status | Closed |
|---|---|---|---|---|---|
| [028-31](31-reclaim-row-without-end-key.md) | Fix | Text about a reclaim row without an end key | none | done | 2026-11-20 |
| [028-30](30-refusal-message-2026-4.md) | Investigate | A refusal message names a release that cannot help: main's, fixed | none | done | 2026-11-20 |
| [028-29](29-index-jobs-harness-stuck.md) | Investigate | IndexJobsHarness counts a slow cleanup as stuck | none | done | 2026-11-20 |
| [028-28](28-kill-restart-verify-old-times.md) | Investigate | The kill-and-restart harness's check at old times | none | done | 2026-11-20 |
| [028-33](33-timing-perf-refused.md) | Fix | timing.sh's perf step is refused right after a build | none | done | 2026-11-20 |
| [028-32](32-frozen-lookup-time.md) | Fix | IndexHarness bounds a frozen lookup time by an earlier time | none | done | 2026-11-19 |
| [028-22](22-old-writer-comments.md) | Fix | Java comments that describe the old writer as today's | none | done | 2026-11-19 |
| [028-24](24-checkers-without-mathlib.md) | Change | The level scripts without Mathlib | none | done | 2026-11-19 |
| [028-25](25-pe-mark-order.md) | Decide | One order of the marks for both ways of PE | decided B | done | 2026-11-19 |
| [028-26](26-reclaim-charge-pe-nodes.md) | Fix | Reclaim's charge omits the index nodes that PE makes | A (Frans) | done | 2026-11-19 |
| [028-27](27-disjoint-test-sets.md) | Change | night, week and timing as disjoint sets of tests; Android in week | decided | done | 2026-11-19 |
| [028-13](13-startup-distance-ranges.md) | Decide | The startup distance: the builders' methods go | decided (11:10) | done | 2026-11-19 |
| [028-21](21-dirty-node-bound-pe.md) | Investigate | Does dirtyNodeBound bound the writer PE? No: three gaps, fixed | none | done | 2026-11-19 |
| [028-20](20-harness-late-exit.md) | Fix | The kill-and-restart harness fails a late exit run | none | done | 2026-11-19 |
| [028-23](23-test-kinds.md) | Change | The test scripts sorted by kind: functional and timing | decided (10:39) | done | 2026-11-19 |
| [028-15](15-startup-distance-in-a-kv.md) | Change | The startup distance out of the meta block, into an internal KV | A (10:50) | done (1b1001ee, 026c322a) | 2026-11-18 |
| [028-18](18-one-startup-transaction.md) | Change | One startup transaction: the creation whole (option C) | C (09:53) | done | 2026-11-19 |
| [028-17](17-creation-kv-not-synced.md) | Fix | A crash after a new database's start left the primordial record alone | none | done | 2026-11-18 |
| [028-16](16-second-start-closes-db.md) | Fix | A refused second start of one Db closes the database the first started | none | done | 2026-11-16 |
| [028-14](14-corrupt-node-no-end.md) | Investigate | A damaged node with its checksum right: a start that does not end | none | done | 2026-11-16 |
| [028-07](07-start-lock-across-sync.md) | Investigate | One start's sync blocks every start of the JVM | none | done | 2026-11-16 |
| [028-10](10-public-start-params.md) | Investigate | The public Db.start(StartParams) takes unchecked values | A | done | 2026-11-14 |
| [028-12](12-take-byte-limit/readme.md) | Investigate | Can the take's byte limit stop the startup section's bound? | A | done | 2026-11-14 |
| [028-04](04-null-value-transformation.md) | Fix | What a null result of a value transformation does | A | done | 2026-11-14 |
| [028-11](11-startup-stale-texts.md) | Fix | Texts that disagree with the code, found by 027-11 | P5 only | done | 2026-11-13 |
| [028-09](09-startup-pos-own-record.md) | Investigate | CheckStartupPos accepts a record's own position | none | done | 2026-11-13 |
| [028-08](08-sd-crash-inside-setter.md) | Investigate | A crash inside setStartupDistance's own record | none | done | 2026-11-13 |
| [028-06](06-maintain-and-pacing-javadoc.md) | Fix | maintain() and pacing, Core Javadoc | none | done | 2026-11-13 |
| [028-05](05-core-api-transformations.md) | Fix | The Core API names the transformations | none | done | 2026-11-13 |
| [028-03](03-write-buffer-sentence.md) | Fix | The package's write buffer sentence | none | done | 2026-11-13 |
| [028-02](02-reclaim-comments.md) | Fix | Reclaim's and Db's comments that disagree with the code | none | done | 2026-11-13 |


Log
===

2026-11-13. Created the item (Frans, 10:13 and 10:18), by coord-1113.

2026-11-13. 028-08, 028-09 and 028-11 done, 028-10 evaluated, for Frans
(a decision), by an agent of coord-1113.

2026-11-15. 028-14 registered: night.sh's one failure (CorruptStreamTester),
by coord-1115.

2026-11-16. 028-15 registered: the startup distance in an internal KV
(Frans, 10:32: wanted in the next release), by coord-1116.

2026-11-16. 028-07 done: starts no longer hold the lock of `DatabaseImp`'s
class, by an agent of coord-1116.

2026-11-16. 028-07 done (6695d48c). 028-16 registered from it, by
coord-1116.

2026-11-16. 028-14 done: a skip pointer to its own top node looped a
get; the walk now takes only older top nodes, by an agent of coord-1116.

2026-11-16. 028-16 done: a refused second start of one `Db` closes
nothing, by an agent of coord-1116.


2026-11-18. 028-15 made and gated on the branch `028-15-sd-kv` (option A,
Frans, 10:50), by an agent of coord-1118.

2026-11-18. 028-17 registered and taken: night.sh's kill-restart failure
(run 2026-11-18-1239), by an agent of coord-1118.

2026-11-18. 028-17 done: a new Pub database's creation was not durable
when start() returned since 028-15; the creating start now syncs its
record of the startup distance; gated on its branch, by an agent of
coord-1118.

2026-11-18. 028-15 closed: landed 1b1001ee, the key `/#i/-sd` 026c322a.
028-18 registered: one startup transaction (Frans, 21:30 and 21:37).

2026-11-19. 028-19 registered: PE's speed and reclaim's pace (Frans, 09:32).

2026-11-19. 028-20 registered and taken: kill-restart's false failure of a
late exit run (026-25, section 6; Frans, 10:14), by an agent of coord-1118.

2026-11-19. 028-21 and 028-22 registered: dirtyNodeBound for PE, and the
Java comments of the old writer; found by an agent of coord-1118 while
bringing 027 up to date with PE (branch `027-pe`).

2026-11-19. 028-18: Frans chose option C (09:53, 09:59); made on the
branch `028-18-option-c` by an agent of coord-1118.

2026-11-19. 028-18 done: option C gated (KILL RESTART OK with seeds 20261118,
20261119 and 20261120) and landed.

2026-11-19. 028-20 done: a late exit run whose JVM ends by itself with
status 0 is an exit; the check `lateexit` fails before the fix and passes
after it; gated on its branch (KILL RESTART OK with seeds 20261119 and
20261121), by an agent of coord-1118.

2026-11-19. 028-23 registered and taken: the test scripts sorted by kind,
functional (before-commit.sh, night.sh, a new week.sh) and timing (a new
timing.sh) (Frans, 10:25 to 10:39), by an agent of coord-1118.

2026-11-19. 028-23 done on its branch: before-commit.sh, night.sh and a
new week.sh functional, a new timing.sh the only one that needs a quiet
machine; 13 load-sensitive checks made robust; the user apps in
java/stress/apps/, by an agent of coord-1118.

2026-11-19. 028-21 done: `dirtyNodeBound` did not bound PE (a new
segment tree cut into parts, a node cut into more parts than its
overflows and one, a new root above a cut segment root); fixed, with
the Lean copy and the argument for PE; by an agent of coord-1118 on the
branch `028-21-dirty-bound`.

2026-11-19. 028-24 registered (Frans, 10:40 and 10:42) and done on the
branch `028-24-checkers-no-mathlib`: the contract checkers build without
Mathlib in `lean/contractcheck/`, by an agent of coord-1118.

2026-11-19. 028-26 registered by coord-1118 from Codex's review of PE
(finding 1) and taken by an agent of coord-1118: reclaim's charge omits
the index nodes that PE makes.

2026-11-19. 028-26 done: Frans chose option A (13:30), the row stored
again after a step with the bytes its batch made dirty after the row;
landed by coord-1118, regated on the merged tree.

2026-11-19. 028-13 done: the startup distance set only by the running
database's setter (Frans, 11:06 and 11:10); `DbBuilder.startupDistance`
and `DatabaseBuilder.startupDistanceInMb` removed; the Core setter clamps
to 10 to 10^9 and returns the value set; gated on the branch
`028-13-startup-distance-setter`, by an agent of coord-1118.

2026-11-19. 028-27 registered (Frans's decision of 2026-11-19) and taken by
an agent of coord-1118: night.sh, week.sh and timing.sh as disjoint sets
of tests, the Android tests in week.sh; branch `028-27-disjoint-test-sets`.

2026-11-19. 028-27 done on its branch: week.sh stands alone with the
Android tests, night.sh without `week` and `large`, the shared machinery
in `java/stress/runlib.sh`; WEEK OK from `week.sh short`, by an agent of
coord-1118.

2026-11-19. 028-28 to 028-31 registered by coord-1118 from the day's
reports; 028-22, 028-24 to 028-27 moved to Closed.

2026-11-19. 028-32 registered and taken: week.sh's harness-soak failure
(run 2026-11-19-1514), a harness bug: IndexHarness bounded a frozen lookup
time by the current time taken before the read, while an index job may
commit between; gated on the branch `028-32-frozen-lookup-time`, by an
agent of coord-1118.

2026-11-20. 028-33 registered by coord-1118 from the first timing runs.

2026-11-20. 028-33 taken and done by an agent of the day's coordinator:
performance.sh waits for a quiet machine up to QUIETWAIT minutes (timing.sh
passes its RUNWAIT and MINIDLE), and timing.sh tells a refusal from the
comparison's alerts; branch `028-33-timing-perf`. Moved to Closed.

2026-11-20. 028-30 and 028-31 taken and done by tx of coord-1120, on the
branch `028-30-31-texts`. 028-30: the message is main's (028-15), not
2026.4's; it told a user of a 2026.4 database to read it with 2026.5,
which refuses it; fixed to the release that wrote it, with the next
release's notes; not a released bug (033). 028-31: 027-13 and
`Reclaim.step`'s Javadoc as the code is since 028-15. Moved to Closed.
2026-11-20. 028-29 and 028-28 taken and done by hf of coord-1120 on the
branch `028-29-28-harness`: four races of IndexJobsHarness's checks (no
fault of the database), its cleanups and builds stuck only with no
progress; KillRestartHarness expects a refusal only at a time that has left
the retention, and verify() then abandons the database. Moved to Closed.
