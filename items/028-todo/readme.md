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
| [028-34](34-transaction-info.md) | Decide | transactionInfo() in the Pub API, or the walk in the Core | as it is for 2026.7 | open |
| [028-65](65-idle-db-space-amplification.md) | Investigate | An idle database keeps several times its live values (031-03, 9.3) | none | open |
| [028-67](67-stale-tail-at-start.md) | Fix | A deleted file's bytes in the last file after a kill (APFS): C1 and C3 in 2026.7 | decided | C1, C3 built; C2 and the nodes' place with 028-77 |
| [028-72](72-action-room-lean-count/readme.md) | Investigate | The action's 7/8: Java's count 76.5 % at worst; A: the text, 10 a level at 14, a test | A | A done; B open |
| [028-75](75-small-put-full-pass/readme.md) | Decide | One small put, then maintain() calls rewrite the whole live data: (c) | decision | open (designed: a record format change) |
| [028-76](76-first-block-a-fill.md) | Fix, Decide | A stream whose first meta block is recovery's fill: fixed; the files before a gap: (a) | decided | open |
| [028-77](77-append-only-or-tail-rewrites.md) | Decide | Strict append-only storage, or tail rewrites at a start; the review is 035-03 | decision | open |
| [028-78](78-deleted-copy-passes-c3.md) | Decide | A deleted copy of the database's bytes in the tail pass C3 (a restore in place; 035-02's storage) | decision, with 028-77 | open |
| [028-79](79-other-bytes-at-first-block.md) | Fix | Other bytes at a meta block's position, once taken, refuse a later start | none; by default 10:30 | fix (1) and two shapes on main; E open (a branch) |


Closed
------

| ID | Kind | What | Frans | Status | Closed |
|---|---|---|---|---|---|
| [028-87](87-g5-st6-slots-vary.md) | Investigate | G5's ST6 varies by run with eviction's timing; its pass does not | none | done | 2026-11-28 |
| [028-66](66-cut-deletes-lag/readme.md) | Investigate | The cut's deletes lag behind a fast writer; C and the rule on `main` | decided | done | 2026-11-28 |
| [028-73](73-new-files-a-tenth-writer-waits.md) | Decide | New files a tenth: the writer waits at a new database's first 10 MB: (b) on `main` | decided | done | 2026-11-28 |
| [028-74](74-commit-time-after-restart.md) | Decide | A commit's time after a restart at or before a time a reader was given: (a) on `main` | decided | done | 2026-11-28 |
| [028-83](83-maintain-interrupt-stop-exceptions/readme.md) | Fix | maintain() no longer spins when interrupted; a write at a stop throws the documented exception; e3 seed 101 explained | none | done | 2026-11-28 |
| [028-84](84-maintain-and-gettrans-documents.md) | Fix | Documents: a maintain() call's work and wait, a commit's getTrans(), an emptied stream | none | done | 2026-11-28 |
| [028-85](85-recreated-directory-test-under-load.md) | Fix | A test deleted a stopped database's directory before close(): now after it; the window a test | none | done | 2026-11-28 |
| [028-86](86-g4-dead-klongs-a-phase/readme.md) | Investigate | G4's M5 failed on a phase after 031-06's pace; G5's limit | none | done | 2026-11-28 |
| [028-80](80-creation-zeros-zero-tail-bound.md) | Fix | A creation left as zeros now refused as one (RB-014); the zero tail's bound for every buffer | none | done | 2026-11-28 |
| [028-81](81-created-txt-id-at-start.md) | Fix | Another database's first file: created.txt's ID compared first (UB-3) | none | done | 2026-11-28 |
| [028-82](82-file-handling-documents-and-messages.md) | Fix | A running database's backup, a decided cut's files, the open's refusals | none | done | 2026-11-28 |
| [028-70](70-refused-start-after-recovery-wrote.md) | Investigate | A refused start wrote recovery's fill: now held until the last check | none | done | 2026-11-28 |
| [028-71](71-large-commits-stream-kept.md) | Investigate | Large commits: a commit's step sized by its allowance; 18 times the live data at 1 MB commits | closed | done | 2026-11-28 |
| [028-53](53-maintain-idle-rewrites/readme.md) | Investigate | Idle rewrites by M1; RB-007 fixed by 031-06; the rest is 028-75 | closed | done | 2026-11-28 |
| [028-68](68-step-reserve-outside-stream.md) | Decide | Step reserve a constant (B), built in 031-06 | B (16:09) | done | 2026-11-27 |
| [028-54](54-p2-inside-maintenance.md) | Investigate | Stop inside maintenance: RB-013, fixed by 031-06 | answered | done | 2026-11-27 |
| [028-69](69-remove-crypto-code.md) | Implement | The internal crypto code removed (`1809e04c`); recorded in 017-10 | none | done | 2026-11-27 |
| [028-60](60-zero-tail-over-meta-block.md) | Fix | RB-012: a kill's zeroed tail; FileStream removes up to 8 MB | FileStream only | done | 2026-11-27 |
| [028-62](62-emptied-file-db-last-file/readme.md) | Decide | RB-011: new files a tenth of the stream; the Javadoc of the stream | neither J nor S | done | 2026-11-26 |
| [028-63](63-large-fill-envelope/readme.md) | Investigate | large run's fill: the seed's key order; the cap scales | none | done | 2026-11-26 |
| [028-64](64-week-run-ten-hours.md) | Change | week.sh in three lanes, about 6 hours, no coverage cut | none | done | 2026-11-26 |
| [028-59](59-maintain-filler-left-live/readme.md) | Investigate | A stop between the filler's put and delete leaves it live: released, S4 | none | done | 2026-11-25 |
| [028-58](58-maintain-two-stretches/readme.md) | Investigate | An emptied database at 790 kB: RB-006 and RB-007; RB-006 fixed in part | none | done | 2026-11-25 |
| [028-61](61-maintain-emptied-several-sd/readme.md) | Investigate | An emptied file database keeps its last file: its own, not RB-007 | none | done | 2026-11-25 |
| [028-57](57-pubtester-force-failure.md) | Investigate | PubTester.testNoCreatedTxtWithoutForce: the test's timing; fixed | none | done | 2026-11-25 |
| [028-56](56-gettrans-walk-concurrent-cut.md) | Fix | getTrans's walk expired a kept transaction during a cut: RB-009, fixed | none | done | 2026-11-25 |
| [028-55](55-gettrans-split-file-stream.md) | Investigate | getTrans refused a large transaction after a cut: RB-008, fixed | none | done | 2026-11-25 |
| [028-19](19-pe-performance/readme.md) | Change | PE's speed; reclaim's pace explained | decided (09:32) | done | 2026-11-24 |
| [028-49](49-release-body-absolute-links.md) | Fix | The GitHub release's body with absolute links: body.sh | none | done | 2026-11-24 |
| [028-51](51-maintain-m1-written-db/readme.md) | Fix | maintain()'s M1 stalled in a written database: fixed, RB-006 | none | done | 2026-11-24 |
| [028-45](45-dirty-count-test.md) | Change | A test of Db's dirty-node count with transformations | A (12:26) | done | 2026-11-24 |
| [028-50](50-key-transformation-count.md) | Fix | The dirty-node count of a key with a key transformation, after it | A (12:26) | done | 2026-11-24 |
| [028-52](52-g4-st6-at-c2-settings.md) | Investigate | G4's ST6 at C2's settings: the gate, given G5's floor | none | done | 2026-11-24 |
| [028-47](47-commits-reclaim-by-clock/readme.md) | Investigate | Commits reclaim by the clock (option B): no change | A (12:30) | done | 2026-11-24 |
| [028-44](44-contract-check-shape-faults.md) | Change | The contract checker fails on a shape fault | none | done | 2026-11-24 |
| [028-48](48-keymodset-scan-stop.md) | Change | KeyModSet's modifiedAfter stops at the bin of the read time | none | done | 2026-11-24 |
| [028-46](46-dagtester-joins-at-62.md) | Change | DagTester's deletes at node size 62, joins by height | none | done | 2026-11-24 |
| [028-01](01-keymodset-bin-spread.md) | Measure | KeyModSet's bins: a mixed hash, 74 times fewer pairs scanned | none | done | 2026-11-24 |
| [028-43](43-large-reclaim-run.md) | Change | Long large reclaim run | none | done | 2026-11-21 |
| [028-42](42-w10m-fin-no-cut.md) | Fix | timing.sh's scenario w10m-fin reaches its cut: maxops 6M | none | done | 2026-11-21 |
| [028-41](41-jdeps-check-jvm-banner.md) | Fix | build.sh's jdeps check and the JVM's "Picked up" line | none | done | 2026-11-20 |
| [028-40](40-core-creation-durable-at-sync.md) | Fix | The Core's creation durable at its first sync: Javadoc; RB-003 | decided | done | 2026-11-20 |
| [028-37](37-contractconf-bridge-twice.md) | Change | contractconf.sh and level2.sh run the bridge checker once | none | done | 2026-11-20 |
| [028-39](39-dirty-node-bound-javadoc.md) | Fix | dirtyNodeBound's Javadoc: the false step about joins, proved and tested | none | done | 2026-11-20 |
| [028-38](38-fresh-tree-bound-small-nodes.md) | Fix | freshTreeBound at node sizes of 4 or less: sizes below 8 refused | decided | done | 2026-11-20 |
| [028-36](36-index-jobs-retried-fault-flake.md) | Investigate | IndexJobsHarness.testRetriedFaultThenDeletedDuringBuild: 028-29's race | none | done | 2026-11-20 |
| [028-35](35-killempty-not-created.md) | Fix | The user app KillEmpty and a kill during a database's creation | none | done | 2026-11-20 |
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

2026-11-20. 028-38 taken and done by fx1 of coord-1120 on the branch
`028-fx1`: Frans decided a minimum node size of 8 in the Dag in place of a
fix of `freshTreeBound` at 4 or less; a Dag refuses sizes below 8, their
branches and tests removed or moved to 8. Moved to Closed.

2026-11-20. 028-39 taken and done by fx1 of coord-1120 on the branch
`028-fx1`: `Dag.dirtyNodeBound`'s Javadoc, 028-21, 027-03 and 027-08 name
the false step about joins (030-29, section 4) and say what is proved
(puts, 030-29) and what is tested (deletes). Moved to Closed.

2026-11-20. 028-37 taken and done by fx1 of coord-1120 on the branch
`028-fx1`: contractconf.sh and level2.sh's step 8b run
lean/contract/check.sh alone, which runs both checkers and their fault
tests; bridge-check.sh no longer checks the same traces again. Moved to
Closed.

2026-11-20. 028-35 and 028-36 taken and done by fx2 of coord-1120 on the
branch `028-fx2`. 028-35: KillEmpty makes a database whose creation a
kill cut again, as Kill does (a kill inside the creating start, or after
it returned, as the Core API's creation is not synced). 028-36: 028-29's
second race, fixed in main; no fault of the database. Moved to Closed.

2026-11-20. 028-40 done by coord-1120: the Javadoc of the Core's creation (Frans decided); RB-003. Moved to Closed.

2026-11-20. 028-41 registered and done by an agent of coord-1120 on the
branch `026-26-app-hunt`, from 026-26's S4-B1: `java/build.sh`'s jdeps
check drops the JVM's "Picked up" lines of `JAVA_TOOL_OPTIONS` and
`_JAVA_OPTIONS`, which failed the build with no class missing; a fault
of the build script, not a released bug (033). Moved to Closed.

2026-11-21. 028-42 registered by coord-1120, from timing.sh's first full
run of the release suite: w10m-fin wants a cut in 4M commits and gets
none, on the candidate and on 2026.5.

2026-11-21. 028-42 done by an agent of coord-1120 on the branch
`028-42-w10m-fin`: w10m-fin's first cut waits for reclaim's first
iteration over the 10M values and then the retention, after 4.01M
commits on main and 3.87M on 2026.5; maxops 4M to 6M in the release
suite. No fault of reclaim. Moved to Closed; the full timing.sh run is
the coordinator's.

2026-11-21. 028-43 registered by coord-1120 and done in a clone: a long
functional run at 10 million keys with reclaim, retention, bounded storage
and recovery (java/stress/large.sh), a step of week.sh. Quick and full
passed: 100 million transactions, 89 physical cuts, bounded kept bytes,
recovery checked; BEFORE COMMIT OK; no database code change. Moved to
Closed.

2026-11-22. 028-34: Frans kept transactionInfo() as it is for 2026.6; open
for a later release.

2026-11-24. 028-44 to 028-46 registered by an agent of lead-1124, from
030-39's findings F6, F7 and F8 (Frans, 2026-11-24, 006-33, point 3): the
contract checker fails a trace with a shape fault; a test of
`Db.checkDirtyNodes`' count with transformations and the cheap estimate;
DagTester's purpose-made deletes at node size 62 with the joins' heights
asserted.

2026-11-24. 028-47 registered by lead-1124: 026-13's option B, not
studied in 2026.6, so that it is not lost when 026 is done (Frans).

2026-11-24. 028-01 taken and done by an agent of lead-1124 on the branch
`028-01`: keys such as `/k/%010d`, sequential or random, fell in 500 of
`KeyModSet`'s 32,000 sub-arrays, and a lookup scanned about 1,500 pairs;
the sub-array index of a hash mixed by fmix64 spreads them, about 21
pairs a lookup, with the same answers and the same stream. Moved to
Closed.

2026-11-24. 028-48 registered by lead-1124, from 028-01's Result:
modifiedAfter stops at the first bin that begins at or before the read time.

2026-11-24. 028-46 done by an agent of lead-1124: PE counts its joins by
the children's height; DagTester's purpose-made deletes run at node sizes
8, 14, 30 and 62 and assert a join at height two or more in each case,
with new cases at 30 and 62; BEFORE COMMIT OK. Moved to Closed.

2026-11-24. 028-48 taken and done by an agent of lead-1124 on the branch
`028-48`: `modifiedAfter` reads the bins down to the first that begins at
or before the read time, with the full scan's answers; a lookup of a key
not recently written reads 1 to 4 bins by its read time, not always 4.
Moved to Closed.

2026-11-24. 028-45 by an agent of lead-1124: the test of Db's dirty-node
counts with transformations, at node sizes 8 and 30, passes; it found the
estimate of a key transformed to a key of more segments short (46 key
nodes marked, counted 39), kept as a test that asserts the fault. Frans:
decision among options A to C (recommended A); in progress.

2026-11-24. 028-49 registered by an agent of lead-1124, from finding 1 of
the review of release 2026.6: the release scripts make the GitHub
release's body with absolute links; for 2026.7 (031).

2026-11-24. 028-47 studied by an agent of lead-1124, for Frans's decision:
option B (a commit begins an iteration also on `maintain()`'s rule) gives
no clear gain, as the cut then waits for the startup pos, which moves with
the stream's growth; B2, B with `maintain()`'s take at commits, gives the
gain but writes 4.3 times the stream at the Pub's default startup
distance. Recommended: A, no change. The entry is a directory now, with
its probes; status open.

2026-11-24. 028-44 done by an agent of lead-1124 on the branch `028-44`:
the contract checker fails a trace with a shape fault (`shapeFaults`, the
premise `FillOk`), kept out of the comparison with `checkVerdict`; a
fault of FillOK alone in faults.sh. Moved to Closed.

2026-11-24. 028-47 done: Frans decided A, no change (12:30); B and B2
stay on local branches of the study's clone, not on the public
repository. Moved to Closed, by an agent of lead-1124.

2026-11-24. 028-51 and 028-52 registered by an agent of lead-1124, from
028-47's findings F1 and F3 (Frans, 12:30): `maintain()`'s M1 stops
beginning iterations in a written database; CountGates' G4 fails ST6 at
C2's settings.

2026-11-24. 028-52 done by an agent of lead-1124 on the branch `028-52`:
G4's ST6 failed at C2's settings because the twin's cache table slots
grow with its drive's length while the emptied database's sit at the
tables' floor (4,096 maps of 16); the gate takes G5's limit, the larger
of twice the twin's and the floor. The database was right. Moved to
Closed.

2026-11-24. 028-50 registered by an agent of lead-1124 and taken: Frans
chose 028-45's option A (12:26), the count of a key with a key
transformation after it (RB-005); branch `028-50`.

2026-11-24. 028-50 done by an agent of lead-1124 on the branch `028-50`:
Db counts a transaction with a key transformation after its key
transformations, with the keys they gave
(`Db.checkDirtyNodesAfterKeyTransformations`); 028-45's known-fault test
turned around; RB-005 fixed on `main` for 2026.7. Moved to Closed.

2026-11-24. 028-45 done: its test landed, and the fault it found, RB-005,
is fixed by 028-50. Moved to Closed.

2026-11-24. 028-51 done by an agent of lead-1124 on the branch `028-51`:
`maintain()`'s M1 begins an iteration also when the next one's cut would
release 400 kB, the stream written since reclaim last stored its table;
F1 broke what the Javadoc of `maintain()` promises, registered as RB-006
(S4). Moved to Closed.

2026-11-24. 028-53 registered by lead-1124, from 028-51's report: an idle
database with live data keeps rewriting it under maintain().

2026-11-24. 028-53 in progress, by an agent of lead-1124 on the branch
`028-53`: the rewriting is M1's first rule, which rewrites the live
values of a database not written to in two sets in turn; a cost, not a
released bug. Found with it RB-007 (S4), the application's writes made
before the cut of an iteration that began within 400 kB of its cut
point, counted by neither rule. Options for the fix in the entry
(Frans: decision); the entry a directory with its probes.

2026-11-24. 028-49 done by an agent of lead-1124 on the branch `028-49`:
`items/034-releases/scripts/body.sh` makes the GitHub release's body from
the notes, every relative link absolute and each checked to answer 200;
`commit-b.sh` makes it and prints its check and `--notes-file` of it.
Moved to Closed.

2026-11-24. 028-19 done by an agent of lead-1124 on the branch `028-19`:
reclaim's pace with PE explained (the 6.8 % and the extra cuts came from
the nodes left out of the charge before 028-26; since, PE writes 0.935
of the old writer's bytes a put); the short way, the routing and the
inner nodes appended to by counts without live lists (the set test 1.04
times the old writer's, CCBench 1.00, the load 0.98), the same trees; gated, timing.sh against
2026.6 TIMING OK. Moved to Closed.

2026-11-25. 028-54 registered by lead-1125, from 031-01's revision: a
stop or a crash between a user record and reclaim's records after it
changes the stream on `main` (`MidCallProbe`); Frans: whether P2 covers
it.

2026-11-25. 028-55 registered by lead-1125, from `week.sh`: Churn's
`getTrans` refused a committed transaction's position; taken by an agent
of lead-1125.

2026-11-25. 028-55 done: `Db.getTrans` walked from the stream's first
position, inside a record, after a cut; RB-008 (S3, 2026.5 and 2026.6)
registered and fixed on `main`; moved to Closed.

2026-11-25. 028-56 and 028-57 registered by lead-1125, from Codex's
review of 028-55: a cut during `getTrans`'s walk refuses a kept
transaction (since 2026.5); a test that failed in Codex's sandbox.

2026-11-25. 028-56 done: a cut during `Db.getTrans`'s walk could expire a
kept large transaction; RB-009 (S3, 2026.5 and 2026.6) registered and
fixed on `main`; moved to Closed.

2026-11-25. 028-57 done: the test's timing, not the database; the test
takes either exception the start may throw; moved to Closed.

2026-11-25. 028-58 and 028-59 registered by lead-1125, from 031-03,
sections 9.1 and 9.2: `maintain()` leaves an emptied database at 790 kB
when its two stretches each stay below 400 kB; a stop between the
filler's put and delete leaves it live.

2026-11-25. 028-60 and 028-61 registered by lead-1125, from 031-02's
findings F1 (S2: after a kill, a zeroed tail over a meta block stops the
start) and F2 (an emptied database keeps 2 to 3 sd under `maintain()`);
both taken by agents of lead-1125.

2026-11-25. 028-58 done: on 2026.5 and 2026.6 the 790 kB are RB-006's and
RB-007's, no new released bug; on `main` RB-007's, and a rest of RB-006
that 028-51 leaves (two stretches each below 400 kB, 783 kB kept);
moved to Closed.

2026-11-25. 028-59 done: the filler left live by a stop or a crash is a
released bug of 2026.5 and 2026.6, S4 (the Javadoc says that it is
deleted at once), for the lead to register; 027-13, section 2,
corrected; moved to Closed.

2026-11-25. 028-61 done: the emptied database's stream is cut to below
400 kB; the rest is the file storage's last file, whose capacity was
chosen while the stream was large. Not RB-007 or 028-58; a fault of its
own against `Database.maintain()`'s Javadoc, which 031-03 does not end.
Moved to Closed.

2026-11-25. 028-62 registered by lead-1125, from 028-61: the fix of
RB-011, the Javadoc or the storage, for Frans.

2026-11-25. 028-60, part 1 done and landed: a meta block of zero bytes is
not valid, so a zeroed tail inside the last record is recovered; RB-012
(S2) fixed in part; part 2, zeros past a record's end, B1 to B3 for
Frans.

2026-11-25. 028-63 registered by lead-1125, from `week.sh`: the large
reclaim run's fresh fill at 10 million keys is 7.24 GB, 3.4 times
028-43's; taken by an agent of lead-1125.

2026-11-26. 028-63 done: the large reclaim run's fill depends on the
seed's key order, the same bytes at `40cb9ae9` and `main`; 028-43's seed
was one of the few local orders. The harness's data cap now scales with
the fill (8 L0 + 3 GB).

2026-11-26. 028-64 registered and taken by an agent of lead-1126, from
the aim that Frans set for `week.sh` (about 10 hours on F53, at most
12). Done: the large reclaim run and the large conformance set
run beside the other steps, each in a clone of its own, with the same
steps, seeds and sizes; about 6 hours estimated; no whole-run hang
guard (Frans). Moved to Closed.

2026-11-26. 028-65 registered by lead-1126, from 031-03, section 9.3: a
database not written to keeps several times its live values under
`maintain()`; a space cost, not a released bug (Frans). 028-63's row
moved to Closed.

2026-11-26. 028-62 decided by Frans (neither J nor S) and done by an
agent of lead-1126: `FileStream` gives a new file a tenth of the stream,
not a quarter; `Database.maintain()`'s Javadoc promises the 400 kB of
the stream; `FileStream`'s Javadoc states the disk's bound and the
backup by a copy of the files. RB-011 fixed for 2026.7. Moved to Closed.

2026-11-26. 028-66 registered by lead-1126, from 028-62's measurement:
the cut's deletes, one file at a time with a force of the directory
after each, lag further behind a fast writer with about three times as
many files.

2026-11-26. 028-67 registered by lead-1126, from 035-02, section 11: on
APFS a write cut by a kill can leave a deleted file's bytes within the
last stream file's length; a start refuses most such tails with unclear
messages and may first append up to 2 GB of zeros; options C1 to C4 for
Frans (C1 recommended now, C3 with the next stream-format change).

2026-11-26. 028-66 measured (branch `028-66`): a directory force per
deleted file keeps 1.3 to 1.6 times the stream on disk at 100 MB/s and
more, and slows a writer with no limit by about 40 % against the
quarter; a batch delete with one force keeps 1.03 to 1.05 and the
writer's speed, but breaks 011-07's order of deletes under the
power-loss model. Not landed; options A to C for Frans.

2026-11-27. 028-68 registered by lead-1127: the reclaim step reserve is
a setting outside the stream that changes its bytes; options A to C for
Frans (A recommended), decided with 031-06's landing.

2026-11-27. 028-69 registered by lead-1127, in progress: the internal
crypto code is removed (Frans); the record of the removal goes into
017-10's log. 028-60's part 2 lands after it, without its opt-out for
encrypted streams.

2026-11-27. 028-69: the internal crypto code removed on `main`
(`1809e04c`; `BEFORE COMMIT OK`), recorded in 017-10's log. New
databases' `created.txt` has no line "crypto key:". A database that an
earlier release encrypted is still refused, by its `created.txt`.

2026-11-27. 028-60, part 2, decided by Frans on 2026-11-26 (neither B1,
B2 nor B3 as written), made by an agent of lead-1126 (branch `028-60b`,
reviewed twice by Codex) and rebased on 028-69 by an agent of lead-1127
without its opt-out for encrypted streams (branch `028-60c`):
`FileStream`'s open leaves a run of zero bytes of at most 8 MB at the
end of its last file out of the stream, and its first append cuts it,
for every stream, on every system; nothing above it changed. RB-012
fixed for 2026.7. Moved to Closed.

2026-11-27. 028-60's part 2 landed (`ac33aa93`): RB-012 fixed on `main`
for 2026.7. 028-69 done with it. Moved to Closed.

2026-11-27. 028-70 registered by lead-1127, from Codex's third review of
028-60's part 2: a start that is refused after its recovery has written
changes the stream.

2026-11-27. 028-71 registered by lead-1127, from the independent review
of 031-06's prototype (F3): one step of at most 16 kB a commit keeps 36
times the live data under commits of 300 kB. 028-68: the same review ran
the step reserve's effect at its default (F7). 028-54: A1 is (e), which
leaves no record between a user's record and its maintenance; its
question for 033 stays open.

2026-11-27. 028-67 decided by Frans (15:50 to 16:02): C1 and C3, in
2026.7, built in 031-06's landing: a meta block holds its position and is
valid only with this database's ID; a record header holds a 24-bit
CRC-32C of the ID, its position and its fields; a tail that fails is
refused before anything is written. C2 after C3 is tested; C4 not taken.
Open until built.

2026-11-27. 028-68 decided by Frans (16:09): B, the reclaim step reserve
a constant, with a hook for tests only. Built in 031-06's landing, step
2 (branch `031-06-landing`); open until it lands on `main`.

2026-11-27. 028-54 done: P2 covers a restart after a stop; the crash
case is not promised (Frans). RB-013 (S4, 2026.5 and 2026.6) registered
in 033 (Frans, 17:12), fixed on `main` for 2026.7 by 031-06, one record
an action (`5b88cc80`). Moved to Closed.

2026-11-27. 028-68 done: built in 031-06's landing, step 2 (`615fad10`),
and on `main` with the merge of 031-06 (`5b88cc80`). Moved to Closed.

2026-11-27. 028-34: as it is in 2026.7, the API's question for a later
release (Frans, 16:45); the copy mark keeps `transactionInfo()` right on
records with copies (031-06).

2026-11-27. 028-72 registered by lead-1127, from the investigation of
BergDB's own long keys (031-06, section 8, O1).

2026-11-27. 028-73 registered by lead-1127, from the timing run on
`main` (the pause probe's load phase) and its bisection to `05fc573c`
(028-62); options (a) to (d) for Frans, (b) recommended.

2026-11-27. 028-72 investigated by an agent of lead-1127: no transaction
within L1 to L5 is refused by the action's 7/8 by Java's count (76.5 % at
worst, node size 8); the Lean's 19 a level is a looser bound of that
count; options A to G for Frans, A recommended. The entry became a
directory with its probes.

2026-11-27. 028-74 and 028-75 registered by lead-1127, from the
independent review of 031-06's landed diff (`review-main.md`, R3 and
R4): a commit's time after a restart against a time given to a reader;
the whole live data rewritten after one small put. Options for Frans;
(a) and (c) recommended.

2026-11-27. 028-66, option C designed and built (branch `028-66c`, not
pushed), from Frans's principle of the day: the cut's deletes a batch
with one directory force; a gap in `FileStream`'s files is taken at the
open, and a start refuses a stream whose first position is after
reclaim's cut, else its cut deletes the files before the gap. Sound;
the writer as fast as with the batch; for Frans: land C (028-66, 5.10).

2026-11-27. 028-66: Frans decided C with the rule of the files before a
gap (17:26). C ported onto `main` and the rule built (branch
`028-66-c-rule`, not pushed): a start deletes the files before a gap
only if each one's first meta block is the database's, else it refuses
before it writes or deletes. Open: the timing run on a quiet machine,
the review, the landing (028-66, section 6).

2026-11-27. 028-66 reviewed (land after the timing run) and the
review's findings R1 to R5 fixed: the power-loss trace's check of a
`CLOSE` force, no `created.txt` written by a refused start, the
refusals' messages, the stream contract's duty of an implementation,
`seekFirstPos` and the rule (028-66, 6.7). Open: the timing run, the
landing.

2026-11-28. 028-66 timed on a quiet F53 against `main` (6.8): C 113,580
transactions a second against 67,052, the disk 1.10 of the stream kept
against 1.62, 27 files against 63. Status: built, reviewed, timed;
landing.

2026-11-28. 028-76 registered by lead-1127 from `week.sh`'s apps-kill-cc
failure on `main`: a start refused a sound database whose first meta
block was recovery's fill (since 028-67's C3); fixed on `main`; for
Frans, the same fill as the first block of a file before a gap (028-66's
rule), (a) recommended.

2026-11-28. 028-71: the step sized by the commit's allowance is on
`main` since 031-06's landing, step 3 (`96daa4bb` to `cdc437b2`), with
its timing run; whether the entry is done waits for Frans (commits of
1 MB keep 18 times the live data, by the cap of 128 KiB a step).

2026-11-28. 028-77 registered by lead-1127 at Frans's request: whether
the stream's files stay strictly append-only, or a start may rewrite
the tail, on a model of what the storage's provider gives (the review
is 035-03); to be taken up after 2026.7's work is stable. 028-67's C2
is held until it is decided (Frans).

2026-11-28. Frans decided 028-73 (b), a floor of 1 MB for new files once
the stream kept reaches 4 MB; 028-74 (a), the limit stated in
`currentTime()`'s Javadoc and P2's draft; and 028-75 (c), a pass only
when the stream kept is a share and a floor over the live bytes (07:27).
None is on `main` yet.

2026-11-28. 028-71 and 028-53 closed by Frans (07:30): 028-71's step is
on `main`, with the limit under commits of 1 MB stated in 027-13;
028-53's RB-007 is fixed by 031-06, and the rewriting after one small
put is 028-75's. 028-67's finding that C3 does not cover nodes goes
with 028-77's review, not into 2026.7 (Frans).

2026-11-28. 028-78, 028-79 and 028-80 registered by lead-1127 from the
review of the start and recovery path (033,
`reviews/2026-11-28-start.md`): F1, a deleted copy of the database's own
bytes in the tail passes C3 (S1 on a storage of 035-02 after a restore
in place), for Frans with 028-77; F2, other bytes at a meta block's
position refuse a later start (S2), the smaller fix by default at
10:30; F3 and F4 (S4), a creation left as zeros and the zero tail's
bound, to an agent. 028-76 has the review's notes on its decided case.

2026-11-28. 028-70 done by an agent of lead-1127 (branch
`028-70-refuse-first`): the refusals of a start after the recovery's
first write listed, six checks, each of what the start reads; the
recovery's writes are held in memory until the last of them, and a
refused start writes nothing. Moved to Closed.

2026-11-28. 028-80 done: F3 and F4 of the review of the start, with
028-70's follow-up, landed on `main` (`d5aa1cf7`, `929537b5`,
`71cf993e`); F3 is RB-014 (033). Moved to Closed.

2026-11-28. 028-81 and 028-82 done: landed on `main` (`710ae35e`,
`49f3838c`, `cc848794`). Moved to Closed.

2026-11-28. 028-85 registered by lead-1127: a test of a directory
deleted after `stop()` failed once in `level3.sh` under load, 021-24's
window left open.

2026-11-28. 028-86 done by an agent of lead-1127: night.sh's failure of
count-gates on `16c64d9a`, G4's M5 (34 / 13), comes from `96daa4bb`
(031-06's pace), which moved the phases of the same 7 key nodes, each
within theta; G4's M5 takes G5's limit, the larger of twice the twin's
and the twin's plus 70. Moved to Closed.

2026-11-28. 028-87 done by an agent of lead-1127: G5's ST6 varies by
run (58,576 to 59,008 slots in 94 runs) with the timing of the capacity
controller's eviction during the fill; its pass cannot vary, as ST6
fails only with fewer than 9 maps without a table, against 408 or more.
The gate prints those maps; its header states the range. In Closed.

2026-11-28. 028-72, A done (Frans: A, by default at 10:00): 024-17's
count with q is 10 nodes a level at node size 14 since 028-21, not 9;
031-06, sections 3 and 9, and 024-17 state that by Java's count the
worst transaction within L1 to L5 takes at most 76.5 % of the action's
7/8; `DagTester.testDirtyNodeBoundOfTheWorstPath` checks Java's count on
the worst path against 14, 10, 8 and 8 a level. B (the Lean's count
restated) waits for the next change of `Bound.lean`.

2026-11-28. 028-84 registered by lead-1127: the documents of 031-08's
UA-4 to UA-7 and 031-02's N1; built on the branch `docs-1128`.

2026-11-28. 028-83 registered by lead-1127 from 031-08, part A (UA-2,
UA-8, UA-9, UA-10 and e3 seed 101's FAIL); built on the branch `028-83`
by an agent of lead-1127.

2026-11-28. 028-85 done by an agent of lead-1127 (branch `028-85`, to
land): the failure was 021-24's window, shown with a delay in
`FileStreamIo.open()`; the test now deletes the directory after
`close()`, as `stop()`'s Javadoc says, and
`testDirectoryReplacedInTheWindowAfterStop` holds the old database in
the window and checks the documented outcome. Moved to Closed.

2026-11-28. 028-75 designed: (c) needs live bytes that each record
carries, a change of the record format, Frans's; the options (c1) to
(c3) and (c0), (c1) recommended (the live bytes in each record's
header, with M2', k = 2 and a floor of 400 kB), measured with a
prototype. Not built. The entry is a directory since.

2026-11-28. 028-83, 028-84 and 028-85 done: on `main` (028-83
`bf949633` to `67d12ae3`; 028-84 `e1438691`, `04307225`; 028-85
`7642c84a`, `3a57aea7`). 028-79's fix (1) and the review's two shapes on
`main` (`2d4d178a`, `b9624ea1`, `01232710`); the second review's
residual (E) open, its fix on the branch `028-79-e`. Moved to Closed:
028-83, 028-84.

2026-11-28. 028-66 (C with the rule, e848c58f..5f867e08, 8a0897cf),
028-73 ((b), 68a26a38) and 028-74 ((a), 1a136a9c) done: on `main`.
Moved to Closed.
