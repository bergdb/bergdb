012-bergdb-c
============

Created 2026-10-27 by Frans Lundberg. Status: open.

BergDB's Core in C: a clone of the Core (`bergdb.core` and what `Db` needs
of the Core Layer) written in C, for F53 first. Its API corresponds to the
public methods of `Db`, and its stream is Java's, byte for byte: a
database made by Java opens in C, and one made by C opens in Java. 006-08
found such a clone feasible; this item plans it and does it.


Files
=====

* [01-overview-plan.md](01-overview-plan.md). 012-01, the overview plan:
  the goal and what "done" means, what the clone ports and leaves out,
  the stream format and what "identical" takes (checked against the Java
  code), the C API, the language, the build and the tests, the tasks
  012-02 to 012-16 with their order and milestones, how the work runs
  unattended, the risks, and the decisions for Frans.

The tasks, one plan each (goal and "Done when", what to read, the work,
the tests, notes, progress), in the order of 012-01, section 8:

* [02-stream-format.md](02-stream-format.md). 012-02, the stream format
  written down, field by field, with Java's scanner and the determinism
  audit; the file becomes the format document.
* [03-c-api.md](03-c-api.md). 012-03, the C API: `bergdb.h` from `Db`'s
  public methods (45 since `fd8f513`).
* [04-c-project.md](04-c-project.md). 012-04, the C project: layout,
  build, test framework, gate, Java's semantics in C, the first modules.
* [05-cross-harness.md](05-cross-harness.md). 012-05, the cross harness:
  the workload format, Java's runner and dumper, the workloads,
  `cross.sh`.
* [06-stream-reader.md](06-stream-reader.md). 012-06, the stream reader
  and C's scanner.
* [07-index-nodes.md](07-index-nodes.md). 012-07, the index nodes: klongs,
  key, value and top nodes, pointers.
* [08-dag-and-replay.md](08-dag-and-replay.md). 012-08, the Dag and reads;
  Java's databases read by full replay.
* [09-write-path.md](09-write-path.md). 012-09, the write path: creation,
  `execute`, the take, the record writer; Java's bytes.
* [10-startup.md](10-startup.md). 012-10, startup and recovery; restarts,
  crashes and turns between Java and C.
* [11-reclaim.md](11-reclaim.md). 012-11, reclaim and the cut (Level 3).
* [12-memory-budget.md](12-memory-budget.md). 012-12, the node table and
  eviction to a budget (Level 4).
* [13-api-complete.md](13-api-complete.md). 012-13, the rest of the API,
  and durability.
* [14-robustness.md](14-robustness.md). 012-14, robustness and scale.
* [15-performance.md](15-performance.md). 012-15, speed, memory and size
  against Java.
* [16-report.md](16-report.md). 012-16, the report and the next steps.


Log
===

2026-10-27. Created the item, at Frans's request ("Create item
012-bergdb-c. The item is for a project to create a clone of the Core of
BergDB written in C. The planning starts now. The implementation is
intended to start tomorrow. It should run unattended as far as
possible."), with 012-01 written by Claude (Opus 5.5, Claude Code) while
Frans was away, beside 006-09's unattended work and without disturbing it.
Then, as Frans named it the next step, the task plans 012-02 to 012-16,
drafts for his approval with 012-01. Nothing else is written yet: no
code, no change outside this item and its index line. 012-01's section
11 holds the decisions D1 to D7 for Frans.

2026-10-28. Frans's decisions on 012-01, section 11: D1a, D2a, D3a, D4a,
D5 as recommended, D6b; and D7, "When I say so. I plan to start a new
Claude Code session for this. It will be the conductor that can work
unattended with 012." His two comments are answered in 012-01: the test
clocks, which the first version left out ("To create equal streams, we
need deterministic time"), are ported, with where the stream's times come
from (section 4.4); and the plan for allocating and freeing memory, asked
for in place of "freed by hand" (section 4.5). Section 9.1 says how the
conductor starts. The task plans that these touch were brought in line:
012-02 to 012-05, 012-07 to 012-09, 012-12 and 012-14. Found on the way:
`SystemClock` does not keep its promise of strictly increasing times
(012-01, 4.4), harmless as `DbClock` makes transaction times increase;
for a 005 entry when the work starts.

2026-10-28, later. Frans changed D1: "Keep the C code in
items/012-bergdb-c/c/ indefinitely for now." 012-01, 012-04 and 012-16
follow: no move at 012-16. At his request, the conductor's prompt is at
the top of 012-01.

2026-10-28, 12:42. Asked whether the plan is ready for long unattended
work, Claude brought it up to date with the morning's Java: the paced take
in `main` (`f89846d`, 007-07), which changed every stream and decides with
doubles; 005-52's new methods of `Db`. And added to 012-01, section 9: the
unattended machinery of 013-02 (state file, check-ins, watchdog, the same
permission mode as the coordinator), pacing by the usage windows, a rule
for a stuck task, and the open question of who commits while a
coordinator owns the commits.

2026-10-28, 13:34. The review of the plans before the conductor starts
(Frans, 13:05: wait for the Java changes that affect the stream, review,
then the conductor), against `main` at `f589ba3`. Brought in line with
005-53 and 005-52 (`fd8f513`): `setStartupDistance` writes nothing for the
value in force, and `Db` has 45 public methods, with a setter and a getter
of the cache size (012-01, 012-03, 012-05, 012-09, 012-12, 012-13). Also:
the take in 012-02's outline, the skip below the cut in 012-11 (005-62),
the ordinal bound in 012-07, no raw output in the repository (012-15),
and the task plans marked approved with 012-01 by Frans's go. Every Java
class, member, path and subitem that the plans cite was checked to exist.
The conductor waits for `/Users/f/fl/bench/012/review-done`.

2026-10-28, 13:43. The implementation started. Frans gave the go by
starting the conductor (the session f1-0f) with the prompt at the top of
012-01, which approves the task plans 012-02 to 012-16. The Java reference
of the first tasks: `main` at `404d2ee` (`java/` as of `fd8f513`). The
conductor's state is in `/Users/f/fl/bench/012/state.md`, with check-ins
every 20 minutes from 06:17 to 21:47 and the watchdog until 07:00 on
2026-10-29. The usage level was tight (the week 25 points ahead of its
time), so at most two subagents at a time, at high effort (012-01, 9.2):
012-02 and 012-04 started at 13:47, each in a scratch clone under
`/Users/f/fl/bench/012/`; 012-05 follows once 012-02's scanner exists, then
012-03. Tonight 006-10's quiet block holds: nothing CPU-heavy of 012 after
21:45, the conductor idle from 22:30 to 06:15.

2026-10-28, 14:18. 012-04 done (`40aa5b8`): the C project in `c/`, its
build, the C gate (`C BEFORE COMMIT OK` in 3 s), the rules of Java's
semantics in C, and the first modules (bytes, Fletcher-16, klongs, keys,
positions, the allocator) with 81 unit tests, Java's own tests of those
classes ported and 957 of Java's vectors agreeing. From 13:55 the agents
run at Frans's higher effort: at least xhigh, max for the hard tasks
(012-02's document is at max).

2026-10-28, 15:21. 012-05 done, with 012-02's scanner: Java's side of the
cross harness in `c/test/cross/` (the workload format, `Run`, `Dump`,
`Gen`, `Export` of `StreamDigest`'s 36 configurations and modes and of
`CoreSame`, `cross.sh` with its quick, full and scale sets and the `C=DIR`
interface for C's tools) and `StreamScan`, Java's scanner ("streamscan
1"). Java against Java in two JVMs, in the main tree: `cross.sh full`
passed (278 workloads, 1,262 crash cuts, 6 runs in turns, 0 differences, a
planted difference found; 788 s), and the C gate runs the quick set (C
BEFORE COMMIT OK, 23 s). No Java finding: every pair of runs gave the same
bytes. 012-02's document is under way (sections 1 to 13 drafted). The
5-hour usage window reached 86% at 15:01: the agents paused until its
reset at 15:50.
