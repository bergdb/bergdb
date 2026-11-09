012-bergdb-c
============

Created 2026-10-27 by Frans Lundberg. Status: done.

BergDB's Core in C: a clone of the Core (`bergdb.core` and what `Db` needs
of the Core Layer) written in C, for F53 first. Its API corresponds to the
public methods of `Db`, and its stream is Java's, byte for byte: a
database made by Java opens in C, and one made by C opens in Java. 006-08
found such a clone feasible; this item plans it and does it.

**A port of Java release 2026.2.** The C code in `c/` matches BergDB's
release 2026.2 (the tag `release-2026.2`), the Java it was brought up to
on 2026-11-05 (015-02). It does not follow Java's changes after that
release, and its cross tests compare with that release's Java
(`c/readme.md`, "Which Java"). The item is meant to stay stable as it is
(Frans, 2026-11-05): a port of a later release would most likely be done
in another item or in another repository, not here.


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
* [17-lto.md](17-lto.md). 012-17, link-time optimization in the release
  build (012-15's first proposal).
* [18-update-to-2026-3.md](18-update-to-2026-3.md). 012-18, a study of
  what updating the C clone to Java's release 2026.3 takes: the Core's
  changes since 2026.2 by kind, which the clone needs, the faults it shares,
  the tests that would show it matches, a plan and its size; feasible in
  about a day. Frans, 2026-11-09, 10:08: the update is a new item, 022,
  and 012 stays the port of 2026.2.


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

2026-10-28, 16:25. 012-02's document written and checked, its review
(step 5) still to come: the stream and the directory field by field, what
decides the bytes (the take replayed from the scans alone with 0 errors
over 299,401 takes), the determinism audit, the differences from the text
of 2015, the scanner's format. The audit found four real dependences:
C1 and C2 on the files, C3 and C4 on the bytes after a restart. Registered
as 005-70 (the STM's `KeyModSet` is empty after a start, a correctness
bug), 005-71 (`DbClock`'s last read time) and 005-72 (the files after a
physical cut depend on timing); C follows Java until they are fixed. Two
questions for Frans in 012-02, section 13 (Q1, how cross tests compare
after reclaim's cuts; Q2, the restart findings), neither blocking before
012-10 and 012-11.

2026-10-28, 16:25. 012-03 done: `c/include/bergdb.h`, the C API, from
`Db`'s 45 public methods (35 with a C counterpart, 10 left out with their
reasons), with the rules of ownership, errors and the clock in its top
comment, and two examples (C's `CoreDemo` and a `getMany` with a prefix)
that compile; their comments hold Java's output for the same calls. The
tables and the decisions D1 to D16 in 012-03. So M1 is reached (012-01,
section 8): the format written down, the API designed, C builds and its
tests run, and Java's reference outputs exist; 012-02's review is the
part of phase A still to come. Phase B runs: 012-06 (the stream reader)
and 012-07 (the index nodes).

2026-10-28, 17:06. 012-02 done: its review by a second agent at max
effort (section 15) found 21 points, 2 errors (a retain duration of
forever lets an iteration in progress go on with its steps and table; a
leaf's key klong never names a delete node), 5 omissions and 14 minor,
all fixed in the document; findings C1 to C4 hold; an independent replay
from the scans agreed on 299,401 records. Phase A is done. Java's slips
found on the way are 005-73 to 005-75.

2026-10-28, 17:07. 012-06 done: the stream reader in C (`err`, `plat`,
`stream`, `meta`, `rstream`, `snode`, `strans`, `nstream`) and the first C
tool, `bergdb-scan`, which prints exactly what Java's `StreamScan` prints:
in the main tree, `cross.sh full` with C as side B passed (278 workloads,
1,262 crash cuts, 498 corrupt variants, 6 in turns, 0 differences; 1,108
s), and the C gate runs C's scanner under the sanitizers in its quick set
(C BEFORE COMMIT OK, 35 s; 100 unit tests). Corrupt input is refused where
Java refuses it; Java's parser on corrupt sizes is 005-74.

2026-10-28, 17:31. 012-07 done: the index nodes in C (`obj`, `node`,
`handle`, `knode`, `tnode`, `vnode`, `opdata`, `topds`, `nwrite`), ported
from `dag` with Java's names in comments, and the memory design of
012-01, 4.5 (a counted head for every index object and handle, the
holders listed against Java's fields, a pending list freed at safe
points). Java's `KeyNodeTester` (45 of 46), `TopTester` and the node
tests ported; Java and C operation by operation agree (480 key node
operations, 196 super roots, 68 `findRoot`s); every node of 012-05's full
set, 55,330,264 nodes in 5,056,194 records, parsed by 012-06's reader and
written again gives its own bytes. C BEFORE COMMIT OK (39 s; 185 unit
tests). The times 17:06 and 17:07 above were first written as 17:10.

2026-10-28, 18:10. 012-09, part 1 done, split from 012-09 by the
conductor so that it ran beside 012-07: what of the write path needs no
index nodes and no Dag. `DbClock` and the clocks, `KeyModSet`, the take
(`TransSeq`, `StartupPos`), the append path (`FileStream`'s files, names,
sizes and open rule, the lock, the buffer, `F_FULLFSYNC`;
`RecoverableStream`'s appends with meta blocks) and `StringMap`. Checked
against Java: the take replayed from C's parsed records with 0 errors
(331,193 takes in the full set, 866,930 in its crash variants); every
record of 232 full-set directories appended again through C gives Java's
directory byte for byte (916.7 MB; the 46 that reclaim cut are skipped,
for 012-11); 293,331 transaction times through C's `DbClock` equal. The
C gate has a new step, `write`. Frans, 17:50, through the Unattended
Lead: "tonight 012 (session f1-0f) has priority on F53. The quiet block
becomes flexible." So 012 goes on through the night, with gaps handed to
006-10's timed steps.

2026-10-28, 21:40. 012-08 done, and with it milestone M2: C reads Java's
databases. The Dag (puts and deletes with Java's splits and new top
nodes, `getOne`, `dirtyNodeBound`), `getMany` in both directions with
every stop condition, `getTrans` with Java's refusals, a full replay of
the stream, and `bergdb-dump`. C's dumps equal Java's on every database of
012-05's sets without reclaim (176 workloads, both sides) and on all
1,262 crash cuts; Java's `DagTester` and 29 of `DbTesterGetMany`'s 33
ported; Java's Dag and C's agree on 960 transactions. In the main tree,
with 012-09 part 1: `cross.sh full` with C's tools OK (279 workloads, 0
differences; 1,437 s), C BEFORE COMMIT OK (51 s; 286 unit tests). Phase
C runs: 012-09 proper (execute, Java's bytes) and 012-10 part 1
(recovery, bounded startup's reads), side by side.

2026-10-28, 22:16. 012-09 done: C creates databases and executes
transactions with Java's bytes, and Java opens C's databases. `Trans` and
its builder, `TransNodes`, the record serializer, `execute` with every
check before the go point and P7 after it, the got-dirty lists, ids and
vpos, `topPos`, the creation's 264 bytes, `setStartupDistance`, the
implementation of `bergdb.h` (`db`, `api`) and `bergdb-run`, C's workload
runner. In 012-09's clone `cross.sh full` with C's tools passed twice:
C ran 104 workloads (`StreamDigest`'s Level 2 configurations in the plain
and reads modes, the 100 MB one included, `CoreSame` plain, 84 random
seeds, and new workloads for a decrease of the startup distance and a
`now` that moves a time), all byte for byte equal to Java's, and Java's
dump with its audit on started each of C's directories and equals C's;
300 more seeds and a million keys gave 0 differences; no byte difference
was met at any step. Workloads with restarts or reclaim still run on Java
until 012-10 and 012-11. In the main tree, with the same `c/`: C BEFORE
COMMIT OK (72 s; 304 unit tests, 4 functional tests).

2026-10-28, 23:26. 012-10 done, and with it milestone M3: Levels 0 to 2
in C. C starts existing databases as Java does (`recover`, `starter`,
`ncoll`, `ntable`, `lmap`, `sdb`): recovery with its fill, the start's
checks, the startup section, Rule R, rule 4 by position, the rerun that
rebuilds D and the take's state, and loads on demand. Checked against
Java: all 1,262 crash copies of the full set recovered to Java's bytes; a
probe comparing every start (D's checksum, the node table, the canonical
objects, the loads, every file read) matched on 482 directories and the
1,262 cuts, with equal reads (441,126 reads, 438 MB, 30,828 loads on both
sides); C's runs of the 241 workloads without reclaim gave Java's files
byte for byte, restarts included (`l2-every1`: 399 restarts), with the
runs in turns and the runs after each crash; a million keys with a
restart, equal files. `cross.sh full` with C's tools OK in 012-10's clone
(343 workloads; 1,632 s). Earlier tonight (22:21) the 10M-key scale set:
C's dumps of the two 10M-key databases equal Java's. In the main tree:
C BEFORE COMMIT OK (98 s; 329 unit tests, 7 functional tests). Java's
`DbStarter.validateTransactions` checks nothing: 005-75.

2026-10-29, 02:14. 012-11 done: reclaim in C (Level 3), with restarts, in
turns and after crashes. `reclaim` ports Java's `Reclaim` line for line
(iterations, steps, the touch, the step reserve, the table in
`StringMap`'s order, safe positions, the cut and the first available
time and position); the front files deleted as `FileStream` and
`CutStream` do; the table restored at a start; reads before the cut
refused; Java's maintenance follower. `cross.sh` compares workloads with
reclaim from the decided cut (012-01, 3.2 point 8; 005-72's option A),
and C now runs every workload of the sets. `cross.sh full` with C's tools
OK in 012-11's clone: 446 workloads (181 with reclaim, all run by C),
1,368 crash cuts, 498 corrupt variants, 6 in turns, 0 differences (1,751
s); by hand 416 more workloads, with and without restarts; every one of
11 mutations of reclaim found. In the main tree: C BEFORE COMMIT OK (130
s; 340 unit tests, 9 functional tests). For Frans (11-reclaim.md, 6.4):
with no thread, C frees a decided cut's disk only at the next sync or
open; recommended, C forces the stream itself when a cut is pending.

2026-10-29, 03:17. 012-12 done, and with it milestone M4: Levels 3 and 4
in C. Index nodes and values not pinned are evicted to the budget (Java's
cache size indicator) at the calls' ends, a deterministic CLOCK after
Java's capacity controller, and loaded again from the stream; the node
table's bytes are the allocator's exact counts; the setter evicts at its
own end. The bytes never change: `cross.sh full` with C's tools OK in
012-12's clone with 1,784 budget runs, from a few kilobytes to unlimited
(446 workloads, 1,368 crash cuts, 498 corrupt variants, 0 differences;
2,544 s). Larger than memory: a million keys (1.2 GB on disk) at a 4 MB
budget give Java's reads and files byte for byte, the resident bytes never
above the budget plus what is pinned (at most 3,999,972), 113 MB of RSS
and 27.9 s against 210.5 MB resident without eviction (Java's run: 974 MB
RSS, 40 s; timed beside other work, so rough). In the main tree: C BEFORE
COMMIT OK (150 s; 345 unit tests, 11 functional).

2026-10-29, 04:00. 012-13 done: every one of `bergdb.h`'s 33 functions
implemented with a functional test (the debug print and check last);
the 13 status values of `Db`'s getters equal Java's at 9 points of a
sequence with every setter, reclaim, sync and a restart; durability
written in `c/readme.md` and tested by killing the process after execute,
after sync, in a record's write and at random moments; close frees
everything. C's `CoreDemo` prints what Java's `CoreDemo` prints, each on
a new directory and on the other's database, and the gate runs both
examples. A guide in `c/readme.md`. Merged with 012-12: `cross.sh full`
with C's tools on the merged tree OK (446 workloads, 1,368 crash cuts,
498 corrupt variants, 6 in turns, 1,784 budget runs, 0 differences;
2,240 s); C BEFORE COMMIT OK (150 s). Questions for Frans: 13-api-complete
Q2 (a closed handle ends at the close, as `fclose`; implemented, as
recommended) and 11-reclaim Q1 (forcing a pending cut).

2026-10-29, 05:06. 012-15 done: speed, memory and size against Java on
F53, the same workloads through `bergdb.h` and Java's `Db`, medians of
three runs in turns on a quiet machine (15-performance.md). C writes at
1.01 to 1.31 of Java's rate, reads at 0.73 to 0.97 in memory and 0.33 to
0.68 under small budgets, starts 1.9 to 2.4 times faster (10M keys warm:
0.99 s against 2.42 s at 50 MB, 4.55 s against 10.3 s at 200 MB), needs
3 to 7 percent less memory per key, and appends the same bytes per put.
16,146 lines of C (006-08's estimate: 11,200 to 17,300), 196 kB of
machine code at `-O2`. Proposals that keep the bytes, not applied:
`-flto` (+15 to +34 percent on every figure), a bounded eviction sweep.
And 012-01's done item 7: the 10M-key scale set with C writing side B,
`cross.sh scale C=build/release` OK, the same bytes as Java's, each
side's dump of both databases equal, Java's with its audit on (257 s).

2026-10-29, 06:14. 012-14, a first pass (05:00 to 06:20; the task stays
open): 1,800 random workloads over wide parameters, 916 with reclaim,
with 2,652 crash cuts and 3,600 budget runs, all equal to Java's; long
runs up to a million transactions with 50 restarts, Java's bytes, no
sanitizer report, a leak in the `bergdb-run` tool fixed; gcc 16 passes
the tests without `-Werror`; 2,199 starts of corrupt variants, refused as
Java refuses them but for a flipped bit in a record's time, where Java's
start throws an `Error` and C aborts (005-75). Java findings added to
005-74 and 005-75. 012-16 has an interim report (section 0) with the
points for Frans to decide.

2026-10-29, 07:35. Frans's answers to the conductor's morning list: 005-70
later; 012-11's Q1 as recommended (C forces the stream when a cut is
pending); 012-13's Q2 no action (the handle ends at the close, as
implemented); D6b changed: "Do not move the format document", so 012-02
stays in the item and `docs/` gets nothing; 012-14's flipped time no
action now. "Continue with 012 until it is finished. Run agents with Opus
5.5 High to preserve usage." (Recorded first, at 68b55e6, against the
wrong list; corrected here.)

2026-10-29, 09:50. 012-11's Q1, option B, as Frans decided: C forces the
stream itself when reclaim has decided a cut that is not yet durable, one
force per cut, so that the cut frees disk without the application's sync.
In the million-transaction run without syncs C's directory now peaks at
25.2 MB (before: 206 to 213 MB; Java: 34.2 MB); the bytes are unchanged.
In its clone: C BEFORE COMMIT OK (167 s, 07:48) and `cross.sh full` with
C's tools OK (446 workloads, 1,357 crash cuts, 498 corrupt variants, 6 in
turns, 1,784 budget runs, 0 differences; 2,468 s). In the main tree the
gate passed with macOS's `leaks` replaced by a stand-in that runs the
programs without a leak check (192 s): since about 08:30 `leaks --atExit`
hangs on F53 for every program, even a trivial one (a machine problem,
for Frans).

2026-10-29, 10:49. 012-14 done: power loss through an I/O seam in the
test build (5,756 power-loss images of C's runs recovered by C as by Java,
2,753 of Java's own, no acknowledged byte lost), allocation failures in
turn (5,991 runs, 0 bad; a short version in the gate), the eviction lag
fixed (`maxOver` 0), exception names as Java's, a read's NOMEM refused
instead of failing the database, gcc 16 without warnings in the library
(by hand, `test/stress/gcc.sh`), and the 10M-key workload at a startup
distance of 200 MB in Java, C and turns, byte for byte. `cross.sh full`
with C's tools OK on the tree merged with main (2,710 s); C BEFORE COMMIT
OK (167 s), with the `leaks` stand-in (macOS `leaks` still hangs).

2026-10-29, 10:49. 012-16 done, and with it 012: status done. The report
is 012-16, section 0: 012-01's "Done when" item by item with its
evidence, the milestones, the departures from Java, what the port found
in Java (005-69 to 005-75), the points for Frans, the code's place and
next steps, and how the work was done (section 0.7: the timeline, the
prompts, the plans, Claude Code and Opus 5.5 as used, the effort per
task, the usage). The C code stays in `c/`; the format document stays
012-02.

2026-10-29, 12:36. Frans on keeping C in step with Java (012-16, 0.6):
"No. For now I want C to be a separate project. Keeps testing, scripts
and everything in 012. Tests can start manually. Good for now." So the C
gate is not added to `night.sh` or to Java's gate; C's tests run by hand
(`c/before-commit.sh`, `c/test/cross/cross.sh`).

2026-10-29, 12:41. Frans on 012-02's Q1: "(a) is good as long as there is an item in 005 to consider (b)". A is what the cross tests do since 012-11; 005-72 stays open for B.

2026-10-29, 12:45. Frans on 012-02's Q2: "I confirm (a)." 005-70 and 005-71 stay
open for the Java fixes; C does as Java.

2026-10-29, 12:51. 012-17 added at Frans's request ("Just add subitem 17
for now."): link-time optimization in the release build, 012-15's first
proposal; a plan, not started. 012's status is open again while it waits.

2026-10-29, 15:27. 012-17 done: the release build links with `-flto`
(`build.sh`; `LTO=` builds without). The semantic flags need nothing at
the link: their effect is in the bitcode (`c/readme.md`, section 1). One
unit test made robust against the optimizer's wider view
(`mem_too_large`), and the gate's rule of no global state reads the
bitcode's symbols. `cross.sh full` with the release tools OK (2018 s); C
BEFORE COMMIT OK with macOS's `leaks`. Gains of `-flto` (1M and 10M keys,
in turns): writes 1.24 to 1.38, reads 1.08 to 1.23, under a 16 MB budget
1.23 to 1.24; the library 20 percent larger, `core_demo` 5 percent.

2026-10-29, 15:33. 012-17 merged into `main` (`ae4aaf9`), its gate there
`C BEFORE COMMIT OK (180 s)` with macOS's own `leaks`; 012's status done
again. The gate with the real `leaks` on `44332aa` (14:01 to 14:04, Frans
had enabled developer mode): `C BEFORE COMMIT OK (172 s)`, 0 leaks in
unit-release and func-release. 012-16 restructured at Frans's request:
the report is the whole file, sections 1 to 8 (section 0 and the plan's
stubs gone; the log's earlier "section 0" means sections 1 to 8 now),
with Frans's answers beside each question, the sizes, and 012-17's
figures.

2026-11-05. The C clone follows release 2026.2 (015-02; Frans: C matches a
release, not the Java of the day): 005-79's integers in the take, reclaim
and eviction, 005-69's clock, 005-73's F1 and F4, the checks of 005-74,
005-75 and 015-07, and the doubles check in the gate. The cross harness
compiles the release's source zip by default (`JAVA_REF`, `c/readme.md`).
The work and its evidence are in 015-02.

2026-11-09. 012-18, the study of an update to 2026.3, by coord-1109's
agent; the update itself is item 022 (Frans, 10:08).
