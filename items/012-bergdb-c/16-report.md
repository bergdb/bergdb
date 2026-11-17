012-16. The report
==================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg, as the plan of 012's report. Written by the conductor
(session f1-0f): an interim report at 05:08 on 2026-10-29, completed at
10:49 after 012-14, with section 8 on how the work was done at Frans's
request; brought up to date and restructured on the afternoon of
2026-10-29 (Frans's later answers, the gate with the real `leaks`, the
sizes, 012-17, done at 15:27). **Status: done** (2026-10-29, 10:49;
updated 15:45).
Phase E (012-01, section 8). Effort: high. After: 012-14, 012-15.

The plan, approved with 012-01 by Frans's go (012-01, 9.1), asked for:
what works, item by item, with its evidence (section 2); speed, memory
and size (3); the departures from Java (4); what the port found in Java
(5); where the format document lives, the code's place once 012 is done,
and the next steps with options and costs (7); 012's log and
`docs/log.md`'s entry (in 012's `readme.md` and in `docs/log.md`). Its
other sections (what to read, the work, tests: none, notes, progress)
are removed; this report is their result.


# 1. In short

BergDB's Core runs in C: Levels 0 to 4, every byte equal to Java's, and
each implementation opens the other's databases. 012-02 to 012-17 are
done: the clone itself (to M4) in 13.5 hours of unattended work from
Frans's go, and 012-02 to 012-16 in 21 hours (section 8). The C code is in
`c/`: about 54,000 lines of code, 22,000 of them the database itself
(section 3). It is built and gated by `c/before-commit.sh` (`C BEFORE
COMMIT OK`, about 150 to 190 s); `c/readme.md` has the guide. 012-17,
added afterwards at Frans's request, made the release build link with
`-flto`: 1.08 to 1.38 times faster, the same bytes (section 3).


# 2. What works: 012-01's "Done when", item by item

1. **Java to C.** Every database of the cross sets opens in C and reads
   as in Java: in `cross.sh full` all 892 side-B dumps are C's (latest
   state, `getMany` both ways, `getOne` at sampled times, `getTrans` of
   every transaction), equal to Java's (012-13's final run, on the merged
   tree of 012-12 and 012-13: 446 workloads, 1,368 crash cuts, 498 corrupt
   variants, 6 runs in turns, 1,784 budget runs, 0 differences, 2,240 s).
   C's startup equals Java's read for read (012-10: a probe compared D,
   the node table, the objects, the loads and every file read on 482
   directories and 1,262 crash cuts). Since 012-11's Q1 the full set has
   1,357 crash cuts (a reclaiming workload's cuts start at C's durable
   length, which the forced cut moved); its last run, with the release
   build's tools at `-O2 -flto`, passed (012-17, 2,018 s).
2. **C to Java.** Java starts each of C's databases with assertions and
   its audit on (`Dump -audit 1`), and its dump equals C's: every
   workload of the sets, and the 10M-key database.
3. **The same bytes.** C runs every workload of the sets (side B's 446
   runs all C's since 012-11), and its files equal Java's: restarts
   (`l2-every1`: 399 restarts), runs in turns between Java and C,
   continuing after crash cuts, eviction budgets, and reclaim, compared
   from the decided cut (012-01, 3.2 point 8). Beyond the sets: 300 seeds
   and a million keys (012-09), 416 reclaim workloads (012-11). No byte
   difference was met at any step of 012-09; the mutations tried in
   012-09 and 012-11 were all found.
4. **The API.** `bergdb.h` (012-03): 35 of `Db`'s 45 public methods have
   their C counterpart in 33 functions, the other 10 are left out with
   reasons; each function has a functional test (012-13). C's `CoreDemo`
   prints what Java's prints, on its own and on Java's databases; the
   gate runs it.
5. **The levels.** 0 and 1 (012-07, 012-08), 2 (012-09, 012-10), 3
   (012-11), 4 (012-12).
6. **Quality.** The C gate: both builds with `-Werror` (C17, Apple clang
   21, `-Wconversion`), 347 unit tests, 25 functional tests, the
   examples, the quick cross set, under AddressSanitizer and
   UndefinedBehaviorSanitizer, `leaks` on the release build, the
   allocator's count 0 after every test, allocation failures in turn
   (5,991 runs in 012-14, 0 bad; 379 in the gate). The deep set passes
   (item 1). Beyond it (012-14): 1,800 random workloads, power loss
   through an I/O seam (5,756 images of C's runs and 2,753 of Java's,
   recovered alike, no acknowledged byte lost), long runs to a million
   transactions, gcc 16 without warnings. From about 08:30 to 14:00 on
   2026-10-29 macOS's `leaks` hung on F53 for every program (developer
   mode off), and the gates of those hours ran with a stand-in that
   skips only the leak check. Frans enabled developer mode at 14:01; the
   gate on `0935005` with the real `/usr/bin/leaks` then passed (`C
   BEFORE COMMIT OK (172 s)`, 14:01 to 14:04): unit-release (346 tests)
   and func-release (25 tests) both "0 leaks for 0 total leaked bytes".
   With 012-17's `-flto` in the release build: `C BEFORE COMMIT OK` in
   its clone (177 s) and again in `main` (180 s), with the real `leaks`.
7. **Scale.** `cross.sh scale` (10M keys) with C writing side B
   (2026-10-29, 05:02): the same bytes as Java's, each side's dumps of
   both databases equal, Java's with its audit (257 s). C at a 4 MB
   budget on a million keys (1.2 GB on disk): Java's bytes and reads,
   resident at most 3,999,972 bytes (012-12).
8. **Measured**: section 3.
9. **Reported**: this report.


# 3. Speed, memory and size

**Speed and memory at `-O2`** (012-15, `15-performance.md`; medians of
three, on a quiet machine): C writes at 1.01 to 1.31 of Java's rate,
reads at 0.73 to 0.97 (in memory) and 0.33 to 0.68 (small budgets),
starts 1.9 to 2.4 times faster (10M keys, warm, 50 MB: 0.99 s against
2.42 s), and needs 3 to 7 percent less memory per key.

**With `-flto`**, the release build since 012-17 (`17-lto.md`, section 6;
C with `-flto`, C at `-O2` and Java in turns, medians of three, the
stream lengths equal in every run). Operations a second, except the open:

| | 1M: `-flto` | gain | C/Java | 10M: `-flto` | gain | C/Java |
|---|---:|---:|---:|---:|---:|---:|
| load | 449,582 | 1.38 | 1.33 | 194,477 | 1.29 | 1.42 |
| batch | 299,255 | 1.25 | 1.27 | 137,670 | 1.26 | 1.38 |
| single | 236,136 | 1.24 | 1.61 | 123,031 | 1.24 | 1.54 |
| syncbatch | 120 | 1.08 | 1.16 | 98.8 | 1.15 | 1.32 |
| getOne, latest | 844,453 | 1.20 | 0.87 | 527,429 | 1.10 | 0.88 |
| getOne, historical | 932,346 | 1.18 | 1.16 | 531,198 | 1.08 | 0.84 |
| getMany | 6,748,686 | 1.23 | 1.05 | 6,847,814 | 1.22 | 0.98 |
| open under 16 MB (s) | 0.921 | 1.18 | 0.50 | 0.991 | 1.14 | 0.50 |
| getOne under 16 MB | 145,587 | 1.24 | 0.67 | 44,310 | 1.23 | 0.41 |

Writes gain 1.24 to 1.38, reads 1.08 to 1.23; the close and a single
synced transaction (bound by the disk's force) gain nothing. Warm
startup on 10M keys: 0.91 s against 1.00 s at `-O2` and 2.49 s in Java
(50 MB), 4.11 s against 4.61 s and 10.5 s (200 MB). C now writes faster
than Java everywhere, reads in memory at 0.84 to 1.16 of Java's rate,
and under a small budget still at 0.41 to 0.67.

**Machine code** (012-15, 012-17): the library 196 kB at `-O2`, 170 kB
at `-Os` (LMDB: 53 kB), 236 kB at `-O2 -flto` with every external function
kept; in an application (`core_demo`, unused code stripped) 151 kB at
`-Os`, 170 kB at `-O2`, 178 kB at `-O2 -flto`.

**Lines**, all counted (comments and blank lines too), on 2026-10-29 at
`0935005`: 53,661 lines in the code files of `c/` (98 `.c`, 49 `.h`, 14
shell scripts, 12 Java files, the Python scripts):

| Part | Lines |
|---|---|
| `src/` (44 modules; 16,146 code lines by 006-08's count) | 21,226 |
| `include/bergdb.h` | 927 |
| `test/`: unit, functional and stress tests, the cross harness | 25,085 |
| `tools/`: the scanner, the dumper, the runner, the checkers | 4,463 |
| `bench/` | 1,322 |
| `examples/` | 424 |
| `build.sh`, `before-commit.sh` | 214 |

Beside the code: 26,835 lines of expected outputs, vectors and workloads
in `c/`, and 10,654 lines of Markdown in the item (the plans, the format
document, this report).


# 4. Departures from Java

Each with its reason in the task files: one caller at a time, no threads
(012-01, 4.2); a transaction is durable at `sync` or close, the buffer
written when full (012-13, `c/readme.md` section 9); a decided cut frees
disk at the next sync or open (012-11, Q1; section 6); a handle ends at
its close (012-13, Q2; section 6); a directory opened once per process
(012-09 part 1's question, decided in 012-13 as recommended); replicas,
encryption and the upper layers left out (012-01, section 1).


# 5. What the port found in Java

All registered in 005 (decision D5), none fixed in 012; C does as Java:

* **005-70, a correctness bug**: the STM's `KeyModSet` is empty after a
  start, so a transaction that read before a restart can commit where it
  is refused without the restart (012-02's audit, C4, with a probe).
* 005-71 (`DbClock`'s last read time not kept across a start), 005-72
  (the files after a physical cut depend on timing; the cross tests
  compare from the decided cut, its option A), 005-69 (`SystemClock`'s
  promise), 005-73 (seven small API findings), 005-74 (a negative node
  size makes the parser loop until the heap is gone), 005-75 (dead checks
  such as `checkIncreasingTime` and `validateTransactions`, and comments).


# 6. Decisions and open points

The questions the work raised for Frans, each with its answer; three
remain open: 1, 6's eviction sweep, and 7.

1. **005-70**, the STM after a start: fix Java soon (its option A, the
   new set's first time at the last transaction's)? Recommended: yes.
   **Open**: Frans will look at it later (07:35).
2. **012-02, Q1 and Q2** (its section 13): the comparison from the
   decided cut (done so, as 012-01 meant) and the restart findings
   registered (done); confirm. Recommended: confirm. **Confirmed** (12:41,
   12:45); 005-72 stays open to consider Q1's option B.
3. **012-11, Q1** (its section 6.4): C forces the stream itself when a
   cut is pending, so that the disk is freed without a sync. Recommended:
   yes. **Yes** (07:35); done in `1c9e888`.
4. **012-13, Q2** (its section 6.5): a closed handle ends at the close,
   as a `FILE` after `fclose` (implemented). Recommended: confirm.
   **Confirmed, no action** (07:35).
5. **D6b**: the format document to `docs/stream-format.md` is due now
   that 012-10 is done (012-01, section 11). Proposed: copy sections 1 to
   12 of 012-02 to `docs/stream-format.md`, kept up to date with the code
   from then on; 012-02 stays as the history (its review and questions);
   `core/doc-files/stream-format.txt` becomes a pointer. **No**: the
   document stays in the item (07:35; section 7).
6. **012-15's proposals** (all keep the bytes): `-flto` (+15 to +34
   percent on every figure), a bounded eviction sweep when D is over the
   budget. Recommended: a small task after 012-14. **`-flto`: yes**, as
   012-17 (added 12:51, started 13:59). **The eviction sweep: open.**
7. **005-69, 005-71 to 005-75**: when to fix, each entry has a
   recommendation. **Open.**
8. **012-14's open points** (14-robustness.md, section 6): one flipped
   bit of a record's time makes Java's start throw an `Error` and C's
   process abort (005-75); C could refuse it first as a format error (a
   prototype exists), or keep Java's behaviour until Java is fixed.
   Recommended: fix Java (005-75) and C together. Also: `-Werror` under
   gcc 16 (40 warnings, the library's 4 false positives), and the names
   of the exceptions C reports for read errors. **No action now** for the
   flipped time (07:35): C keeps Java's behaviour. The gcc warnings and
   the exceptions' names were not asked; they wait with 005-75.
9. **Where C lives and what tests it** (section 7). **Decided** (12:36):
   C stays a separate project in this item; its tests run by hand.

Frans's words, 2026-10-29. At 07:35, to the conductor's list of the same
morning (its numbers, not this section's): "1. Good catch. I will look at
it later." (005-70) "2. Do as recommended." (012-11's Q1) "3. Ok, no
action now." (012-13's Q2) "4. Do not move the format document." (D6b)
"5. No action now." (012-14's flipped time). At 12:36 on point 9: "No.
For now I want C to be a separate project. Keeps testing, scripts and
everything in 012. Tests can start manually. Good for now." At 12:41 on
012-02's Q1: "(a) is good as long as there is an item in 005 to consider
(b)"; at 12:45 on its Q2: "I confirm (a)."


# 7. The format document, the code's place, and next steps

* **The format document** stays 012-02 in this item (D6b changed by
  Frans, 2026-10-29: "Do not move the format document"). Being in a done
  item, it is history and is not kept up to date with Java; a change of
  Java's bytes after `decc677` is not in it.
* **The code** stays in `c/` (D1, "indefinitely for now"). Once 012 is
  done, the C clone follows Java no further by itself: a change of Java's
  bytes will make C's cross tests fail, but nothing runs them unless
  someone does. Frans chose option (c) (12:36, section 6). The options
  were: (a) run the C gate in `night.sh` (about 3 minutes; it builds
  Java's Core Layer for the cross tests), so that a Java change that
  breaks equality shows the next morning; (b) the C gate in
  `java/before-commit.sh`, which keeps them in step at every commit at
  about 3 minutes' cost; (c) nothing until a new item takes C up.
  Recommended was (a).
* **Next steps**, each a possible item, with a rough size from 012's
  pace:
  1. **Small fixes in C** (hours): `-flto` in the release build (+15 to
     +34 percent, 012-15; now 012-17), a bounded eviction sweep when D is
     over the budget, a faster close (an arena), the flipped record time
     with Java's 005-75 fix.
  2. **Java's fixes found by the port**: 005-70 (the STM after a start,
     a correctness bug), then 005-69 and 005-71 to 005-75; C follows each.
     And 005-79 (Frans, 2026-10-29): integers instead of doubles in the
     take, reclaim and eviction, so that every language and target gives
     the same bytes without floating point's traps.
  3. **Linux** (a day or two): the platform module (`plat`) is the only
     one that knows macOS; `F_FULLFSYNC` becomes `fdatasync`, and the
     cross sets run there.
  4. **An embedded target** (006-08's open questions): memory and writes
     at small startup distances, raw flash, 005-60's block storage. The
     C clone's 150 to 200 kB of code and its exact memory count are a
     start.
  5. **Readers in other threads**, which C left out (one caller).
  6. **A C trace exporter** for the Lean checker (`docs/trace-format.md`),
     so that C's runs are checked against the model directly.


# 8. How the work was done

Frans, 2026-10-29, 09:02: "This port to C is valuable in itself. And also
valuable as a capability test for AI porting. We might do similar jobs in
the future." This section is written for that: how an AI ported BergDB's
Core, what it took, and what to do again. The conductor's raw notes are
in `/Users/f/fl/bench/012/report-data.md` and its state file in
`/Users/f/fl/bench/012/state.md` (outside the repository).

## 8.1 The people and the tools

* **Frans** asked for the item, took the decisions D1 to D7, gave the
  go, and set the rules for effort and usage. He was away for most of the
  run.
* **Claude Opus 5.5 in Claude Code** (the VS Code extension, auto
  permission mode) did everything else: one *planning session*
  ("012-bergdb-c") and one *conductor session* ("f1-0f"), and the
  subagents the conductor started.
* F53, Frans's MacBook (Apple M1 Pro, 10 cores, 32 GB), with Apple clang
  21 and OpenJDK 27. No other tools.

## 8.2 The timeline

| When | What |
|---|---|
| 2026-10-27, evening | Frans's request ("Create item 012-bergdb-c ... a clone of the Core of BergDB written in C ... The stream format must be identical ..."); the planning session writes 012-01, the overview plan, while Frans is away, and then the task plans 012-02 to 012-16 |
| 2026-10-28, morning | Frans's decisions D1 to D7 and two comments (deterministic time needs the test clock; a plan for allocating and freeing memory), answered in 012-01, 4.4 and 4.5 |
| 2026-10-28, 13:05 to 13:40 | The plans reviewed against Java's `main` of that hour (the paced take, 005-52, 005-53) |
| 2026-10-28, 13:43 | Frans's go: the conductor's prompt pasted into a new session |
| 13:47 to 16:25 | Phase A: the format document with Java's scanner, the C API, the C project with its gate, the cross harness (M1) |
| 16:20 to 21:40 | Phase B: the C stream reader and scanner, the index nodes, the Dag and full replay (M2) |
| 17:09 to 23:26 | Phase C: the write path, startup and recovery (M3) |
| 22:32 to 03:17 | Phase D: reclaim, the memory budget (M4) |
| 2026-10-29, 02:16 to 06:14 | Phase E: the rest of the API, the measurements, robustness's first pass, the interim report; `news.md` at 06:17 |
| 07:35 to 10:49 | Frans's answers; the forced cut (012-11, Q1); robustness's rest (012-14 done 10:49); this report; 012 done |
| 12:36 to 12:51 | Frans, remote: C stays a separate project; 012-02's Q1 and Q2 confirmed; 012-17 (`-flto`) added as a plan |
| 13:59 to 14:04 | Frans: 012-17 started; developer mode enabled, the gate with the real `leaks` passes |
| 14:00 to 15:45 | 012-17: `-flto`, the gate, `cross.sh full` with the release tools, the timed runs (14:45 to 15:23); merged and gated in `main` |

The C that reads and writes Java's bytes, Levels 0 to 4, took 13.5 hours
from the go (13:43 to 03:17); with the API, the measurements and a first
pass of robustness, 16.5 hours (to 06:14). There were two pauses for the
usage window (15:02 to 15:53, and the first F53 gap) and two hand-overs of
the machine to another session's timed measurements (18:11 to 20:40,
23:55 to 01:11).

The milestones, with their commits:

| Milestone | When | Commit |
|---|---|---|
| M1, phase A: format, API, project, harness | 2026-10-28 16:25; 012-02's review 17:06 | `a6ba2d7`, `ab2dca4` |
| M2: C reads Java's databases | 21:40 | `74b08a3` |
| M3: Levels 0 to 2, C writes and restarts as Java | 23:26 | `1d1e2fb`, `3d9dcca` |
| M4: Levels 3 and 4 | 2026-10-29 03:17 | `e068fba`, `237d7c1` |
| Phase E: API and durability, measurements | 04:00, 05:06 | `7fd3704`, `0659ceb` |
| 012-11's Q1 (the forced cut), 012-14 done, this report | 09:50, 10:49, 10:49 | `1c9e888`, `8dde2aa` |

## 8.3 The prompts

Frans's words to the conductor, all of them:

* 13:43, the conductor's prompt (012-01, at its top), pasted with the
  night's rules: "You are the conductor of bergdb item 012, the C clone
  of BergDB's Core. Read items/012-bergdb-c/01-overview-plan.md in full,
  and 013-01 for the way of working. Then work through 012's tasks
  unattended, as its section 9 says, with the decisions of its section
  11. Start with phase A."
* 13:48: "Good luck! See you in the morning. Hope you have some
  impressive C clone for me to show by 07:00. Do your best to work
  unattended until then or until completion."
* 13:55: "I want at least Extra High for this work with the C clone. This
  is very important. The 5hr session limit must be followed, but the
  weekly is a later problem. Feel free to spend up to 75% of the weekly
  usage while you are working."
* 14:03: "What I really meant was that you can use up to 75% of the
  weekly budget before throttling usage because of it. Do not stop,
  continue beyond 75% if necessary. 012-02 at max was a good choice. Nice
  to see the coders at xhigh."
* 17:50, to another session that relayed it: "tonight 012 (session f1-0f)
  has priority on F53. The quiet block becomes flexible."
* 2026-10-29, 07:35: answers to five questions (section 6), and
  "Continue with 012 until it is finished. Run agents with Opus 5.5 High
  to preserve usage."; 07:40: "work unattended"; 09:02: this section's
  request.
* 12:36 to 12:45: where C lives, and 012-02's Q1 and Q2 (section 6).
* 12:47 and 12:51, on 012-15's first proposal: "build with -flto. Yes,
  why not? Tell me more."; "Just add subitem 17 for now."
* 13:59: "Yes to 012-17. Start an agent for it." 14:01: "Yes to
  "Rerunning the C gate". Use a separate agent. Developer mode is
  enabled. I will have lunch now. So, run unattended if possible."
  14:07: "Yes, commit and push when done."

Everything else came from the plans: each subagent's brief named its task
plan, the clone, the files it might write, the conventions shared with
the agents beside it, the hard stop, and the report's length.

## 8.4 The plans

* **012-01, the overview plan**: the goal and nine "Done when" items;
  what "identical bytes" takes, checked against the code before any line
  of C (the determinism of the stream, the inputs to fix, Java's
  arithmetic in C); what is ported, rewritten and left out; the rules of
  the design (one caller, no global state, the platform in one module,
  faithful before clever); the memory plan (counted references, frees at
  safe points); the C API's mapping; the build, the tests and the gate;
  the fifteen tasks in five phases with milestones; how the work runs
  unattended; the risks; the decisions.
* **The task plans 012-02 to 012-16**: each with its goal and "Done
  when", what to read in Java, the steps, the tests, notes and a Progress
  section, which the agents kept as they went, so that a stopped agent
  could be resumed from its file. Each plan is now also the record of its
  task.
* What the plans got right: the order (the format document with a Java
  scanner first; a cross harness that compared Java with Java before any
  C existed, so that C's tools could take side B one by one: the scanner,
  the dumper, the runner); byte equality as the single test of
  faithfulness; small node sizes and startup distances in the workloads.
  What the conductor changed: it split 012-09, 012-10 and 012-11 into a
  part that needed no earlier task and the rest, so that two agents could
  work at once on a mostly sequential plan; in practice the part-1 agents
  of 012-10 and 012-11 went on into the whole task.

## 8.5 Claude Code and Opus 5.5, as used

* **The conductor** (Opus 5.5 at its default xhigh) planned the order,
  wrote the briefs, read the reports and checked their claims (the diffs,
  the gate's output, the full runs), merged the clones (in scratch
  clones; the conflicts were the shared test tables and `Vectors.java`,
  resolved by keeping both sides), gated the combined tree in `main`,
  committed in Frans's name with path lists, pushed, and kept `news.md`,
  012's log and the 005 entries.
* **Subagents** (the Agent tool), one task each, in a git clone of their
  own under `/Users/f/fl/bench/012/`; 20 in all, two to four at a time.
  Their reports were about 20 lines; the details went into the task
  files.
* **Messages** (SendMessage) paused agents at a safe point for the usage
  window and for the machine's hand-overs, resumed them, and told them to
  pull `main` when a task they built on was merged.
* **Keeping going unattended**: check-ins every 20 minutes
  (CronCreate), one-off check-ins at the usage window's resets and the
  gaps' ends, a watchdog script (`caffeinate`, a log, `news.md` if the
  session died), a usage watcher (Claude Code's `/usage`, run headless
  every 5 minutes, which woke the conductor at 85 percent of the 5-hour
  window), and a state file. 013-01 and 013-02 describe the machinery.
* **Effort**, set on every agent: max for the format document and its
  review and for 012-07 to 012-10, the hardest tasks; xhigh for the rest;
  xhigh only once the week passed 75 percent (23:41); high from 07:35, at
  Frans's word. The two first agents started at high, as the usage level
  was tight, and were restarted at max and xhigh at 13:56 when Frans
  raised the effort.

| Task | Effort | Clock time |
|---|---|---|
| 012-02, the format document; its review | max; max | 13:47 to 16:16; 16:27 to 17:05 |
| 012-03, the C API | xhigh | 15:55 to 16:21 |
| 012-04, the C project | xhigh | 13:47 to 14:16 |
| 012-05, the cross harness | xhigh | 13:58 to 15:06 |
| 012-06, the stream reader | xhigh | 15:55 to 16:48 |
| 012-07, the index nodes | max | 16:20 to 17:30 |
| 012-08, the Dag and replay | max | 17:32 to 21:14, paused 18:11 to 20:53 |
| 012-09, the write path (two parts) | xhigh, max | 17:09 to 18:07; 20:55 to 22:14 |
| 012-10, startup | max | 21:32 to 23:23 |
| 012-11, reclaim; its Q1 | xhigh; high | 22:32 to 02:11, paused 23:55 to 01:12; 07:37 to 09:45 |
| 012-12, the memory budget | xhigh | 01:52 to 03:14 |
| 012-13, the API's rest | xhigh | 02:16 to 03:17 |
| 012-14, robustness (two passes) | xhigh; high | 05:00 to 06:13; 07:37 to 10:49 (in `main`) |
| 012-15, measurements | xhigh | 03:18 to 04:59 |
| The gate with the real `leaks` | high | 2026-10-29, 14:01 to 14:05 |
| 012-17, `-flto` | high | 2026-10-29, 14:00 to 15:28 |

## 8.6 Usage

The plan's usage, as Claude Code's `/usage` reports it for the whole
account: the week went from 49 percent at 13:45 on 2026-10-28 to 65
percent at 20:53, 76 percent at 01:52, 84 percent at 07:35, 88 percent at
09:51 and 91 percent at 10:49 on 2026-10-29 when 012-16 was done: about
42 points of a week in 21 hours. 012-17 and the afternoon's work took it
to 93 percent at 15:40. Other sessions worked in the same hours
(the 006-10 session until about 21:00, and its night's measurements), so
012's own share is somewhat less; the tool gives no figure per session.
The 5-hour window was the limit that bounded the pace: it reached the
conductor's pause point (85 percent) three times; the week passed 75
percent at 23:41, after which the conductor ran at most two agents, at
xhigh. The full log is `/Users/f/fl/bench/012/usage.log`.

## 8.7 What made it work, and what did not

* **Byte equality made faithfulness testable.** Every task's claim was
  checked by comparing C's files with Java's, so a wrong port could not
  pass as a right one. No byte difference was met in 012-09, and the
  mutations tried in 012-09 and 012-11 were all found.
* **The format document and Java's scanner first.** When the scanners'
  texts agree, a byte difference points at its field. The document's
  independent review at max effort found 2 errors and 5 omissions before
  any writer was written.
* **Java's own vectors and tests** (`Vectors.java`, Java's testers ported)
  checked each module against Java before the modules met.
* **Clones and a conductor that merges.** Agents never touched `main`;
  every merge was gated in a scratch clone and again in `main`.
* **The usage window, not the agent count, bounded the work**: more
  agents only reached the pause sooner. The pauses were used to hand the
  machine to another session's timed runs.
* **What went wrong**: the conductor wrote several log times without
  reading the clock (corrected in later commits); it once passed C's side
  to `cross.sh` as an environment variable instead of an argument (the
  run was killed and repeated); it first recorded Frans's morning answers
  against the wrong list (corrected). macOS's `leaks` began to hang on
  every program at about 08:30 on 2026-10-29, which stalled one agent's
  run for an hour before a check-in found it; the gate then ran with a
  stand-in that skips only the leak check, until Frans enabled developer
  mode at 14:01 and the real `leaks` passed (section 2, item 6).
* **For a next port**: the same shape (overview plan, task plans, a
  format document first, a harness that compares the two implementations
  from the start, byte or output equality as the test, clones and a
  conductor) should carry over to another language or another
  deterministic system. Plan the usage windows into the timeline, and
  give the conductor a list of what it may decide itself (012's plan did:
  the testing choices were left to it).
