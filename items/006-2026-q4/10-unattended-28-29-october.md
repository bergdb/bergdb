# 006-10 Unattended work, 28 to 29 October 2026

Created 2026-10-28 by Claude (Opus 5.5, Claude Code), at Frans's request.
Status: done (2026-10-29; see Outcome). The plan for the unattended work
from 2026-10-28, noon, to
2026-10-29, 07:00, the progress through the night, and the outcome. The way
of working is 013-01's, from 006-09. Lead: the session Unattended-006-09
(Frans, 09:34).


## 1. The request

Frans, 2026-10-28, 09:18: "You gave me proposed work for tonight. Create
006-10 for planning tonight's unattended work. Similar to 006-09 in way of
working."

The proposal was made at 08:40, from 006-09's Outcome, after Frans's
decisions of the morning (relayed to the session Unattended-006-09 at
09:12; 005-48 closed by Frans at 09:10, `3950a96`, with 005-64 for the
buffer time): one quiet block for 005-64's sweep, 009's 8-thread case
(005-65), 007-07's quick performance suite and `night.sh`.

**To answer before the work starts** (each with a recommendation):

1. **The lead session.** The session Unattended-006-09 works today on
   007-07 with D4:B, 009's closure (005-65) and 005-56, and has offered to
   prepare the next quiet block. Recommended: it leads this plan too, so
   that one session commits the day's `java/` changes and the night
   measures them; this plan is then its next plan. Or this session (f1-a5)
   leads, and Unattended-006-09 hands over what it has put in `main` by
   21:00.
2. **Commits.** The lead commits this plan's step scripts, entries and
   write-ups in Frans's name, as in 006-09. Nothing of this plan goes into
   `java/`. Recommended: yes.
3. **W4.1, 007-03's step 4 in Lean,** once 007-07 is in `main`: BergDB's
   take as a policy of the model. Recommended: yes, at max effort, as the
   next step of 007 (the top priority); stopped at 21:45 with its state
   written, if not done.
4. **W2, a fix for 005-65.** Recommended: tonight only the explanation; a
   fix (for example, a reader that evicts a batch itself instead of
   waiting) is a design choice for Frans, after the runs.
5. **W3 on s1 as well.** Recommended: yes, as 005-48's s1 tables are the
   baseline and s1's disk is not F53's; `ps` before the run.

Frans's answers, 2026-10-28:

1. 09:34: "You are the lead session for the planned 006-10 session too."
   The lead is Unattended-006-09.
2. 09:36: yes, as recommended: the lead commits in Frans's name.
3. 09:36: yes, as recommended: W4.1 at max effort once 007-07 is in
   `main`, stopped at 21:45 with its state written if not done; the
   005-62 session is asked first.
4. 09:36: the explanation only, as recommended; a fix is Frans's choice
   after the runs.
5. 09:36: yes, as recommended: W3 on s1 too, `ps` first.


## 2. Ground rules

013-01, section 4, with these for today:

* **Other sessions** (at 09:20). Unattended-006-09: 007-07 with D4:B, 009's
  closure and 005-65, 005-56, each with subagents in scratch clones. "005-62,
  Lean, handles": removes the design before handles from `lean/`. 005-63 is
  done (`322c5d1`, `74c8920`). 012-bergdb-c and sk26-7f are idle. This plan
  does not touch their entries; it measures 007-07 once that session has put
  it in `main`. A session still busy at 22:30 keeps the quiet check from
  passing, so each is asked to be idle by then.
* **Clones and outputs.** Work in `/Users/f/fl/bench/006-10/`. The step
  scripts go into their entries' `night/` directories; the raw output stays
  in `/Users/f/fl/bench/006-10/night/out/` and out of the repository.
* **Gates.** As 013-01. This plan changes no `java/` or `lean/` code but
  W4's; W4.1 needs a clean `lake build`, no `sorry` and no new axiom.
* **Smoke tests parse the output.** A step is READY only after `SMOKE=1`
  gave output that its summary script reads (013-01, section 9: Props).
* **`performance.sh` inside the conductor** runs with `FORCE=1`: the
  conductor has checked the machine already (013-01, section 9).
* **Subagents.** At most 4 at a time; effort high for the step scripts, max
  for Lean and for W2's reading.
* **`night.sh`** stays at 02:10.
* **News.** `tools/news.sh` as work finishes, fails or needs Frans; the
  summary by 07:00 on 2026-10-29.


## 3. The work, in order

The day's other work that the night depends on, not this plan's: 007-07
with D4:B (Unattended-006-09; in `main` after its gates, with 007-06's
step-2 runs on it), 009's closure and the new 005-65, and 005-56.

### W1. 007-07's performance check

007-07's section 8 leaves "the quick performance suite, in a quiet block".
Only if 007-07 is in `main` by 21:00; otherwise the steps are not READY and
the conductor skips them.

1. `performance.sh ab` with the quick suite, on two preserved builds: `main`
   just before 007-07 and `main` with it (ABBA, as `performance.sh` does).
   007-07 changes every stream: no scenario may lose more than its CV, and
   the startup and update scenarios are read first.
2. Props in turns on the same two builds, four rounds of each: MEM, CORE and
   SS.

Found while planning: last night's Props did run. The CORE line follows a
row of progress dots, and `nightsum.py` did not read it, so the summary
says "CORE ?" and the step exited 1. From the files in
`46-stream-file-lock/night/out/props/`: CORE 0.22 to 0.24 on HEAD and 0.23
to 0.24 on `bf19075`, four rounds each (lower is faster). So 005-46 needs
no rerun of Props; the parser is fixed before W1.2.

### W2. 005-65, readers waiting for the eviction thread with 8 threads

Last night's ScaleBench C from the OS's cache, 665 MB under ZGC, 8 threads:
the longest gets of 27 and 36 ms on HEAD (`bf19075`: 2.1 ms), with 22 and
26 waits of a reader's load for the eviction thread over 10 ms; with 4
threads under 6 ms. The step ran NOT QUIET. 009 is to be closed with this
case open in 005-65 (Frans, 09:12; Unattended-006-09 registers 005-65).

1. **Day: the reading.** Where a load waits for the eviction thread (when
   the resident bytes run ahead, the load waits for the next batch: 009-02,
   step 3d), and what the commits between `bf19075` and `4f7cd60` change on
   that path: 005-46 (`eaec93e`), 005-55 (`cec0032`), 005-57 (`07b6375`)
   and 005-51 (`c2aab10`, the eviction thread's waits). The hypothesis, in
   005-65: F53 is an M1 Pro with 8 performance cores; since 005-46 the
   readers no longer block on a file's monitor (`bf19075`: 3 to 13 percent
   of samples), so 8 readers take all 8 cores, and the eviction thread runs
   behind. What would refute it is written down first.
2. **Night: the runs.** ScaleBench C, 665 MB, ZGC, with 4, 6 and 8 threads,
   on three builds in turns, two rounds: `bf19075`, `eaec93e` (005-46 alone)
   and `4f7cd60` (last night's HEAD), with the eviction thread's CPU time and
   the waits counted as last night. If `eaec93e` has the waits, 005-46's
   faster readers are the cause; if only `4f7cd60`, one of the three others
   is.
3. **Morning.** The explanation and a recommendation in 005-65, for Frans.

### W3. 005-64, the buffer time: 20, 50 or 100 ms

1. **Day.** A suite in 005-64's directory from `performance-bufftime.suite`
   (Perf's `bufftime=`): writers that do not sync (`a-100`, `a-1k`,
   `a-1k-x100`; question 1) and writers that sync after each transaction
   (`d-t1`, `d-t16`, `d-t64`; question 2, a check), at 20, 50 and 100 ms;
   for question 3, mixed threads, a scenario or a small probe if Perf has
   none. Question 4's trickle (10 transactions a second) and idle runs with
   005-14's `procstat.c`. Question 5, the data at risk, is written out from
   the code; no runs.
2. **Night.** On F53 in the block, one build, the three buffer times in
   turns. On s1 the same suite in the background from 22:30, if Frans
   agrees (question 5 of section 1).
3. **Morning.** The tables and a recommendation in 005-64: keep 20 ms or
   change the default.

### W4. If there is time, in this order

1. **007-03's step 4,** once 007-07 is in `main` and if Frans agrees
   (question 3): BergDB's take as a policy in `lean/SIS/Bound.lean`, with
   the pace and the deadline as 007-07 and D4:B leave them, and T3 for runs
   with it (`KeepsUp`, d = d_h). In a clone, beside the 005-62 session's
   removals in `lean/`, which it is asked about first.
2. **005-53's options A to D for the Pub API,** once D4:B is in the core: a
   report, no code.

### Not tonight

Decisions: 005-05, 005-11, 005-47, and 012's D1 to D7 (Frans). Other
sessions': 005-56, 007-07, 009, 005-62. 005-52's Pub API needs an API
decision. 005-06, 005-07, 005-54 and 005-60 come later.


## 4. The principles (010)

Each piece is checked against 010-01; a departure is written there, under
its principle. Across all of it: no new setting (P10), no global state
(P9), no new timer or polling thread (P3), and the simple solution first
(P11).

| Work | Principles | What they ask of it |
|---|---|---|
| W1, 007-07 | P4, P5, P2 | A commit's index writes in proportion to its own size, with no throughput lost for it; the section bounded; the stream deterministic (007-07's StreamDigest) |
| W2, 005-65 | P1, P11 | BergDB's own waits at most about 20 ms, readers included; the explanation before any fix |
| W3, 005-64 | P3, P10, P2 | Fewer wake-ups while data trickles in; a default, not a new setting; the stream's bytes the same at any buffer time |
| W4.1, step 4 | P5 | The bound proved for the take that Java runs |


## 5. Timeline

Times in CET. Two windows for the quiet block, as in 006-09: 22:30 to 02:05,
and from `night.sh`'s end (about 03:00) to 06:15.

| Time | What |
|---|---|
| 09:20–11:30 | The plan with Frans; this file |
| by 12:00 | The conductor started, the check-ins scheduled (section 6) |
| 12:00–19:00 | W2.1 and W3.1 in clones; W4 if 007-07 is in `main` and there is room |
| 19:00–21:30 | W1's builds preserved; every step smoke-tested and READY |
| 21:45 | CPU-heavy work stops, Lean included; the conductor's steps checked |
| 22:30–02:05 | Window 1 on F53, the lead idle: W1, W2, W3; W3 on s1 in the background |
| 02:10–03:00 | `night.sh`, from launchd |
| 03:00–06:15 | Window 2, for what did not fit |
| 06:15–07:00 | Results into 007-07, 005-65 and 005-64; the Outcome; the summary in `news.md` |

The quiet block's steps, with their minutes (estimates; each script's
`# minutes:` line sets its own):

| Step | Where | Minutes | Condition |
|---|---|---|---|
| W1.1 `performance.sh ab`, quick | F53 | 40 | 007-07 in `main` |
| W1.2 Props in turns | F53 | 15 | the same |
| W2.2 ScaleBench C, 3 builds, 4 to 8 threads | F53 | 75 | |
| W3.2 the buffer-time suite | F53 | 90 | |
| W3.2 trickle and idle | F53 | 25 | |
| W3.2 the buffer-time suite | s1 | 60 | question 5 |

About 4 hours on F53, against about 6.5 hours of windows, so a step that
waits 30 minutes for quiet still fits.


## 6. If this session stops

As 013-01, section 6:

* **The conductor**, 013-01's `conductor.sh`, copied to
  `/Users/f/fl/bench/006-10/night/` with `BASE` and its news text set to
  006-10, started with `nohup caffeinate -i` by 12:00; `steps.txt` lists
  the steps of section 5. At 06:50 it writes a short summary if
  `summary-written` is missing.
* **Check-ins**, 013-01's prompts (section 10): every hour from 12:17 to
  21:17, at 21:41, and at 05:57, 06:27 and 06:44.
* **State** in this file's progress section, the entries' State notes, and
  a `state.md` in the lead's scratchpad.


## 7. Progress

2026-10-28, 09:21. The draft plan written by the session f1-a5, from the
proposal of 08:40 and 013-01; waits for Frans's answers to section 1.

2026-10-28, 09:23. Unattended-006-09 on the draft: no conductor or
check-ins of its own until Frans names the lead. Its 009 agent fixes
Props' parser (the smoke test checks the parsed CORE) and writes W2.2's
night script on `bf19075`, `eaec93e` and `4f7cd60`; its 007-07 agent aims
to be gated by about 19:30, so that W1 can run. W3's script is not written
yet.

2026-10-28, 09:37. Frans named the lead (09:34) and answered questions 2
to 5 as recommended (09:36). In `main` since the draft: 005-56 (`04f1546`,
`43bdb09`); 009 closed and 005-65 registered (`fab16db`, `bf9fc7f`);
Props' parser fixed (`e10b928`), so W1.2 can use `props.sh` with `JARS`.
W2.2's script is 005-65's `night/threads.sh`, smoke-tested on its parsed
summary, with its builds in `/Users/f/fl/bench/006-09/d2-009-builds`.
007-07 with D4:B still runs (a subagent at max effort).


2026-10-28, 10:08. W3.1 done (`da371c0`): 005-64's `night/run-f53.sh` (90
minutes, up to 9 rounds of 20, 50 and 100 ms rotated, MixedProbe for
question 3), `trickle.sh` (26 minutes, question 4) and `run-s1.sh` (60
minutes), on the preserved build `main-bf9fc7f` (before 007-07; the buffer
time does not depend on it); question 5 written from the code. Each smoke
test passed its parse check (every expected row, every cell); s1 idle and
its smoke mode OK. In `steps.txt` with READY markers. Also in `main`:
005-66 (another session, `83b7ac0`), 005-56's follow-ups with the Core
Layer built alone nightly in `night.sh` (`43e631f`), 010-01's P12
(`64af8da`).

2026-10-28, 10:20. W2.1 done (`67c1c54`, `cfdc901`): 005-65's reading. A
reader's load enters `evictorLock` in `Eviction.wake` after a slow-path load,
unbounded; it parks for a batch only under pressure, which last night never
reached, so the waits over 10 ms were at the monitor's entry. The likely
commit is `eaec93e` (005-46: all 8 readers runnable, 1.8 times the gets and
loads); ZGC cleared. Five hypotheses with predictions; the measurement now
tells them apart (after-load calls by pressure, gets over 10 ms, blocked
times, the machine's busy cores). `prep.sh` made again, `threads.sh`'s smoke
OK with the new tables, READY again.

2026-10-28, 11:05. 005-67 done, at Frans's request (`5dc6954`, `dad6bd2`,
`058eca2`): `StorageManagerTester.testAddReplica2` asserted the lengths
before the replica's buffer had written them (and once a buffer had written
more); the test was wrong, not the code. Forced by sleeps: 97 to 100 of 100
before, 0 after; 4 failures in 40,000 runs before, 0 in 400,000 after;
`before-commit.sh`, `core-build.sh` and `level2.sh quick` pass. Also found:
`testAddReplicaWhileAppending` appended without the write lock (fixed), and
for 005-11 a replica being copied in when the manager closes is never
closed (not fixed; for the Outcome). 005-62 is done in `main` (`90153f2`,
its session), so `lean/` is free for W4.1 once 007-07 is in.

2026-10-28, 11:58. 007-07 with D4:B in `main` (`f89846d`, `b4aa91c`), so W1
runs tonight: the deadline is streamLength − max(2·sd, span), the span from
the oldest section transaction to the newest, so after a decrease it comes
down with the lag and never jumps, with no stored distance (a start rebuilds
the span; no format change); a raise needs nothing. Gates full: before-commit,
level2 (BryanRepro 40 cycles, 0 failures), level3, level4. StreamDigest: the
patched build's two runs identical. 007-06's step 2 again: a one-call decrease
from 1000 to 100 MB writes records of at most 3.6 MB (486 MB with the patch
alone), the section below 2 sd after 0.6M puts and then at 1.04 to 1.10 sd.
W1's steps READY: 007-07's `night/run-quick.sh` (40 minutes) and
`night/props-ab.sh` (`eeda4e5`; a copy of 005-46's `props.sh` outside the
repository, on `main-cefb473` and `d4b-f89846d` in
`/Users/f/fl/bench/006-10/w1props`; smoke parsed). W4.1 started: step 4 in
Lean, a subagent at max effort, hard stop 21:45. 007-07's open points for the
Outcome: the 200 kB padding counted as the record's own bytes, the deadline's
extra takes during a catch-up, P1's and P2's bullets in 010-01, 50M keys.

2026-10-28, 12:15. W4.2 done (`22c9874`): 005-53 and 005-52 ready to
decide. 005-53: a new option E recommended, `Database.setStartupDistanceInMb`
and a getter, kept in the stream's meta blocks; one call is enough since
D4:B; B and D (a `Job`) obsolete. 005-52: B recommended, a setter and getter
for the cache size, clamped as the builder, for the run only. Both as one
pattern and one commit: a setting that changes the stream's bytes is kept
in the stream (P2), one that does not lasts for the run. Questions with
recommended answers in both entries; for Frans.

2026-10-28, 12:35. Frans (12:32): "53 and 52. Yes, do this as
recommended.", the smaller questions "as recommended", and "Start subagents
for the tasks." Started, each with a hard stop at 21:30: 005-53's E with
005-52's B in the code (one commit, gates before-commit, level3 and level4
full); 010-01's P1 and P2 lines after 007-07; 007-07's runs at 50M keys
(byte counts, on F53 at the lowest priority or on s1 before 21:30). With
W4.1, four agents.

2026-10-28, 12:45. W4.1 done (`db1eca8` to `8b6669f`): 007-08, step 4 of
007-03. BergDB's take as a policy in `lean/SIS/Bound.lean` (`javaTake`,
checked against Java's `TransSeq.take` on 300 cases), and T3 for it: the
section stays below 2·M while the setting stays at most M (`T3_take`, with
restarts); after a decrease to sd' it ends below 2·sd' or shrinks by at
least one unit a transaction (`T3_take_decrease`); what startup reruns and
reads (`T3_take_rerun`, `T3_take_reads`). The plan's `KeepsUp` is false
with D4:B, shown by a `#guard`. `lake build` clean, axioms standard. Also
010-01's P1 and P2 after 007-07 (`b362a8b`). An independent review of 007-08
at max effort started.

2026-10-28, 13:06. 007-08's review done (`f5a09cf`): faithful to
`TransSeq.take` but for the record limit and the meta blocks, not vacuous,
no error in a definition, statement or proof; `lake build` and the axioms
checked again. To fix: one wrong comment ("never costs more than after
T(m)" holds only when that section is at least 2·sd'), README.md's "Bounded
startup is proved" says more than T3, and the unused trusted definitions to
be marked so. For Frans: the 128-byte meta-block gap at records ending on a
200,000-byte boundary; `take` given `getNextPos()` instead of `getLength()`
would make the model exact (a code change).

2026-10-28, 13:10. Frans: "as recommended" on 007-08's three questions
(keep `share`, `dither` and `javaPace` with a note; record lengths in the
traces later; no model of how fast the section comes down) and on the
review's code point: `take` given `getNextPos()`, as a new fix entry with
StreamDigest. A subagent does both and the review's small fixes, hard stop
21:30.

2026-10-28, 13:14. 005-53 (E) and 005-52 (B) in `main` (`fd8f513`,
`ce5c489`): `Database.setStartupDistanceInMb`, `getStartupDistanceInMb`,
`setCacheSizeInMb`, `getCacheSizeInMb`; `Db.setCacheSizeIndicator` and its
getter (Db 43 to 45 public methods), JMX through them; a lowered budget
wakes the eviction thread, so an idle database gives memory back (20 MB to
4 MB with no further calls). Gates: before-commit, level3 and level4 full,
level2 quick; StreamDigest identical (36 of 36). Left for the Outcome:
005-52's pause probe with a lowered budget (a quiet block), and the retain
duration, which changes the stream's bytes but is not kept in the stream.

2026-10-28, 13:25. The review's small fixes in `main` (`3d21792`: the
comment of `T3_take_decrease`, README.md's and docs/levels.md's wording,
the unused trusted definitions marked, Frans's answers in 007-08; `lake
build` clean, trace tests OK). The review's code point did not hold: a
record that ends on a 200,000-byte boundary has its meta block written in
the same append, so `getLength()` equals `getNextPos()` whenever `take` runs
(0 of 5,524,901 calls differed); 005-68 registered and dropped (`3c4f535`),
no code changed. At Frans's request (13:20) 012's plan committed as it is,
decided and not started (`eff970d`), and `main` pushed to `origin`; the old
012 entry in `news.md` removed, as D1 to D7 are decided.

2026-10-28, 16:00. 007-07 at 50M keys done (`3c6b545`, 007-07 section 11):
the whole set of 12 runs on F53 at the lowest priority, 12:36 to 15:55.
Steady: the section at most 1.11 sd (10M: 1.10), no record over 2.3 times
the mean; the long delete run (16.6 sd of stream) at most 1.06 sd. After a
one-call decrease the section shrinks at every record and stays below the
new 2 sd, in fewer puts than at 10M. But the largest record of a decrease
grows with the keys: 13.3 to 15.4 MB from 1000 to 100 MB (10M: 3.3 to 3.6
MB), put down to the pace's factor S/sd (up to 10), not the deadline; a cap
is a decision for Frans, for the Outcome. 100M keys needs more heap than
F53 has. No agent runs now.

2026-10-28, 17:58. Frans, 17:50: tonight 012 (session f1-0f) has priority
on F53, and the quiet block becomes flexible. The conductor is stopped;
the six steps run in 012's gaps: f1-0f writes "quiet until HH:MM" to
`/Users/f/fl/bench/f53-owner.txt` and tells this session, which starts
`gaprun.sh` (in `/Users/f/fl/bench/006-10/night/`, from the conductor: a
step only if its minutes plus 5 end before HH:MM, the same quiet check for
at most 10 minutes, the same results files; "012" written back at the
end). 64-s1 runs on s1 since 17:55. Frans also asked to unload the 02:10
`night.sh` and run it by hand in a gap; this session's permissions refused
the `launchctl bootout`, so `night.sh` stays at 02:10 and f1-0f was asked
to keep F53 quiet from 02:05 to about 03:00. A fallback news entry at 06:50
(`fallback.sh`), and check-ins every hour through the night.

2026-10-28, 20:41. 012's first gap, 18:11 to 20:50 (handed back at 20:40),
ran five steps: `night.sh` (by hand; session f1-ea unloaded the 02:10 job at
18:00 at Frans's request) NIGHT FAILED only in level1's SS limits, SS3
1.65 against 1.63 and SS4 2.40 against 2.38, after 007-07's paced take,
every other step OK; 007-07's quick suite, 005-65's thread sweep, 005-64's
trickle and Props before and after 007-07, all exit 0; most marked not
quiet after the 10-minute check. 64-s1 exit 0 on s1. Left: 64-f53 (90
minutes), if 012 gives a gap of 95 minutes.

2026-10-29, 01:12. 012's second gap, 23:55 to 01:50 (handed back at
01:11): 005-64's F53 runs, all 9 rounds in 65 minutes, exit 0, every row
parsed (marked not quiet after the 10-minute check). Every step of the night
is done; F53 is 012's until the morning.

## 8. Outcome

2026-10-29, 06:04, by Claude (Opus 5.5, Claude Code).

**Done, in `main`, on 28 October** (in Frans's name; code gated in clones on
trees with the changes before it; `main` pushed at 13:24):

* 005-48 closed at 20 ms, 005-64 registered (`3950a96`).
* 005-56, the package lists and `java/deps.py` in `before-commit.sh`
  (`04f1546`, `43bdb09`); its follow-ups, with the Core Layer built alone
  nightly in `night.sh` (`43e631f`, `64af8da`).
* 009 closed (`bf9fc7f`); 005-65 registered (`fab16db`) and read
  (`67c1c54`, `cfdc901`); Props' parser (`e10b928`).
* 005-67, `testAddReplica2`: the test was wrong (`dad6bd2`, `058eca2`).
* 007-07, 007-03's step 3 with D4:B (`f89846d`, `b4aa91c`); at 50M keys
  (`3c6b545`); 010-01's P1 and P2 (`b362a8b`).
* 007-08, step 4 in Lean, T3 for BergDB's take (`db1eca8` to `8b6669f`),
  reviewed at max effort (`f5a09cf`), the review's fixes (`3d21792`);
  005-68 registered and dropped, as the review's code point did not hold
  (`3c4f535`).
* 005-53 (E) and 005-52 (B): the startup distance and the cache size
  change while the database runs (`fd8f513`, `ce5c489`).
* 013-ai-work with 013-01 (`cb5baa0`); 012's plan committed (`eff970d`).
* Other sessions the same day: 005-62 (`90153f2`), 005-63 and 005-66, 013-02,
  and 012's first unattended run (012-04 to 012-16's interim report).

**The night**, in 012's gaps (Frans, 17:50: 012 first on F53; the conductor
stopped at 17:55): gap 1, 18:11 to 20:40, and gap 2, 23:55 to 01:11. Every
step ran, all but `night.sh` with exit 0; most were marked not quiet after
the 10-minute check (the machine at 82 to 86 percent idle).

* `night.sh`, by hand (session f1-ea unloaded the 02:10 job at 18:00, at
  Frans's request; loaded again at 05:58): NIGHT FAILED only in level1's SS
  limits, after 007-07 (below); every other step OK (report
  `java/build/night/2026-10-28-1822/report.txt`).
* 007-07's quick suite and Props (007-07, section 12, `234c852`): no alerts;
  with finite retention commit p99 and p99.9 9 to 11 percent higher, the
  median faster; startup 1 to 4 percent slower; MEM 130 to 129, CORE 0.237
  to 0.240; SS3 1.62 to 1.65 and SS4 2.37 to 2.40.
* 005-65 (`71beee8`): with 8 readers and ZGC F53 runs at 9.6 of 10 cores
  (since 005-46 the readers no longer block on a file), and readers enter
  `evictorLock` 78,000 times a second (3,000 with 4); those calls explain
  about a fifth of the gets over 10 ms. The eviction thread does not fall
  behind; other processes and later commits are ruled out.
* 005-64 (`c802258`): 100 ms costs 13 to 16 percent of the puts a second and
  slows a rare sync (p50 5.6 to 8.4 ms) and saves no energy; 50 ms saves 11
  to 35 percent of the forces at twice the data at risk; syncing writers
  and idle are the same at every buffer time. On F53 and s1.

**For Frans to decide** (each with a recommendation):

1. level1's SS limits: `night.sh` fails on `main` until they change.
   Recommended: `SS_MAX="1.52 1.11 1.21 1.66 2.41"` with the reason in
   `docs/log.md` (drafted in 007-07, section 12.3: since 005-49 the setting
   is the section's target, so at Props' 50 MB the take writes more).
2. 005-64: the buffer time. Recommended: keep 20 ms, and close 005-64; the
   replica's 2,000 ms (question 6) waits for 005-11.
3. 005-65: a fix. Recommended: loads skip `evictorLock` when a request is
   already pending (a volatile flag, re-checked under the lock; about 20
   lines, a race test, one `threads.sh` run), and the rest accepted as a
   full machine, outside 009's target.
4. 007-07 at 50M keys: the largest record of a decrease grows with the keys
   (13 to 15 MB from 1000 to 100 MB, against 3.5 MB at 10M), from the pace's
   factor S/sd (up to 10). Recommended: a 005 entry to test a cap of that
   factor at 10M and 50M keys.
5. 007-07's quick suite: commit p99 up 9 to 11 percent with finite
   retention, not yet explained. Recommended: look at it with point 4.
6. The retain duration changes the stream's bytes but is not kept in the
   stream, against the rule of 005-53 and 005-52. Recommended: a 005 entry
   to decide: keep it in the stream, or say so in its Javadoc.
7. 005-11: a replica being copied in when the database closes is never
   closed, its directory locked until the JVM ends (005-67's probe).
   Recommended: note it in 005-11, fixed with 005-11's decision.
8. 005-52's pause probe with a lowered budget, not run (a quiet block).
   Recommended: in the next quiet block.
9. Small, 007-08: the fourth counterexample as a `#guard`, and README's
   "the meta blocks are not modelled", which 005-68 showed make no difference
   to the take. Recommended: both, small.

Not this plan's: 012-16's interim report has seven points for Frans (from
the 012 session).

**Frans's decisions, 2026-10-29 morning:**

1. A: level1's SS limits raised (`f6fc56b`); also, at his word, `MEM_MAX`
   lowered from 228 to 131 (`f648f96`).
2. The default buffer time is 50 ms, for fewer forces (SSD wear, torn
   pages) at about twice the unsynced data at risk (`27ec238`; 005-64
   done); 005-76 registered for the rest: wake the consumer when the
   buffer passes a quarter (`d5c2c4b`).
3. A: 005-65's fix, loads skip `evictorLock` when a request is pending,
   and the rest accepted as a full machine; under way, the thread sweep
   again in the next quiet block.
4. A: 005-77, cap the pace's factor S/sd (`bcc7d3b`).
5. The quick suite's p99 question added to 005-77 (`f6b8ab9`).
6. 005-78, the retain duration is to be kept in the stream (P2), an
   investigate entry, to be studied first (`08da06e`).
7. The replica leak noted in 005-11 (`49029f3`).
8. 005-52's pause probe in the next quiet block.
9. The fourth counterexample a `#guard`, the meta-block wording softened
   (`9cf8a82`); `lake build` clean, trace tests OK.

**Left:** nothing of the night's steps; points 1 to 9 above. The raw output
of the night is in `/Users/f/fl/bench/006-10/night/out/`, out of the
repository.
